use anyhow::Result;
use everscale_types::cell::{Cell, CellBuilder, CellFamily, Store};
use everscale_types::models::{
    BouncePhase, ExecutedBouncePhase, Lazy, MsgInfo, NoFundsBouncePhase, StorageUsedShort,
};
use everscale_types::num::Tokens;

use crate::phase::receive::ReceivedMessage;
use crate::util::{
    check_rewrite_dst_addr, new_varuint56_truncate, ExtStorageStat, StorageStatLimits,
};
use crate::ExecutorState;

/// Bounce phase input context.
pub struct BouncePhaseContext<'a> {
    /// Gas fees from the compute phase (if any).
    pub gas_fees: Tokens,
    /// Action fine from the action phase (if any).
    pub action_fine: Tokens,
    /// Received message (internal only).
    pub received_message: &'a ReceivedMessage,
}

impl ExecutorState<'_> {
    /// Bounce phase of ordinary transactions.
    ///
    /// - Tries to send an inbound message back to the sender;
    /// - Defined only for internal inbound messages;
    /// - Remaining message balance is substracted from the account balance;
    /// - Fees are paid using the remaining inbound message balance;
    ///
    /// Returns an executed [`BouncePhase`].
    ///
    /// Fails if the origin workchain of the message doesn't exist or
    /// disabled. Can also fail on [`total_fees`] overflow, but this should
    /// not happen on networks with valid value flow.
    ///
    /// [`total_fees`]: Self::total_fees
    pub fn bounce_phase(&mut self, ctx: BouncePhaseContext<'_>) -> Result<BouncePhase> {
        let mut info = ctx.received_message.root.parse::<MsgInfo>()?;
        let MsgInfo::Int(int_msg_info) = &mut info else {
            anyhow::bail!("bounce phase is defined only for internal messages");
        };

        // Reverse message direction.
        std::mem::swap(&mut int_msg_info.src, &mut int_msg_info.dst);
        if !check_rewrite_dst_addr(&self.config.workchains, &mut int_msg_info.dst) {
            // FIXME: Just ignore this phase in that case? What if we disable
            // the message origin workchain and this message bounces? However,
            // for that we should at least have other workchains .
            anyhow::bail!("invalid destination address in a bounced message");
        }

        // Compute additional full body cell.
        let full_body = if self.params.full_body_in_bounce {
            let (cell, range) = &ctx.received_message.body;
            Some(if range.is_full(cell.as_ref()) {
                cell.clone()
            } else {
                CellBuilder::build_from(range.apply_allow_special(cell.as_ref()))?
            })
        } else {
            None
        };

        // Overwrite msg balance.
        let mut msg_value = ctx.received_message.balance_remaining.clone();

        // Compute message storage stats.
        let stats = 'stats: {
            let mut stats = ExtStorageStat::with_limits(StorageStatLimits {
                bit_count: self.config.size_limits.max_msg_bits,
                cell_count: self.config.size_limits.max_msg_cells,
            });

            // Root cell is free, but all children must be accounted.
            'valid: {
                // Msg value can contain some cells.
                if let Some(extra_currencies) = msg_value.other.as_dict().root() {
                    if !stats.add_cell(extra_currencies.as_ref()) {
                        break 'valid;
                    }
                }

                // We must also include a msg body if `params.full_body_in_bounce` is enabled.
                if let Some(body) = &full_body {
                    if !stats.add_cell(body.as_ref()) {
                        break 'valid;
                    }
                }

                // Exit this block with a valid storage stats info.
                break 'stats stats.stats();
            }

            // Fallback to NoFunds if the returned message cannot fit into the limits.
            // We require an "infinite" amount of tokens here if storage overflows.
            let stats = stats.stats();
            return Ok(BouncePhase::NoFunds(NoFundsBouncePhase {
                msg_size: StorageUsedShort {
                    bits: new_varuint56_truncate(stats.bit_count),
                    cells: new_varuint56_truncate(stats.cell_count),
                },
                req_fwd_fees: Tokens::MAX,
            }));
        };

        // Compute forwarding fee.
        let use_mc_prices = self.address.is_masterchain() || int_msg_info.dst.is_masterchain();
        let prices = self.config.fwd_prices(use_mc_prices);

        let mut fwd_fees = prices.compute_fwd_fee(stats);
        let msg_size = StorageUsedShort {
            cells: new_varuint56_truncate(stats.cell_count),
            bits: new_varuint56_truncate(stats.bit_count),
        };

        // Try to substract all fees from the remaining message balance.
        msg_value.tokens = match msg_value
            .tokens
            .checked_sub(ctx.gas_fees)
            .and_then(|t| t.checked_sub(ctx.action_fine))
        {
            Some(msg_balance) if msg_balance >= fwd_fees => msg_balance,
            msg_balance => {
                return Ok(BouncePhase::NoFunds(NoFundsBouncePhase {
                    msg_size,
                    req_fwd_fees: fwd_fees - msg_balance.unwrap_or_default(),
                }));
            }
        };

        // Take message balance back from the account balance.
        self.balance.try_sub_assign(&msg_value)?;

        // Split forwarding fee.
        let msg_fees = prices.get_first_part(fwd_fees);
        fwd_fees -= msg_fees;
        self.total_fees.try_add_assign(msg_fees)?;

        // Finalize message.
        int_msg_info.ihr_disabled = true;
        int_msg_info.bounce = false;
        int_msg_info.bounced = true;
        int_msg_info.value = msg_value;
        int_msg_info.ihr_fee = Tokens::ZERO;
        int_msg_info.fwd_fee = fwd_fees;
        int_msg_info.created_lt = self.end_lt;
        int_msg_info.created_at = self.params.block_unixtime;

        let msg = {
            const ROOT_BODY_BITS: u16 = 256;
            const BOUNCE_SELECTOR: u32 = u32::MAX;

            let body_prefix = {
                let (cell, range) = &ctx.received_message.body;
                range
                    .apply_allow_special(cell.as_ref())
                    .get_prefix(ROOT_BODY_BITS, 0)
            };

            let c = Cell::empty_context();
            let mut b = CellBuilder::new();
            info.store_into(&mut b, c)?;
            b.store_bit_zero()?; // init:(Maybe ...) -> nothing$0

            if b.has_capacity(body_prefix.size_bits() + 33, 0) {
                b.store_bit_zero()?; // body:(Either X ^X) -> left$0 X
                b.store_u32(BOUNCE_SELECTOR)?;
                b.store_slice_data(body_prefix)?;
                if let Some(full_body) = full_body {
                    b.store_reference(full_body)?;
                }
            } else {
                let child = {
                    let mut b = CellBuilder::new();
                    b.store_u32(BOUNCE_SELECTOR)?;
                    b.store_slice_data(body_prefix)?;
                    if let Some(full_body) = full_body {
                        b.store_reference(full_body)?;
                    }
                    b.build()?
                };

                b.store_bit_one()?; // body:(Either X ^X) -> right$1 ^X
                b.store_reference(child)?
            }

            Lazy::from_raw(b.build()?)
        };

        // Add message to output.
        self.out_msgs.push(msg);
        self.end_lt += 1;

        // Done
        Ok(BouncePhase::Executed(ExecutedBouncePhase {
            msg_size,
            msg_fees,
            fwd_fees,
        }))
    }
}
