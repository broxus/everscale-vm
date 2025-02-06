use anyhow::Result;
use everscale_types::models::{CurrencyCollection, IntAddr, MsgInfo, StateInit};
use everscale_types::prelude::*;

use crate::util::{ExtStorageStat, StorageStatLimits};
use crate::ExecutorState;

impl ExecutorState<'_> {
    /// "Pre" phase of ordinary transactions.
    ///
    /// - Validates the inbound message cell;
    /// - For internal messages updates an LT range;
    /// - For external messages charges a fwd fee
    ///   (updates [`self.balance`] and [`self.total_fees`]).
    ///
    /// Returns a parsed received message ([`ReceivedMessage`]).
    ///
    /// Fails if the message is invalid or can't be imported.
    ///
    /// [`self.balance`]: Self::balance
    /// [`self.total_fees`]: Self::total_fees
    pub fn receive_in_msg(&mut self, msg_root: Cell) -> Result<ReceivedMessage> {
        let is_masterchain = self.address.is_masterchain();

        let is_external;
        let bounce_enabled;
        let mut msg_balance_remaining;

        // Process message header.
        let mut slice = msg_root.as_slice_allow_pruned();
        match MsgInfo::load_from(&mut slice)? {
            // Handle internal message.
            MsgInfo::Int(info) => {
                self.check_message_dst(&info.dst)?;

                // Update flags.
                is_external = false;
                bounce_enabled = info.bounce;

                // Update message balance
                msg_balance_remaining = info.value;
                msg_balance_remaining.try_add_assign_tokens(info.ihr_fee)?;

                // Adjust LT range.
                if info.created_lt >= self.start_lt {
                    self.start_lt = info.created_lt + 1;
                    self.end_lt = self.start_lt + 1;
                }
            }
            // Handle external (in) message.
            MsgInfo::ExtIn(info) => {
                self.check_message_dst(&info.dst)?;

                // Update flags.
                is_external = true;
                bounce_enabled = false;

                // Compute forwarding fees.
                let Some(mut stats) =
                    ExtStorageStat::compute_for_slice(&slice, StorageStatLimits {
                        bit_count: self.config.size_limits.max_msg_bits,
                        cell_count: self.config.size_limits.max_msg_cells,
                    })
                else {
                    anyhow::bail!("inbound message limits exceeded");
                };

                stats.cell_count -= 1; // root cell is ignored.
                stats.bit_count -= slice.size_bits() as u64; // bits in the root cells are free.

                let fwd_fee = self
                    .config
                    .fwd_prices(is_masterchain)
                    .compute_fwd_fee(stats);

                // Deduct fees.
                if self.balance.tokens < fwd_fee {
                    anyhow::bail!("cannot pay for importing an external message");
                }
                self.balance.tokens -= fwd_fee;
                self.total_fees.try_add_assign(fwd_fee)?;

                // External message cannot carry value.
                msg_balance_remaining = CurrencyCollection::ZERO;
            }
            // Reject all other message types.
            MsgInfo::ExtOut(_) => anyhow::bail!("unexpected incoming ExtOut message"),
        }

        // Process message state init.
        let init = if slice.load_bit()? {
            Some(if slice.load_bit()? {
                // State init as reference.
                let state_root = slice.load_reference()?;
                anyhow::ensure!(
                    !state_root.is_exotic(),
                    "state init must be an ordinary cell"
                );

                let mut slice = state_root.as_slice_allow_pruned();
                let parsed = StateInit::load_from(&mut slice)?;
                anyhow::ensure!(slice.is_empty(), "state init contains extra data");

                MsgStateInit {
                    hash: *state_root.repr_hash(),
                    parsed,
                }
            } else {
                // Inline state init.
                let mut state_init_cs = slice;

                // Read StateInit.
                let parsed = StateInit::load_from(&mut slice)?;
                // Rebuild it as cell to get hash.
                state_init_cs.skip_last(slice.size_bits(), slice.size_refs())?;
                let state_root = CellBuilder::build_from(state_init_cs)?;

                MsgStateInit {
                    hash: *state_root.repr_hash(),
                    parsed,
                }
            })
        } else {
            None
        };

        // Process message body.
        let body = if slice.load_bit()? {
            // Body as cell.
            let body_cell = slice.load_reference_cloned()?;
            anyhow::ensure!(slice.is_empty(), "message contains extra data");

            let body_range = CellSliceRange::full(body_cell.as_ref());
            (body_cell, body_range)
        } else {
            // Inline body.
            let body_range = slice.range();
            (msg_root.clone(), body_range)
        };

        // Done
        Ok(ReceivedMessage {
            root: msg_root,
            init,
            body,
            is_external,
            bounce_enabled,
            balance_remaining: msg_balance_remaining,
        })
    }

    fn check_message_dst(&self, dst: &IntAddr) -> Result<()> {
        match dst {
            IntAddr::Std(dst) => {
                anyhow::ensure!(dst.anycast.is_none(), "anycast is not supported");
                anyhow::ensure!(*dst == self.address, "message destination address mismatch");
                Ok(())
            }
            IntAddr::Var(_) => anyhow::bail!("`addr_var` is not supported"),
        }
    }
}

/// Parsed inbound message.
#[derive(Debug, Clone)]
pub struct ReceivedMessage {
    /// Message root cell.
    pub root: Cell,
    /// Parsed message [`StateInit`].
    pub init: Option<MsgStateInit>,
    /// Message body.
    pub body: CellSliceParts,

    /// Whether this message is an `ExtIn`.
    pub is_external: bool,
    /// Whether this message can be bounced back on error.
    pub bounce_enabled: bool,

    /// The remaining attached value of the received message.
    /// NOTE: Always zero for external messages.
    pub balance_remaining: CurrencyCollection,
}

/// Message state init.
#[derive(Debug, Clone)]
pub struct MsgStateInit {
    /// [`StateInit`] hash.
    pub hash: HashBytes,
    /// Parsed [`StateInit`].
    pub parsed: StateInit,
}
