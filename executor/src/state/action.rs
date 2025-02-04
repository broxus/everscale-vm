use anyhow::Result;
use everscale_types::cell::CellTreeStats;
use everscale_types::error::Error;
use everscale_types::models::{
    AccountState, AccountStatus, AccountStatusChange, ActionPhase, ChangeLibraryMode,
    CurrencyCollection, ExecutedComputePhase, Lazy, LibRef, OutAction, OwnedMessage,
    OwnedRelaxedMessage, RelaxedMsgInfo, ReserveCurrencyFlags, SendMsgFlags, SimpleLib, StateInit,
    StorageUsedShort,
};
use everscale_types::num::{Tokens, VarUint56};
use everscale_types::prelude::*;

use crate::state::{ExecutorState, TransactionInput};
use crate::util::{
    check_rewrite_dst_addr, check_rewrite_src_addr, check_state_limits, check_state_limits_diff,
    ExtStorageStat, StateLimitsResult, StorageStatLimits,
};

pub struct ActionPhaseContext<'a> {
    /// Parsed transaction input.
    pub input: &'a mut TransactionInput,
    /// Original account balance before the compute phase.
    pub original_balance: CurrencyCollection,
    /// New account state to apply.
    pub new_state: StateInit,
    /// Actions list.
    pub actions: Cell,
    /// Successfully executed compute phase.
    pub compute_phase: &'a ExecutedComputePhase,
}

pub struct ActionPhaseFull {
    /// Resulting action phase.
    pub action_phase: ActionPhase,
    /// Resulting account status.
    pub account_status: AccountStatus,
    /// Additional fee in case of failure.
    pub action_fine: Tokens,
    /// Whether state can't be updated due to limits.
    pub state_exceeds_limits: bool,
    /// Whether bounce phase is required.
    pub bounce: bool,
}

impl ExecutorState<'_> {
    pub fn action_phase(&mut self, mut ctx: ActionPhaseContext<'_>) -> Result<ActionPhaseFull> {
        const MAX_ACTIONS: u16 = 255;

        let mut res = ActionPhaseFull {
            action_phase: ActionPhase {
                success: false,
                valid: false,
                no_funds: false,
                status_change: AccountStatusChange::Unchanged,
                total_fwd_fees: None,
                total_action_fees: None,
                result_code: -1,
                result_arg: None,
                total_actions: 0,
                special_actions: 0,
                skipped_actions: 0,
                messages_created: 0,
                action_list_hash: *ctx.actions.repr_hash(),
                total_message_size: StorageUsedShort::ZERO,
            },
            // NOTE: Action phase can only be executed on an active account.
            account_status: AccountStatus::Active,
            action_fine: Tokens::ZERO,
            state_exceeds_limits: false,
            bounce: false,
        };

        // Unpack actions list.
        let mut action_idx = 0u16;

        let mut list = Vec::new();
        let mut actions = ctx.actions.as_ref();
        loop {
            if actions.is_exotic() {
                // Actions list item must be an ordinary cell.
                res.action_phase.result_code = ResultCode::ActionListInvalid as i32;
                res.action_phase.result_arg = Some(action_idx as _);
                res.action_phase.valid = false;
                return Ok(res);
            }

            list.push(actions);

            // NOTE: We have checked that this cell is an ordinary.
            let mut cs = actions.as_slice_allow_pruned();
            if cs.is_empty() {
                // Actions list terminates with an empty cell.
                break;
            }

            actions = match cs.load_reference() {
                Ok(child) => child,
                Err(_) => {
                    // Each action must contain at least one reference.
                    res.action_phase.result_code = ResultCode::ActionListInvalid as i32;
                    res.action_phase.result_arg = Some(action_idx as _);
                    res.action_phase.valid = false;
                    return Ok(res);
                }
            };

            action_idx += 1;
            if action_idx > MAX_ACTIONS {
                // There can be at most N actions.
                res.action_phase.result_code = ResultCode::TooManyActions as i32;
                res.action_phase.result_arg = Some(action_idx as _);
                res.action_phase.valid = false;
                return Ok(res);
            }
        }

        res.action_phase.total_actions = action_idx;

        // Parse actions.
        let mut parsed_list = Vec::with_capacity(list.len());
        for (action_idx, item) in list.into_iter().rev().enumerate() {
            let mut cs = item.as_slice_allow_pruned();
            cs.load_reference().ok(); // Skip first reference.

            // Try to parse one action.
            let mut cs_parsed = cs.clone();
            if let Ok(item) = OutAction::load_from(&mut cs_parsed) {
                if cs_parsed.is_empty() {
                    // Add this action if slices contained it exclusively.
                    parsed_list.push(Some(item));
                    continue;
                }
            }

            // Special brhaviour for `SendMsg` action when we can at least parse its flags.
            if cs.size_bits() >= 40 && cs.load_u32()? == OutAction::TAG_SEND_MSG {
                let mode = SendMsgFlags::from_bits_retain(cs.load_u8()?);
                if mode.contains(SendMsgFlags::IGNORE_ERROR) {
                    // "IGNORE_ERROR" flag means that we can just skip this action.
                    res.action_phase.skipped_actions += 1;
                    parsed_list.push(None);
                    continue;
                } else if mode.contains(SendMsgFlags::BOUNCE_ON_ERROR) {
                    // "BOUNCE_ON_ERROR" flag means that we fail the action phase,
                    // but require a bounce phase to run afterwards.
                    res.bounce = true;
                }
            }

            res.action_phase.result_code = ResultCode::ActionInvalid as i32;
            res.action_phase.result_arg = Some(action_idx as _);
            res.action_phase.valid = false;
            return Ok(res);
        }

        // Action list itself is ok.
        res.action_phase.valid = true;

        // Execute actions.
        let mut action_ctx = ActionContext {
            need_bounce_on_fail: false,
            input: ctx.input,
            original_balance: &ctx.original_balance,
            remaining_balance: self.balance.clone(),
            reserved_balance: CurrencyCollection::ZERO,
            action_fine: &mut res.action_fine,
            new_state: &mut ctx.new_state,
            end_lt: self.end_lt,
            out_msgs: Vec::new(),
            delete_account: false,
            compute_phase: ctx.compute_phase,
            action_phase: &mut res.action_phase,
        };

        for (action_idx, action) in parsed_list.into_iter().enumerate() {
            let Some(action) = action else {
                continue;
            };

            action_ctx.need_bounce_on_fail = false;
            action_ctx.action_phase.result_code = -1;
            action_ctx.action_phase.result_arg = Some(action_idx as _);

            let action = match action {
                OutAction::SendMsg { mode, out_msg } => {
                    let mut rewrite = None;
                    loop {
                        match self.do_send_message(mode, &out_msg, &mut action_ctx, rewrite) {
                            Ok(SendMsgResult::Sent) => break Ok(()),
                            Ok(SendMsgResult::Rewrite(r)) => rewrite = Some(r),
                            Err(e) => break Err(e),
                        }
                    }
                }
                OutAction::SetCode { new_code } => self.do_set_code(new_code, &mut action_ctx),
                OutAction::ReserveCurrency { mode, value } => {
                    self.do_reserve_currency(mode, value, &mut action_ctx)
                }
                OutAction::ChangeLibrary { mode, lib } => {
                    self.do_change_library(mode, lib, &mut action_ctx)
                }
            };

            if let Err(ActionFailed) = action {
                let result_code = &mut action_ctx.action_phase.result_code;
                if *result_code == -1 {
                    *result_code = ResultCode::ActionInvalid as i32;
                }
                if *result_code == ResultCode::NotEnoughBalance as i32
                    || *result_code == ResultCode::NotEnoughExtraBalance as i32
                {
                    action_ctx.action_phase.no_funds = true;
                }

                // TODO: Enforce state limits here if we want to persist
                // library changes even if action phase fails. This is
                // not the case for now, but this is how the reference
                // implementation works.

                // Compute the resulting action fine (it must not be greater than the account balance).
                let fine = *action_ctx.action_fine;
                *action_ctx.action_fine = std::cmp::min(fine, self.balance.tokens);

                // Charge the account balance for the action fine.
                action_ctx.action_phase.total_action_fees = Some(fine).filter(|t| !t.is_zero());
                self.balance.tokens -= fine;
                self.total_fees.try_add_assign(fine)?;

                // Apply flags.
                res.bounce |= action_ctx.need_bounce_on_fail;

                // Ignore all other action.
                return Ok(res);
            }
        }

        if !action_ctx.action_fine.is_zero() {
            action_ctx
                .action_phase
                .total_action_fees
                .get_or_insert_default()
                .try_add_assign(*action_ctx.action_fine)?;
        }

        // Check that the new state does not exceed size limits.
        // TODO: Ignore this step if account is going to be deleted anyway?
        if !self.is_special {
            let limits = &self.config.size_limits;
            let is_masterchain = self.address.is_masterchain();
            let check = match &self.state {
                AccountState::Active(current_state) => check_state_limits_diff(
                    current_state,
                    action_ctx.new_state,
                    limits,
                    is_masterchain,
                ),
                AccountState::Uninit | AccountState::Frozen(_) => check_state_limits(
                    action_ctx.new_state.code.as_ref(),
                    action_ctx.new_state.data.as_ref(),
                    &action_ctx.new_state.libraries,
                    limits,
                    is_masterchain,
                ),
            };

            // TODO: Save the resulting `ExtStorageStat` to use it later.
            if matches!(check, StateLimitsResult::Exceeds) {
                res.action_phase.result_code = ResultCode::StateOutOfLimits as i32;
                res.state_exceeds_limits = true;
                return Ok(res);
            }
        }

        action_ctx
            .remaining_balance
            .try_add_assign(&action_ctx.reserved_balance)?;

        action_ctx.action_phase.result_code = 0;
        action_ctx.action_phase.result_arg = None;
        action_ctx.action_phase.success = true;

        if action_ctx.delete_account {
            action_ctx.action_phase.status_change = AccountStatusChange::Deleted;
        }

        if let Some(fees) = action_ctx.action_phase.total_action_fees {
            // NOTE: Forwarding fees are not collected here.
            self.total_fees.try_add_assign(fees)?;
        }
        self.balance = action_ctx.remaining_balance;

        self.out_msgs = action_ctx.out_msgs;
        self.end_lt = action_ctx.end_lt;
        self.state = AccountState::Active(ctx.new_state);

        Ok(res)
    }

    /// `SendMsg` action.
    fn do_send_message(
        &self,
        mode: SendMsgFlags,
        out_msg: &Lazy<OwnedRelaxedMessage>,
        ctx: &mut ActionContext<'_>,
        mut rewrite: Option<MessageRewrite>,
    ) -> Result<SendMsgResult, ActionFailed> {
        const MASK: u8 = SendMsgFlags::all().bits();
        const INVALID_MASK: SendMsgFlags =
            SendMsgFlags::ALL_BALANCE.union(SendMsgFlags::WITH_REMAINING_BALANCE);
        const EXT_MSG_MASK: u8 = SendMsgFlags::PAY_FEE_SEPARATELY
            .union(SendMsgFlags::IGNORE_ERROR)
            .union(SendMsgFlags::BOUNCE_ON_ERROR)
            .bits();

        // Check and apply mode flags.
        if mode.contains(SendMsgFlags::BOUNCE_ON_ERROR) {
            ctx.need_bounce_on_fail = true;
        }

        if mode.bits() & !MASK != 0 || mode.contains(INVALID_MASK) {
            // - Mode has some unknown bits;
            // - Or "ALL_BALANCE" flag was used with "WITH_REMAINING_BALANCE".
            return Err(ActionFailed);
        }

        // We should only skip if at least the mode is correct.
        let skip_invalid = mode.contains(SendMsgFlags::IGNORE_ERROR);
        let check_skip_invalid = |e: ResultCode, ctx: &mut ActionContext<'_>| {
            if skip_invalid {
                ctx.action_phase.skipped_actions += 1;
                Ok(SendMsgResult::Sent)
            } else {
                ctx.action_phase.result_code = e as i32;
                Err(ActionFailed)
            }
        };

        // Output message must be an ordinary cell.
        if out_msg.inner().is_exotic() {
            return Err(ActionFailed);
        }

        // Unpack message.
        let mut relaxed_info;
        let mut state_init_cs;
        let mut body_cs;

        {
            let mut cs = out_msg.inner().as_slice_allow_pruned();

            relaxed_info = RelaxedMsgInfo::load_from(&mut cs)?;
            state_init_cs = load_state_init_as_slice(&mut cs)?;
            body_cs = load_body_as_slice(&mut cs)?;

            if !cs.is_empty() {
                // Any remaining data in the message slice is treated as malicious data.
                return Err(ActionFailed);
            }
        }

        // Apply rewrite.
        let rewritten_state_init_cb;
        if let Some(MessageRewrite::StateInitToCell) = rewrite {
            if state_init_cs.size_refs() >= 2 {
                // Move state init to cell if it is more optimal.
                rewritten_state_init_cb = rewrite_state_init_to_cell(state_init_cs);
                state_init_cs = rewritten_state_init_cb.as_full_slice();
            } else {
                // Or try to move body to cell instead.
                rewrite = Some(MessageRewrite::BodyToCell);
            }
        }

        let rewritten_body_cs;
        if let Some(MessageRewrite::BodyToCell) = rewrite {
            if body_cs.size_bits() > 1 && !body_cs.get_bit(0).unwrap() {
                // Try to move a non-empty plain body to cell.
                rewritten_body_cs = rewrite_body_to_cell(body_cs);
                body_cs = rewritten_body_cs.as_full_slice();
            }
        }

        // Check info.
        let mut use_mc_prices = self.address.is_masterchain();
        match &mut relaxed_info {
            // Check internal outbound message.
            RelaxedMsgInfo::Int(info) => {
                // Rewrite source address.
                if !check_rewrite_src_addr(&self.address, &mut info.src) {
                    // NOTE: For some reason we are not ignoring this error.
                    ctx.action_phase.result_code = ResultCode::InvalidSrcAddr as i32;
                    return Err(ActionFailed);
                };

                // Rewrite destination address.
                if !check_rewrite_dst_addr(&self.config.workchains, &mut info.dst) {
                    return check_skip_invalid(ResultCode::InvalidDstAddr, ctx);
                }
                use_mc_prices |= info.dst.is_masterchain();

                // Reset fees.
                info.ihr_fee = Tokens::ZERO;
                info.fwd_fee = Tokens::ZERO;

                // Rewrite message timings.
                info.created_at = self.params.block_unixtime;
                info.created_lt = ctx.end_lt;

                // Clear flags.
                info.ihr_disabled = true;
                info.bounced = false;
            }
            // Check external outbound message.
            RelaxedMsgInfo::ExtOut(info) => {
                if mode.bits() & !EXT_MSG_MASK != 0 {
                    // Invalid mode for an outgoing external message.
                    return Err(ActionFailed);
                }

                // Rewrite source address.
                if !check_rewrite_src_addr(&self.address, &mut info.src) {
                    ctx.action_phase.result_code = ResultCode::InvalidSrcAddr as i32;
                    return Err(ActionFailed);
                }

                // Rewrite message timings.
                info.created_at = self.params.block_unixtime;
                info.created_lt = ctx.end_lt;
            }
        };

        // Compute fine per cell. Account is required to pay it for every visited cell.
        let prices = self.config.fwd_prices(use_mc_prices);
        let mut max_cell_count = self.config.size_limits.max_msg_cells;
        let fine_per_cell;
        if self.is_special {
            fine_per_cell = 0;
        } else {
            fine_per_cell = (prices.cell_price >> 16) / 4;

            let mut funds = ctx.remaining_balance.tokens;
            if let RelaxedMsgInfo::Int(info) = &relaxed_info {
                if !mode.contains(SendMsgFlags::ALL_BALANCE)
                    && !mode.contains(SendMsgFlags::PAY_FEE_SEPARATELY)
                {
                    let mut new_funds = info.value.tokens;

                    if mode.contains(SendMsgFlags::WITH_REMAINING_BALANCE) {
                        if (|| {
                            let msg_balance_remaining = match ctx.input {
                                TransactionInput::Ordinary(msg) => msg.balance_remaining.tokens,
                                TransactionInput::TickTock(_) => Tokens::ZERO,
                            };
                            new_funds.try_add_assign(msg_balance_remaining)?;
                            new_funds.try_sub_assign(ctx.compute_phase.gas_fees)?;
                            new_funds.try_sub_assign(*ctx.action_fine)?;

                            Ok::<_, everscale_types::error::Error>(())
                        })()
                        .is_err()
                        {
                            return check_skip_invalid(ResultCode::NotEnoughBalance, ctx);
                        }
                    }

                    funds = std::cmp::min(funds, new_funds);
                }
            }

            if funds < Tokens::new(max_cell_count as u128 * fine_per_cell as u128) {
                debug_assert_ne!(fine_per_cell, 0);
                max_cell_count = (funds.into_inner() / fine_per_cell as u128)
                    .try_into()
                    .unwrap_or(u32::MAX);
            }
        }

        let collect_fine = |cells: u32, ctx: &mut ActionContext<'_>| {
            let mut fine = Tokens::new(
                fine_per_cell.saturating_mul(std::cmp::min(max_cell_count, cells) as u64) as _,
            );
            fine = std::cmp::min(fine, ctx.remaining_balance.tokens);
            ctx.action_fine.try_add_assign(fine)?;
            ctx.remaining_balance.try_sub_assign_tokens(fine)
        };

        // Compute size of the message.
        let stats = 'stats: {
            let mut stats = ExtStorageStat::with_limits(StorageStatLimits {
                bit_count: u32::MAX,
                cell_count: max_cell_count,
            });

            'valid: {
                for cell in state_init_cs.references() {
                    if !stats.add_cell(cell) {
                        break 'valid;
                    }
                }

                for cell in body_cs.references() {
                    if !stats.add_cell(cell) {
                        break 'valid;
                    }
                }

                if let RelaxedMsgInfo::Int(int) = &relaxed_info {
                    if let Some(cell) = int.value.other.as_dict().root() {
                        if !stats.add_cell(cell.as_ref()) {
                            break 'valid;
                        }
                    }
                }

                break 'stats stats.stats();
            }

            collect_fine(stats.cells, ctx)?;
            return check_skip_invalid(ResultCode::MessageOutOfLimits, ctx);
        };

        // Make sure that `check_skip_invalid` will collect fine.
        let check_skip_invalid = move |e: ResultCode, ctx: &mut ActionContext<'_>| {
            collect_fine(stats.cell_count as _, ctx)?;
            check_skip_invalid(e, ctx)
        };

        // Compute forwarding fees.
        let fwd_fee = if self.is_special {
            Tokens::ZERO
        } else {
            prices.compute_fwd_fee(stats)
        };

        // Finalize message.
        let msg;
        let fees_collected;
        match &mut relaxed_info {
            RelaxedMsgInfo::Int(info) => {
                // Rewrite message value and compute how much will be withdwarn.
                let value_to_pay = match ctx.rewrite_message_value(&mut info.value, mode, fwd_fee) {
                    Ok(total_value) => total_value,
                    Err(_) => return check_skip_invalid(ResultCode::NotEnoughBalance, ctx),
                };

                // Check if remaining balance is enough to pay `total_value`.
                if ctx.remaining_balance.tokens < value_to_pay {
                    return check_skip_invalid(ResultCode::NotEnoughBalance, ctx);
                }

                // Try to withdraw extra currencies from the remaining balance.
                let other = match ctx.remaining_balance.other.checked_sub(&info.value.other) {
                    Ok(other) => other,
                    Err(_) => return check_skip_invalid(ResultCode::NotEnoughExtraBalance, ctx),
                };

                // Split forwarding fee.
                fees_collected = prices.get_first_part(fwd_fee);
                info.fwd_fee = fwd_fee - fees_collected;

                // Finalize message.
                msg = match build_message(&relaxed_info, &state_init_cs, &body_cs) {
                    Ok(msg) => msg,
                    Err(_) => match MessageRewrite::next(rewrite) {
                        Some(rewrite) => return Ok(SendMsgResult::Rewrite(rewrite)),
                        None => return check_skip_invalid(ResultCode::FailedToFitMessage, ctx),
                    },
                };

                // Clear message balance if it was used.
                if let TransactionInput::Ordinary(msg) = ctx.input {
                    if mode.contains(SendMsgFlags::ALL_BALANCE)
                        || mode.contains(SendMsgFlags::WITH_REMAINING_BALANCE)
                    {
                        msg.balance_remaining = CurrencyCollection::ZERO;
                    }
                }

                // Update the remaining balance.
                ctx.remaining_balance.tokens -= value_to_pay;
                ctx.remaining_balance.other = other;
            }
            RelaxedMsgInfo::ExtOut(_) => {
                // Check if the remaining balance is enough to pay forwarding fees.
                if ctx.remaining_balance.tokens < fwd_fee {
                    return check_skip_invalid(ResultCode::NotEnoughBalance, ctx);
                }

                // Finalize message.
                msg = match build_message(&relaxed_info, &state_init_cs, &body_cs) {
                    Ok(msg) => msg,
                    Err(_) => match MessageRewrite::next(rewrite) {
                        Some(rewrite) => return Ok(SendMsgResult::Rewrite(rewrite)),
                        None => return check_skip_invalid(ResultCode::FailedToFitMessage, ctx),
                    },
                };

                // Update the remaining balance.
                ctx.remaining_balance.tokens -= fwd_fee;
                fees_collected = fwd_fee;
            }
        }

        update_total_msg_stat(
            &mut ctx.action_phase.total_message_size,
            stats,
            msg.inner().bit_len(),
        );

        ctx.action_phase.messages_created += 1;
        ctx.end_lt += 1;

        ctx.out_msgs.push(msg);

        *ctx.action_phase.total_action_fees.get_or_insert_default() += fees_collected;
        *ctx.action_phase.total_fwd_fees.get_or_insert_default() += fwd_fee;

        if mode.contains(SendMsgFlags::DELETE_IF_EMPTY) {
            ctx.delete_account =
                ctx.reserved_balance.tokens.is_zero() && ctx.reserved_balance.other.is_empty();
        }

        Ok(SendMsgResult::Sent)
    }

    /// `SetCode` action.
    fn do_set_code(&self, new_code: Cell, ctx: &mut ActionContext<'_>) -> Result<(), ActionFailed> {
        // Update context.
        ctx.new_state.code = Some(new_code);
        ctx.action_phase.special_actions += 1;

        // Done
        Ok(())
    }

    /// `ReserveCurrency` action.
    fn do_reserve_currency(
        &self,
        mode: ReserveCurrencyFlags,
        mut reserve: CurrencyCollection,
        ctx: &mut ActionContext<'_>,
    ) -> Result<(), ActionFailed> {
        const MASK: u8 = ReserveCurrencyFlags::all().bits();

        // Check and apply mode flags.
        if mode.contains(ReserveCurrencyFlags::BOUNCE_ON_ERROR) {
            ctx.need_bounce_on_fail = true;
        }

        if mode.bits() & !MASK != 0 {
            // Invalid mode.
            return Err(ActionFailed);
        }

        if mode.contains(ReserveCurrencyFlags::WITH_ORIGINAL_BALANCE) {
            if mode.contains(ReserveCurrencyFlags::REVERSE) {
                reserve = ctx.original_balance.checked_sub(&reserve)?;
            } else {
                reserve.try_add_assign(ctx.original_balance)?;
            }
        } else if mode.contains(ReserveCurrencyFlags::REVERSE) {
            // Invalid mode.
            return Err(ActionFailed);
        }

        if mode.contains(ReserveCurrencyFlags::IGNORE_ERROR) {
            // Clamp balance.
            reserve = reserve.checked_clamp(&ctx.remaining_balance)?;
        }

        // Reserve balance.
        let mut new_balance = CurrencyCollection {
            tokens: match ctx.remaining_balance.tokens.checked_sub(reserve.tokens) {
                Some(tokens) => tokens,
                None => {
                    ctx.action_phase.result_code = ResultCode::NotEnoughBalance as i32;
                    return Err(ActionFailed);
                }
            },
            other: match ctx.remaining_balance.other.checked_sub(&reserve.other) {
                Ok(other) => other,
                Err(_) => {
                    ctx.action_phase.result_code = ResultCode::NotEnoughExtraBalance as i32;
                    return Err(ActionFailed);
                }
            },
        };

        // Apply "ALL_BUT" flag. Leave only "new_balance", reserve everything else.
        if mode.contains(ReserveCurrencyFlags::ALL_BUT) {
            std::mem::swap(&mut new_balance, &mut reserve);
        }

        // Update context.
        ctx.remaining_balance = new_balance;
        ctx.reserved_balance.try_add_assign(&reserve)?;
        ctx.action_phase.special_actions += 1;

        // Done
        Ok(())
    }

    /// `ChangeLibrary` action.
    fn do_change_library(
        &self,
        mode: ChangeLibraryMode,
        lib: LibRef,
        ctx: &mut ActionContext<'_>,
    ) -> Result<(), ActionFailed> {
        // Having both "ADD_PRIVATE" and "ADD_PUBLIC" flags is invalid.
        const INVALID_MODE: ChangeLibraryMode = ChangeLibraryMode::from_bits_retain(
            ChangeLibraryMode::ADD_PRIVATE.bits() | ChangeLibraryMode::ADD_PUBLIC.bits(),
        );

        // Check and apply mode flags.
        if mode.contains(ChangeLibraryMode::BOUNCE_ON_ERROR) {
            ctx.need_bounce_on_fail = true;
        }

        if mode.contains(INVALID_MODE) {
            return Err(ActionFailed);
        }

        let hash = match &lib {
            LibRef::Cell(cell) => cell.repr_hash(),
            LibRef::Hash(hash) => hash,
        };

        let add_public = mode.contains(ChangeLibraryMode::ADD_PUBLIC);
        if add_public || mode.contains(ChangeLibraryMode::ADD_PRIVATE) {
            // Add new library.
            if let Ok(Some(prev)) = ctx.new_state.libraries.get(hash) {
                if prev.public == add_public {
                    // Do nothing if library already exists with the same `public` flag.
                    ctx.action_phase.special_actions += 1;
                    return Ok(());
                }
            }

            let LibRef::Cell(root) = lib else {
                ctx.action_phase.result_code = ResultCode::NoLibCode as i32;
                return Err(ActionFailed);
            };

            let mut stats = ExtStorageStat::with_limits(StorageStatLimits {
                bit_count: u32::MAX,
                cell_count: self.config.size_limits.max_library_cells,
            });
            if !stats.add_cell(root.as_ref()) {
                ctx.action_phase.result_code = ResultCode::LibOutOfLimits as i32;
                return Err(ActionFailed);
            }

            // Add library.
            if ctx
                .new_state
                .libraries
                .set(*root.repr_hash(), SimpleLib {
                    public: add_public,
                    root,
                })
                .is_err()
            {
                ctx.action_phase.result_code = ResultCode::InvalidLibrariesDict as i32;
                return Err(ActionFailed);
            }
        } else {
            // Remove library.
            if ctx.new_state.libraries.remove(hash).is_err() {
                ctx.action_phase.result_code = ResultCode::InvalidLibrariesDict as i32;
                return Err(ActionFailed);
            }
        }

        // Update context.
        ctx.action_phase.special_actions += 1;

        // Done
        Ok(())
    }
}

struct ActionContext<'a> {
    need_bounce_on_fail: bool,
    input: &'a mut TransactionInput,
    original_balance: &'a CurrencyCollection,
    remaining_balance: CurrencyCollection,
    reserved_balance: CurrencyCollection,
    action_fine: &'a mut Tokens,
    new_state: &'a mut StateInit,
    end_lt: u64,
    out_msgs: Vec<Lazy<OwnedMessage>>,
    delete_account: bool,

    compute_phase: &'a ExecutedComputePhase,
    action_phase: &'a mut ActionPhase,
}

impl ActionContext<'_> {
    fn rewrite_message_value(
        &mut self,
        value: &mut CurrencyCollection,
        mut mode: SendMsgFlags,
        fees_total: Tokens,
    ) -> Result<Tokens, ActionFailed> {
        // Update `value` based on flags.
        if mode.contains(SendMsgFlags::ALL_BALANCE) {
            // Attach all remaining balance to the message.
            *value = self.remaining_balance.clone();
            // Pay fees from the attached value.
            mode.remove(SendMsgFlags::PAY_FEE_SEPARATELY);
        } else if mode.contains(SendMsgFlags::WITH_REMAINING_BALANCE) {
            if let TransactionInput::Ordinary(msg) = self.input {
                // Attach all remaining balance of the inbound message.
                // (in addition to the original value).
                value.try_add_assign(&msg.balance_remaining)?;
            }

            if !mode.contains(SendMsgFlags::PAY_FEE_SEPARATELY) {
                // Try to exclude fees from the attached value.
                value.try_sub_assign_tokens(*self.action_fine)?;
                value.try_sub_assign_tokens(self.compute_phase.gas_fees)?;
            }
        }

        // Compute `value + fees`.
        let mut total = value.tokens;
        if mode.contains(SendMsgFlags::PAY_FEE_SEPARATELY) {
            total.try_add_assign(fees_total)?;
        } else {
            value.tokens.try_sub_assign(fees_total)?;
        }

        // Done
        Ok(total)
    }
}

struct ActionFailed;

impl From<anyhow::Error> for ActionFailed {
    #[inline]
    fn from(_: anyhow::Error) -> Self {
        Self
    }
}

impl From<Error> for ActionFailed {
    #[inline]
    fn from(_: Error) -> Self {
        Self
    }
}

#[derive(Debug, Clone, Copy)]
enum SendMsgResult {
    Sent,
    Rewrite(MessageRewrite),
}

#[derive(Debug, Clone, Copy)]
enum MessageRewrite {
    StateInitToCell,
    BodyToCell,
}

impl MessageRewrite {
    pub fn next(rewrite: Option<Self>) -> Option<Self> {
        match rewrite {
            None => Some(Self::StateInitToCell),
            Some(Self::StateInitToCell) => Some(Self::BodyToCell),
            Some(Self::BodyToCell) => None,
        }
    }
}

fn load_state_init_as_slice<'a>(cs: &mut CellSlice<'a>) -> Result<CellSlice<'a>, Error> {
    let mut res_cs = cs.clone();

    // (Maybe (Either StateInit ^StateInit))
    if cs.load_bit()? {
        if cs.load_bit()? {
            // right$1 ^StateInit
            let state_root = cs.load_reference()?;
            if state_root.is_exotic() {
                // Only ordinary cells are allowed as state init.
                return Err(Error::InvalidData);
            }

            // Validate `StateInit` by reading.
            let mut cs = state_root.as_slice_allow_pruned();
            StateInit::load_from(&mut cs)?;

            // And ensure that nothing more was left.
            if !cs.is_empty() {
                return Err(Error::CellOverflow);
            }
        } else {
            // left$0 StateInit

            // Validate `StateInit` by reading.
            StateInit::load_from(cs)?;
        }
    }

    res_cs.skip_last(cs.size_bits(), cs.size_refs())?;
    Ok(res_cs)
}

fn load_body_as_slice<'a>(cs: &mut CellSlice<'a>) -> Result<CellSlice<'a>, Error> {
    let res_cs = cs.clone();

    if cs.load_bit()? {
        // right$1 ^X
        cs.skip_first(0, 1)?;
    } else {
        // left$0 X
        cs.load_remaining();
    }

    Ok(res_cs)
}

fn rewrite_state_init_to_cell(mut cs: CellSlice<'_>) -> CellBuilder {
    // Skip prefix `just$1 (left$0 ...)`.
    let prefix = cs.load_small_uint(2).unwrap();
    debug_assert_eq!(prefix, 0b10);

    // Build ^StateInit.
    let cell = CellBuilder::build_from(cs).unwrap();

    // Build `just$1 (right$1 ^StateInit)`.
    let mut b = CellBuilder::new();
    b.store_small_uint(0b11, 2).unwrap();
    b.store_reference(cell).unwrap();

    // Done
    b
}

fn rewrite_body_to_cell(mut cs: CellSlice<'_>) -> CellBuilder {
    // Skip prefix `left$0 ...`.
    let prefix = cs.load_bit().unwrap();
    debug_assert!(!prefix);

    // Build ^X.
    let cell = CellBuilder::build_from(cs).unwrap();

    // Build `right$1 ^X`.
    let mut b = CellBuilder::new();
    b.store_bit_one().unwrap();
    b.store_reference(cell).unwrap();

    // Done
    b
}

fn build_message(
    info: &RelaxedMsgInfo,
    state_init_cs: &CellSlice<'_>,
    body_cs: &CellSlice<'_>,
) -> Result<Lazy<OwnedMessage>, Error> {
    CellBuilder::build_from((info, state_init_cs, body_cs)).map(Lazy::from_raw)
}

fn update_total_msg_stat(
    total_message_size: &mut StorageUsedShort,
    stats: CellTreeStats,
    root_bits: u16,
) {
    let bits_diff = VarUint56::new(stats.bit_count.saturating_add(root_bits as _));
    let cells_diff = VarUint56::new(stats.cell_count.saturating_add(1));

    total_message_size.bits = total_message_size.bits.saturating_add(bits_diff);
    total_message_size.cells = total_message_size.cells.saturating_add(cells_diff);
}

#[repr(i32)]
#[derive(Debug, thiserror::Error)]
enum ResultCode {
    #[error("invalid action list")]
    ActionListInvalid = 32,
    #[error("too many actions")]
    TooManyActions = 33,
    #[error("invalid or unsupported action")]
    ActionInvalid = 34,
    #[error("invalid source address")]
    InvalidSrcAddr = 35,
    #[error("invalid destination address")]
    InvalidDstAddr = 36,
    #[error("not enough balance (base currency)")]
    NotEnoughBalance = 37,
    #[error("not enough balance (extra currency)")]
    NotEnoughExtraBalance = 38,
    #[error("failed to fit message into cell")]
    FailedToFitMessage = 39,
    #[error("message exceeds limits")]
    MessageOutOfLimits = 40,
    #[error("library code not found")]
    NoLibCode = 41,
    #[error("failed to change libraries dict")]
    InvalidLibrariesDict = 42,
    #[error("too many library cells")]
    LibOutOfLimits = 43,
    #[error("state exceeds limits")]
    StateOutOfLimits = 50,
}
