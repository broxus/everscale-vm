use anyhow::Result;
use everscale_types::cell::{Cell, CellBuilder, CellSliceRange, CellTreeStats, HashBytes, Load};
use everscale_types::dict::Dict;
use everscale_types::models::{
    AccountState, AccountStatusChange, ActionPhase, ChangeLibraryMode, ComputePhase,
    ComputePhaseSkipReason, CreditPhase, CurrencyCollection, ExecutedComputePhase, LibRef, MsgInfo,
    OutAction, ReserveCurrencyFlags, SendMsgFlags, SimpleLib, SizeLimitsConfig,
    SkippedComputePhase, StateInit, StdAddr, StoragePhase, StorageUsedShort, TickTock,
};
use everscale_types::num::{Tokens, VarUint24, VarUint56};
use num_bigint::{BigInt, Sign};
use tycho_vm::{tuple, SafeRc, SmcInfoBase, Stack, VmState};

use crate::util::{is_masterchain, ExtStorageStat};
use crate::{ExecutorState, ExtMsgRejected, ExtMsgRejectedReason, MsgStateInit, TransactionInput};

#[repr(i32)]
#[derive(Debug, thiserror::Error)]
enum ResultCode {
    #[error("invalid action list")]
    ActionListInvalid = 32,
    #[error("too many actions")]
    TooManyActions = 33,
    #[error("invalid or unsupported action")]
    ActionInvalid = 34,
    #[error("not enough balance (base currency)")]
    NotEnoughBalance = 37,
    #[error("not enough balance (extra currency)")]
    NotEnoughExtraBalance = 38,
    #[error("library code not found")]
    NoLibCode = 41,
    #[error("failed to change libraries dict")]
    InvalidLibrariesDict = 42,
    #[error("too many library cells")]
    LibOutOfLimits = 43,
    #[error("state exceeds limits")]
    StateOutOfLimits = 50,
}

const MAX_ALLOWED_MERKLE_DEPTH: u8 = 2;

impl ExecutorState<'_> {
    // === Receive Inbound Message ===

    pub fn receive_in_msg(&mut self, msg_root: Cell) -> Result<()> {
        let is_masterchain = is_masterchain(self.workchain);

        // Process message header.
        let mut slice = msg_root.as_slice_allow_pruned();
        match MsgInfo::load_from(&mut slice)? {
            // Handle internal message.
            MsgInfo::Int(int) => {
                // Update message balance
                self.message_balance_remaining = int.value;
                self.message_balance_remaining
                    .try_add_assign_tokens(int.ihr_fee)?;

                // Adjust LT range.
                if int.created_lt >= self.start_lt {
                    self.start_lt = int.created_lt + 1;
                    self.end_lt = self.start_lt + 1;
                }
            }
            // Handle external (in) message.
            MsgInfo::ExtIn(_) => {
                // Update flags.
                self.is_in_msg_external = true;

                // Compute forwarding fees.
                let Some(mut stats) = ExtStorageStat::compute_for_slice(
                    &slice,
                    MAX_ALLOWED_MERKLE_DEPTH,
                    CellTreeStats {
                        bit_count: self.config.size_limits.max_msg_bits as u64,
                        cell_count: self.config.size_limits.max_msg_cells as u64,
                    },
                ) else {
                    anyhow::bail!(ExtMsgRejected {
                        reason: ExtMsgRejectedReason::ExceedsLimits,
                    });
                };

                stats.bit_count -= slice.size_bits() as u64; // bits in the root cells are free.

                let fwd_fee = self
                    .config
                    .fwd_prices(is_masterchain)
                    .compute_fwd_fee(stats);

                // Deduct fees.
                if self.account.balance.tokens < fwd_fee {
                    anyhow::bail!(ExtMsgRejected {
                        reason: ExtMsgRejectedReason::ImportFailed,
                    });
                }
                self.account.balance.tokens -= fwd_fee;
                self.total_fees.try_add_assign(fwd_fee)?;

                // External message cannot carry value.
                self.message_balance_remaining = CurrencyCollection::ZERO;
            }
            // Reject all other message types.
            MsgInfo::ExtOut(_) => anyhow::bail!("unexpected incoming ExtOut message"),
        }

        // Process message state init.
        if slice.load_bit()? {
            self.msg_state_init = Some(if slice.load_bit()? {
                // State init as reference.
                let state_root = slice.load_reference()?;

                MsgStateInit {
                    hash: *state_root.repr_hash(),
                    parsed: state_root.parse()?,
                    used: false,
                }
            } else {
                // Inline state init.
                let mut state_init_cs = slice.clone();

                // Read StateInit.
                let parsed = StateInit::load_from(&mut slice)?;
                // Rebuild it as cell to get hash.
                state_init_cs.skip_last(slice.size_bits(), slice.size_refs())?;
                let state_root = CellBuilder::build_from(state_init_cs)?;

                MsgStateInit {
                    hash: *state_root.repr_hash(),
                    parsed,
                    used: false,
                }
            })
        }

        // Process message body.
        if slice.load_bit()? {
            // Body as cell.
            let body_cell = slice.load_reference_cloned()?;
            anyhow::ensure!(slice.is_empty(), "message contains extra data");

            let body_range = CellSliceRange::full(body_cell.as_ref());
            self.msg_body = (body_cell, body_range);
        } else {
            // Inline body.
            let body_range = slice.range();
            self.msg_body = (msg_root, body_range);
        }

        // Done
        Ok(())
    }

    // === Credit Phase ===

    pub fn credit_phase(&mut self) -> Result<CreditPhase> {
        // Remaining message balance is added to the account balamce.
        self.account
            .balance
            .try_add_assign(&self.message_balance_remaining)?;

        Ok(CreditPhase {
            // Due payment is only collected in storage phase.
            // For messages with bounce flag, contract always receives
            // the amount specified in message.
            due_fees_collected: None,
            credit: self.message_balance_remaining.clone(),
        })
    }

    // === Storage Phase ===

    pub fn storage_phase(&mut self, adjust_msg_value: bool) -> Result<StoragePhase> {
        anyhow::ensure!(
            self.params.block_unixtime >= self.account.storage_stat.last_paid,
            "current unixtime is less than the account last_paid",
        );

        let is_masterchain = is_masterchain(self.workchain);
        let config = self.config.gas_prices(is_masterchain);

        // Compute how much this account must pay for storing its state up until now.
        let mut to_pay = self.config.compute_storage_fees(
            &self.account.storage_stat,
            self.params.block_unixtime,
            self.is_special,
            is_masterchain,
        );
        if let Some(due_payment) = self.account.storage_stat.due_payment {
            // TODO: Use saturating math here?
            to_pay.try_add_assign(due_payment)?;
        }

        // Update `last_paid` (only for ordinary accounts).
        self.account.storage_stat.last_paid = if self.is_special {
            0
        } else {
            self.params.block_unixtime
        };

        // Start filling the storage phase.
        let storage_fees_collected;
        let storage_fees_due;
        let status_change;

        if to_pay.is_zero() {
            // No fees at all.
            storage_fees_collected = Tokens::ZERO;
            storage_fees_due = None;
            status_change = AccountStatusChange::Unchanged;
        } else if let Some(new_balance) = self.account.balance.tokens.checked_sub(to_pay) {
            // Account balance is enough to pay storage fees.
            storage_fees_collected = to_pay;
            storage_fees_due = None;
            status_change = AccountStatusChange::Unchanged;

            // Update account balance.
            self.account.balance.tokens = new_balance;
            // Reset `due_payment` if there was any.
            self.account.storage_stat.due_payment = None;
        } else {
            let fees_due = to_pay - self.account.balance.tokens;

            // Account balance is not enough to pay storage fees,
            // so we use all of its balance and try to freeze the account.
            storage_fees_collected = std::mem::take(&mut self.account.balance.tokens);
            storage_fees_due = Some(fees_due).filter(|t| !t.is_zero());

            debug_assert!(self.account.balance.tokens.is_zero());

            // NOTE: Keep all cases explicit here without "default" branch.
            status_change = match &self.account.state {
                // Do nothing for special accounts.
                _ if self.is_special => AccountStatusChange::Unchanged,
                // Try to delete account.
                // TODO: Add flag for skip this behaviour for `Frozen` accounts.
                AccountState::Uninit | AccountState::Frozen { .. }
                    if fees_due.into_inner() > config.delete_due_limit as u128
                        && !self.account.balance.other.is_empty() =>
                {
                    AccountStatusChange::Deleted
                }
                // Do nothing if not deleting.
                AccountState::Uninit | AccountState::Frozen { .. } => {
                    AccountStatusChange::Unchanged
                }
                // Freeze account with big enough due.
                AccountState::Active { .. }
                    if fees_due.into_inner() > config.freeze_due_limit as u128 =>
                {
                    // NOTE: We are not changing the account state yet.
                    AccountStatusChange::Frozen
                }
                // Do nothing if `fees_due` is not big enough.
                AccountState::Active { .. } => AccountStatusChange::Unchanged,
            };

            // TODO: Add flag to disable this behaviour for all accounts. (?)
            if !self.is_special {
                // Update account's due payment.
                self.account.storage_stat.due_payment = storage_fees_due;
            }
        };

        // Adjust message value.
        if adjust_msg_value && self.message_balance_remaining.tokens > self.account.balance.tokens {
            self.message_balance_remaining.tokens = self.account.balance.tokens;
        }

        // Add fees.
        self.total_fees.try_add_assign(storage_fees_collected)?;

        // Done
        Ok(StoragePhase {
            storage_fees_collected,
            storage_fees_due,
            status_change,
        })
    }

    // === Compute Phase ===

    pub fn compute_phase(&mut self) -> Result<ComputePhase> {
        let is_masterchain = is_masterchain(self.workchain);

        // Adjust original balance for action phase.
        self.original_balance = self.account.balance.clone();
        self.original_balance
            .try_sub_assign(&self.message_balance_remaining)?;

        // Compute VM gas limits.
        if self.account.balance.tokens.is_zero() {
            return Ok(ComputePhase::Skipped(SkippedComputePhase {
                reason: ComputePhaseSkipReason::NoGas,
            }));
        }

        let gas = self.config.compute_gas_params(
            &self.account.balance.tokens,
            &self.message_balance_remaining.tokens,
            self.is_special,
            is_masterchain,
            self.input.is_ordinary(),
            self.is_in_msg_external,
        );
        if gas.limit == 0 && gas.credit == 0 {
            return Ok(ComputePhase::Skipped(SkippedComputePhase {
                reason: ComputePhaseSkipReason::NoGas,
            }));
        }

        // Apply internal message state.
        let Some(addr) = self.account.address.as_std() else {
            anyhow::bail!("unexpected account address type");
        };
        anyhow::ensure!(addr.anycast.is_none(), "anycast is not supported");

        let state_libs;
        let msg_libs;
        match (&mut self.msg_state_init, &self.account.state) {
            // Uninit account cannot run anything without deploy.
            (None, AccountState::Uninit) => {
                return Ok(ComputePhase::Skipped(SkippedComputePhase {
                    reason: ComputePhaseSkipReason::NoState,
                }))
            }
            // Frozen account cannot run anything until receives its old state.
            (None, AccountState::Frozen { .. }) => {
                return Ok(ComputePhase::Skipped(SkippedComputePhase {
                    reason: ComputePhaseSkipReason::BadState,
                }))
            }
            // Active account simply runs its code. (use libraries from its state).
            (None, AccountState::Active(StateInit { libraries, .. })) => {
                state_libs = Some(libraries);
                msg_libs = None;
            }
            // Received a new state init for an uninit account or an old state for a frozen account.
            (Some(from_msg), AccountState::Uninit | AccountState::Frozen(..)) => {
                let target_hash = if let AccountState::Frozen(old_hash) = &self.account.state {
                    old_hash
                } else {
                    &addr.address
                };

                if &from_msg.hash != target_hash {
                    // State hash mismatch, cannot use this state.
                    return Ok(ComputePhase::Skipped(SkippedComputePhase {
                        reason: ComputePhaseSkipReason::BadState,
                    }));
                }

                // Use state from the message.
                let old_code = std::mem::replace(&mut self.new_code, from_msg.parsed.code.clone());
                let old_data = std::mem::replace(&mut self.new_data, from_msg.parsed.data.clone());
                let old_libs =
                    std::mem::replace(&mut self.new_libraries, from_msg.parsed.libraries.clone());

                // Check if we can use this new state.
                let mut limits = self.config.size_limits.clone();
                if is_masterchain && matches!(&self.account.state, AccountState::Uninit) {
                    // Forbid public libraries when deploying, allow for unfreezing.
                    limits.max_acc_public_libraries = 0;
                }

                if matches!(
                    check_state_limits(
                        &self.account.state,
                        &self.new_code,
                        &self.new_data,
                        &self.new_libraries,
                        &limits
                    ),
                    StateLimitsResult::Exceeds
                ) {
                    self.new_code = old_code;
                    self.new_data = old_data;
                    self.new_libraries = old_libs;
                    return Ok(ComputePhase::Skipped(SkippedComputePhase {
                        reason: ComputePhaseSkipReason::BadState,
                    }));
                }

                // Use state
                from_msg.used = true;

                // Use libraries.
                state_libs = None;
                msg_libs = Some(from_msg.parsed.libraries.clone());
            }
            (Some(from_msg), AccountState::Active(StateInit { libraries, .. })) => {
                // Check if a state from the external message has the correct hash.
                if self.is_in_msg_external && from_msg.hash != addr.address {
                    return Ok(ComputePhase::Skipped(SkippedComputePhase {
                        reason: ComputePhaseSkipReason::BadState,
                    }));
                }

                // Use libraries.
                state_libs = Some(libraries);
                msg_libs = Some(from_msg.parsed.libraries.clone());
            }
        }

        // Run vm.
        let stack = self.prepare_vm_stack(addr);

        let mut code = self.new_code.clone();

        let smc_info = SmcInfoBase::new()
            .with_now(self.params.block_unixtime)
            .with_block_lt(self.params.block_lt)
            .with_tx_lt(self.start_lt)
            .with_mixed_rand_seed(&self.params.rand_seed, &addr.address)
            .with_account_balance(self.account.balance.clone())
            .with_account_addr(addr.clone().into())
            .with_config(self.config.raw.clone())
            .require_ton_v4()
            .with_code(code.clone().unwrap_or_default())
            .with_message_balance(self.message_balance_remaining.clone())
            .with_storage_fees(self.total_fees) // TODO: Replace with storage fees
            .require_ton_v6()
            .with_unpacked_config(self.config.unpacked.as_tuple());

        // Special case for library cells as code root.
        if let Some(code) = &mut code {
            if code.is_exotic() {
                *code = CellBuilder::build_from(&*code)?;
            }
        }

        let libraries = (msg_libs, state_libs, &self.params.libraries);
        let mut vm = VmState::builder()
            .with_smc_info(smc_info)
            .with_code_opt(code)
            .with_data(self.new_data.clone().unwrap_or_default())
            .with_libraries(&libraries)
            .with_init_selector(false)
            .with_raw_stack(stack)
            .with_gas(gas)
            .with_modifiers(self.params.modifiers)
            .build();

        let exit_code = !vm.run();

        // Parse VM state.
        let accepted = vm.gas.credit() == 0;
        if !accepted && self.is_in_msg_external {
            anyhow::bail!(ExtMsgRejected {
                reason: ExtMsgRejectedReason::NotAccepted,
            })
        }
        let success = accepted && vm.commited_state.is_some();

        let gas_used = std::cmp::min(vm.gas.consumed(), vm.gas.limit());
        let gas_fees = if accepted && !self.is_special {
            self.config
                .gas_prices(is_masterchain)
                .compute_gas_fee(gas_used)
        } else {
            // We don't add any fees for messages that were not accepted.
            Tokens::ZERO
        };

        let msg_state_used = if let Some(s) = &self.msg_state_init {
            self.account_activated = accepted && s.used;
            s.used
        } else {
            false
        };

        if let Some(commited) = vm.commited_state {
            if accepted {
                self.new_data = Some(commited.c4);
                self.actions = Some(commited.c5);
            }
        }

        self.account.balance.try_sub_assign_tokens(gas_fees)?;
        self.total_fees.try_add_assign(gas_fees)?;

        Ok(ComputePhase::Executed(ExecutedComputePhase {
            success,
            msg_state_used,
            account_activated: self.account_activated,
            gas_fees,
            gas_used: new_varuint56_truncate(gas_used),
            gas_limit: new_varuint56_truncate(gas.limit),
            gas_credit: (gas.credit != 0).then(|| {
                VarUint24::new(std::cmp::min(gas.credit, VarUint24::MAX.into_inner() as u64) as _)
            }),
            mode: 0,
            exit_code,
            exit_arg: if success {
                None
            } else {
                vm.stack.get_exit_arg().filter(|x| *x != 0)
            },
            vm_steps: vm.steps.try_into().unwrap_or(u32::MAX),
            vm_init_state_hash: HashBytes::ZERO,
            vm_final_state_hash: HashBytes::ZERO,
        }))
    }

    fn prepare_vm_stack(&self, addr: &StdAddr) -> SafeRc<Stack> {
        SafeRc::new(Stack::with_items(match &self.input {
            TransactionInput::Ordinary { msg_root } => {
                tuple![
                    int self.account.balance.tokens.into_inner(),
                    int self.message_balance_remaining.tokens.into_inner(),
                    cell msg_root.clone(),
                    slice self.msg_body.clone(),
                    int if self.is_in_msg_external { -1 } else { 0 },
                ]
            }
            TransactionInput::TickTock(ty) => {
                tuple![
                    int self.account.balance.tokens.into_inner(),
                    int BigInt::from_bytes_be(Sign::Plus, addr.address.as_array()),
                    int match ty {
                        TickTock::Tick => 0,
                        TickTock::Tock => -1,
                    },
                    int -2,
                ]
            }
        }))
    }

    // === Action Phase ===

    pub fn action_phase(&mut self, mut actions: Cell) -> Result<ActionPhase> {
        const MAX_ACTIONS: u16 = 255;

        let mut needs_bounce = false;
        let mut phase = ActionPhase {
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
            action_list_hash: *actions.repr_hash(),
            total_message_size: StorageUsedShort::ZERO,
        };

        let old_code = self.new_code.as_ref();
        let old_data = self.new_data.as_ref();
        let old_libx = self.new_libraries.root().as_ref();

        // Unpack actions list.
        let mut action_idx = 0u16;

        let mut list = Vec::new();
        let mut actions = actions.as_ref();
        loop {
            if actions.is_exotic() {
                // Actions list item must be an ordinary cell.
                phase.result_code = ResultCode::ActionListInvalid as i32;
                phase.result_arg = Some(action_idx as _);
                phase.valid = false;
                return Ok(phase);
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
                    phase.result_code = ResultCode::ActionListInvalid as i32;
                    phase.result_arg = Some(action_idx as _);
                    phase.valid = false;
                    return Ok(phase);
                }
            };

            action_idx += 1;
            if action_idx > MAX_ACTIONS {
                // There can be at most N actions.
                phase.result_code = ResultCode::TooManyActions as i32;
                phase.result_arg = Some(action_idx as _);
                phase.valid = false;
                return Ok(phase);
            }
        }

        phase.total_actions = action_idx;

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
                    phase.skipped_actions += 1;
                    parsed_list.push(None);
                    continue;
                } else if mode.contains(SendMsgFlags::BOUNCE_ON_ERROR) {
                    // "BOUNCE_ON_ERROR" flag means that we fail the action phase,
                    // but require a bounce phase to run afterwards.
                    needs_bounce = true;
                }
            }

            phase.result_code = ResultCode::ActionInvalid as i32;
            phase.result_arg = Some(action_idx as _);
            phase.valid = false;
            return Ok(phase);
        }

        // Action list itself is ok.
        phase.valid = true;

        // Execute actions.
        let mut remaining_balance = self.account.balance.clone();
        let mut reserved_balance = CurrencyCollection::ZERO;
        let mut new_code = None;
        let mut new_libs = self.new_libraries.clone();

        for (action_idx, action) in parsed_list.into_iter().enumerate() {
            let Some(action) = action else {
                continue;
            };

            phase.result_arg = Some(action_idx as _);

            let mut ctx = ActionContext {
                need_bounce_on_fail: false,
                remaining_balance: &mut remaining_balance,
                reserved_balance: &mut reserved_balance,
                new_code: &mut new_code,
                new_libs: &mut new_libs,
                result_code: None,
                special_actions: &mut phase.special_actions,
            };

            let res = match action {
                OutAction::SendMsg { mode, out_msg } => todo!(),
                OutAction::SetCode { new_code } => self.do_set_code(new_code, &mut ctx),
                OutAction::ReserveCurrency { mode, value } => {
                    self.do_reserve_currency(mode, value, &mut ctx)
                }
                OutAction::ChangeLibrary { mode, lib } => {
                    self.do_change_library(mode, lib, &mut ctx)
                }
                OutAction::CopyLeft { license, address } => todo!(),
            };
        }

        Ok(())
    }

    /// `SetCode` action.
    fn do_set_code(&self, new_code: Cell, ctx: &mut ActionContext<'_>) -> Result<(), ActionFailed> {
        // Update context.
        *ctx.new_code = Some(new_code);
        *ctx.special_actions += 1;

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
                reserve = self.original_balance.checked_sub(&reserve)?;
            } else {
                reserve.try_add_assign(&self.original_balance)?;
            }
        } else if mode.contains(ReserveCurrencyFlags::REVERSE) {
            // Invalid mode.
            return Err(ActionFailed);
        }

        if mode.contains(ReserveCurrencyFlags::IGNORE_ERROR) {
            // Clamp balance.
            reserve = reserve.checked_clamp(ctx.remaining_balance)?;
        }

        // Reserve balance.
        let mut new_balance = CurrencyCollection {
            tokens: match ctx.remaining_balance.tokens.checked_sub(reserve.tokens) {
                Some(tokens) => tokens,
                None => {
                    ctx.result_code = Some(ResultCode::NotEnoughBalance);
                    return Err(ActionFailed);
                }
            },
            other: match ctx.remaining_balance.other.checked_sub(&reserve.other) {
                Ok(other) => other,
                Err(_) => {
                    ctx.result_code = Some(ResultCode::NotEnoughExtraBalance);
                    return Err(ActionFailed);
                }
            },
        };

        // Apply "ALL_BUT" flag. Leave only "new_balance", reserve everything else.
        if mode.contains(ReserveCurrencyFlags::ALL_BUT) {
            std::mem::swap(&mut new_balance, &mut reserve);
        }

        // Update context.
        *ctx.remaining_balance = new_balance;
        ctx.reserved_balance.try_add_assign(&reserve)?;
        *ctx.special_actions += 1;

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
            if let Ok(Some(prev)) = ctx.new_libs.get(hash) {
                if prev.public == add_public {
                    // Do nothing if library already exists with the same `public` flag.
                    *ctx.special_actions += 1;
                    return Ok(());
                }
            }

            let LibRef::Cell(root) = lib else {
                ctx.result_code = Some(ResultCode::NoLibCode);
                return Err(ActionFailed);
            };

            let mut stats = ExtStorageStat::with_limits(MAX_ALLOWED_MERKLE_DEPTH, CellTreeStats {
                bit_count: u64::MAX,
                cell_count: self.config.size_limits.max_library_cells as u64,
            });
            if !stats.add_cell(root.as_ref()) {
                ctx.result_code = Some(ResultCode::LibOutOfLimits);
                return Err(ActionFailed);
            }

            // Add library.
            if ctx
                .new_libs
                .set(*root.repr_hash(), SimpleLib {
                    public: add_public,
                    root,
                })
                .is_err()
            {
                ctx.result_code = Some(ResultCode::InvalidLibrariesDict);
                return Err(ActionFailed);
            }
        } else {
            // Remove library.
            if ctx.new_libs.remove(hash).is_err() {
                ctx.result_code = Some(ResultCode::InvalidLibrariesDict);
                return Err(ActionFailed);
            }
        }

        // Update context.
        *ctx.special_actions += 1;

        // Done
        Ok(())
    }
}

struct ActionContext<'a> {
    need_bounce_on_fail: bool,
    remaining_balance: &'a mut CurrencyCollection,
    reserved_balance: &'a mut CurrencyCollection,
    new_code: &'a mut Option<Cell>,
    new_libs: &'a mut Dict<HashBytes, SimpleLib>,
    result_code: Option<ResultCode>,
    special_actions: &'a mut u16,
}

struct ActionFailed;

impl From<anyhow::Error> for ActionFailed {
    #[inline]
    fn from(_: anyhow::Error) -> Self {
        Self
    }
}

impl From<everscale_types::error::Error> for ActionFailed {
    #[inline]
    fn from(_: everscale_types::error::Error) -> Self {
        Self
    }
}

enum StateLimitsResult {
    Unchanged,
    Exceeds,
    Fits,
}

fn new_varuint56_truncate(value: u64) -> VarUint56 {
    VarUint56::new(std::cmp::min(value, VarUint56::MAX.into_inner()))
}

fn check_state_limits(
    state: &AccountState,
    new_code: &Option<Cell>,
    new_data: &Option<Cell>,
    new_libs: &Dict<HashBytes, SimpleLib>,
    limits: &SizeLimitsConfig,
) -> StateLimitsResult {
    let (old_code, old_data, old_libs) = match state {
        AccountState::Active(state) => (
            state.code.as_ref(),
            state.data.as_ref(),
            state.libraries.root().as_ref(),
        ),
        AccountState::Uninit | AccountState::Frozen(..) => (None, None, None),
    };

    // Early exit if nothing changed.
    if old_code == new_code.as_ref()
        && old_data == new_data.as_ref()
        && old_libs == new_libs.root().as_ref()
    {
        return StateLimitsResult::Unchanged;
    }

    // Compute storage stats.
    let mut stats = ExtStorageStat::with_limits(MAX_ALLOWED_MERKLE_DEPTH, CellTreeStats {
        bit_count: limits.max_acc_state_bits as u64,
        cell_count: limits.max_acc_state_cells as u64,
    });

    if let Some(code) = new_code {
        if !stats.add_cell(code.as_ref()) {
            return StateLimitsResult::Exceeds;
        }
    }

    if let Some(data) = new_data {
        if !stats.add_cell(data.as_ref()) {
            return StateLimitsResult::Exceeds;
        }
    }

    if let Some(libs) = new_libs.root() {
        if !stats.add_cell(libs.as_ref()) {
            return StateLimitsResult::Exceeds;
        }
    }

    // Check public libraries.
    if old_libs != new_libs.root().as_ref() {
        let mut public_libs_count = 0;
        for lib in new_libs.values() {
            let Ok(lib) = lib else {
                return StateLimitsResult::Exceeds;
            };

            public_libs_count += lib.public as usize;
            if public_libs_count > limits.max_acc_public_libraries as usize {
                return StateLimitsResult::Exceeds;
            }
        }
    }

    // Ok
    StateLimitsResult::Fits
}
