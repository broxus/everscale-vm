use anyhow::Result;
use everscale_types::cell::{Cell, CellBuilder, CellSliceRange, CellTreeStats, HashBytes, Load};
use everscale_types::models::{
    AccountState, AccountStatusChange, ComputePhase, ComputePhaseSkipReason, CreditPhase,
    CurrencyCollection, ExecutedComputePhase, MsgInfo, SkippedComputePhase, StateInit, StdAddr,
    StoragePhase, TickTock,
};
use everscale_types::num::{Tokens, VarUint24, VarUint56};
use num_bigint::{BigInt, Sign};
use tycho_vm::{tuple, SafeRc, SmcInfoBase, Stack, VmState};

use crate::util::{is_masterchain, ExtStorageStat};
use crate::{ExecutorState, ExtMsgRejected, ExtMsgRejectedReason, MsgStateInit, TransactionInput};

impl ExecutorState<'_> {
    // === Receive Inbound Message ===

    pub fn receive_in_msg(&mut self, msg_root: Cell) -> Result<()> {
        const MAX_ALLOWED_MERKLE_DEPTH: u8 = 2;

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

                // Use state from message.
                self.new_code = from_msg.parsed.code.clone();
                self.new_data = from_msg.parsed.data.clone();
                // TODO: Check size limits (with `max_acc_public_libraries`)
                from_msg.used = true;

                // Use libraries.
                state_libs = None;
                msg_libs = Some(from_msg.parsed.libraries.clone());
            }
            (Some(from_msg), AccountState::Active(StateInit { libraries, .. })) => {
                state_libs = Some(libraries);
                msg_libs = Some(from_msg.parsed.libraries.clone());
            }
        }

        if let Some(from_msg) = &self.msg_state_init {
            if self.is_in_msg_external && from_msg.hash != addr.address {
                return Ok(ComputePhase::Skipped(SkippedComputePhase {
                    reason: ComputePhaseSkipReason::BadState,
                }));
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
}

fn new_varuint56_truncate(value: u64) -> VarUint56 {
    VarUint56::new(std::cmp::min(value, VarUint56::MAX.into_inner()))
}
