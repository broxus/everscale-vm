use anyhow::Result;
use everscale_types::models::{
    AccountState, AccountStatus, ComputePhase, ComputePhaseSkipReason, CurrencyCollection,
    ExecutedComputePhase, SkippedComputePhase, StateInit, TickTock,
};
use everscale_types::num::Tokens;
use everscale_types::prelude::*;
use num_bigint::{BigInt, Sign};
use tycho_vm::{tuple, SafeRc, SmcInfoBase, Stack, VmState};

use crate::phase::receive::{MsgStateInit, ReceivedMessage};
use crate::util::{
    check_state_limits_diff, new_varuint24_truncate, new_varuint56_truncate, StateLimitsResult,
};
use crate::ExecutorState;

/// Compute phase input context.
pub struct ComputePhaseContext<'a> {
    /// Parsed transaction input.
    pub input: TransactionInput<'a>,
    /// Fees collected during the storage phase.
    pub storage_fee: Tokens,
}

/// Parsed transaction input.
#[derive(Debug, Clone, Copy)]
pub enum TransactionInput<'a> {
    Ordinary(&'a ReceivedMessage),
    TickTock(TickTock),
}

impl<'a> TransactionInput<'a> {
    const fn is_ordinary(&self) -> bool {
        matches!(self, Self::Ordinary(_))
    }

    fn in_msg(&self) -> Option<&'a ReceivedMessage> {
        match self {
            Self::Ordinary(msg) => Some(msg),
            Self::TickTock(_) => None,
        }
    }

    fn in_msg_init(&self) -> Option<&'a MsgStateInit> {
        match self {
            Self::Ordinary(msg) => msg.init.as_ref(),
            Self::TickTock(_) => None,
        }
    }
}

/// Executed compute phase with additional info.
pub struct ComputePhaseFull {
    /// Resulting comput phase.
    pub compute_phase: ComputePhase,
    /// Whether the inbound message was accepted.
    ///
    /// NOTE: Message can be accepted even without a commited state,
    /// so we can't use [`ExecutedComputePhase::success`].
    pub accepted: bool,
    /// Original account balance before this phase.
    pub original_balance: CurrencyCollection,
    /// New account state.
    pub new_state: StateInit,
    /// Resulting actions list.
    pub actions: Cell,
}

impl ExecutorState<'_> {
    /// Compute phase of ordinary or ticktock transactions.
    ///
    /// - Tries to deploy or unfreeze account if it was [`Uninit`] or [`Frozen`];
    /// - Executes contract code and produces a new account state;
    /// - Produces an action list on successful execution;
    /// - External messages can be ignored if they were not accepted;
    /// - Necessary for all types of messages or even without them;
    ///
    /// Returns an executed [`ComputePhase`] with extra data.
    ///
    /// Fails only on account balance overflow. This should not happen on networks
    /// with valid value flow.
    ///
    /// [`Uninit`]: AccountState::Uninit
    /// [`Frozen`]: AccountState::Frozen
    pub fn compute_phase(&mut self, ctx: ComputePhaseContext<'_>) -> Result<ComputePhaseFull> {
        let is_masterchain = self.address.is_masterchain();

        // Compute original balance for the action phase.
        let mut original_balance = self.balance.clone();
        if let Some(msg) = ctx.input.in_msg() {
            original_balance.try_sub_assign(&msg.balance_remaining)?;
        }

        // Prepare full phase output.
        let new_state = if let AccountState::Active(current) = &self.state {
            current.clone()
        } else {
            Default::default()
        };

        let mut res = ComputePhaseFull {
            compute_phase: ComputePhase::Skipped(SkippedComputePhase {
                reason: ComputePhaseSkipReason::NoGas,
            }),
            accepted: false,
            original_balance,
            new_state,
            actions: Cell::empty_cell(),
        };

        // Compute VM gas limits.
        if self.balance.tokens.is_zero() {
            res.compute_phase = ComputePhase::Skipped(SkippedComputePhase {
                reason: ComputePhaseSkipReason::NoGas,
            });
            return Ok(res);
        }

        let (msg_balance_remaining, is_external) = match ctx.input.in_msg() {
            Some(msg) => (msg.balance_remaining.clone(), msg.is_external),
            None => (CurrencyCollection::ZERO, false),
        };

        let gas = self.config.compute_gas_params(
            &self.balance.tokens,
            &msg_balance_remaining.tokens,
            self.is_special,
            is_masterchain,
            ctx.input.is_ordinary(),
            is_external,
        );
        if gas.limit == 0 && gas.credit == 0 {
            res.compute_phase = ComputePhase::Skipped(SkippedComputePhase {
                reason: ComputePhaseSkipReason::NoGas,
            });
            return Ok(res);
        }

        // Apply internal message state.
        let state_libs;
        let msg_libs;
        let msg_state_used;
        match (ctx.input.in_msg_init(), &self.state) {
            // Uninit account cannot run anything without deploy.
            (None, AccountState::Uninit) => {
                res.compute_phase = ComputePhase::Skipped(SkippedComputePhase {
                    reason: ComputePhaseSkipReason::NoState,
                });
                return Ok(res);
            }
            // Frozen account cannot run anything until receives its old state.
            (None, AccountState::Frozen { .. }) => {
                res.compute_phase = ComputePhase::Skipped(SkippedComputePhase {
                    reason: ComputePhaseSkipReason::BadState,
                });
                return Ok(res);
            }
            // Active account simply runs its code. (use libraries from its state).
            (None, AccountState::Active(StateInit { libraries, .. })) => {
                state_libs = Some(libraries);
                msg_libs = None;
                msg_state_used = false;
            }
            // Received a new state init for an uninit account or an old state for a frozen account.
            (Some(from_msg), AccountState::Uninit | AccountState::Frozen(..)) => {
                let target_hash = if let AccountState::Frozen(old_hash) = &self.state {
                    old_hash
                } else {
                    &self.address.address
                };

                if from_msg.hash != *target_hash || from_msg.parsed.split_depth.is_some() {
                    // State hash mismatch, cannot use this state.
                    // We also forbid using `split_depth` (for now).
                    res.compute_phase = ComputePhase::Skipped(SkippedComputePhase {
                        reason: ComputePhaseSkipReason::BadState,
                    });
                    return Ok(res);
                }

                // Check if we can use the new state from the message.
                let mut limits = self.config.size_limits.clone();
                if is_masterchain && matches!(&self.state, AccountState::Uninit) {
                    // Forbid public libraries when deploying, allow for unfreezing.
                    limits.max_acc_public_libraries = 0;
                }

                if matches!(
                    check_state_limits_diff(
                        &res.new_state,
                        &from_msg.parsed,
                        &limits,
                        is_masterchain,
                        &mut self.cached_storage_stat,
                    ),
                    StateLimitsResult::Exceeds
                ) {
                    res.compute_phase = ComputePhase::Skipped(SkippedComputePhase {
                        reason: ComputePhaseSkipReason::BadState,
                    });
                    return Ok(res);
                }

                // NOTE: At this point the `cached_storage_stat` will always contain
                // visited cells because previous state was not active and we
                // handled a case when check overflowed.

                // Use state
                res.new_state = from_msg.parsed.clone();
                self.state = AccountState::Active(res.new_state.clone());
                msg_state_used = true;

                // Use libraries.
                state_libs = None;
                msg_libs = Some(from_msg.parsed.libraries.clone());
            }
            (Some(from_msg), AccountState::Active(StateInit { libraries, .. })) => {
                // Check if a state from the external message has the correct hash.
                if is_external && from_msg.hash != self.address.address {
                    res.compute_phase = ComputePhase::Skipped(SkippedComputePhase {
                        reason: ComputePhaseSkipReason::BadState,
                    });
                    return Ok(res);
                }

                // We use only libraries here.
                msg_state_used = false;

                // Use libraries.
                state_libs = Some(libraries);
                msg_libs = Some(from_msg.parsed.libraries.clone());
            }
        }

        // Run vm.
        let stack = self.prepare_vm_stack(ctx.input);

        let mut code = res.new_state.code.clone();

        let smc_info = SmcInfoBase::new()
            .with_now(self.params.block_unixtime)
            .with_block_lt(self.params.block_lt)
            .with_tx_lt(self.start_lt)
            .with_mixed_rand_seed(&self.params.rand_seed, &self.address.address)
            .with_account_balance(self.balance.clone())
            .with_account_addr(self.address.clone().into())
            .with_config(self.config.raw.clone())
            .require_ton_v4()
            .with_code(code.clone().unwrap_or_default())
            .with_message_balance(msg_balance_remaining.clone())
            .with_storage_fees(ctx.storage_fee)
            .require_ton_v6()
            .with_unpacked_config(self.config.unpacked.as_tuple())
            .require_ton_v9();

        // Special case for library cells as code root.
        if let Some(code) = &mut code {
            if code.is_exotic() {
                *code = CellBuilder::build_from(&*code).unwrap();
            }
        }

        let libraries = (msg_libs, state_libs, &self.params.libraries);
        let mut vm = VmState::builder()
            .with_smc_info(smc_info)
            .with_code_opt(code)
            .with_data(res.new_state.data.clone().unwrap_or_default())
            .with_libraries(&libraries)
            .with_init_selector(false)
            .with_raw_stack(stack)
            .with_gas(gas)
            .with_modifiers(self.params.vm_modifiers)
            .build();

        let exit_code = !vm.run();

        // Parse VM state.
        res.accepted = vm.gas.credit() == 0;
        debug_assert!(
            is_external || res.accepted,
            "internal messages must be accepted"
        );

        let success = res.accepted && vm.commited_state.is_some();

        let gas_used = std::cmp::min(vm.gas.consumed(), vm.gas.limit());
        let gas_fees = if res.accepted && !self.is_special {
            self.config
                .gas_prices(is_masterchain)
                .compute_gas_fee(gas_used)
        } else {
            // We don't add any fees for messages that were not accepted.
            Tokens::ZERO
        };

        let mut account_activated = false;
        if res.accepted && msg_state_used {
            account_activated = self.orig_status != AccountStatus::Active;
            self.end_status = AccountStatus::Active;
        }

        if let Some(commited) = vm.commited_state {
            if res.accepted {
                res.new_state.data = Some(commited.c4);
                res.actions = commited.c5;
            }
        }

        self.balance.try_sub_assign_tokens(gas_fees)?;
        self.total_fees.try_add_assign(gas_fees)?;

        res.compute_phase = ComputePhase::Executed(ExecutedComputePhase {
            success,
            msg_state_used,
            account_activated,
            gas_fees,
            gas_used: new_varuint56_truncate(gas_used),
            gas_limit: new_varuint56_truncate(gas.limit),
            gas_credit: (gas.credit != 0).then(|| new_varuint24_truncate(gas.credit)),
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
        });
        Ok(res)
    }

    fn prepare_vm_stack(&self, input: TransactionInput<'_>) -> SafeRc<Stack> {
        SafeRc::new(Stack::with_items(match input {
            TransactionInput::Ordinary(msg) => {
                tuple![
                    int self.balance.tokens.into_inner(),
                    int msg.balance_remaining.tokens.into_inner(),
                    cell msg.root.clone(),
                    slice msg.body.clone(),
                    int if msg.is_external { -1 } else { 0 },
                ]
            }
            TransactionInput::TickTock(ty) => {
                tuple![
                    int self.balance.tokens.into_inner(),
                    int BigInt::from_bytes_be(Sign::Plus, self.address.address.as_array()),
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
