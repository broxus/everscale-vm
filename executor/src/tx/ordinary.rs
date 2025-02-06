use anyhow::{anyhow, Context};
use everscale_types::models::{AccountStatus, ComputePhase, OrdinaryTxInfo};
use everscale_types::num::Tokens;
use everscale_types::prelude::*;

use crate::error::{TxError, TxResult};
use crate::phase::{
    ActionPhaseContext, BouncePhaseContext, ComputePhaseContext, ComputePhaseFull,
    StoragePhaseContext, TransactionInput,
};
use crate::ExecutorState;

impl ExecutorState<'_> {
    pub fn run_ordinary_transaction(
        &mut self,
        is_external: bool,
        msg_root: Cell,
    ) -> TxResult<OrdinaryTxInfo> {
        // Receive inbound message.
        let mut msg = match self.receive_in_msg(msg_root) {
            Ok(msg) if msg.is_external == is_external => msg,
            Ok(_) => {
                return Err(TxError::Fatal(anyhow!(
                    "received an unexpected inbound message"
                )))
            }
            // Invalid external messages can be safely skipped.
            Err(_) if is_external => return Err(TxError::Skipped),
            Err(e) => return Err(TxError::Fatal(e)),
        };

        // Order of credit and storage phases depends on the `bounce` flag
        // of the inbound message.
        let storage_phase;
        let credit_phase;
        if msg.bounce_enabled {
            // Run storage phase.
            storage_phase = self
                .storage_phase(StoragePhaseContext {
                    adjust_msg_balance: false,
                    received_message: Some(&mut msg),
                })
                .context("storage phase failed")?;

            // Run credit phase (only for internal messages).
            credit_phase = if is_external {
                None
            } else {
                Some(self.credit_phase(&msg).context("credit phase failed")?)
            };
        } else {
            // Run credit phase (only for internal messages).
            credit_phase = if is_external {
                None
            } else {
                Some(self.credit_phase(&msg).context("credit phase failed")?)
            };

            // Run storage phase.
            storage_phase = self
                .storage_phase(StoragePhaseContext {
                    adjust_msg_balance: true,
                    received_message: Some(&mut msg),
                })
                .context("storage phase failed")?;
        }

        // Run compute phase.
        let ComputePhaseFull {
            compute_phase,
            accepted,
            original_balance,
            new_state,
            actions,
        } = self
            .compute_phase(ComputePhaseContext {
                input: TransactionInput::Ordinary(&msg),
            })
            .context("compute phase failed")?;

        if !accepted {
            debug_assert!(is_external);
            // Not accepted external message can be safely ignored.
            return Err(TxError::Skipped);
        }

        // Run action phase only if compute phase succeeded.
        let mut aborted = true;
        let mut state_exceeds_limits = false;
        let mut bounce_required = false;
        let mut action_fine = Tokens::ZERO;
        let mut destroyed = false;

        let mut action_phase = None;
        if let ComputePhase::Executed(compute_phase) = &compute_phase {
            if compute_phase.success {
                let res = self
                    .action_phase(ActionPhaseContext {
                        received_message: Some(&mut msg),
                        original_balance,
                        new_state,
                        actions,
                        compute_phase,
                    })
                    .context("action phase failed")?;

                aborted = !res.action_phase.success;
                state_exceeds_limits = res.state_exceeds_limits;
                bounce_required = res.bounce;
                action_fine = res.action_fine;
                destroyed = self.end_status == AccountStatus::NotExists;

                action_phase = Some(res.action_phase);
            }
        }

        // Run bounce phase for internal messages if something failed.
        let mut bounce_phase = None;
        if msg.bounce_enabled
            && (!matches!(&compute_phase, ComputePhase::Executed(p) if p.success)
                || state_exceeds_limits
                || bounce_required)
        {
            debug_assert!(!is_external);

            let gas_fees = match &compute_phase {
                ComputePhase::Executed(phase) => phase.gas_fees,
                ComputePhase::Skipped(_) => Tokens::ZERO,
            };

            bounce_phase = Some(
                self.bounce_phase(BouncePhaseContext {
                    gas_fees,
                    action_fine,
                    received_message: &msg,
                })
                .context("bounce phase failed")?,
            );
        }

        // Build transaction info.
        Ok(OrdinaryTxInfo {
            credit_first: !msg.bounce_enabled,
            storage_phase: Some(storage_phase),
            credit_phase,
            compute_phase,
            action_phase,
            aborted,
            bounce_phase,
            destroyed,
        })
    }
}
