use anyhow::Result;
use everscale_types::models::{AccountState, AccountStatusChange, CreditPhase, StoragePhase};
use everscale_types::num::Tokens;

use crate::util::is_masterchain;
use crate::ExecutorState;

impl ExecutorState<'_> {
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
        let mut to_pay = self.config.compoute_storage_fees(
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
}
