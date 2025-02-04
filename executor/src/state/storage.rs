use anyhow::Result;
use everscale_types::models::{AccountState, AccountStatusChange, StoragePhase};
use everscale_types::num::Tokens;

use crate::state::receive::ReceivedMessage;
use crate::state::ExecutorState;

pub struct StoragePhaseContext<'a> {
    /// Whether to delete frozen accounts who can't pay
    /// the required sum ([`delete_due_limit`]).
    ///
    /// [`delete_due_limit`]: everscale_types::models::GasLimitsPrices::delete_due_limit
    pub allow_delete_frozen_accounts: bool,
    /// Whether to adjust remaining message balance
    /// if it becomes greater than the account balance.
    pub adjust_msg_balance: bool,
    /// Received message (external or internal).
    pub received_message: Option<&'a mut ReceivedMessage>,
}

impl ExecutorState<'_> {
    /// Storage phase of ordinary or ticktock transactions.
    ///
    /// - Precedes the credit phase when [`bounce_enabled`],
    ///   otherwise must be called after it;
    /// - Necessary for all types of messages or even without them;
    /// - Computes storage fee and due payment;
    /// - Tries to charge the account balance for the storage fees;
    /// - Freezes or deletes the account if its balance is not enough
    ///   (doesn't change the state itself, but rather tells other
    ///   phases to do so).
    ///
    /// Returns an executed [`StoragePhase`].
    ///
    /// Fails if called in an older context than account's [`last_paid`].
    /// Can also fail on [`total_fees`] overflow, but this should
    /// not happen on networks with valid value flow.
    ///
    /// [`bounce_enabled`]: ReceivedMessage::bounce_enabled
    /// [`last_paid`]: everscale_types::models::StorageInfo::last_paid
    /// [`total_fees`]: Self::total_fees
    pub fn storage_phase(&mut self, ctx: StoragePhaseContext<'_>) -> Result<StoragePhase> {
        anyhow::ensure!(
            self.params.block_unixtime >= self.storage_stat.last_paid,
            "current unixtime is less than the account last_paid",
        );

        let is_masterchain = self.address.is_masterchain();
        let config = self.config.gas_prices(is_masterchain);

        // Compute how much this account must pay for storing its state up until now.
        let mut to_pay = self.config.compute_storage_fees(
            &self.storage_stat,
            self.params.block_unixtime,
            self.is_special,
            is_masterchain,
        );
        if let Some(due_payment) = self.storage_stat.due_payment {
            // NOTE: We are using saturating math here to reduce strange
            // invariants. If account must pay more than `Tokens::MAX`,
            // it will certanly be frozen in almost any real scenario.
            to_pay = to_pay.saturating_add(due_payment);
        }

        // Update `last_paid` (only for ordinary accounts).
        self.storage_stat.last_paid = if self.is_special {
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
        } else if let Some(new_balance) = self.balance.tokens.checked_sub(to_pay) {
            // Account balance is enough to pay storage fees.
            storage_fees_collected = to_pay;
            storage_fees_due = None;
            status_change = AccountStatusChange::Unchanged;

            // Update account balance.
            self.balance.tokens = new_balance;
            // Reset `due_payment` if there was any.
            self.storage_stat.due_payment = None;
        } else {
            // Account balance is not enough to pay storage fees,
            // so we use all of its balance and try to freeze the account.
            let fees_due = to_pay - self.balance.tokens;

            storage_fees_collected = std::mem::take(&mut self.balance.tokens);
            storage_fees_due = Some(fees_due).filter(|t| !t.is_zero());

            debug_assert!(self.balance.tokens.is_zero());

            // NOTE: Keep all cases explicit here without "default" branch.
            status_change = match &self.state {
                // Do nothing for special accounts.
                _ if self.is_special => AccountStatusChange::Unchanged,
                // Try to delete account.
                AccountState::Uninit | AccountState::Frozen { .. }
                    if (matches!(&self.state, AccountState::Uninit)
                        || ctx.allow_delete_frozen_accounts)
                        && fees_due.into_inner() > config.delete_due_limit as u128
                        && !self.balance.other.is_empty() =>
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

            if !self.is_special {
                // Update account's due payment.
                self.storage_stat.due_payment = storage_fees_due;
            }
        };

        // Adjust message value.
        if let Some(msg) = ctx.received_message {
            if ctx.adjust_msg_balance && msg.balance_remaining.tokens > self.balance.tokens {
                msg.balance_remaining.tokens = self.balance.tokens;
            }
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
