use anyhow::Result;
use everscale_types::models::CreditPhase;

use crate::phase::receive::ReceivedMessage;
use crate::ExecutorState;

impl ExecutorState<'_> {
    /// Credit phase of ordinary transactions.
    ///
    /// - Adds the remainder of the message balance to the account balance;
    /// - Requires calling the [`receive_in_msg`] first;
    /// - Only makes sense for internal messages;
    /// - Follows the storage phase when [`bounce_enabled`],
    ///   otherwise must be called before it.
    ///
    /// Returns an executed [`CreditPhase`].
    ///
    /// Fails only on account balance overflow. This should not happen on networks
    /// with valid value flow.
    ///
    /// [`receive_in_msg`]: Self::receive_in_msg
    /// [`bounce_enabled`]: ReceivedMessage::bounce_enabled
    pub fn credit_phase(&mut self, received: &ReceivedMessage) -> Result<CreditPhase> {
        // Remaining message balance is added to the account balamce.
        self.balance.try_add_assign(&received.balance_remaining)?;

        Ok(CreditPhase {
            // Due payment is only collected in storage phase.
            // For messages with bounce flag, contract always receives
            // the amount specified in message.
            due_fees_collected: None,
            credit: received.balance_remaining.clone(),
        })
    }
}
