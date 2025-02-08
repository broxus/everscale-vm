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

#[cfg(test)]
mod tests {
    use everscale_types::cell::Cell;
    use everscale_types::models::CurrencyCollection;
    use everscale_types::num::Tokens;

    use super::*;
    use crate::tests::{make_default_config, make_default_params};

    #[test]
    fn credit_phase_works() {
        let params = make_default_params();
        let config = make_default_config();

        let mut state = ExecutorState::new_uninit(
            &params,
            &config,
            &Default::default(),
            Tokens::new(1_000_000_000),
        );
        let prev_balance = state.balance.clone();
        let prev_total_fees = state.total_fees;

        let msg_balance = CurrencyCollection::from(Tokens::new(123_000_000_000));
        let credit_phase = state
            .credit_phase(&ReceivedMessage {
                root: Cell::default(),
                init: None,
                body: Default::default(),
                is_external: false,
                bounce_enabled: false,
                balance_remaining: msg_balance.clone(),
            })
            .unwrap();

        // No due fees must be collected on the credit phase.
        assert!(credit_phase.due_fees_collected.is_none());
        // Credit must be the same as message balance.
        assert_eq!(credit_phase.credit, msg_balance);
        // Account balance must receive the message balance.
        assert_eq!(
            state.balance,
            prev_balance.checked_add(&msg_balance).unwrap()
        );
        // No fees must be collected on the credit phase.
        assert_eq!(state.total_fees, prev_total_fees);
    }
}
