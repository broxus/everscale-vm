use everscale_types::models::{Account, CurrencyCollection, LibDescr, StateInit, TickTock};
use everscale_types::num::Tokens;
use everscale_types::prelude::*;
use tycho_vm::BehaviourModifiers;

use crate::config::ParsedConfig;

mod config;
mod phases;
mod util;

pub struct ExecutorState<'a> {
    pub params: &'a ExecutorParams,
    pub config: &'a ParsedConfig,

    pub input: TransactionInput,
    pub is_special: bool,
    pub workchain: i32,
    pub account: Account,

    pub start_lt: u64,
    pub end_lt: u64,

    pub is_in_msg_external: bool,
    pub msg_body: CellSliceParts,
    pub msg_state_init: Option<MsgStateInit>,
    pub new_code: Option<Cell>,
    pub new_data: Option<Cell>,
    pub actions: Option<Cell>,
    pub account_activated: bool,

    pub original_balance: CurrencyCollection,
    pub message_balance_remaining: CurrencyCollection,
    pub total_fees: Tokens,
}

pub struct MsgStateInit {
    pub hash: HashBytes,
    pub parsed: StateInit,
    pub used: bool,
}

#[derive(Default)]
pub struct ExecutorParams {
    pub libraries: Dict<HashBytes, LibDescr>,
    pub rand_seed: HashBytes,
    pub block_unixtime: u32,
    pub block_lt: u64,
    pub modifiers: BehaviourModifiers,
}

#[derive(Debug, Clone)]
pub enum TransactionInput {
    Ordinary { msg_root: Cell },
    TickTock(TickTock),
}

impl TransactionInput {
    pub const fn is_ordinary(&self) -> bool {
        matches!(self, Self::Ordinary { .. })
    }
}

#[derive(Debug, thiserror::Error)]
#[error("external message rejected: {reason}")]
pub struct ExtMsgRejected {
    #[source]
    pub reason: ExtMsgRejectedReason,
}

#[derive(Debug, Clone, Copy, thiserror::Error)]
pub enum ExtMsgRejectedReason {
    #[error("message exceeds size limits")]
    ExceedsLimits,
    #[error("cannot pay for importing")]
    ImportFailed,
    #[error("message was not accepted during execution")]
    NotAccepted,
}
