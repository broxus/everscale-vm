use everscale_types::dict::Dict;
use everscale_types::models::{
    AccountState, CurrencyCollection, Lazy, LibDescr, OwnedMessage, StdAddr, StorageInfo, TickTock,
};
use everscale_types::num::Tokens;
use everscale_types::prelude::*;
use tycho_vm::BehaviourModifiers;

use self::receive::{MsgStateInit, ReceivedMessage};
use crate::config::ParsedConfig;

mod action;
mod bounce;
mod compute;
mod credit;
mod receive;
mod storage;

pub struct ExecutorState<'a> {
    pub params: &'a ExecutorParams,
    pub config: &'a ParsedConfig,

    pub is_special: bool,

    pub address: StdAddr,
    pub storage_stat: StorageInfo,
    pub balance: CurrencyCollection,
    pub state: AccountState,

    pub start_lt: u64,
    pub end_lt: u64,

    pub out_msgs: Vec<Lazy<OwnedMessage>>,
    pub total_fees: Tokens,
}

#[derive(Default)]
pub struct ExecutorParams {
    pub libraries: Dict<HashBytes, LibDescr>,
    pub rand_seed: HashBytes,
    pub block_unixtime: u32,
    pub block_lt: u64,
    pub vm_modifiers: BehaviourModifiers,
    pub full_body_in_bounce: bool,
}

#[derive(Debug, Clone)]
pub enum TransactionInput {
    Ordinary(ReceivedMessage),
    TickTock(TickTock),
}

impl TransactionInput {
    pub const fn is_ordinary(&self) -> bool {
        matches!(self, Self::Ordinary(_))
    }

    pub fn in_msg(&self) -> Option<&'_ ReceivedMessage> {
        match self {
            Self::Ordinary(msg) => Some(msg),
            Self::TickTock(_) => None,
        }
    }

    pub fn in_msg_mut(&mut self) -> Option<&'_ mut ReceivedMessage> {
        match self {
            Self::Ordinary(msg) => Some(msg),
            Self::TickTock(_) => None,
        }
    }

    pub fn in_msg_init(&self) -> Option<&'_ MsgStateInit> {
        match self {
            Self::Ordinary(msg) => msg.init.as_ref(),
            Self::TickTock(_) => None,
        }
    }
}
