use everscale_types::models::{Account, CurrencyCollection, LibDescr};
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

    pub is_special: bool,
    pub workchain: i32,
    pub account: Account,

    pub message_balance_remaining: CurrencyCollection,
    pub total_fees: Tokens,
}

#[derive(Default)]
pub struct ExecutorParams {
    pub libraries: Dict<HashBytes, LibDescr>,
    pub rand_seed: HashBytes,
    pub block_unixtime: u32,
    pub block_lt: u64,
    pub modifiers: BehaviourModifiers,
}
