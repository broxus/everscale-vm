use anyhow::{Context, Result};
use everscale_types::dict;
use everscale_types::error::Error;
use everscale_types::models::{
    AccountState, AccountStatus, CurrencyCollection, HashUpdate, IntAddr, Lazy, LibDescr, Message,
    OwnedMessage, ShardAccount, StdAddr, StorageInfo, StorageUsed, TickTock, Transaction, TxInfo,
};
use everscale_types::num::{Tokens, Uint15};
use everscale_types::prelude::*;

pub use self::config::ParsedConfig;
pub use self::error::{TxError, TxResult};

mod config;
mod error;
mod util;

pub mod phase {
    pub use self::action::{ActionPhaseContext, ActionPhaseFull};
    pub use self::bounce::BouncePhaseContext;
    pub use self::compute::{ComputePhaseContext, ComputePhaseFull, TransactionInput};
    pub use self::receive::{MsgStateInit, ReceivedMessage};
    pub use self::storage::StoragePhaseContext;

    mod action;
    mod bounce;
    mod compute;
    mod credit;
    mod receive;
    mod storage;
}

mod tx {
    mod ordinary;
    mod ticktock;
}

/// Transaction executor.
pub struct Executor<'a> {
    params: &'a ExecutorParams,
    config: &'a ParsedConfig,
    min_lt: u64,
    // TODO: Always check the config instead?
    is_special: bool,
}

impl<'a> Executor<'a> {
    pub fn new(params: &'a ExecutorParams, config: &'a ParsedConfig) -> Self {
        Self {
            params,
            config,
            min_lt: 0,
            is_special: false,
        }
    }

    pub fn with_min_lt(mut self, min_lt: u64) -> Self {
        self.set_min_lt(min_lt);
        self
    }

    pub fn set_min_lt(&mut self, min_lt: u64) {
        self.min_lt = min_lt;
    }

    pub fn special(mut self, is_special: bool) -> Self {
        self.set_special(is_special);
        self
    }

    pub fn set_special(&mut self, is_special: bool) {
        self.is_special = is_special;
    }

    pub fn begin_ordinary<M>(
        &self,
        address: &StdAddr,
        is_external: bool,
        msg: M,
        state: &ShardAccount,
    ) -> TxResult<UncommitedTransaction<'a>>
    where
        M: LoadMessage,
    {
        let msg_root = msg.load_message_root()?;

        let mut exec = self.begin(address, state, self.is_special)?;
        let info = exec.run_ordinary_transaction(is_external, msg_root.clone())?;

        UncommitedTransaction::with_info(exec, state, Some(msg_root), info).map_err(TxError::Fatal)
    }

    pub fn begin_tick_tock(
        &self,
        address: &StdAddr,
        kind: TickTock,
        state: &ShardAccount,
    ) -> TxResult<UncommitedTransaction<'a>> {
        let mut exec = self.begin(address, state, self.is_special)?;
        let info = exec.run_tick_tock_transaction(kind)?;

        UncommitedTransaction::with_info(exec, state, None, info).map_err(TxError::Fatal)
    }

    fn begin(
        &self,
        address: &StdAddr,
        state: &ShardAccount,
        is_special: bool,
    ) -> Result<ExecutorState<'a>> {
        let account = state.load_account()?;

        let acc_address;
        let acc_storage_stat;
        let acc_balance;
        let acc_state;
        let orig_status;
        let start_lt;
        match account {
            Some(acc) => {
                acc_address = 'addr: {
                    if let IntAddr::Std(acc_addr) = acc.address {
                        if acc_addr == *address {
                            break 'addr acc_addr;
                        }
                    }
                    anyhow::bail!("account address mismatch");
                };
                acc_storage_stat = acc.storage_stat;
                acc_balance = acc.balance;
                acc_state = acc.state;
                orig_status = acc_state.status();
                start_lt = std::cmp::max(self.min_lt, acc.last_trans_lt);
            }
            None => {
                acc_address = address.clone();
                acc_storage_stat = StorageInfo {
                    used: StorageUsed::ZERO,
                    last_paid: 0,
                    due_payment: None,
                };
                acc_balance = CurrencyCollection::ZERO;
                acc_state = AccountState::Uninit;
                orig_status = AccountStatus::NotExists;
                start_lt = self.min_lt;
            }
        };

        Ok(ExecutorState {
            params: self.params,
            config: self.config,
            is_special,
            address: acc_address,
            storage_stat: acc_storage_stat,
            balance: acc_balance,
            state: acc_state,
            orig_status,
            end_status: orig_status,
            start_lt,
            end_lt: start_lt + 1,
            out_msgs: Vec::new(),
            total_fees: Tokens::ZERO,
        })
    }
}

/// Shared state for executor phases.
pub struct ExecutorState<'a> {
    pub params: &'a ExecutorParams,
    pub config: &'a ParsedConfig,

    pub is_special: bool,

    pub address: StdAddr,
    pub storage_stat: StorageInfo,
    pub balance: CurrencyCollection,
    pub state: AccountState,

    pub orig_status: AccountStatus,
    pub end_status: AccountStatus,
    pub start_lt: u64,
    pub end_lt: u64,

    pub out_msgs: Vec<Lazy<OwnedMessage>>,
    pub total_fees: Tokens,
}

/// Executor configuration parameters.
#[derive(Default)]
pub struct ExecutorParams {
    pub libraries: Dict<HashBytes, LibDescr>,
    pub rand_seed: HashBytes,
    pub block_unixtime: u32,
    pub block_lt: u64,
    pub vm_modifiers: tycho_vm::BehaviourModifiers,
    pub allow_delete_frozen_accounts: bool,
    pub full_body_in_bounce: bool,
}

/// Executed transaction.
pub struct UncommitedTransaction<'a> {
    last_trans_hash: HashBytes,
    last_trans_lt: u64,
    exec: ExecutorState<'a>,
    in_msg: Option<Cell>,
    info: Lazy<TxInfo>,
}

impl<'a> UncommitedTransaction<'a> {
    #[inline]
    fn with_info(
        exec: ExecutorState<'a>,
        state: &ShardAccount,
        in_msg: Option<Cell>,
        info: impl Into<TxInfo>,
    ) -> Result<Self> {
        let info = Lazy::new(&info.into())?;
        Ok(Self {
            last_trans_hash: state.last_trans_hash,
            last_trans_lt: state.last_trans_lt,
            exec,
            in_msg,
            info,
        })
    }

    pub fn finish_uncommited(&self) -> Result<Transaction> {
        thread_local! {
            static EMPTY_STATE_UPDATE: Lazy<HashUpdate> = Lazy::new(&HashUpdate {
                old: HashBytes::ZERO,
                new: HashBytes::ZERO,
            })
            .unwrap();
        }

        Ok(Transaction {
            account: self.exec.address.address,
            lt: self.exec.start_lt,
            prev_trans_hash: self.last_trans_hash,
            prev_trans_lt: self.last_trans_lt,
            now: self.exec.params.block_unixtime,
            out_msg_count: Uint15::new(self.exec.out_msgs.len() as _),
            orig_status: self.exec.orig_status,
            end_status: self.exec.end_status,
            in_msg: self.in_msg.clone(),
            out_msgs: build_out_msgs(&self.exec.out_msgs)?,
            total_fees: self.exec.total_fees.into(),
            state_update: EMPTY_STATE_UPDATE.with(Clone::clone),
            info: self.info.clone(),
        })
    }
}

/// Message cell source.
pub trait LoadMessage {
    fn load_message_root(self) -> Result<Cell>;
}

impl<T: LoadMessage + Clone> LoadMessage for &T {
    #[inline]
    fn load_message_root(self) -> Result<Cell> {
        T::load_message_root(T::clone(self))
    }
}

impl LoadMessage for Cell {
    #[inline]
    fn load_message_root(self) -> Result<Cell> {
        Ok(self)
    }
}

impl<T: EquivalentRepr<OwnedMessage>> LoadMessage for Lazy<T> {
    #[inline]
    fn load_message_root(self) -> Result<Cell> {
        Ok(self.into_inner())
    }
}

impl LoadMessage for OwnedMessage {
    #[inline]
    fn load_message_root(self) -> Result<Cell> {
        CellBuilder::build_from(self).context("failed to serialize inbound message")
    }
}

impl LoadMessage for Message<'_> {
    #[inline]
    fn load_message_root(self) -> Result<Cell> {
        CellBuilder::build_from(self).context("failed to serialize inbound message")
    }
}

fn build_out_msgs(out_msgs: &[Lazy<OwnedMessage>]) -> Result<Dict<Uint15, Cell>, Error> {
    dict::build_dict_from_sorted_iter(
        out_msgs
            .iter()
            .enumerate()
            .map(|(i, msg)| (Uint15::new(i as _), msg.inner().clone())),
        15,
        Cell::empty_context(),
    )
    .map(Dict::from_raw)
}
