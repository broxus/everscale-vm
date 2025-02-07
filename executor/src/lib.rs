use anyhow::{Context, Result};
use everscale_types::dict;
use everscale_types::error::Error;
use everscale_types::models::{
    Account, AccountState, AccountStatus, CurrencyCollection, HashUpdate, IntAddr, Lazy, LibDescr,
    Message, OptionalAccount, OwnedMessage, ShardAccount, SimpleLib, StdAddr, StorageInfo,
    StorageUsed, TickTock, Transaction, TxInfo,
};
use everscale_types::num::{Tokens, Uint15};
use everscale_types::prelude::*;

pub use self::config::ParsedConfig;
pub use self::error::{TxError, TxResult};
pub use self::util::{ExtStorageStat, OwnedExtStorageStat, StorageStatLimits};

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

    pub fn begin_ordinary<'s, M>(
        &self,
        address: &StdAddr,
        is_external: bool,
        msg: M,
        state: &'s ShardAccount,
    ) -> TxResult<UncommitedTransaction<'a, 's>>
    where
        M: LoadMessage,
    {
        let msg_root = msg.load_message_root()?;

        let mut exec = self.begin(address, state, self.is_special)?;
        let info = exec.run_ordinary_transaction(is_external, msg_root.clone())?;

        UncommitedTransaction::with_info(exec, state, Some(msg_root), info).map_err(TxError::Fatal)
    }

    pub fn begin_tick_tock<'s>(
        &self,
        address: &StdAddr,
        kind: TickTock,
        state: &'s ShardAccount,
    ) -> TxResult<UncommitedTransaction<'a, 's>> {
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
        let end_status;
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
                end_status = orig_status;
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
                end_status = AccountStatus::Uninit;
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
            end_status,
            start_lt,
            end_lt: start_lt + 1,
            out_msgs: Vec::new(),
            total_fees: Tokens::ZERO,
            cached_storage_stat: None,
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

    pub cached_storage_stat: Option<OwnedExtStorageStat>,
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
pub struct UncommitedTransaction<'a, 's> {
    original: &'s ShardAccount,
    exec: ExecutorState<'a>,
    in_msg: Option<Cell>,
    info: Lazy<TxInfo>,
    brief_info: BriefTxInfo,
}

struct BriefTxInfo {
    gas_used: u64,
}

impl<'a, 's> UncommitedTransaction<'a, 's> {
    #[inline]
    fn with_info(
        exec: ExecutorState<'a>,
        original: &'s ShardAccount,
        in_msg: Option<Cell>,
        info: impl Into<TxInfo>,
    ) -> Result<Self> {
        use everscale_types::models::ComputePhase;

        let info = info.into();
        let gas_used = match &info {
            TxInfo::Ordinary(info) => match &info.compute_phase {
                ComputePhase::Executed(phase) => phase.gas_used.into_inner(),
                ComputePhase::Skipped(_) => 0,
            },
            TxInfo::TickTock(info) => match &info.compute_phase {
                ComputePhase::Executed(phase) => phase.gas_used.into_inner(),
                ComputePhase::Skipped(_) => 0,
            },
        };

        let info = Lazy::new(&info)?;
        Ok(Self {
            original,
            exec,
            in_msg,
            info,
            brief_info: BriefTxInfo { gas_used },
        })
    }

    /// Creates a partially finalized transaction.
    ///
    /// It differs from the normal transaction by having a stub `state_update`
    /// and possibly denormalized `end_status`.
    pub fn build_uncommited(&self) -> Result<Transaction, Error> {
        thread_local! {
            static EMPTY_STATE_UPDATE: Lazy<HashUpdate> = Lazy::new(&HashUpdate {
                old: HashBytes::ZERO,
                new: HashBytes::ZERO,
            })
            .unwrap();
        }

        self.build_transaction(self.exec.end_status, EMPTY_STATE_UPDATE.with(Clone::clone))
    }

    /// Creates a final transaction and a new contract state.
    pub fn commit(self) -> Result<ExecutorOutput> {
        // Finalize account state.
        let account_state = self.build_state()?;

        // Collect brief account state info.
        let new_state_meta;
        let end_status = match &account_state {
            None => {
                new_state_meta = AccountMeta {
                    balance: CurrencyCollection::ZERO,
                    libraries: Dict::new(),
                    exists: false,
                };

                AccountStatus::NotExists
            }
            Some(account) => {
                let libraries = match &account.state {
                    AccountState::Active(state) => state.libraries.clone(),
                    AccountState::Frozen(..) | AccountState::Uninit => Dict::new(),
                };

                new_state_meta = AccountMeta {
                    balance: account.balance.clone(),
                    libraries,
                    exists: true,
                };

                account.state.status()
            }
        };

        // Serialize account state.
        let account_state = CellBuilder::build_from(OptionalAccount(account_state))?;

        // Serialize transaction.
        let state_update = Lazy::new(&HashUpdate {
            old: *self.original.account.inner().repr_hash(),
            new: *account_state.repr_hash(),
        })?;
        let transaction = self
            .build_transaction(end_status, state_update)
            .and_then(CellBuilder::build_from)
            .map(Lazy::from_raw)?;

        // Collect brief transaction info.
        let transaction_meta = TransactionMeta {
            total_fees: self.exec.total_fees,
            next_lt: self.exec.end_lt,
            out_msgs: self.exec.out_msgs,
            gas_used: self.brief_info.gas_used,
        };

        // New shard account state.
        let new_state = ShardAccount {
            account: Lazy::from_raw(account_state),
            last_trans_hash: *transaction.inner().repr_hash(),
            last_trans_lt: self.exec.start_lt,
        };

        // Done
        Ok(ExecutorOutput {
            new_state,
            new_state_meta,
            transaction,
            transaction_meta,
        })
    }

    fn build_state(&self) -> Result<Option<Account>> {
        if self.exec.end_status == AccountStatus::NotExists
            || self.exec.end_status == AccountStatus::Uninit && self.exec.balance.is_zero()
        {
            // NOTE: Uninit accounts with zero balance are deleted.
            return Ok(None);
        }

        let state = match self.exec.end_status {
            // Account was deleted.
            AccountStatus::NotExists => return Ok(None),
            // Uninit account we zero balance is also treated as deleted.
            AccountStatus::Uninit if self.exec.balance.is_zero() => return Ok(None),
            // Uninit account stays the same.
            AccountStatus::Uninit => AccountState::Uninit,
            // Active account must have a known active state.
            AccountStatus::Active => {
                debug_assert!(matches!(self.exec.state, AccountState::Active(_)));
                self.exec.state.clone()
            }
            // Normalize frozen state.
            AccountStatus::Frozen => {
                let cell;
                let frozen_hash = match &self.exec.state {
                    // Uninit accounts can't be frozen, but if they accidentialy can
                    // just use the account address as frozen state hash to produce the
                    // same uninit state.
                    AccountState::Uninit => &self.exec.address.address,
                    // To freeze an active account we must compute a hash of its state.
                    AccountState::Active(state_init) => {
                        cell = CellBuilder::build_from(state_init)?;
                        cell.repr_hash()
                    }
                    // Account is already frozen.
                    AccountState::Frozen(hash_bytes) => hash_bytes,
                };

                // Normalize account state.
                if frozen_hash == &self.exec.address.address {
                    AccountState::Uninit
                } else {
                    AccountState::Frozen(*frozen_hash)
                }
            }
        };

        let account = Account {
            address: self.exec.address.clone().into(),
            storage_stat: self.exec.storage_stat.clone(),
            last_trans_lt: self.exec.end_lt,
            balance: self.exec.balance.clone(),
            state,
        };

        // TODO: Update storage stat.

        Ok(Some(account))
    }

    fn build_transaction(
        &self,
        end_status: AccountStatus,
        state_update: Lazy<HashUpdate>,
    ) -> Result<Transaction, Error> {
        Ok(Transaction {
            account: self.exec.address.address,
            lt: self.exec.start_lt,
            prev_trans_hash: self.original.last_trans_hash,
            prev_trans_lt: self.original.last_trans_lt,
            now: self.exec.params.block_unixtime,
            out_msg_count: Uint15::new(self.exec.out_msgs.len() as _),
            orig_status: self.exec.orig_status,
            end_status,
            in_msg: self.in_msg.clone(),
            out_msgs: build_out_msgs(&self.exec.out_msgs)?,
            total_fees: self.exec.total_fees.into(),
            state_update,
            info: self.info.clone(),
        })
    }
}

/// Commited transaction output.
#[derive(Clone, Debug)]
pub struct ExecutorOutput {
    pub new_state: ShardAccount,
    pub new_state_meta: AccountMeta,
    pub transaction: Lazy<Transaction>,
    pub transaction_meta: TransactionMeta,
}

/// Short account description.
#[derive(Clone, Debug)]
pub struct AccountMeta {
    pub balance: CurrencyCollection,
    pub libraries: Dict<HashBytes, SimpleLib>,
    pub exists: bool,
}

/// Short transaction description.
#[derive(Clone, Debug)]
pub struct TransactionMeta {
    pub total_fees: Tokens,
    pub out_msgs: Vec<Lazy<OwnedMessage>>,
    pub gas_used: u64,
    pub next_lt: u64,
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

#[cfg(test)]
mod tests {
    use std::rc::Rc;

    use everscale_types::boc::BocRepr;
    use everscale_types::models::{
        Account, BlockchainConfig, ExtInMsgInfo, MsgInfo, OptionalAccount, SizeLimitsConfig,
        StateInit,
    };

    use super::*;

    pub fn make_default_config() -> Rc<ParsedConfig> {
        thread_local! {
            pub static PARSED_CONFIG: Rc<ParsedConfig> = {
                let mut config: BlockchainConfig = BocRepr::decode(include_bytes!("../res/config.boc")).unwrap();

                config.params.set_global_id(100).unwrap();

                // TODO: Update config BOC
                config.params.set_size_limits(&SizeLimitsConfig {
                    max_msg_bits: 1 << 21,
                    max_msg_cells: 1 << 13,
                    max_library_cells: 1000,
                    max_vm_data_depth: 512,
                    max_ext_msg_size: 65535,
                    max_ext_msg_depth: 512,
                    max_acc_state_cells: 1 << 16,
                    max_acc_state_bits: (1 << 16) * 1023,
                    max_acc_public_libraries: 256,
                    defer_out_queue_size_limit: 256,
                }).unwrap();

                Rc::new(ParsedConfig::parse(config.params, u32::MAX).unwrap())
            };
        }

        PARSED_CONFIG.with(Clone::clone)
    }

    pub fn make_uninit_with_balance<T: Into<CurrencyCollection>>(
        address: &StdAddr,
        balance: T,
    ) -> ShardAccount {
        ShardAccount {
            account: Lazy::new(&OptionalAccount(Some(Account {
                address: address.clone().into(),
                storage_stat: StorageInfo::default(),
                last_trans_lt: 1001,
                balance: balance.into(),
                state: AccountState::Uninit,
            })))
            .unwrap(),
            last_trans_hash: HashBytes([0x11; 32]),
            last_trans_lt: 1000,
        }
    }

    pub fn make_owned_body(builder: CellBuilder) -> CellSliceParts {
        let cell = builder.build().unwrap();
        let range = CellSliceRange::full(cell.as_ref());
        (cell, range)
    }

    #[test]
    fn ever_wallet_deploys() -> anyhow::Result<()> {
        let config = make_default_config();
        let params = ExecutorParams {
            block_unixtime: 1738799198,
            full_body_in_bounce: false,
            vm_modifiers: tycho_vm::BehaviourModifiers {
                chksig_always_succeed: true,
                ..Default::default()
            },
            ..Default::default()
        };

        let code = Boc::decode_base64("te6cckEBBgEA/AABFP8A9KQT9LzyyAsBAgEgAgMABNIwAubycdcBAcAA8nqDCNcY7UTQgwfXAdcLP8j4KM8WI88WyfkAA3HXAQHDAJqDB9cBURO68uBk3oBA1wGAINcBgCDXAVQWdfkQ8qj4I7vyeWa++COBBwiggQPoqFIgvLHydAIgghBM7mRsuuMPAcjL/8s/ye1UBAUAmDAC10zQ+kCDBtcBcdcBeNcB10z4AHCAEASqAhSxyMsFUAXPFlAD+gLLaSLQIc8xIddJoIQJuZgzcAHLAFjPFpcwcQHLABLM4skB+wAAPoIQFp4+EbqOEfgAApMg10qXeNcB1AL7AOjRkzLyPOI+zYS/")?;
        let data = CellBuilder::build_from((HashBytes::ZERO, 0u64))?;

        let state_init = StateInit {
            split_depth: None,
            special: None,
            code: Some(code),
            data: Some(data),
            libraries: Dict::new(),
        };
        let address = StdAddr::new(0, *CellBuilder::build_from(&state_init)?.repr_hash());

        let msg = OwnedMessage {
            info: MsgInfo::ExtIn(ExtInMsgInfo {
                src: None,
                dst: address.clone().into(),
                import_fee: Tokens::ZERO,
            }),
            init: Some(state_init),
            body: make_owned_body({
                let mut b = CellBuilder::new();
                // just$1 Signature
                b.store_bit_one()?;
                b.store_u256(&HashBytes::ZERO)?;
                b.store_u256(&HashBytes::ZERO)?;
                // just$1 Pubkey
                b.store_bit_one()?;
                b.store_zeros(256)?;
                // header_time:u64
                b.store_u64((params.block_unixtime - 10) as u64 * 1000)?;
                // header_expire:u32
                b.store_u32(params.block_unixtime + 40)?;
                // sendTransaction
                b.store_u32(0x4cee646c)?;
                // ...
                b.store_reference({
                    let mut b = CellBuilder::new();
                    // dest:address
                    address.store_into(&mut b, Cell::empty_context())?;
                    // value:uint128
                    b.store_u128(10000000)?;
                    // bounce:false
                    b.store_bit_zero()?;
                    // mode:uint8
                    b.store_u8(0b11)?;
                    // payload:cell
                    b.store_reference(Cell::empty_cell())?;
                    //
                    b.build()?
                })?;
                //
                b
            }),
            layout: None,
        };

        let state = make_uninit_with_balance(&address, CurrencyCollection::new(1_000_000_000));

        let tx = Executor::new(&params, config.as_ref())
            .begin_ordinary(&address, true, &msg, &state)?
            .build_uncommited()?;
        println!("TX: {:#?}", tx);

        let info = tx.load_info()?;
        println!("INFO: {info:#?}");

        Ok(())
    }
}
