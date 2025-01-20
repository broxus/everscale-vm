use ahash::HashMap;
use everscale_types::error::Error;
use everscale_types::models::{
    BlockchainConfigParams, GasLimitsPrices, GlobalVersion, LibDescr, MsgForwardPrices,
    SizeLimitsConfig, StoragePrices, WorkchainDescription,
};
use everscale_types::prelude::*;
use tycho_vm::{BehaviourModifiers, UnpackedConfig};

pub struct ExecutorState {
    pub total_fees: u128,
    // TODO
}

#[derive(Default)]
pub struct ExecutorParams {
    pub libraries: Dict<HashBytes, LibDescr>,
    pub rand_seed: HashBytes,
    pub block_unixtime: u32,
    pub block_lt: u64,
    pub modifiers: BehaviourModifiers,
}

pub struct ParsedConfig {
    pub mc_gas_prices: GasLimitsPrices,
    pub gas_prices: GasLimitsPrices,
    pub mc_fwd_prices: MsgForwardPrices,
    pub fwd_prices: MsgForwardPrices,
    pub size_limits: SizeLimitsConfig,
    pub storage_prices: Vec<StoragePrices>,
    pub global_id: i32,
    pub global: GlobalVersion,
    pub workchains: HashMap<i32, WorkchainDescription>,
    pub raw: BlockchainConfigParams,
    pub unpacked: UnpackedConfig,
}

impl ParsedConfig {
    // TODO: Pass `global_id` here as well? For now we assume that
    //       `params` will contain a global id entry (`ConfigParam19`).
    pub fn parse(params: BlockchainConfigParams, now: u32) -> Result<Self, Error> {
        let dict = params.as_dict();

        let Some(mc_gas_prices_raw) = dict.get(20)? else {
            return Err(Error::CellUnderflow);
        };
        let Some(gas_prices_raw) = dict.get(21)? else {
            return Err(Error::CellUnderflow);
        };

        let Some(mc_fwd_prices_raw) = dict.get(24)? else {
            return Err(Error::CellUnderflow);
        };
        let Some(fwd_prices_raw) = dict.get(25)? else {
            return Err(Error::CellUnderflow);
        };

        let storage_prices_dict = RawDict::<32>::from(dict.get(18)?);
        let mut storage_prices = Vec::new();
        let mut latest_storage_prices = None;
        for value in storage_prices_dict.values_owned() {
            let value = value?;
            let prices = StoragePrices::load_from(&mut value.1.apply_allow_special(&value.0))?;
            if prices.utime_since > now {
                break;
            }

            storage_prices.push(prices);
            latest_storage_prices = Some(value);
        }

        let workchains_dict = params.get_workchains()?;
        let mut workchains = HashMap::<i32, WorkchainDescription>::default();
        for entry in workchains_dict.iter() {
            let (workchain, desc) = entry?;
            workchains.insert(workchain, desc);
        }

        let global_id_raw = dict.get(19)?;
        let global = params.get_global_version()?;

        // Fallback to default if param not present in config?
        let Some(size_limits_raw) = dict.get(43)? else {
            return Err(Error::CellUnderflow);
        };

        Ok(Self {
            mc_gas_prices: mc_gas_prices_raw.parse::<GasLimitsPrices>()?,
            gas_prices: gas_prices_raw.parse::<GasLimitsPrices>()?,
            mc_fwd_prices: mc_fwd_prices_raw.parse::<MsgForwardPrices>()?,
            fwd_prices: fwd_prices_raw.parse::<MsgForwardPrices>()?,
            size_limits: size_limits_raw.parse::<SizeLimitsConfig>()?,
            storage_prices,
            global_id: match &global_id_raw {
                None => 0, // Return error?
                Some(param) => param.parse::<i32>()?,
            },
            global,
            workchains,
            raw: params,
            unpacked: UnpackedConfig {
                latest_storage_prices,
                global_id: global_id_raw,
                mc_gas_prices: Some(mc_gas_prices_raw),
                gas_prices: Some(gas_prices_raw),
                mc_fwd_prices: Some(mc_fwd_prices_raw),
                fwd_prices: Some(fwd_prices_raw),
                size_limits_config: Some(size_limits_raw),
            },
        })
    }
}
