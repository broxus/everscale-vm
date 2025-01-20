use ahash::HashMap;
use anyhow::Result;
use everscale_types::error::Error;
use everscale_types::models::{
    BlockchainConfigParams, GasLimitsPrices, GlobalVersion, MsgForwardPrices, SizeLimitsConfig,
    StorageInfo, StoragePrices, WorkchainDescription,
};
use everscale_types::num::Tokens;
use everscale_types::prelude::*;
use tycho_vm::UnpackedConfig;

use crate::util::shift_ceil_price;

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
    // TODO: Return error if storage prices `utime_since` is not properly sorted.
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
            if prices.utime_since <= now {
                latest_storage_prices = Some(value);
            }

            storage_prices.push(prices);
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

    pub fn gas_prices(&self, is_masterchain: bool) -> &GasLimitsPrices {
        if is_masterchain {
            &self.mc_gas_prices
        } else {
            &self.gas_prices
        }
    }

    /// Computes fees of storing `storage_stat.used` bits and refs
    /// since `storage_stat.last_paid` and up until `now`.
    ///
    /// NOTE: These fees don't include `due_payment`.
    pub fn compoute_storage_fees(
        &self,
        storage_stat: &StorageInfo,
        now: u32,
        is_special: bool,
        is_masterchain: bool,
    ) -> Tokens {
        // No fees in following cases:
        // - Time has not moved forward since the last transaction;
        // - Account was just created (last_paid: 0);
        // - Special accounts;
        // - No storage prices.
        if now <= storage_stat.last_paid || storage_stat.last_paid == 0 || is_special {
            return Tokens::ZERO;
        }

        let Some(oldest_prices) = self.storage_prices.first() else {
            // No storage prices.
            return Tokens::ZERO;
        };
        if now <= oldest_prices.utime_since {
            // No storage prices (being active for long enought time).
            return Tokens::ZERO;
        }

        let get_prices = if is_masterchain {
            |prices: &StoragePrices| (prices.mc_bit_price_ps, prices.mc_cell_price_ps)
        } else {
            |prices: &StoragePrices| (prices.bit_price_ps, prices.cell_price_ps)
        };

        let mut total = 0u128;

        // Sum fees for all segments (starting from the most recent).
        let mut upto = now;
        for prices in self.storage_prices.iter().rev() {
            if prices.utime_since > upto {
                continue;
            }

            // Compute for how long the segment was active
            let delta = upto - std::cmp::max(prices.utime_since, storage_stat.last_paid);

            // Sum fees
            let (bit_price, cell_price) = get_prices(prices);
            let fee = (bit_price as u128 * storage_stat.used.bits.into_inner() as u128)
                .saturating_add(cell_price as u128 * storage_stat.used.cells.into_inner() as u128)
                .saturating_mul(delta as u128);
            total = total.saturating_add(fee);

            // Stop on the first outdated segment.
            upto = prices.utime_since;
            if upto <= storage_stat.last_paid {
                break;
            }
        }

        // Convert from fixed point int.
        Tokens::new(shift_ceil_price(total))
    }
}
