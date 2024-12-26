use std::borrow::Cow;
use std::rc::Rc;

use everscale_types::cell::CellTreeStats;
use everscale_types::dict::DictKey;
use everscale_types::error::Error;
use everscale_types::models::{GasLimitsPrices, MsgForwardPrices, StoragePrices};
use everscale_types::num::Tokens;
use everscale_types::prelude::*;
use num_bigint::{BigInt, Sign};
use num_traits::{One, ToPrimitive, Zero};

#[derive(Default, Debug, Clone)]
#[repr(transparent)]
pub struct OwnedCellSlice(CellSliceParts);

impl OwnedCellSlice {
    pub fn new(cell: Cell) -> Self {
        let range = CellSliceRange::full(cell.as_ref());
        Self((cell, range))
    }

    pub fn apply(&self) -> Result<CellSlice<'_>, Error> {
        self.range().apply(self.cell())
    }

    pub fn apply_allow_special(&self) -> CellSlice<'_> {
        self.range().apply_allow_special(self.cell())
    }

    #[inline]
    pub fn range(&self) -> CellSliceRange {
        self.0 .1
    }

    #[inline]
    pub fn range_mut(&mut self) -> &mut CellSliceRange {
        &mut self.0 .1
    }

    #[inline]
    pub fn cell(&self) -> &Cell {
        &self.0 .0
    }

    #[inline]
    pub fn set_range(&mut self, range: CellSliceRange) {
        self.0 .1 = range
    }

    pub fn fits_into(&self, builder: &CellBuilder) -> bool {
        let range = self.range();
        let bits = range.size_bits();
        let refs = range.size_refs();
        builder.has_capacity(bits, refs)
    }
}

impl std::fmt::Display for OwnedCellSlice {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let (cell, range) = &self.0;
        let bits_end = range.offset_bits() + range.size_bits();
        let refs_end = range.offset_refs() + range.size_refs();
        write!(
            f,
            "CS{{Cell {{{}}} bits: {}..{}; refs: {}..{}}}",
            cell.repr_hash(),
            range.offset_bits(),
            bits_end,
            range.offset_refs(),
            refs_end
        )
    }
}

impl From<Cell> for OwnedCellSlice {
    #[inline]
    fn from(value: Cell) -> Self {
        Self::new(value)
    }
}

impl From<CellSliceParts> for OwnedCellSlice {
    #[inline]
    fn from(parts: CellSliceParts) -> Self {
        Self(parts)
    }
}

impl PartialEq<CellSlice<'_>> for OwnedCellSlice {
    fn eq(&self, right: &CellSlice<'_>) -> bool {
        let left = self.apply_allow_special();
        matches!(left.contents_eq(right), Ok(true))
    }
}

#[repr(transparent)]
pub struct Uint4(pub usize);

impl DictKey for Uint4 {
    const BITS: u16 = 4;

    #[inline]
    fn from_raw_data(raw_data: &[u8; 128]) -> Option<Self> {
        Some(Self((raw_data[0] & 0xf) as usize))
    }
}

impl Store for Uint4 {
    fn store_into(&self, builder: &mut CellBuilder, _: &mut dyn CellContext) -> Result<(), Error> {
        if self.0 > 0xf {
            return Err(Error::IntOverflow);
        }
        builder.store_small_uint(self.0 as _, 4)
    }
}

impl Load<'_> for Uint4 {
    #[inline]
    fn load_from(slice: &mut CellSlice<'_>) -> Result<Self, Error> {
        Ok(Self(ok!(slice.load_small_uint(4)) as usize))
    }
}

pub trait GasLimitsPricesExt {
    fn compute_gas_fee(&self, gas_used: u64) -> Tokens;
}

impl GasLimitsPricesExt for GasLimitsPrices {
    fn compute_gas_fee(&self, gas_used: u64) -> Tokens {
        let mut res = self.flat_gas_price as u128;
        if let Some(extra_gas) = gas_used.checked_sub(self.flat_gas_limit) {
            res = res.saturating_add(shift_ceil_price(self.gas_price as u128 * extra_gas as u128));
        }
        Tokens::new(res)
    }
}

pub trait StoragePricesExt {
    fn compute_storage_fee(&self, is_masterchain: bool, delta: u64, stats: CellTreeStats)
        -> Tokens;
}

impl StoragePricesExt for StoragePrices {
    fn compute_storage_fee(
        &self,
        is_masterchain: bool,
        delta: u64,
        stats: CellTreeStats,
    ) -> Tokens {
        let mut res = if is_masterchain {
            (stats.cell_count as u128 * self.mc_cell_price_ps as u128)
                .saturating_add(stats.bit_count as u128 * self.mc_bit_price_ps as u128)
        } else {
            (stats.cell_count as u128 * self.cell_price_ps as u128)
                .saturating_add(stats.bit_count as u128 * self.bit_price_ps as u128)
        };
        res = res.saturating_mul(delta as u128);
        Tokens::new(shift_ceil_price(res))
    }
}

pub trait MsgForwardPricesExt {
    fn compute_fwd_fee(&self, stats: CellTreeStats) -> Tokens;
}

impl MsgForwardPricesExt for MsgForwardPrices {
    fn compute_fwd_fee(&self, stats: CellTreeStats) -> Tokens {
        let lump = self.lump_price as u128;
        let extra = shift_ceil_price(
            (stats.cell_count as u128 * self.cell_price as u128)
                .saturating_add(stats.bit_count as u128 * self.bit_price as u128),
        );
        Tokens::new(lump.saturating_add(extra))
    }
}

pub const fn shift_ceil_price(value: u128) -> u128 {
    let r = value & 0xffff != 0;
    (value >> 16) + r as u128
}

pub fn ensure_empty_slice(slice: &CellSlice) -> Result<(), Error> {
    if slice.is_data_empty() && slice.is_refs_empty() {
        Ok(())
    } else {
        Err(Error::InvalidData)
    }
}

pub fn load_int_from_slice(
    slice: &mut CellSlice<'_>,
    bits: u16,
    signed: bool,
) -> Result<BigInt, Error> {
    match bits {
        0 => Ok(BigInt::zero()),
        0..=64 if !signed => slice.load_uint(bits).map(BigInt::from),
        0..=64 if signed => slice.load_uint(bits).map(|mut int| {
            if bits < 64 {
                // Clone sign bit into all high bits
                int |= ((int >> (bits - 1)) * u64::MAX) << (bits - 1);
            }
            BigInt::from(int as i64)
        }),
        _ => {
            let rem = bits % 8;
            let mut buffer = [0u8; 33];
            slice.load_raw(&mut buffer, bits).map(|buffer| {
                let mut int = if signed {
                    BigInt::from_signed_bytes_be(buffer)
                } else {
                    BigInt::from_bytes_be(Sign::Plus, buffer)
                };
                if bits % 8 != 0 {
                    int >>= 8 - rem;
                }
                int
            })
        }
    }
}

pub fn store_int_to_builder(
    x: &BigInt,
    bits: u16,
    signed: bool,
    builder: &mut CellBuilder,
) -> Result<(), Error> {
    let int_bits = bitsize(x, signed);
    if bits < int_bits {
        return Err(Error::IntOverflow);
    }
    store_int_to_builder_unchecked(x, bits, signed, builder)
}

pub fn store_int_to_builder_unchecked(
    x: &BigInt,
    bits: u16,
    signed: bool,
    builder: &mut CellBuilder,
) -> Result<(), Error> {
    match x.to_u64() {
        Some(value) => builder.store_uint(value, bits),
        None => {
            let int = if bits % 8 != 0 {
                let align = 8 - bits % 8;
                Cow::Owned(x.clone() << align)
            } else {
                Cow::Borrowed(x)
            };

            let minimal_bytes = ((bits + 7) / 8) as usize;

            let (prefix, mut bytes) = if signed {
                let bytes = int.to_signed_bytes_le();
                (
                    bytes
                        .last()
                        .map(|first| (first >> 7) * 255)
                        .unwrap_or_default(),
                    bytes,
                )
            } else {
                (0, int.to_bytes_le().1)
            };
            bytes.resize(minimal_bytes, prefix);
            bytes.reverse();

            builder.store_raw(&bytes, bits)
        }
    }
}

pub fn load_uint_leq(cs: &mut CellSlice, upper_bound: u32) -> Result<u64, Error> {
    let bits = 32 - upper_bound.leading_zeros();
    let result = cs.load_uint(bits as u16)?;
    if result > upper_bound as u64 {
        return Err(Error::IntOverflow);
    };
    Ok(result)
}

pub fn bitsize(int: &BigInt, signed: bool) -> u16 {
    let mut bits = int.bits() as u16;
    if signed {
        match int.sign() {
            Sign::NoSign => bits,
            Sign::Minus if int.magnitude().is_one() => bits + 1,
            Sign::Plus => bits + 1,
            Sign::Minus => {
                // Check if `int` magnitude is not a power of 2
                let mut digits = int.iter_u64_digits().rev();
                if let Some(hi) = digits.next() {
                    if !hi.is_power_of_two() || !digits.all(|digit| digit == 0) {
                        bits += 1;
                    }
                }
                bits
            }
        }
    } else {
        bits
    }
}

pub fn in_bitsize_range(x: &BigInt, signed: bool) -> bool {
    signed || x.sign() != Sign::Minus
}

pub fn remove_trailing(slice: &mut CellSlice<'_>) -> Result<(), everscale_types::error::Error> {
    let bits = slice.size_bits();
    if bits == 0 {
        return Ok(());
    }

    let n = ok!(slice.count_trailing(false));
    // NOTE: Skip one additional bit for non-empty slice
    slice.skip_last(n + (n != bits) as u16, 0)
}

#[inline]
pub fn rc_ptr_eq<T1: ?Sized, T2: ?Sized>(lhs: &Rc<T1>, rhs: &Rc<T2>) -> bool {
    let lhs = Rc::as_ptr(lhs) as *const ();
    let rhs = Rc::as_ptr(rhs) as *const ();
    lhs == rhs
}

#[cfg(test)]
mod tests {
    use num_traits::ToPrimitive;

    use super::*;

    #[test]
    fn store_int_to_builder_works() -> anyhow::Result<()> {
        let bits = 19;
        let value = BigInt::from(106029);

        let mut builder1 = CellBuilder::new();
        store_int_to_builder(&value, bits, false, &mut builder1)?;

        let mut builder2 = CellBuilder::new();
        builder2.store_uint(value.to_u64().unwrap(), bits)?;

        assert_eq!(builder1, builder2);
        Ok(())
    }
}
