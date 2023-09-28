use std::sync::OnceLock;

use everscale_types::error::Error;
use everscale_types::prelude::*;
use num_bigint::{BigInt, BigUint, Sign};
use num_traits::{One, Zero};

#[derive(Clone)]
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

    #[inline]
    pub fn range(&self) -> CellSliceRange {
        self.0 .1
    }

    #[inline]
    pub fn cell(&self) -> &Cell {
        &self.0 .0
    }

    #[inline]
    pub fn set_range(&mut self, range: CellSliceRange) {
        self.0 .1 = range
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
        if let Ok(left) = self.apply() {
            if let Ok(std::cmp::Ordering::Equal) = left.cmp_by_content(right) {
                return true;
            }
        }
        false
    }
}

pub fn store_int_to_builder(
    int: &BigInt,
    bits: u16,
    signed: bool,
    builder: &mut CellBuilder,
) -> Result<(), Error> {
    let value = int.magnitude();
    if value.bits() > bits as u64 {
        return Err(Error::IntOverflow);
    }

    let is_negative = int.sign() == Sign::Minus;
    let bytes = to_signed_bytes_be(is_negative, value);
    let value_bits = (bytes.len() * 8) as u16;

    if bytes.is_empty() {
        builder.store_zeros(bits)
    } else if bits > value_bits {
        let diff = bits - value_bits;
        ok!(if is_negative {
            builder.store_ones(diff)
        } else {
            builder.store_zeros(diff)
        });
        builder.store_raw(&bytes, value_bits)
    } else {
        let bits_offset = value_bits - bits;
        let bytes_offset = (bits_offset / 8) as usize;
        let rem = bits_offset % 8;

        let (left, right) = bytes.split_at(bytes_offset + 1);
        if let Some(left) = left.last() {
            ok!(builder.store_small_uint(*left << rem, 8 - rem));
        }
        if !right.is_empty() {
            ok!(builder.store_raw(right, (right.len() * 8) as u16));
        }
        Ok(())
    }
}

pub fn bitsize(int: &BigInt, signed: bool) -> u16 {
    fn minus_one() -> &'static BigInt {
        static MINUS_ONE: OnceLock<BigInt> = OnceLock::new();
        MINUS_ONE.get_or_init(|| BigInt::from_biguint(Sign::Minus, BigUint::one()))
    }

    let mut bits = int.bits() as u16;
    if signed {
        if int.is_zero() || int == minus_one() {
            return 1;
        } else if int.sign() == Sign::Plus {
            return bits + 1;
        }

        let mut modpow2 = int.magnitude().clone();
        modpow2 &= &modpow2 - 1u32;
        if !modpow2.is_zero() {
            bits += 1;
        }
    }

    bits
}

pub fn to_signed_bytes_be(is_negative: bool, value: &BigUint) -> Vec<u8> {
    #[inline]
    fn is_zero(value: &u8) -> bool {
        *value == 0
    }

    #[inline]
    pub fn twos_complement_le(digits: &mut [u8]) {
        let mut carry = true;
        for digit in digits {
            *digit = !*digit;
            if carry {
                let (d, c) = digit.overflowing_add(1);
                *digit = d;
                carry = c;
            }
        }
    }

    fn negative_to_signed_bytes_be(value: &BigUint) -> Vec<u8> {
        let mut bytes = value.to_bytes_le();
        let last_byte = bytes.last().cloned().unwrap_or(0);
        if last_byte > 0x7f && !(last_byte == 0x80 && bytes.iter().rev().skip(1).all(is_zero)) {
            // msb used by magnitude, extend by 1 byte
            bytes.push(0);
        }
        twos_complement_le(&mut bytes);
        bytes.reverse();
        bytes
    }

    if is_negative {
        negative_to_signed_bytes_be(value)
    } else {
        value.to_bytes_be()
    }
}
