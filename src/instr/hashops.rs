use std::ops::Range;

use everscale_crypto::ed25519;
use everscale_types::cell::{CellBuilder, CellSlice};
use everscale_types::error::Error;
use num_bigint::{BigInt, Sign};
use sha2::Digest;
use tycho_vm_proc::vm_module;

use crate::error::VmResult;
use crate::gas::GasConsumer;
use crate::saferc::SafeRc;
use crate::stack::{Stack, StackValueType, Tuple};
use crate::state::VmState;

pub struct Hashops;

#[vm_module]
impl Hashops {
    #[op(code = "f900", fmt = "HASHCU", args(src = HashSource::Cell))]
    #[op(code = "f901", fmt = "HASHSU", args(src = HashSource::Slice))]
    fn exec_compute_hash(st: &mut VmState, src: HashSource) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);

        let hash = match src {
            HashSource::Cell => *ok!(stack.pop_cell()).repr_hash(),
            HashSource::Slice => {
                let cs = ok!(stack.pop_cs());
                let cell = CellBuilder::build_from_ext(cs.apply_allow_special(), &mut st.gas)?;
                *cell.repr_hash()
            }
        };

        let int = BigInt::from_bytes_be(Sign::Plus, hash.as_slice());
        ok!(stack.push_int(int));
        Ok(0)
    }

    #[op(code = "f902", fmt = "SHA256U")]
    fn exec_compute_sha256(st: &mut VmState) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        let cs = ok!(stack.pop_cs());
        let mut cs = cs.apply()?;
        let data_bits = cs.size_bits();
        vm_ensure!(data_bits % 8 == 0, CellError(Error::CellUnderflow));

        let mut data = [0; 128];
        let data = cs.load_raw(&mut data, data_bits)?;

        let hash = sha2::Sha256::digest(data);
        ok!(stack.push_int(BigInt::from_bytes_be(Sign::Plus, &hash)));
        Ok(0)
    }

    #[op(code = "f90$01pr#ii", fmt = DisplayHashArgsExt { p, r, i })]
    fn exec_hash_ext(st: &mut VmState, p: bool, r: bool, mut i: u32) -> VmResult<i32> {
        ok!(st.version.require_ton(4..));

        let stack = SafeRc::make_mut(&mut st.stack);
        if i == 255 {
            i = ok!(stack.pop_smallint_range(0, 254));
        }
        let max_depth = stack.depth().saturating_sub(1);
        let count = ok!(stack.pop_smallint_range(0, max_depth.try_into().unwrap_or(u32::MAX)));

        // TODO: pop_many on error?
        let hash = ok!(compute_hash_ext(stack, &mut st.gas, i, count, r));
        ok!(stack.pop_many(count as _));

        if p {
            // Append to a builder.
            let mut cb = ok!(stack.pop_builder());
            SafeRc::make_mut(&mut cb).store_raw(&hash, hash.len() as u16 * 8)?;
            ok!(stack.push_raw(cb));
        } else if hash.len() <= 32 {
            // Convert to a single int.
            let int = BigInt::from_bytes_be(Sign::Plus, &hash);
            ok!(stack.push_int(int));
        } else {
            // Convert to a tuple of ints.
            let mut tuple = Tuple::with_capacity(hash.len().div_ceil(32));
            for chunk in hash.chunks(32) {
                let int = BigInt::from_bytes_be(Sign::Plus, chunk);
                tuple.push(SafeRc::new_dyn_value(int));
            }
            ok!(stack.push_raw(SafeRc::new(tuple)));
        }

        Ok(0)
    }

    #[op(code = "f910", fmt = "CHKSIGNU", args(from_slice = false))]
    #[op(code = "f911", fmt = "CHKSIGNS", args(from_slice = true))]
    fn exec_ed25519_check_signature(st: &mut VmState, from_slice: bool) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        let key_int = ok!(stack.pop_int());
        let signature_cs = ok!(stack.pop_cs());

        let mut data = [0; 128];
        let data_len = if from_slice {
            let cs = ok!(stack.pop_cs());
            let mut cs = cs.apply()?;

            let cs_bits = cs.size_bits();
            vm_ensure!(cs_bits % 8 == 0, CellError(Error::CellUnderflow));
            cs.load_raw(&mut data, cs_bits)?;

            (cs_bits / 8) as usize
        } else {
            let int = ok!(stack.pop_int());
            vm_ensure!(int.sign() != Sign::Minus, IntegerOutOfRange {
                min: 0,
                max: isize::MAX,
                actual: int.to_string(),
            });

            let mut bytes = int.magnitude().to_bytes_le();
            bytes.truncate(32);
            bytes.reverse();
            data[32 - bytes.len()..32].copy_from_slice(&bytes);

            32
        };

        let mut signature = [0; 64];
        signature_cs.apply()?.load_raw(&mut signature, 512)?;

        vm_ensure!(key_int.sign() != Sign::Minus, IntegerOutOfRange {
            min: 0,
            max: isize::MAX,
            actual: key_int.to_string(),
        });
        let mut key_bytes = key_int.magnitude().to_bytes_le();
        key_bytes.resize(32, 0);
        key_bytes.reverse();

        st.gas.try_consume_check_signature_gas()?;

        let is_valid = 'valid: {
            let Some(pubkey) =
                ed25519::PublicKey::from_bytes(key_bytes.as_slice().try_into().unwrap())
            else {
                break 'valid false;
            };

            pubkey.verify_raw(&data[..data_len], &signature)
        };

        ok!(stack.push_bool(is_valid || st.modifiers.chksig_always_succeed));
        Ok(0)
    }
}

macro_rules! define_compute_hash_ext {
    ($($hash_id:literal => $fn:ident($bpg:literal, $hash:path) -> $out:ty),*$(,)?) => {
        fn compute_hash_ext(
            stack: &mut Stack,
            gas: &mut GasConsumer,
            hash_id: u32,
            count: u32,
            reverse: bool,
        ) -> VmResult<Vec<u8>> {
            let mut reader = HashInputReader {
                count: count as _,
                reverse,
                index: 0,
                total_bits: 0,
                gas_consumed: 0,
                rem_bits: 0,
                prev_byte: 0,
                stack,
                gas,
            };

            let bytes = match hash_id {
                $($hash_id => ok!($fn(&mut reader)).to_vec()),*,
                _ => vm_bail!(IntegerOutOfRange {
                    min: 0,
                    max: 0,
                    actual: hash_id.to_string(),
                }),
            };
            Ok(bytes)
        }

        $(fn $fn(reader: &'_ mut HashInputReader<'_>) -> VmResult<$out> {
            let mut hasher = <$hash>::new();

            let mut buffer = HashInputReader::chunk_buffer();
            while let Some(bytes) = reader.load_next($bpg, &mut buffer) {
                hasher.update(ok!(bytes));
            }

            Ok(hasher.finalize().into())
        })*
    };
}

define_compute_hash_ext! {
    0 => compute_hash_ext_sha256(33, sha2::Sha256) -> [u8; 32],
    1 => compute_hash_ext_sha512(16, sha2::Sha512) -> [u8; 64],
    2 => compute_hash_ext_blake2b512(19, blake2::Blake2b512) -> [u8; 64],
}

struct HashInputReader<'a> {
    count: usize,
    reverse: bool,
    index: usize,
    total_bits: u64,
    gas_consumed: u64,
    rem_bits: u16,
    prev_byte: u8,
    stack: &'a Stack,
    gas: &'a mut GasConsumer,
}

impl<'a> HashInputReader<'a> {
    const fn chunk_buffer() -> ChunkBuffer {
        // First byte for unaligned bits, the rest is for slice data
        [0; 129]
    }

    fn load_next<'b>(
        &mut self,
        bytes_per_gas_unit: u64,
        buffer: &'b mut ChunkBuffer,
    ) -> Option<VmResult<&'b [u8]>> {
        while self.index < self.count {
            // Try load bytes at the current index
            let range = match self.load_bytes(self.index, buffer) {
                Ok(range) => range,
                Err(e) => return Some(Err(e)),
            };

            // Try consume the gas difference
            let gas_total = (self.index as u64 + 1) * GasConsumer::HASH_EXT_ENTRY_GAS_PRICE
                + self.total_bits / 8 / bytes_per_gas_unit;
            if let Err(e) = self.gas.try_consume(gas_total - self.gas_consumed) {
                return Some(Err(e.into()));
            }
            self.gas_consumed = gas_total;

            // Increment the index for the next iteration
            self.index += 1;

            // Return only non-empty slices
            if !range.is_empty() {
                return Some(Ok(&buffer[range]));
            }
        }

        // Require all input to be aligned
        if self.rem_bits != 0 {
            return Some(Err(Error::CellUnderflow.into()));
        }

        None
    }

    fn load_bytes(&mut self, index: usize, buffer: &mut ChunkBuffer) -> VmResult<Range<usize>> {
        let mut data = ok!(self.get_data_slice(index));
        let mut data_bits = data.size_bits();
        self.total_bits += data_bits as u64;

        // Combine the previous unaligned byte
        let is_aligned = self.rem_bits == 0;
        if !is_aligned {
            let bits_to_align_prev = 8 - self.rem_bits;

            if data_bits < bits_to_align_prev {
                // Append more bits for an unaligned byte but don't hash yet
                let shift = bits_to_align_prev - data_bits;
                self.rem_bits += data_bits;
                self.prev_byte |= data.load_small_uint(data_bits)? << shift;
                return Ok(Range::default());
            }

            // Write prev byte to the start of the result
            buffer[0] = self.prev_byte | data.load_small_uint(bits_to_align_prev)?;
            data_bits -= bits_to_align_prev;
        } else if (1..8).contains(&data_bits) {
            // Store the beginning of the byte
            let shift = 8 - data_bits;
            self.rem_bits = data_bits;
            self.prev_byte = data.load_small_uint(data_bits)? << shift;
            return Ok(Range::default());
        }

        // Load the remainder of the slice
        debug_assert_eq!(data.size_bits(), data_bits);
        data.load_raw(&mut buffer[1..], data_bits)?;

        let byte_len = data_bits as usize / 8;

        // Update unalized byte info
        self.rem_bits = data_bits % 8;
        self.prev_byte = if self.rem_bits == 0 {
            0
        } else {
            buffer[1 + byte_len]
        };

        // Return a possibly extended subslice
        Ok(is_aligned as usize..1 + byte_len)
    }

    fn get_data_slice(&self, mut index: usize) -> VmResult<CellSlice<'a>> {
        if !self.reverse {
            index = self.count - 1 - index;
        }

        let value = ok!(self.stack.fetch(index));
        if let Some(slice) = value.as_cell_slice() {
            slice.apply().map_err(Into::into)
        } else if let Some(builder) = value.as_cell_builder() {
            Ok(builder.as_data_slice())
        } else {
            vm_bail!(InvalidType {
                expected: StackValueType::Slice,
                actual: value.ty()
            })
        }
    }
}

type ChunkBuffer = [u8; 129];

struct DisplayHashArgsExt {
    p: bool,
    r: bool,
    i: u32,
}

impl std::fmt::Display for DisplayHashArgsExt {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let if_append = if self.p { "A" } else { "" };
        let is_rev = if self.r { "R" } else { "" };
        let hash_id = if self.i == 255 { -1 } else { self.i as i32 };
        write!(f, "HASHEXT{if_append}{is_rev} {hash_id}")
    }
}

enum HashSource {
    Cell,
    Slice,
}

#[cfg(test)]
mod tests {
    use everscale_crypto::ed25519;
    use everscale_types::cell::{CellBuilder, HashBytes};
    use num_bigint::{BigInt, Sign};
    use sha2::Digest;
    use tracing_test::traced_test;

    use crate::saferc::SafeRc;
    use crate::stack::RcStackValue;
    use crate::util::OwnedCellSlice;

    #[test]
    #[traced_test]
    fn hashext_sha256_vs_sha256u() {
        let target = 0x0123456789abcdef_u64.to_be_bytes();
        let target_hash = build_int(sha2::Sha256::digest(target));

        assert_run_vm!(
            r#"
            PUSHSLICE x{0123456789abcdef} SHA256U
            PUSHSLICE x{0123456789abcdef} INT 1 HASHEXT_SHA256
            DUP EQUAL

            PUSHSLICE x{01}
            PUSHSLICE x{2}
            PUSHSLICE b{001101} NEWC STSLICE
            PUSHSLICE b{0}
            PUSHSLICE b{00101} NEWC STSLICE
            PUSHSLICE x{6789a}
            PUSHSLICE b{1}
            PUSHSLICE b{0111100}
            PUSHSLICE x{def}
            INT 9 HASHEXT_SHA256

            PUSHSLICE x{01}
            PUSHSLICE x{2}
            PUSHSLICE b{001101} NEWC STSLICE
            PUSHSLICE b{0}
            PUSHSLICE b{00101} NEWC STSLICE
            PUSHSLICE x{6789a}
            PUSHSLICE b{1}
            PUSHSLICE b{0111100}
            PUSHSLICE x{def}
            REVERSE 9, 0
            INT 9 HASHEXTR_SHA256
            DUP EQUAL
            "#,
            [] => [raw target_hash.clone(), int -1, raw target_hash, int -1]
        );
    }

    #[test]
    #[traced_test]
    fn hashexta() {
        assert_run_vm!(
            r#"
            NEWC
                PUSHSLICE x{ff} STSLICER PUSHSLICE x{01234567} SHA256U STUR 256
            ENDC CTOS

            NEWC
                PUSHSLICE x{ff} STSLICER PUSHSLICE x{0123} PUSHSLICE x{4567} INT 2 HASHEXTA_SHA256
            ENDC CTOS

            NEWC
                PUSHSLICE x{ff} STSLICER PUSHSLICE x{4567} PUSHSLICE x{0123} INT 2 HASHEXTAR_SHA256
            ENDC CTOS

            DUP SDEQ
            ROTREV SDEQ
            "#,
            [] => [int -1, int -1],
        );
    }

    #[test]
    #[traced_test]
    fn hashext_tuple_hashes() {
        let data = b"look ma, raw bytes";
        let sha512_hash = sha2::Sha512::digest(data);
        let blake2_hash = blake2::Blake2b512::digest(data);

        let (sha512_low, sha512_high) = {
            let (low, high) = sha512_hash.split_at(32);
            (build_int(low), build_int(high))
        };
        assert_run_vm!(
            r#"INT 1 HASHEXT_SHA512 UNPAIR"#,
            [raw build_slice(data)] => [raw sha512_low.clone(), raw sha512_high.clone()]
        );
        assert_run_vm!(
            r#"NEWC STSLICE INT 1 HASHEXT_SHA512 UNPAIR"#,
            [raw build_slice(data)] => [raw sha512_low, raw sha512_high]
        );

        let (blake2_low, blake2_high) = {
            let (low, high) = blake2_hash.split_at(32);
            (build_int(low), build_int(high))
        };
        assert_run_vm!(
            r#"INT 1 HASHEXT_BLAKE2B UNPAIR"#,
            [raw build_slice(data)] => [raw blake2_low.clone(), raw blake2_high.clone()]
        );
        assert_run_vm!(
            r#"NEWC STSLICE INT 1 HASHEXT_BLAKE2B UNPAIR"#,
            [raw build_slice(data)] => [raw blake2_low, raw blake2_high]
        );
    }

    #[test]
    #[traced_test]
    fn chksign() -> anyhow::Result<()> {
        let secret = "403cbda795d10f129d81ac9963840f6100f8025e9341d486b247602e4b11f404"
            .parse::<HashBytes>()?;
        let keypair = ed25519::KeyPair::from(&ed25519::SecretKey::from_bytes(secret.0));

        let data = [0xda_u8; 40];
        let data_signature = keypair.sign_raw(&data);

        let data_hash = sha2::Sha256::digest(data);
        let data_hash_signature = keypair.sign_raw(&data_hash);

        assert_run_vm!(
            "CHKSIGNS",
            [
                raw build_slice(data),
                raw build_slice(data_signature),
                raw build_int(keypair.public_key.as_bytes()),
            ] => [int -1]
        );

        // Equivalent to `SHA256U` + `CHKSIGNU`
        assert_run_vm!(
            "ROT SHA256U ROTREV CHKSIGNU",
            [
                raw build_slice(data),
                raw build_slice(data_hash_signature),
                raw build_int(keypair.public_key.as_bytes()),
            ] => [int -1]
        );

        let args = SafeRc::new(vec![
            build_int(data_hash),
            build_slice(data_hash_signature),
            build_int(keypair.public_key.as_bytes()),
        ]);

        assert_run_vm!(
            "UNTRIPLE CHKSIGNU",
            [raw args.clone()] => [int -1]
        );

        // Equivalent to `CHKSIGNU`
        assert_run_vm!(
            r#"
            UNTRIPLE
            ROT NEWC STU 256 ENDC CTOS ROTREV
            CHKSIGNS
            "#,
            [raw args] => [int -1]
        );

        // Invalid pubkey
        assert_run_vm!(
            "CHKSIGNS",
            [
                raw build_slice(data),
                raw build_slice(data_hash_signature),
                int 123,
            ] => [int 0]
        );

        // Invalid signature
        assert_run_vm!(
            "CHKSIGNS",
            [
                raw build_slice(data),
                raw build_slice(data_hash_signature), // <--
                raw build_int(keypair.public_key.as_bytes()),
            ] => [int 0]
        );
        assert_run_vm!(
            "CHKSIGNU",
            [
                int 123,
                raw build_slice(data_hash_signature),
                raw build_int(keypair.public_key.as_bytes()),
            ] => [int 0]
        );

        Ok(())
    }

    fn build_slice<T: AsRef<[u8]>>(data: T) -> RcStackValue {
        let data = data.as_ref();
        let b = CellBuilder::from_raw_data(data, data.len() as u16 * 8).unwrap();
        SafeRc::new_dyn_value(OwnedCellSlice::from(b.build().unwrap()))
    }

    fn build_int<T: AsRef<[u8]>>(data: T) -> RcStackValue {
        SafeRc::new_dyn_value(BigInt::from_bytes_be(Sign::Plus, data.as_ref()))
    }
}
