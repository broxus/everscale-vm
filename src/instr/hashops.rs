use std::fmt::Formatter;
use std::rc::Rc;
use std::string::ToString;

use blake2::Blake2b512;
use everscale_types::cell::{CellBuilder, CellSlice};
use everscale_types::error::Error;
use everscale_types::prelude::{Cell, CellFamily, Store};
use everscale_vm::stack::{Stack, Tuple};
use everscale_vm_proc::vm_module;
use num_bigint::{BigInt, Sign};
use num_integer::Integer;
use sha2::{Digest, Sha256, Sha512};

use crate::error::VmResult;
use crate::stack::{RcStackValue, StackValueType};
use crate::state::GasConsumer;
use crate::util::OwnedCellSlice;
use crate::VmState;

pub struct Hashops;

#[vm_module]
impl Hashops {
    #[instr(code = "f900", fmt = ("{}", s.display()), args(s = HashArgs(0)))]
    #[instr(code = "f901", fmt = ("{}", s.display()), args(s = HashArgs(1)))]
    fn exec_compute_hash(st: &mut VmState, s: HashArgs) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let hash = if !s.if_s() {
            let cell: Rc<Cell> = ok!(stack.pop_cell());
            *cell.repr_hash()
        } else {
            let slice: Rc<OwnedCellSlice> = ok!(stack.pop_cs());
            let mut cb = CellBuilder::new();
            let slice = slice.apply()?;
            slice.store_into(&mut cb, &mut Cell::empty_context())?;
            *cb.build()?.repr_hash()
        };

        let hash_int = BigInt::from_bytes_be(Sign::Plus, hash.as_slice());
        ok!(stack.push_int(hash_int));
        Ok(0)
    }

    #[instr(
        code = "f90$01pr#nn",
        fmt = ("{}", DisplayHashArgsExt {p,r,n}),
        args(p = ((args >> 9) & 1) != 0, r = ((args >> 8) & 1) != 0)
    )]
    fn exec_hash_ext(st: &mut VmState, p: bool, r: bool, n: u32) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let mut hash_id = n;
        if hash_id == 255 {
            hash_id = ok!(stack.pop_smallint_range(0, 254));
        };

        let cnt = ok!(stack.pop_smallint_range(0, (stack.depth() - 1) as u32));

        let hash: Vec<u8> = ok!(calc_hash_ext(stack, &mut st.gas, hash_id, cnt as usize, r));

        let len = (hash.len() * 8) as u16;
        if p {
            let mut rc_builder: Rc<CellBuilder> = ok!(stack.pop_builder());
            if !rc_builder.has_capacity(len, 0) {
                vm_bail!(CellError(Error::CellOverflow))
            }
            let builder = Rc::make_mut(&mut rc_builder);
            builder.store_raw(hash.as_slice(), len)?;
            ok!(stack.push_raw(rc_builder));
        } else if hash.len() <= 32 {
            let int = BigInt::from_bytes_be(Sign::Plus, hash.as_slice());
            ok!(stack.push_int(int));
        } else {
            let mut tuple = Tuple::new();
            for i in hash.chunks(32) {
                let int = BigInt::from_bytes_be(Sign::Plus, i);
                tuple.push(Rc::new(int));
            }
            ok!(stack.push_raw(Rc::new(tuple)));
        }

        Ok(0)
    }
    #[instr(code = "f910", fmt = "CHECKSIGNU", args(from_slice = false))]
    #[instr(code = "f911", fmt = "CHECKSIGNU", args(from_slice = true))]
    fn exec_ed25519_check_signature(st: &mut VmState, from_slice: bool) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let key_int = ok!(stack.pop_int());
        let signature_cs: Rc<OwnedCellSlice> = ok!(stack.pop_cs());

        //let data_len: u16;
        let mut data = Vec::with_capacity(128);
        let mut key = [0u8; 32];
        let mut signature = [0u8; 64];

        if from_slice {
            let cs: Rc<OwnedCellSlice> = ok!(stack.pop_cs());
            let cs = cs.apply()?;
            if cs.size_bits() & 7 == 1 {
                vm_bail!(CellError(Error::CellUnderflow))
            }
            let data_len = cs.size_bits() >> 3;
            vm_ensure!(data_len as usize <= data.len(), IntegerOverflow);
            cs.get_raw(0, &mut data, data_len)?;
        } else {
            let hash_int: Rc<BigInt> = ok!(stack.pop_int());
            let hash_bytes = hash_int.to_bytes_be().1;
            vm_ensure!(hash_bytes.len() == 32usize, IntegerOverflow);
            //data_len = 32;
            data.extend_from_slice(hash_bytes.as_slice());
        }

        let signature_cs = signature_cs.apply()?;
        signature_cs.get_raw(0, &mut signature, 512)?;

        let key_bytes = key_int.to_bytes_be().1;
        vm_ensure!(key_bytes.len() == 32usize, IntegerOverflow);
        key.copy_from_slice(key_bytes.as_slice());

        st.gas.try_consume_check_signature_gas()?;
        let key = everscale_crypto::ed25519::PublicKey::from_bytes(key);
        let Some(key) = key else {
            vm_bail!(Unknown(
                "failed to constuct ed25519 public key from bytes".to_string()
            ))
        };

        let result = key.verify_raw(data.as_ref(), &signature);
        ok!(stack.push_bool(result)); // todo: or check sig is always success by config

        Ok(0)
    }
}

pub fn calc_hash_ext<'a>(
    stack: &mut Stack,
    gas: &mut GasConsumer,
    hash_id: u32,
    cnt: usize,
    is_rev: bool,
) -> VmResult<Vec<u8>> {
    let mut total_bits: usize = 0;
    let mut gas_consumed: u64 = 0;
    let mut hasher = Hasher::new(hash_id);

    let mut remaining_bits_in_buffer: usize = 1024;
    let mut filled_bits: usize = 0;

    let mut rem_bits_from_prev_step: u8 = 0;
    let mut rem_value: Option<CellSlice> = None;

    let mut buffer = [0u8; 128];

    for i in 0..cnt {
        let idx = if is_rev { i } else { cnt - 1 - i };

        let stack_value_opt: Option<&RcStackValue> = stack.items.get(stack.items.len() - 1 - idx);

        //load next slice on stack
        let mut data_slice = match get_data_slice(stack_value_opt) {
            Ok(data) => data,
            Err(e) => {
                ok!(stack.pop_many(cnt));
                return Err(e);
            }
        };
        // check if we have remaining bits from previous step. 0 is for first step
        let remaining_filled = match remaining_bits_in_buffer {
            0 => true,
            1024 => false,
            _ => {
                match (rem_bits_from_prev_step > 0, rem_value) {
                    (true, Some(mut rem_value)) => {
                        let int = data_slice.load_small_uint(8 - rem_bits_from_prev_step as u16)?;
                        let value =
                            rem_value.load_small_uint(rem_bits_from_prev_step as u16)? | int;

                        buffer[filled_bits / 8] = value;
                        remaining_bits_in_buffer -= 8;
                        filled_bits += 8;
                    }
                    _ => (),
                }

                if remaining_bits_in_buffer == 0 {
                    true
                } else {
                    false
                }
            }
        };
        if remaining_filled {
            hasher.append(buffer.as_ref());
            remaining_bits_in_buffer = 128 * 8;
            filled_bits = 0;
            buffer.fill(0);
        }

        let (bytes, rem_bits) = data_slice.size_bits().div_rem(&8);
        if remaining_bits_in_buffer >= data_slice.size_bits() as usize {
            let nb = data_slice.load_raw(&mut buffer[(filled_bits / 8)..], bytes * 8)?;
            remaining_bits_in_buffer -= bytes as usize * 8;
            filled_bits += bytes as usize * 8;

            if rem_bits != 0 {
                rem_bits_from_prev_step = rem_bits as u8;
                rem_value = Some(data_slice.load_remaining());
            }

            total_bits += filled_bits;
            let gas_total = GasConsumer::calc_hash_ext_consumption(i, total_bits, hash_id);
            gas.try_consume(gas_total - gas_consumed)?;
            gas_consumed = gas_total;
        } else {
            //load what we can to a remaining buffer
            data_slice.load_raw(
                &mut buffer[(filled_bits / 8)..],
                remaining_bits_in_buffer as u16,
            )?;

            total_bits += filled_bits;
            let gas_total = GasConsumer::calc_hash_ext_consumption(i, total_bits, hash_id);
            gas.try_consume(gas_total - gas_consumed)?;
            gas_consumed = gas_total;

            // append hasher and update buffer
            hasher.append(buffer.as_ref());
            remaining_bits_in_buffer = 128 * 8;
            filled_bits = 0;
            buffer.fill(0);

            //load rest of slice to a new buffer
            let (bytes, rem_bits) = data_slice.size_bits().div_rem(&8);
            data_slice.load_raw(&mut buffer, bytes * 8)?;
            if rem_bits != 0 {
                rem_bits_from_prev_step = rem_bits as u8;
                rem_value = Some(data_slice.load_remaining());
            }
            remaining_bits_in_buffer -= bytes as usize * 8;
            filled_bits += bytes as usize * 8;

            total_bits += filled_bits;
            let gas_total = GasConsumer::calc_hash_ext_consumption(i, total_bits, hash_id);
            gas.try_consume(gas_total - gas_consumed)?;
            gas_consumed = gas_total;
        };

        // final step. We have to force finish hasher update
        if i == cnt - 1 {
            // check if we still can hash
            if rem_bits_from_prev_step != 0 {
                vm_log!("Can not hash data with bit len % 8 != 0");
                vm_bail!(CellError(Error::CellUnderflow)) // data does not consist of an integer number of bytes
            }
            hasher.append(buffer[0..filled_bits / 8].as_ref());
        }
    }

    ok!(stack.pop_many(cnt));
    let hash = hasher.finalize();

    Ok(hash)
}

pub fn get_data_slice(stack_value_opt: Option<&RcStackValue>) -> VmResult<CellSlice> {
    let Some(stack_value) = stack_value_opt else {
        vm_bail!(InvalidType {
            expected: StackValueType::Slice,
            actual: StackValueType::Null
        }) //TODO: or builder type because can be expected
    };
    match stack_value.as_slice() {
        Some(slice) => Ok(slice.apply()?),
        None => {
            match stack_value.as_builder() {
                Some(builder) => Ok(builder.as_data_slice()),
                None => {
                    vm_bail!(InvalidType {
                        expected: StackValueType::Builder,
                        actual: stack_value.ty()
                    }) //TODO: or slice as expected
                }
            }
        }
    }
}

pub struct HashArgsExt(u32);

pub struct DisplayHashArgsExt {
    p: bool,
    r: bool,
    n: u32,
}

impl std::fmt::Display for DisplayHashArgsExt {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let if_append = if self.p { "A" } else { "" };
        let is_rev = if self.r { "R" } else { "" };
        let hash_id = if self.n == 255 { -1 } else { self.n as i32 };
        write!(f, "HASHEXT{if_append}{is_rev} {hash_id}")
    }
}

pub struct HashArgs(u32);
impl HashArgs {
    pub fn if_s(&self) -> bool {
        self.0 & 0b1 != 0
    }

    pub fn display(&self) -> DisplayHashArgs {
        DisplayHashArgs(self.0)
    }
}

pub struct DisplayHashArgs(u32);

impl std::fmt::Display for DisplayHashArgs {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let args = HashArgs(self.0);
        let if_s = if args.if_s() { "S" } else { "C" };
        write!(f, "HASH{if_s}U")
    }
}

pub struct Hasher {
    hash_id: u32,
    sha256: Sha256,
    sha512: Sha512,
    blake2b: Blake2b512,
}

impl Hasher {
    pub fn new(hash_id: u32) -> Hasher {
        Self {
            hash_id,
            sha256: Sha256::new(),
            sha512: Sha512::new(),
            blake2b: Blake2b512::new(),
        }
    }

    pub fn append(&mut self, data: &[u8]) {
        println!("append data {data:?}");
        match self.hash_id {
            0 => Digest::update(&mut self.sha256, data),
            1 => Digest::update(&mut self.sha512, data),
            2 => Digest::update(&mut self.blake2b, data),
            _ => unimplemented!("hash_id {} not supported", self.hash_id),
        }
    }

    pub fn finalize(self) -> Vec<u8> {
        match self.hash_id {
            0 => self.sha256.finalize().to_vec(),
            1 => self.sha512.finalize().to_vec(),
            2 => self.blake2b.finalize().to_vec(),
            _ => unimplemented!("hash_id {} not supported", self.hash_id),
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::stack::RcStackValue;
    use crate::stack::StackValueType::Cell;
    use crate::util::OwnedCellSlice;
    use everscale_types::cell::CellBuilder;
    use num_bigint::{BigInt, Sign};
    use sha2::Digest;
    use std::rc::Rc;
    use tracing_test::traced_test;

    #[test]
    #[traced_test]
    fn extended_hash_1() {
        let mut sha256 = sha2::Sha256::new();

        let x = [1u8; 32];
        sha256.update(x.as_ref());
        let mut cb = CellBuilder::new();
        cb.store_raw(x.as_ref(), 256).unwrap();
        let cell1 = cb.build().unwrap();

        let y = [2u8; 32];
        sha256.update(y.as_ref());
        let mut cb = CellBuilder::new();
        cb.store_raw(y.as_ref(), 256).unwrap();
        let cell2 = cb.build().unwrap();

        let slice1 = OwnedCellSlice::from(cell1);
        let slice2 = OwnedCellSlice::from(cell2);

        let raw1: RcStackValue = Rc::new(slice1);
        let raw2: RcStackValue = Rc::new(slice2);

        let hash: Vec<u8> = sha256.finalize().to_vec();
        let int1: RcStackValue = Rc::new(BigInt::from_bytes_be(Sign::Plus, hash.as_ref()));

        assert_run_vm!(
            "HASHEXT_SHA256",
            [raw raw1, raw raw2, int 2] => [raw int1]
        );
    }

    #[test]
    #[traced_test]
    fn extended_hash_2() {
        let mut sha256 = sha2::Sha256::new();

        let x = [3u8; 64];
        sha256.update(x.as_ref());
        let mut cb = CellBuilder::new();
        cb.store_raw(x.as_ref(), 512).unwrap();
        let cell1 = cb.build().unwrap();

        let y = [4u8; 64];
        sha256.update(y.as_ref());
        let mut cb = CellBuilder::new();
        cb.store_raw(y.as_ref(), 512).unwrap();
        let cell2 = cb.build().unwrap();

        let slice1 = OwnedCellSlice::from(cell1);
        let slice2 = OwnedCellSlice::from(cell2);

        let raw1: RcStackValue = Rc::new(slice1);
        let raw2: RcStackValue = Rc::new(slice2);

        let hash: Vec<u8> = sha256.finalize().to_vec();
        let int1: RcStackValue = Rc::new(BigInt::from_bytes_be(Sign::Plus, hash.as_ref()));

        assert_run_vm!(
            "HASHEXT_SHA256",
            [raw raw1, raw raw2, int 2] => [raw int1]
        );
    }

    #[test]
    #[traced_test]
    fn extended_hash_3() {
        let mut sha256 = sha2::Sha256::new();

        let x = [3u8; 64];
        sha256.update(x.as_ref());
        let mut cb = CellBuilder::new();
        cb.store_raw(x.as_ref(), 512).unwrap();
        let cell1 = cb.build().unwrap();

        let y = [4u8; 64];
        sha256.update(y.as_ref());
        let mut cb = CellBuilder::new();
        cb.store_raw(y.as_ref(), 511).unwrap();
        let cell2 = cb.build().unwrap();

        let slice1 = OwnedCellSlice::from(cell1);
        let slice2 = OwnedCellSlice::from(cell2);

        let raw1: RcStackValue = Rc::new(slice1);
        let raw2: RcStackValue = Rc::new(slice2);

        let hash: Vec<u8> = sha256.finalize().to_vec();
        let int1: RcStackValue = Rc::new(BigInt::from_bytes_be(Sign::Plus, hash.as_ref()));

        assert_run_vm!(
            "HASHEXT_SHA256",
            [raw raw1, raw raw2, int 2] => [],
            exit_code: 9
        );
    }

    // #[test]
    // #[traced_test]
    // fn extended_hash_4() {
    //     let mut sha256 = sha2::Sha256::new();
    //
    //     let mut cb = CellBuilder::new();
    //     let x = [1u8; 31];
    //     let int1: u8 = 0b1111111;
    //     cb.store_raw(x.as_ref(), x.len() as u16 * 8).unwrap();
    //     cb.store_small_uint(int1, 7).unwrap();
    //     let cell1 = cb.build().unwrap();
    //
    //     let mut cb = CellBuilder::new();
    //     let y = [2u8; 32];
    //     let int2: u8 = 0b1;
    //     cb.store_raw(x.as_ref(), x.len() as u16 * 8).unwrap();
    //     cb.store_small_uint(int1, 1).unwrap();
    //     let cell2 = cb.build().unwrap();
    //
    //     let slice1 = OwnedCellSlice::from(cell1);
    //     let slice2 = OwnedCellSlice::from(cell2);
    //
    //     let raw1: RcStackValue = Rc::new(slice1);
    //     let raw2: RcStackValue = Rc::new(slice2);
    //
    //     let hash: Vec<u8> = sha256.finalize().to_vec();
    //     let int1: RcStackValue = Rc::new(BigInt::from_bytes_be(Sign::Plus, hash.as_ref()));
    //
    //     assert_run_vm!(
    //         "HASHEXT_SHA256",
    //         [raw raw1, raw raw2, int 2] => [],
    //         exit_code: 9
    //     );
    // }
}
