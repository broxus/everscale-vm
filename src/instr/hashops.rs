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
    let mut hasher = Hasher::new();

    let mut remaining_bits_in_buffer: usize = 128 * 8;
    let mut filled_bits: usize = 0;

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
            1024 => false,
            p if p > 0 && p < 8 => {
                // we have remaining bits lt one byte.
                let rem = data_slice.load_small_uint(p as u16)?;
                buffer[127] |= rem;
                remaining_bits_in_buffer -= p;
                filled_bits += p;
                true
            }
            p if p == 8 => {
                // exactly one byte
                let rem = data_slice.load_small_uint(p as u16)?;
                buffer[127] = rem;
                remaining_bits_in_buffer -= p;
                filled_bits += p;
                true
            }
            p if p > 8 => {
                // more than one byte
                let target_len = (p + 7) / 8; //compute how many bytes we need to fill in remaining bits
                let (byte_count, bit_remainder) = p.div_rem(&8usize);
                let rem = data_slice.load_small_uint(bit_remainder as u16)?;
                buffer[128 - target_len] |= rem;
                let loaded = data_slice
                    .load_raw(&mut buffer[(128 - byte_count)..], byte_count as u16 * 8)?;
                remaining_bits_in_buffer -= loaded.len();
                filled_bits += loaded.len();

                if remaining_bits_in_buffer == 0 {
                    true
                } else {
                    false
                }
            }
            _ => false, // remaining bits cannot be negative
        };

        if remaining_filled {
            hasher.append(hash_id, buffer.as_ref());
            remaining_bits_in_buffer = 128 * 8;
            filled_bits = 0;
            buffer.fill(0);
        }

        let size = data_slice.size_bits() as usize;
        total_bits += size;

        let gas_total = GasConsumer::calc_hash_ext_consumption(i, total_bits, hash_id);
        gas.try_consume(gas_total - gas_consumed)?;
        gas_consumed = gas_total;

        if data_slice.has_remaining(data_slice.size_bits(), 0) {
            data_slice = data_slice.load_remaining();
            let result = data_slice.load_raw(&mut buffer, data_slice.size_bits())?;

            remaining_bits_in_buffer -= result.len() * 8;
            filled_bits += result.len() * 8;
        } else {
            remaining_bits_in_buffer = 0;
            filled_bits += size;
        }

        // final step. We have to force finish hasher update
        if i == cnt - 1 {
            // check if we still can hash
            if filled_bits % 8 != 0 {
                vm_bail!(CellError(Error::CellUnderflow)) // data does not consist of an integer number of bytes
            }
            hasher.append(hash_id, buffer[0..filled_bits / 8].as_ref());
        }
    }

    ok!(stack.pop_many(cnt));
    let hash = hasher.finalize(hash_id);

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
    sha256: Sha256,
    sha512: Sha512,
    blake2b: Blake2b512,
}

impl Hasher {
    pub fn new() -> Hasher {
        Self {
            sha256: Sha256::new(),
            sha512: Sha512::new(),
            blake2b: Blake2b512::new(),
        }
    }

    pub fn append(&mut self, hash_id: u32, data: &[u8]) {
        match hash_id {
            0 => Digest::update(&mut self.sha256, data),
            1 => Digest::update(&mut self.sha512, data),
            2 => Digest::update(&mut self.blake2b, data),
            _ => unimplemented!("hash_id {} not supported", hash_id),
        }
    }

    pub fn finalize(self, hash_id: u32) -> Vec<u8> {
        match hash_id {
            0 => self.sha256.finalize().to_vec(),
            1 => self.sha512.finalize().to_vec(),
            2 => self.blake2b.finalize().to_vec(),
            _ => unimplemented!("hash_id {} not supported", hash_id),
        }
    }
}
