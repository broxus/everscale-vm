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
        code = "f90$01ss",
        fmt = ("{}", s.display()),
        args(s = HashArgsExt(args))
    )]
    fn exec_hash_ext(st: &mut VmState, s: HashArgsExt) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);

        let mut hash_id = s.hash_id();
        if hash_id == 255 {
            hash_id = ok!(stack.pop_smallint_range(0, 254));
        };

        let cnt = ok!(stack.pop_smallint_range(0, (stack.depth() - 1) as u32));
        let hash: Vec<u8> = ok!(calc_hash_ext(
            stack,
            &mut st.gas,
            hash_id,
            cnt as usize,
            s.is_rev()
        ));

        let len = (hash.len() * 8) as u16;
        if s.is_append() {
            let mut rc_builder: Rc<CellBuilder> = ok!(stack.pop_builder());
            if !rc_builder.has_capacity(len, 0) {
                vm_bail!(CellError(Error::CellOverflow))
            }
            let builder = Rc::make_mut(&mut rc_builder);
            builder.store_raw(hash.as_slice(), len)?;
            ok!(stack.push_raw(rc_builder));
        } else {
            if hash.len() <= 32 {
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

    let mut buffer = [0u8; 129];

    for i in 0..cnt {
        let previous_empty_bits = buffer[0];
        let idx = if is_rev { i } else { cnt - 1 - i };

        let stack_value_opt: Option<&RcStackValue> = stack.items.get(idx);

        let mut data_slice = match get_data_slice(stack_value_opt) {
            Ok(data) => data,
            Err(e) => {
                ok!(stack.pop_many(cnt));
                return Err(e);
            }
        };
        let filled = match previous_empty_bits {
            p if p > 0 && p < 8 => {
                let rem = data_slice.load_small_uint(p as u16)?;
                buffer[128] |= rem;
                true
            }
            p if p == 8 => {
                let rem = data_slice.load_small_uint(p as u16)?;
                buffer[128] = rem;
                true
            }
            p if p > 8 => {
                let target_len = ((p + 7) / 8) as usize;
                let (byte_count, bit_remainder) = p.div_rem(&8u8);
                let rem = data_slice.load_small_uint(bit_remainder as u16)?;
                buffer[129 - target_len] |= rem;
                data_slice.load_raw(
                    &mut buffer[(129 - byte_count as usize)..],
                    bit_remainder as u16,
                )?;
                true
            }
            _ => false, // remaining bits cannot be negative
        };

        if filled {
            hasher.append(hash_id, buffer[1..129].as_ref());
        }

        total_bits += data_slice.size_bits() as usize;

        data_slice = data_slice.load_remaining();

        let gas_total = GasConsumer::calc_hash_ext_consumption(i, total_bits, hash_id);
        gas.try_consume(gas_total - gas_consumed)?;
        gas_consumed = gas_total;

        data_slice.load_raw(&mut buffer[1..129], data_slice.size_bits())?;

        let new_empty_bits = 1024 - data_slice.size_bits();
        buffer[0] = new_empty_bits as u8;
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

impl HashArgsExt {
    fn is_rev(&self) -> bool {
        (self.0 >> 8) & 1 != 0
    }

    fn is_append(&self) -> bool {
        (self.0 >> 9) & 1 != 0
    }

    fn hash_id(&self) -> u32 {
        self.0 & 255
    }

    fn hash_id_display(&self) -> i64 {
        let id = self.hash_id();
        if id == 255 {
            -1
        } else {
            id as i64
        }
    }

    pub fn display(&self) -> DisplayHashArgsExt {
        DisplayHashArgsExt(self.0)
    }
}

pub struct DisplayHashArgsExt(u32);

impl std::fmt::Display for DisplayHashArgsExt {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        todo!()
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

    pub fn append(&mut self, hash_id: u32, data: &[u8]) -> () {
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
