use std::fmt::Formatter;
use std::rc::Rc;
use std::string::ToString;
use everscale_types::cell::{CellBuilder, LevelMask};
use everscale_types::error::Error;
use everscale_types::prelude::{Cell, CellFamily, Store};
use num_bigint::{BigInt, Sign};
use everscale_vm_proc::vm_module;
use crate::error::VmResult;
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
            *cell.hash(LevelMask::MAX_LEVEL)
        } else {
            let slice: Rc<OwnedCellSlice> = ok!(stack.pop_cs());
            let mut cb = CellBuilder::new();
            let slice = slice.apply()?;
            slice.store_into(&mut cb, &mut Cell::empty_context())?;
            *cb.build()?.hash(LevelMask::MAX_LEVEL)
        };

        let hash_int = BigInt::from_bytes_be(Sign::Plus, hash.as_slice());
        ok!(stack.push_int(hash_int));
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
        let mut key = [0u8;32];
        let mut signature = [0u8;64];

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
            vm_ensure!(hash_bytes.len() == 32usize, IntegerOverflow );
            //data_len = 32;
            data.extend_from_slice(hash_bytes.as_slice());
        }

        let signature_cs = signature_cs.apply()?;
        signature_cs.get_raw(0, &mut signature, 512)?;

        let key_bytes = key_int.to_bytes_be().1;
        vm_ensure!(key_bytes.len() == 32usize, IntegerOverflow );
        key.copy_from_slice(key_bytes.as_slice());

        //todo: register checksign counter and consume gas
        let key = everscale_crypto::ed25519::PublicKey::from_bytes(key);
        let Some(key) = key else {
            vm_bail!(Unknown("failed to constuct ed25519 public key from bytes".to_string()))
        };

        let result = key.verify_raw(data.as_ref(), &signature);
        ok!(stack.push_bool(result)); // todo: or check sig is always success by config

        Ok(0)
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
        let if_s= if args.if_s() { "S" } else { "C" };
        write!(f, "HASH{if_s}U")
    }
}