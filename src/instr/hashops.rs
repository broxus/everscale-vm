use std::fmt::Formatter;
use std::rc::Rc;
use everscale_types::cell::{CellBuilder, LevelMask};
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