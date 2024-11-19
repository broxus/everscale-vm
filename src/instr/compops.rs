use std::cmp::Ordering;
use std::ops::Deref;
use std::rc::Rc;
use num_bigint::BigInt;
use everscale_vm_proc::vm_module;
use crate::error::VmResult;
use crate::VmState;

pub struct CompOps;

#[vm_module]
impl CompOps {

    #[instr(code = "b9", fmt = "LESS", args(mode = 0x887, quiet = false))]
    #[instr(code = "ba", fmt = "EQUAL", args(mode = 0x878, quiet = false))]
    #[instr(code = "bb", fmt = "LEQ", args(mode = 0x877, quiet = false))]
    #[instr(code = "bc", fmt = "GREATER", args(mode = 0x788, quiet = false))]
    #[instr(code = "bd", fmt = "NEQ", args(mode = 0x787, quiet = false))]
    #[instr(code = "be", fmt = "GEQ", args(mode = 0x778, quiet = false))]
    #[instr(code = "bf", fmt = "CMP", args(mode = 0x987, quiet = false))]

    #[instr(code = "b7b9", fmt = "QLESS", args(mode = 0x887, quiet = true))]
    #[instr(code = "b7ba", fmt = "QEQUAL", args(mode = 0x878, quiet = true))]
    #[instr(code = "b7bb", fmt = "QLEQ", args(mode = 0x877, quiet = true))]
    #[instr(code = "b7bc", fmt = "QGREATER", args(mode = 0x788, quiet = true))]
    #[instr(code = "b7bd", fmt = "QNEQ", args(mode = 0x787, quiet = true))]
    #[instr(code = "b7be", fmt = "QGEQ", args(mode = 0x778, quiet = true))]
    #[instr(code = "b7bf", fmt = "QCMP", args(mode = 0x987, quiet = true))]
    fn exec_cmp(st: &mut VmState, mode: i32, quiet: bool) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let first: Option<Rc<BigInt>> = ok!(stack.pop_int_or_nan());
        let second: Option<Rc<BigInt>> = ok!(stack.pop_int_or_nan());
        match (first, second) {
            (Some(sec), Some(f)) => {
                println!("{f} {sec}");
                let z = match f.cmp(&sec) {
                    Ordering::Greater => 1,
                    Ordering::Equal => 0,
                    Ordering::Less => -1
                };

                let res = ((mode >> (4 + z * 4)) & 15) - 8;
                ok!(stack.push_int(res));
            }
            _ if quiet => ok!(stack.push_nan()),
            _ => vm_bail!(IntegerOverflow),
        }

        Ok(0)
    }


    fn exec_cmp_int(st: &mut VmState, args: u32, mode: i32, quiet: bool) -> VmResult<i32> {
        let y = args as i32; //TODO: check orig impl
        let stack = Rc::make_mut(&mut st.stack);
        let first: Option<Rc<BigInt>> = ok!(stack.pop_int_or_nan());
        match first {
            Some(f) => {
                let z = match f.deref().cmp(&BigInt::from(y)) {
                    Ordering::Greater => 1,
                    Ordering::Equal => 0,
                    Ordering::Less => -1
                };

                let res = ((mode >> (4 + z * 4)) & 15) - 8;
                ok!(stack.push_int(res));
            }
            _ if quiet => ok!(stack.push_nan()),
            _ => vm_bail!(IntegerOverflow),
        }

        Ok(0)
    }

    #[instr(code = "c4", fmt = "ISNAN")]
    fn exec_is_nan(st: &mut VmState) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let int: Option<Rc<BigInt>> = ok!(stack.pop_int_or_nan());
        let result = if int.is_some() { 0 } else { -1 };
        ok!(stack.push_int(result));
        Ok(0)
    }

    #[instr(code = "c5", fmt = "CHKNAN")]
    fn exec_chk_nan(st: &mut VmState) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let int = ok!(stack.pop_int());
        ok!(stack.push_raw(int));
        Ok(0)
    }

}

pub struct CompareArgs {
    mode: i32,
    quiet: bool,
    name: String
}

impl CompareArgs {

}