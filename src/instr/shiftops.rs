use std::env::args;
use crate::error::VmResult;
use crate::VmState;
use everscale_vm_proc::vm_module;
use num_bigint::BigInt;
use std::ops::{BitAnd, BitOr, BitXor, Deref, Shl};
use std::rc::Rc;

pub struct Shiftops;

#[vm_module]
impl Shiftops {
    #[instr(code = "b1", fmt = "OR", args(quiet = false))]
    #[instr(code = "b7b1", fmt = "QOR", args(quiet = false))]
    fn exec_or(st: &mut VmState, quiet: bool) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let y: Rc<BigInt> = ok!(stack.pop_int());
        let x: Option<Rc<BigInt>> = ok!(stack.pop_int_or_nan());
        match x {
            Some(f) => {
                let result = f.deref().bitor(y.deref());
                ok!(stack.push_raw_int(Rc::new(result), quiet));
            }
            _ if quiet => ok!(stack.push_nan()),
            _ => vm_bail!(IntegerOverflow),
        }

        Ok(0)
    }

    #[instr(code = "b0", fmt = "AND", args(quiet = false))]
    #[instr(code = "b7b0", fmt = "QAND", args(quiet = false))]
    fn exec_and(st: &mut VmState, quiet: bool) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let y: Rc<BigInt> = ok!(stack.pop_int());
        let x: Option<Rc<BigInt>> = ok!(stack.pop_int_or_nan());
        match x {
            Some(f) => {
                let result = f.deref().bitand(y.deref());
                ok!(stack.push_raw_int(Rc::new(result), quiet));
            }
            _ if quiet => ok!(stack.push_nan()),
            _ => vm_bail!(IntegerOverflow),
        }

        Ok(0)
    }

    #[instr(code = "b2", fmt = "XOR", args(quiet = false))]
    #[instr(code = "b7b2", fmt = "QXOR", args(quiet = false))]
    fn exec_xor(st: &mut VmState, quiet: bool) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let y: Rc<BigInt> = ok!(stack.pop_int());
        let x: Option<Rc<BigInt>> = ok!(stack.pop_int_or_nan());
        match x {
            Some(f) => {
                let result = f.deref().bitxor(y.deref());
                ok!(stack.push_raw_int(Rc::new(result), quiet));
            }
            _ if quiet => ok!(stack.push_nan()),
            _ => vm_bail!(IntegerOverflow),
        }

        Ok(0)
    }


    #[instr(code = "aayy", fmt = "LSHIFT {y}", args(y = (args & 0xff) + 1, quiet = false))]
    #[instr(code = "b7aayy", fmt = "QLSHIFT {y}", args(y = (args & 0xff) + 1, quiet = true))]
    fn exec_lshift_tinyint8(st: &mut VmState, y: u32, quiet: bool) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        match ok!(stack.pop_int_or_nan()) {
            Some(mut x) => {
                *Rc::make_mut(&mut x) <<= y;
                ok!(stack.push_raw_int(x, quiet));
            }
            _ if quiet => ok!(stack.push_nan()),
            _ => vm_bail!(IntegerOverflow),
        }
        Ok(0)
    }

    #[instr(code = "abyy", fmt = "RSHIFT {y}", args(y = (args & 0xff) + 1, quiet = false))]
    #[instr(code = "b7abyy", fmt = "QRSHIFT {y}", args(y = (args & 0xff) + 1, quiet = true))]
    fn exec_rshift_tinyint8(st: &mut VmState, y: u32, quiet: bool) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        match ok!(stack.pop_int_or_nan()) {
            Some(mut x) => {
                *Rc::make_mut(&mut x) >>= y;
                ok!(stack.push_raw_int(x, quiet));
            }
            _ if quiet => ok!(stack.push_nan()),
            _ => vm_bail!(IntegerOverflow),
        }
        Ok(0)
    }

    #[instr(code = "ac", fmt = "LSHIFT", args(quiet = false))]
    #[instr(code = "b7ac", fmt = "QLSHIFT", args(quiet = true))]
    fn exec_lshift(st: &mut VmState, quiet: bool) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let y = ok!(stack.pop_smallint_range(0, 1023));
        match ok!(stack.pop_int_or_nan()) {
            Some(mut x) => {
                *Rc::make_mut(&mut x) <<= y;
                ok!(stack.push_raw_int(x, quiet));
            }
            _ if quiet => ok!(stack.push_nan()),
            _ => vm_bail!(IntegerOverflow),
        }
        Ok(0)
    }

    #[instr(code = "ad", fmt = "RSHIFT", args(quiet = false))]
    #[instr(code = "b7ad", fmt = "QRSHIFT", args(quiet = true))]
    fn exec_rshift(st: &mut VmState, quiet: bool) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let y = ok!(stack.pop_smallint_range(0, 1023));
        match ok!(stack.pop_int_or_nan()) {
            Some(mut x) => {
                *Rc::make_mut(&mut x) >>= y;
                ok!(stack.push_raw_int(x, quiet));
            }
            _ if quiet => ok!(stack.push_nan()),
            _ => vm_bail!(IntegerOverflow),
        }
        Ok(0)
    }

    #[instr(code = "ae", fmt = "POW2", args(quiet = false))]
    #[instr(code = "b7ae", fmt = "QPOW2", args(quiet = true))]
    fn exec_pow2(st: &mut VmState, quiet: bool) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let y = ok!(stack.pop_smallint_range(0, 1023));
        let result = BigInt::from(2).pow(y);
        ok!(stack.push_raw_int(Rc::new(result), quiet));
        Ok(0)
    }

}
