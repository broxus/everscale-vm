use std::ops::{Not, Shl};
use std::rc::Rc;

use everscale_vm_proc::vm_module;
use num_bigint::BigInt;

use crate::error::VmResult;
use crate::VmState;

pub struct Shiftops;

#[vm_module]
impl Shiftops {
    #[instr(code = "b1", fmt = "OR", args(quiet = false))]
    #[instr(code = "b7b1", fmt = "QOR", args(quiet = true))] // TODO: differs from the specification. Original C++ implementation has the same problem
    fn exec_or(st: &mut VmState, quiet: bool) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let y: Option<Rc<BigInt>> = ok!(stack.pop_int_or_nan());
        let x: Option<Rc<BigInt>> = ok!(stack.pop_int_or_nan());
        match (x, y) {
            (Some(mut x), Some(y)) => {
                *Rc::make_mut(&mut x) |= y.as_ref();
                ok!(stack.push_raw_int(x, quiet));
            }
            _ if quiet => ok!(stack.push_nan()),
            _ => vm_bail!(IntegerOverflow),
        }

        Ok(0)
    }

    #[instr(code = "b0", fmt = "AND", args(quiet = false))]
    #[instr(code = "b7b0", fmt = "QAND", args(quiet = true))] // TODO: differs from the specification. Original C++ implementation has the same problem
    fn exec_and(st: &mut VmState, quiet: bool) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let y: Option<Rc<BigInt>> = ok!(stack.pop_int_or_nan());
        let x: Option<Rc<BigInt>> = ok!(stack.pop_int_or_nan());
        match (x, y) {
            (Some(mut x), Some(y)) => {
                *Rc::make_mut(&mut x) &= y.as_ref();
                ok!(stack.push_raw_int(x, quiet));
            }
            _ if quiet => ok!(stack.push_nan()),
            _ => vm_bail!(IntegerOverflow),
        }

        Ok(0)
    }

    #[instr(code = "b2", fmt = "XOR", args(quiet = false))]
    #[instr(code = "b7b2", fmt = "QXOR", args(quiet = true))]
    fn exec_xor(st: &mut VmState, quiet: bool) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let y: Option<Rc<BigInt>> = ok!(stack.pop_int_or_nan());
        let x: Option<Rc<BigInt>> = ok!(stack.pop_int_or_nan());
        match (x, y) {
            (Some(mut x), Some(y)) => {
                *Rc::make_mut(&mut x) ^= y.as_ref();
                ok!(stack.push_raw_int(x, quiet));
            }
            _ if quiet => ok!(stack.push_nan()),
            _ => vm_bail!(IntegerOverflow),
        }

        Ok(0)
    }

    #[instr(code = "b3", fmt = "NOT", args(quiet = false))]
    #[instr(code = "b7b3", fmt = "QNOT", args(quiet = true))]
    fn exec_not(st: &mut VmState, quiet: bool) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        // let y = ok!(stack.pop_smallint_range(0, 1023));
        let x: Option<Rc<BigInt>> = ok!(stack.pop_int_or_nan());
        match x {
            Some(x) => {
                let x = x.as_ref().not();
                ok!(stack.push_raw_int(Rc::new(x), quiet));
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
        let x = BigInt::from(1).shl(y);
        ok!(stack.push_raw_int(Rc::new(x), quiet));
        Ok(0)
    }
}

#[cfg(test)]
mod tests {
    use num_bigint::BigInt;
    use tracing_test::traced_test;

    #[test]
    #[traced_test]
    pub fn shift_tests() {
        assert_run_vm!("AND", [int 1, int 1] => [int 1]);
        assert_run_vm!("AND", [int 0, int 1] => [int 0]);
        assert_run_vm!("AND", [int 0, int 0] => [int 0]);
        assert_run_vm!("AND", [nan, int 1] => [int 0], exit_code: 4);
        assert_run_vm!("QAND", [nan, int 1] => [nan]);

        assert_run_vm!("OR", [int 1, int 1] => [int 1]);
        assert_run_vm!("OR", [int 0, int 1] => [int 1]);
        assert_run_vm!("OR", [int 0, int 0] => [int 0]);
        assert_run_vm!("OR", [nan, int 1] => [int 0], exit_code: 4);
        assert_run_vm!("QOR", [nan, int 1] => [nan]);

        assert_run_vm!("XOR", [int 1, int 1] => [int 0]);
        assert_run_vm!("XOR", [int 0, int 1] => [int 1]);
        assert_run_vm!("XOR", [int 0, int 0] => [int 0]);
        assert_run_vm!("XOR", [nan, int 1] => [int 0], exit_code: 4);
        assert_run_vm!("QXOR", [nan, int 1] => [nan]);

        assert_run_vm!("NOT", [int 1] => [int -2]);
        assert_run_vm!("NOT", [int 0] => [int -1]);
        assert_run_vm!("NOT", [int 4] => [int -5]);
        assert_run_vm!("NOT", [int -4] => [int 3]);
        assert_run_vm!("NOT", [nan] => [int 0], exit_code: 4);
        assert_run_vm!("QNOT", [nan] => [nan]);

        assert_run_vm!("LSHIFT# 5", [int 1] => [int 32]);
        assert_run_vm!("RSHIFT# 5", [int 32] => [int 1]);

        assert_run_vm!("RSHIFT", [int 32, int 5] => [int 1]);
        assert_run_vm!("RSHIFT", [int 5] => [int 0], exit_code: 2);
        assert_run_vm!("QRSHIFT", [nan, int 5] => [nan]);

        assert_run_vm!("LSHIFT", [int 1, int 5] => [int 32]);
        assert_run_vm!("LSHIFT", [int 1, int 255] => [int (BigInt::from(1) << 255)]);
        assert_run_vm!("LSHIFT", [int 5] => [int 0], exit_code: 2);
        assert_run_vm!("QLSHIFT", [nan, int 5] => [nan]);

        assert_run_vm!("RSHIFT", [int 32, int 5] => [int 1]);
        assert_run_vm!("RSHIFT", [int 5] => [int 0], exit_code: 2);
        assert_run_vm!("QRSHIFT", [nan, int 5] => [nan]);

        assert_run_vm!("POW2", [int 1] => [int 2]);
        assert_run_vm!("POW2", [int 0] => [int 1]);
        assert_run_vm!("QPOW2", [int 1] => [int 2]);
        assert_run_vm!("QPOW2", [int 0] => [int 1]);
        assert_run_vm!("POW2", [] => [int 0], exit_code: 2);
        assert_run_vm!("QPOW2", [] => [int 0], exit_code: 2);
        assert_run_vm!("QPOW2", [int 1024] => [int 0], exit_code: 5);
        assert_run_vm!("POW2", [int 1024] => [int 0], exit_code: 5);
        assert_run_vm!("POW2", [int -1] => [int 0], exit_code: 5);
    }
}
