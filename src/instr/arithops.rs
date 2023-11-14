use std::cmp::Ordering;
use std::rc::Rc;

use anyhow::Result;
use everscale_vm_proc::vm_module;
use num_bigint::BigInt;
use num_integer::Integer;
use num_traits::Zero;

use crate::dispatch::Opcodes;
use crate::error::VmError;
use crate::VmState;

pub struct Arithops;

#[vm_module]
impl Arithops {
    // === Int constants ===

    #[init]
    fn init_int_const_ext(&self, t: &mut Opcodes) -> Result<()> {
        t.add_ext_range(0x82 << 5, (0x82 << 5) + 31, 13, exec_push_int)?;
        Ok(())
    }

    #[instr(code = "7x", fmt = "PUSHINT {x}", args(x = ((args as i32 + 5) & 0xf) - 5))]
    #[instr(code = "80xx", fmt = "PUSHINT {x}", args(x = args as i8 as i32))]
    #[instr(code = "81xxxx", fmt = "PUSHINT {x}", args(x = args as i16 as i32))]
    fn exec_push_tinyint4(st: &mut VmState, x: i32) -> Result<i32> {
        ok!(Rc::make_mut(&mut st.stack).push_int(x));
        Ok(0)
    }

    fn exec_push_int(st: &mut VmState, args: u32, bits: u16) -> Result<i32> {
        let l = (args as u16 & 0b11111) + 2;
        let value_len = 3 + l * 8;
        anyhow::ensure!(
            st.code.range().has_remaining(bits + value_len, 0),
            VmError::InvalidOpcode
        );
        st.code.range_mut().try_advance(bits, 0);

        let mut bytes = [0u8; 33];
        let rem = value_len % 8;
        let mut int = {
            let mut cs = st.code.apply()?;
            let bytes = cs.load_raw(&mut bytes, value_len)?;
            st.code.set_range(cs.range());
            num_bigint::BigUint::from_bytes_be(bytes)
        };
        if rem != 0 {
            int >>= 8 - rem;
        }
        vm_log!("execute PUSHINT {int}");

        ok!(Rc::make_mut(&mut st.stack).push_int(int));

        Ok(0)
    }

    #[instr(code = "83xx", range_to = "83ff", fmt = "PUSHPOW2 {x}", args(x = (args & 0xff) + 1))]
    pub fn exec_push_pow2(st: &mut VmState, x: u32) -> Result<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        ok!(stack.push_int(BigInt::from(1) << x));
        Ok(0)
    }

    #[instr(code = "83ff", fmt = "PUSHNAN")]
    fn exec_push_nan(st: &mut VmState) -> Result<i32> {
        ok!(Rc::make_mut(&mut st.stack).push_nan());
        Ok(0)
    }

    #[instr(code = "84xx", fmt = "PUSHPOW2DEC {x}", args(x = (args & 0xff) + 1))]
    fn exec_push_pow2dec(st: &mut VmState, x: u32) -> Result<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let mut value = BigInt::from(1) << x;
        value -= 1;
        ok!(stack.push_int(value));
        Ok(0)
    }

    #[instr(code = "85xx", fmt = "PUSHNEGPOW2 {x}", args(x = (args & 0xff) + 1))]
    fn exec_push_negpow2(st: &mut VmState, x: u32) -> Result<i32> {
        ok!(Rc::make_mut(&mut st.stack).push_int(-(BigInt::from(1) << x)));
        Ok(0)
    }

    // === Simple math instructions ===
    #[instr(code = "a0", fmt = "ADD", args(quiet = false))]
    #[instr(code = "b7a0", fmt = "QADD", args(quiet = true))]
    fn exec_add(st: &mut VmState, quiet: bool) -> Result<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let y = ok!(stack.pop_int_or_nan());
        let x = ok!(stack.pop_int_or_nan());
        match (x, y) {
            (Some(mut x), Some(y)) => {
                *Rc::make_mut(&mut x) += y.as_ref();
                ok!(stack.push_raw_int(x, quiet));
            }
            _ if quiet => ok!(stack.push_nan()),
            _ => anyhow::bail!(VmError::IntegerOverflow),
        }
        Ok(0)
    }

    #[instr(code = "a1", fmt = "SUB", args(quiet = false))]
    #[instr(code = "b7a1", fmt = "QSUB", args(quiet = true))]
    fn exec_sub(st: &mut VmState, quiet: bool) -> Result<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let y = ok!(stack.pop_int_or_nan());
        let x = ok!(stack.pop_int_or_nan());
        match (x, y) {
            (Some(mut x), Some(y)) => {
                *Rc::make_mut(&mut x) -= y.as_ref();
                ok!(stack.push_raw_int(x, quiet));
            }
            _ if quiet => ok!(stack.push_nan()),
            _ => anyhow::bail!(VmError::IntegerOverflow),
        }
        Ok(0)
    }

    #[instr(code = "a2", fmt = "SUBR", args(quiet = false))]
    #[instr(code = "b7a2", fmt = "QSUBR", args(quiet = true))]
    fn exec_subr(st: &mut VmState, quiet: bool) -> Result<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let y = ok!(stack.pop_int_or_nan());
        let x = ok!(stack.pop_int_or_nan());
        match (x, y) {
            (Some(x), Some(mut y)) => {
                *Rc::make_mut(&mut y) -= x.as_ref();
                ok!(stack.push_raw_int(y, quiet));
            }
            _ if quiet => ok!(stack.push_nan()),
            _ => anyhow::bail!(VmError::IntegerOverflow),
        }
        Ok(0)
    }

    #[instr(code = "a3", fmt = "NEGATE", args(quiet = false))]
    #[instr(code = "b7a3", fmt = "QNEGATE", args(quiet = true))]
    fn exec_negate(st: &mut VmState, quiet: bool) -> Result<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        match ok!(stack.pop_int_or_nan()) {
            Some(mut x) => {
                {
                    let x = Rc::make_mut(&mut x);
                    *x = -std::mem::take(x);
                }
                ok!(stack.push_raw_int(x, quiet));
            }
            _ if quiet => ok!(stack.push_nan()),
            _ => anyhow::bail!(VmError::IntegerOverflow),
        }
        Ok(0)
    }

    #[instr(code = "a4", fmt = "INC", args(quiet = false))]
    #[instr(code = "b7a4", fmt = "QINC", args(quiet = true))]
    fn exec_inc(st: &mut VmState, quiet: bool) -> Result<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        match ok!(stack.pop_int_or_nan()) {
            Some(mut x) => {
                *Rc::make_mut(&mut x) += 1;
                ok!(stack.push_raw_int(x, quiet));
            }
            _ if quiet => ok!(stack.push_nan()),
            _ => anyhow::bail!(VmError::IntegerOverflow),
        }
        Ok(0)
    }

    #[instr(code = "a5", fmt = "DEC", args(quiet = false))]
    #[instr(code = "b7a5", fmt = "QDEC", args(quiet = true))]
    fn exec_dec(st: &mut VmState, quiet: bool) -> Result<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        match ok!(stack.pop_int_or_nan()) {
            Some(mut x) => {
                *Rc::make_mut(&mut x) -= 1;
                ok!(stack.push_raw_int(x, quiet));
            }
            _ if quiet => ok!(stack.push_nan()),
            _ => anyhow::bail!(VmError::IntegerOverflow),
        }
        Ok(0)
    }

    #[instr(code = "a6yy", fmt = "ADDINT {y}", args(y = args as i8, quiet = false))]
    #[instr(code = "b7a6yy", fmt = "QADDINT {y}", args(y = args as i8, quiet = true))]
    fn exec_addint(st: &mut VmState, y: i8, quiet: bool) -> Result<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        match ok!(stack.pop_int_or_nan()) {
            Some(mut x) => {
                *Rc::make_mut(&mut x) += y;
                ok!(stack.push_raw_int(x, quiet));
            }
            _ if quiet => ok!(stack.push_nan()),
            _ => anyhow::bail!(VmError::IntegerOverflow),
        }
        Ok(0)
    }

    #[instr(code = "a7yy", fmt = "MULINT {y}", args(y = args as i8, quiet = false))]
    #[instr(code = "b7a7yy", fmt = "QMULINT {y}", args(y = args as i8, quiet = true))]
    fn exec_mulint(st: &mut VmState, y: i8, quiet: bool) -> Result<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        match ok!(stack.pop_int_or_nan()) {
            Some(mut x) => {
                *Rc::make_mut(&mut x) *= y;
                ok!(stack.push_raw_int(x, quiet));
            }
            _ if quiet => ok!(stack.push_nan()),
            _ => anyhow::bail!(VmError::IntegerOverflow),
        }
        Ok(0)
    }

    #[instr(code = "a8", fmt = "MUL", args(quiet = false))]
    #[instr(code = "b7a8", fmt = "QMUL", args(quiet = true))]
    fn exec_mul(st: &mut VmState, quiet: bool) -> Result<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let y = ok!(stack.pop_int_or_nan());
        let x = ok!(stack.pop_int_or_nan());
        match (x, y) {
            (Some(mut x), Some(y)) => {
                *Rc::make_mut(&mut x) *= y.as_ref();
                ok!(stack.push_raw_int(x, quiet));
            }
            _ if quiet => ok!(stack.push_nan()),
            _ => anyhow::bail!(VmError::IntegerOverflow),
        }
        Ok(0)
    }

    // === Division instructions ===
    #[instr(code = "a90m", fmt = "DIV/MOD {m}", args(quiet = false))]
    fn exec_divmod(st: &mut VmState, m: u32, quiet: bool) -> Result<i32> {
        enum Operation {
            Div,
            Mod,
            Divmod,
        }

        fn nearest_rounding_required(r: &BigInt, x: &BigInt, y: &BigInt) -> bool {
            if r.is_zero() {
                return false;
            }

            let r_x2: BigInt = r << 1;
            match r_x2.magnitude().cmp(y.magnitude()) {
                Ordering::Greater => true,
                Ordering::Equal if x.sign() == y.sign() => true,
                _ => false,
            }
        }

        fn ceil_rounding_required(r: &BigInt, y: &BigInt) -> bool {
            !r.is_zero() && r.sign() == y.sign()
        }

        let round_mode = ok!(RoundMode::from_args(m & 0b11));
        let operation = match (m >> 2) & 0b11 {
            1 => Operation::Div,
            2 => Operation::Mod,
            3 => Operation::Divmod,
            _ => anyhow::bail!(VmError::InvalidOpcode),
        };

        let stack = Rc::make_mut(&mut st.stack);
        let y = ok!(stack.pop_int_or_nan());
        let x = ok!(stack.pop_int_or_nan());
        match (x, y) {
            (Some(x), Some(y)) if !y.is_zero() => match operation {
                Operation::Div => {
                    let res = match round_mode {
                        RoundMode::Floor => x.div_floor(&y),
                        RoundMode::Nearest => {
                            let (mut q, r) = x.div_rem(&y);
                            if nearest_rounding_required(&r, &x, &y) {
                                if x.sign() == y.sign() {
                                    q += 1;
                                } else {
                                    q -= 1;
                                }
                            }
                            q
                        }
                        RoundMode::Ceiling => {
                            let (mut q, r) = x.div_rem(&y);
                            if ceil_rounding_required(&r, &y) {
                                if x.sign() == y.sign() {
                                    q += 1;
                                } else {
                                    q -= 1;
                                }
                            }
                            q
                        }
                    };
                    ok!(stack.push_raw_int(update_or_new_rc(x, res), quiet));
                }
                Operation::Mod => {
                    let res = match round_mode {
                        RoundMode::Floor => x.mod_floor(y.as_ref()),
                        RoundMode::Nearest => {
                            let (_, mut r) = x.div_rem(&y);
                            if nearest_rounding_required(&r, &x, &y) {
                                if r.sign() == y.sign() {
                                    r -= y.as_ref();
                                } else {
                                    r += y.as_ref();
                                }
                            }
                            r
                        }
                        RoundMode::Ceiling => {
                            let (_, mut r) = x.div_rem(&y);
                            if ceil_rounding_required(&r, &y) {
                                r -= y.as_ref();
                            }
                            r
                        }
                    };
                    ok!(stack.push_raw_int(update_or_new_rc(x, res), quiet));
                }
                Operation::Divmod => {
                    let (q, r) = match round_mode {
                        RoundMode::Floor => x.div_mod_floor(&y),
                        RoundMode::Nearest => {
                            let (mut q, mut r) = x.div_rem(&y);
                            if nearest_rounding_required(&r, &x, &y) {
                                if x.sign() == y.sign() {
                                    q += 1;
                                } else {
                                    q -= 1;
                                }
                                if r.sign() == y.sign() {
                                    r -= y.as_ref();
                                } else {
                                    r += y.as_ref();
                                }
                            }
                            (q, r)
                        }
                        RoundMode::Ceiling => {
                            let (mut q, mut r) = x.div_rem(&y);
                            if ceil_rounding_required(&r, &y) {
                                r -= y.as_ref();
                                if x.sign() == y.sign() {
                                    q += 1;
                                } else {
                                    q -= 1;
                                }
                            }
                            (q, r)
                        }
                    };
                    ok!(stack.push_raw_int(update_or_new_rc(x, q), quiet));
                    ok!(stack.push_raw_int(update_or_new_rc(y, r), quiet));
                }
            },
            _ if quiet => {
                ok!(stack.push_nan());
                if let Operation::Divmod = operation {
                    ok!(stack.push_nan());
                }
            }
            _ => anyhow::bail!(VmError::IntegerOverflow),
        }
        Ok(0)
    }
}

enum RoundMode {
    Floor,
    Nearest,
    Ceiling,
}

impl RoundMode {
    fn from_args(args: u32) -> Result<Self> {
        Ok(match args {
            0 => Self::Floor,
            1 => Self::Nearest,
            2 => Self::Ceiling,
            _ => anyhow::bail!(VmError::InvalidOpcode),
        })
    }
}

fn update_or_new_rc(mut rc: Rc<BigInt>, value: BigInt) -> Rc<BigInt> {
    match Rc::get_mut(&mut rc) {
        None => Rc::new(value),
        Some(x) => {
            *x = value;
            rc
        }
    }
}

#[cfg(test)]
mod tests {

    #[test]
    fn op_divmod() {
        assert_run_vm!("DIV", [int 5, int 5] => [int 1]);
        assert_run_vm!("DIV", [int 5, int 2] => [int 2]);
        assert_run_vm!("DIVR", [int 10, int 3] => [int 3]);
        assert_run_vm!("DIVC", [int 10, int 3] => [int 4]);

        assert_run_vm!("MOD", [int 5, int 5] => [int 0]);
        assert_run_vm!("MOD", [int 5, int 2] => [int 1]);
        assert_run_vm!("MODR", [int 10, int 3] => [int 1]);
        assert_run_vm!("MODC", [int 10, int 3] => [int -2]);

        assert_run_vm!("DIVMOD", [int 5, int 5] => [int 1, int 0]);
        assert_run_vm!("DIVMOD", [int 5, int 2] => [int 2, int 1]);
        assert_run_vm!("DIVMODR", [int 10, int 3] => [int 3, int 1]);
        assert_run_vm!("DIVMODC", [int 10, int 3] => [int 4, int -2]);
    }
}
