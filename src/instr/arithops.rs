use std::cmp::Ordering;
use std::ops::Shr;
use std::rc::Rc;

use anyhow::Result;
use everscale_types::error::Error;
use everscale_vm_proc::vm_module;
use num_bigint::{BigInt, Sign};
use num_integer::Integer;
use num_traits::Zero;

use crate::dispatch::Opcodes;
use crate::error::VmResult;
use crate::util::load_int_from_slice;
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
    fn exec_push_tinyint4(st: &mut VmState, x: i32) -> VmResult<i32> {
        ok!(Rc::make_mut(&mut st.stack).push_int(x));
        Ok(0)
    }

    fn exec_push_int(st: &mut VmState, args: u32, bits: u16) -> VmResult<i32> {
        let l = (args as u16 & 0b11111) + 2;
        let value_len = 3 + l * 8;
        vm_ensure!(
            st.code.range().has_remaining(bits + value_len, 0),
            InvalidOpcode
        );
        st.code.range_mut().skip_first(bits, 0).ok();

        let mut cs = st.code.apply()?;
        let int = load_int_from_slice(&mut cs, value_len, true)?;
        st.code.set_range(cs.range());

        vm_log!("execute PUSHINT {int}");

        ok!(Rc::make_mut(&mut st.stack).push_int(int));
        Ok(0)
    }

    #[instr(code = "83xx", range_to = "83ff", fmt = "PUSHPOW2 {x}", args(x = (args & 0xff) + 1))]
    pub fn exec_push_pow2(st: &mut VmState, x: u32) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        ok!(stack.push_int(BigInt::from(1) << x));
        Ok(0)
    }

    #[instr(code = "83ff", fmt = "PUSHNAN")]
    fn exec_push_nan(st: &mut VmState) -> VmResult<i32> {
        ok!(Rc::make_mut(&mut st.stack).push_nan());
        Ok(0)
    }

    #[instr(code = "84xx", fmt = "PUSHPOW2DEC {x}", args(x = (args & 0xff) + 1))]
    fn exec_push_pow2dec(st: &mut VmState, x: u32) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let mut value = BigInt::from(1) << x;
        value -= 1;
        ok!(stack.push_int(value));
        Ok(0)
    }

    #[instr(code = "85xx", fmt = "PUSHNEGPOW2 {x}", args(x = (args & 0xff) + 1))]
    fn exec_push_negpow2(st: &mut VmState, x: u32) -> VmResult<i32> {
        ok!(Rc::make_mut(&mut st.stack).push_int(-(BigInt::from(1) << x)));
        Ok(0)
    }

    // === Simple math instructions ===
    #[instr(code = "a0", fmt = "ADD", args(quiet = false))]
    #[instr(code = "b7a0", fmt = "QADD", args(quiet = true))]
    fn exec_add(st: &mut VmState, quiet: bool) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let y = ok!(stack.pop_int_or_nan());
        let x = ok!(stack.pop_int_or_nan());
        match (x, y) {
            (Some(mut x), Some(y)) => {
                *Rc::make_mut(&mut x) += y.as_ref();
                ok!(stack.push_raw_int(x, quiet));
            }
            _ if quiet => ok!(stack.push_nan()),
            _ => vm_bail!(IntegerOverflow),
        }
        Ok(0)
    }

    #[instr(code = "a1", fmt = "SUB", args(quiet = false))]
    #[instr(code = "b7a1", fmt = "QSUB", args(quiet = true))]
    fn exec_sub(st: &mut VmState, quiet: bool) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let y = ok!(stack.pop_int_or_nan());
        let x = ok!(stack.pop_int_or_nan());
        match (x, y) {
            (Some(mut x), Some(y)) => {
                *Rc::make_mut(&mut x) -= y.as_ref();
                ok!(stack.push_raw_int(x, quiet));
            }
            _ if quiet => ok!(stack.push_nan()),
            _ => vm_bail!(IntegerOverflow),
        }
        Ok(0)
    }

    #[instr(code = "a2", fmt = "SUBR", args(quiet = false))]
    #[instr(code = "b7a2", fmt = "QSUBR", args(quiet = true))]
    fn exec_subr(st: &mut VmState, quiet: bool) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let y = ok!(stack.pop_int_or_nan());
        let x = ok!(stack.pop_int_or_nan());
        match (x, y) {
            (Some(x), Some(mut y)) => {
                *Rc::make_mut(&mut y) -= x.as_ref();
                ok!(stack.push_raw_int(y, quiet));
            }
            _ if quiet => ok!(stack.push_nan()),
            _ => vm_bail!(IntegerOverflow),
        }
        Ok(0)
    }

    #[instr(code = "a3", fmt = "NEGATE", args(quiet = false))]
    #[instr(code = "b7a3", fmt = "QNEGATE", args(quiet = true))]
    fn exec_negate(st: &mut VmState, quiet: bool) -> VmResult<i32> {
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
            _ => vm_bail!(IntegerOverflow),
        }
        Ok(0)
    }

    #[instr(code = "a4", fmt = "INC", args(quiet = false))]
    #[instr(code = "b7a4", fmt = "QINC", args(quiet = true))]
    fn exec_inc(st: &mut VmState, quiet: bool) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        match ok!(stack.pop_int_or_nan()) {
            Some(mut x) => {
                *Rc::make_mut(&mut x) += 1;
                ok!(stack.push_raw_int(x, quiet));
            }
            _ if quiet => ok!(stack.push_nan()),
            _ => vm_bail!(IntegerOverflow),
        }
        Ok(0)
    }

    #[instr(code = "a5", fmt = "DEC", args(quiet = false))]
    #[instr(code = "b7a5", fmt = "QDEC", args(quiet = true))]
    fn exec_dec(st: &mut VmState, quiet: bool) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        match ok!(stack.pop_int_or_nan()) {
            Some(mut x) => {
                *Rc::make_mut(&mut x) -= 1;
                ok!(stack.push_raw_int(x, quiet));
            }
            _ if quiet => ok!(stack.push_nan()),
            _ => vm_bail!(IntegerOverflow),
        }
        Ok(0)
    }

    #[instr(code = "a6yy", fmt = "ADDINT {y}", args(y = args as i8, quiet = false))]
    #[instr(code = "b7a6yy", fmt = "QADDINT {y}", args(y = args as i8, quiet = true))]
    fn exec_addint(st: &mut VmState, y: i8, quiet: bool) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        match ok!(stack.pop_int_or_nan()) {
            Some(mut x) => {
                *Rc::make_mut(&mut x) += y;
                ok!(stack.push_raw_int(x, quiet));
            }
            _ if quiet => ok!(stack.push_nan()),
            _ => vm_bail!(IntegerOverflow),
        }
        Ok(0)
    }

    #[instr(code = "a7yy", fmt = "MULINT {y}", args(y = args as i8, quiet = false))]
    #[instr(code = "b7a7yy", fmt = "QMULINT {y}", args(y = args as i8, quiet = true))]
    fn exec_mulint(st: &mut VmState, y: i8, quiet: bool) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        match ok!(stack.pop_int_or_nan()) {
            Some(mut x) => {
                *Rc::make_mut(&mut x) *= y;
                ok!(stack.push_raw_int(x, quiet));
            }
            _ if quiet => ok!(stack.push_nan()),
            _ => vm_bail!(IntegerOverflow),
        }
        Ok(0)
    }

    #[instr(code = "a8", fmt = "MUL", args(quiet = false))]
    #[instr(code = "b7a8", fmt = "QMUL", args(quiet = true))]
    fn exec_mul(st: &mut VmState, quiet: bool) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let y = ok!(stack.pop_int_or_nan());
        let x = ok!(stack.pop_int_or_nan());
        match (x, y) {
            (Some(mut x), Some(y)) => {
                *Rc::make_mut(&mut x) *= y.as_ref();
                ok!(stack.push_raw_int(x, quiet));
            }
            _ if quiet => ok!(stack.push_nan()),
            _ => vm_bail!(IntegerOverflow),
        }
        Ok(0)
    }

    // === Division instructions ===
    #[instr(code = "a90m", fmt = ("{}", DumpDivmod(m)), args(quiet = false))]
    #[instr(code = "b7a90m", fmt = ("Q{}", DumpDivmod(m)), args(quiet = true))]
    fn exec_divmod(st: &mut VmState, m: u32, quiet: bool) -> VmResult<i32> {
        enum Operation {
            Div,
            Mod,
            Divmod,
        }

        let round_mode = ok!(RoundMode::from_args(m & 0b11));
        let operation = match (m >> 2) & 0b11 {
            1 => Operation::Div,
            2 => Operation::Mod,
            3 => Operation::Divmod,
            _ => vm_bail!(InvalidOpcode),
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
            _ => vm_bail!(IntegerOverflow),
        }
        Ok(0)
    }

    #[instr(code = "a92m", fmt = ("{}", DumpShrmod(m, false)), args(imm = false, q = false))]
    #[instr(code = "a93mmm", fmt = ("{}", DumpShrmod(m, true)), args(imm = true, q = false))]
    #[instr(code = "b7a92m", fmt = ("Q{}", DumpShrmod(m, false)), args(imm = false, q = false))]
    fn exec_shrmod(st: &mut VmState, mut m: u32, imm: bool, q: bool) -> VmResult<i32> {
        enum Operation {
            RShift,
            ModPow2,
            RShiftMod,
        }

        let y = if imm {
            let y = (m & 0xff) + 1;
            m >>= 8;
            Some(y)
        } else {
            None
        };

        let mut round_mode = ok!(RoundMode::from_args(m & 0b11));
        let operation = match (m >> 2) & 0b11 {
            1 => Operation::RShift,
            2 => Operation::ModPow2,
            3 => Operation::RShiftMod,
            _ => vm_bail!(InvalidOpcode),
        };

        let stack = Rc::make_mut(&mut st.stack);
        let y = match y {
            Some(y) => y,
            None => ok!(stack.pop_smallint_range(0, 256)),
        };

        if y == 0 {
            round_mode = RoundMode::Floor;
        }

        match ok!(stack.pop_int_or_nan()) {
            Some(x) => match operation {
                Operation::RShift => {
                    let res = match round_mode {
                        RoundMode::Floor => x.as_ref().shr(y),
                        RoundMode::Nearest => todo!(),
                        RoundMode::Ceiling => todo!(),
                    };
                    ok!(stack.push_raw_int(update_or_new_rc(x, res), q));
                }
                Operation::ModPow2 => todo!(),
                Operation::RShiftMod => todo!(),
            },
            _ if q => {
                ok!(stack.push_nan());
                if let Operation::RShiftMod = operation {
                    ok!(stack.push_nan());
                }
            }
            _ => vm_bail!(IntegerOverflow),
        }

        Ok(0)
    }

    // === Other opcodes ===

    #[instr(code = "b608", fmt = "MIN", args(mn = true, mx = false, q = false))]
    #[instr(code = "b609", fmt = "MAX", args(mn = false, mx = true, q = false))]
    #[instr(code = "b60a", fmt = "MINMAX", args(mn = true, mx = true, q = false))]
    #[instr(code = "b7b608", fmt = "QMIN", args(mn = true, mx = false, q = true))]
    #[instr(code = "b7b609", fmt = "QMAX", args(mn = false, mx = true, q = true))]
    #[instr(code = "b7b60a", fmt = "QMINMAX", args(mn = true, mx = true, q = true))]
    fn exec_minmax(st: &mut VmState, mn: bool, mx: bool, q: bool) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let x = ok!(stack.pop_int_or_nan());
        let y = ok!(stack.pop_int_or_nan());
        match (x, y) {
            (Some(mut x), Some(mut y)) => {
                if x > y {
                    std::mem::swap(&mut x, &mut y);
                }
                if mn {
                    ok!(stack.push_raw(x));
                }
                if mx {
                    ok!(stack.push_raw(y));
                }
            }
            _ if q => {
                if mn {
                    ok!(stack.push_nan());
                }
                if mx {
                    ok!(stack.push_nan());
                }
            }
            _ => vm_bail!(IntegerOverflow),
        }
        Ok(0)
    }

    #[instr(code = "b60b", fmt = "ABS", args(quiet = false))]
    #[instr(code = "b7b60b", fmt = "QABS", args(quiet = true))]
    fn exec_abs(st: &mut VmState, quiet: bool) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        match ok!(stack.pop_int_or_nan()) {
            Some(mut x) => {
                if x.sign() == Sign::Minus {
                    let x = Rc::make_mut(&mut x);
                    *x = -std::mem::take(x);
                }
                ok!(stack.push_raw_int(x, quiet));
            }
            None if quiet => ok!(stack.push_nan()),
            None => vm_bail!(IntegerOverflow),
        }
        Ok(0)
    }
}

struct DumpDivmod(u32);

impl std::fmt::Display for DumpDivmod {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match (self.0 >> 2) & 0b11 {
            1 => "DIV",
            2 => "MOD",
            3 => "DIVMOD",
            _ => return f.write_str("DIV/MOD"),
        })?;
        f.write_str(match self.0 & 0b11 {
            1 => "R",
            2 => "C",
            _ => "",
        })
    }
}

struct DumpShrmod(u32, bool);

impl std::fmt::Display for DumpShrmod {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut m = self.0;
        let y = if self.1 {
            let y = (m & 0xff) + 1;
            m >>= 8;
            Some(y)
        } else {
            None
        };

        f.write_str(match (m >> 2) & 0b11 {
            1 => "RSHIFT",
            2 => "MODPOW2",
            3 => "RSHIFTMOD",
            _ => return f.write_str("SHR/MOD"),
        })?;
        f.write_str(match m & 0b11 {
            1 => "R",
            2 => "C",
            _ => "",
        })?;

        if let Some(y) = y {
            write!(f, " {y}")
        } else {
            Ok(())
        }
    }
}

enum RoundMode {
    Floor = 0,
    Nearest = 1,
    Ceiling = 2,
}

impl RoundMode {
    fn from_args(args: u32) -> VmResult<Self> {
        Ok(match args {
            0 => Self::Floor,
            1 => Self::Nearest,
            2 => Self::Ceiling,
            _ => vm_bail!(InvalidOpcode),
        })
    }
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
    use tracing_test::traced_test;

    use super::*;

    #[test]
    #[traced_test]
    fn op_pushconst() {
        assert_run_vm!("PUSHINT 1", [] => [int 1]);
        assert_run_vm!("PUSHINT 127", [] => [int 127]);
        assert_run_vm!("PUSHINT 32767", [] => [int 32767]);
        assert_run_vm!("PUSHINT 0x7FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF", [] => [int 0x7FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFi128]);
        assert_run_vm!("PUSHPOW2 1", [] => [int 2]);
        assert_run_vm!("PUSHPOW2 10", [] => [int (1 << 10)]);
        assert_run_vm!("PUSHPOW2 255", [] => [int (BigInt::from(1) << 255)]);
        assert_run_vm!("PUSHNAN", [] => [nan]);
        assert_run_vm!("PUSHPOW2DEC 1", [] => [int 1]);
        assert_run_vm!("PUSHPOW2DEC 10", [] => [int (1 << 10) - 1]);
        assert_run_vm!("PUSHPOW2DEC 256", [] => [int (BigInt::from(1) << 256) - 1]);
        assert_run_vm!("PUSHNEGPOW2 1", [] => [int -2]);
        assert_run_vm!("PUSHNEGPOW2 10", [] => [int (-1 << 10)]);
        assert_run_vm!("PUSHNEGPOW2 255", [] => [int (BigInt::from(-1) << 255)]);
    }

    #[test]
    #[traced_test]
    fn op_simple_math() {
        // === ADD/ADDINT/QADD/QADDINT ===

        // pos
        assert_run_vm!("ADD", [int 2, int 5] => [int 7]);
        assert_run_vm!("ADD", [int -5, int 5] => [int 0]);
        assert_run_vm!("ADDINT 2", [int 5] => [int 7]);
        assert_run_vm!("ADDINT -5", [int 5] => [int 0]);
        // neg
        assert_run_vm!("ADD", [] => [int 0], exit_code: 2);
        assert_run_vm!("ADDINT 123", [] => [int 0], exit_code: 2);
        assert_run_vm!("ADD", [int 123] => [int 0], exit_code: 2);
        assert_run_vm!("ADD", [null, int 5] => [int 0], exit_code: 7);
        assert_run_vm!("ADDINT 5", [nan] => [int 0], exit_code: 4);
        assert_run_vm!("ADD", [int int257_max(), int 1] => [int 0], exit_code: 4);
        assert_run_vm!("ADDINT 1", [int int257_max()] => [int 0], exit_code: 4);

        // pos
        assert_run_vm!("QADD", [int 2, int 5] => [int 7]);
        assert_run_vm!("QADD", [int -5, int 5] => [int 0]);
        assert_run_vm!("QADD", [int int257_max(), int 0] => [int int257_max()]);
        assert_run_vm!("QADD", [int int257_max() + 1, int 1] => [nan]);
        assert_run_vm!("QADD", [int int257_max() + 1, int 0] => [nan]);
        assert_run_vm!("QADD", [nan, int 5] => [nan]);
        assert_run_vm!("QADDINT 2", [int 5] => [int 7]);
        assert_run_vm!("QADDINT -5", [int 5] => [int 0]);
        assert_run_vm!("QADDINT 2", [nan] => [nan]);
        assert_run_vm!("QADDINT -5", [int 5] => [int 0]);
        // neg
        assert_run_vm!("QADD", [] => [int 0], exit_code: 2);
        assert_run_vm!("QADD", [int 123] => [int 0], exit_code: 2);
        assert_run_vm!("QADDINT 0", [] => [int 0], exit_code: 2);

        // === SUB/SUBINT/QSUB ===

        // pos
        assert_run_vm!("SUB", [int 2, int 5] => [int -3]);
        assert_run_vm!("SUB", [int -5, int 5] => [int -10]);
        assert_run_vm!("SUBINT 2", [int 5] => [int 3]);
        assert_run_vm!("SUBINT -5", [int 5] => [int 10]);
        // neg
        assert_run_vm!("SUB", [int -5, null] => [int 0], exit_code: 7);
        assert_run_vm!("SUB", [int int257_min(), int 1] => [int 0], exit_code: 4);

        // pos
        assert_run_vm!("QSUB", [int 2, int 5] => [int -3]);
        assert_run_vm!("QSUB", [int -5, int 5] => [int -10]);
        assert_run_vm!("QSUB", [int int257_max(), int 0] => [int int257_max()]);
        assert_run_vm!("QSUB", [int int257_min() + 1, int 1] => [int int257_min()]);
        assert_run_vm!("QSUB", [int int257_min(), int 1] => [nan]);
        assert_run_vm!("QSUB", [nan, int 5] => [nan]);
        // neg
        assert_run_vm!("QSUB", [] => [int 0], exit_code: 2);
        assert_run_vm!("QSUB", [int 123] => [int 0], exit_code: 2);

        // === SUBR/QSUBR ===

        // pos
        assert_run_vm!("SUBR", [int 5, int 2] => [int -3]);
        assert_run_vm!("SUBR", [int 5, int -5] => [int -10]);
        // neg
        assert_run_vm!("SUBR", [] => [int 0], exit_code: 2);
        assert_run_vm!("SUBR", [int 123] => [int 0], exit_code: 2);
        assert_run_vm!("SUBR", [int 5, null] => [int 0], exit_code: 7);
        assert_run_vm!("SUBR", [int -1, int int257_max()] => [int 0], exit_code: 4);

        // pos
        assert_run_vm!("QSUBR", [int 5, int 2] => [int -3]);
        assert_run_vm!("QSUBR", [int 5, int -5] => [int -10]);
        assert_run_vm!("QSUBR", [int 0, int int257_max()] => [int int257_max()]);
        assert_run_vm!("QSUBR", [int 1, int int257_min() + 1] => [int int257_min()]);
        assert_run_vm!("QSUBR", [int 1, int int257_min()] => [nan]);
        assert_run_vm!("QSUBR", [int 5, nan] => [nan]);
        // neg
        assert_run_vm!("QSUBR", [] => [int 0], exit_code: 2);
        assert_run_vm!("QSUBR", [int 123] => [int 0], exit_code: 2);

        // === NEGATE/QNEGATE ===

        // pos
        assert_run_vm!("NEGATE", [int 123] => [int -123]);
        assert_run_vm!("NEGATE", [int 0] => [int 0]);
        assert_run_vm!("NEGATE", [int -10] => [int 10]);
        assert_run_vm!("NEGATE", [int int257_min() + 1] => [int int257_max()]);
        assert_run_vm!("NEGATE", [int int257_max()] => [int int257_min() + 1]);
        // neg
        assert_run_vm!("NEGATE", [] => [int 0], exit_code: 2);
        assert_run_vm!("NEGATE", [nan] => [int 0], exit_code: 4);

        // pos
        assert_run_vm!("QNEGATE", [int 123] => [int -123]);
        assert_run_vm!("QNEGATE", [nan] => [nan]);
        // neg
        assert_run_vm!("QNEGATE", [] => [int 0], exit_code: 2);
        assert_run_vm!("QNEGATE", [null] => [int 0], exit_code: 7);

        // === INC/QINC ===

        // pos
        assert_run_vm!("INC", [int 10] => [int 11]);
        assert_run_vm!("INC", [int -1] => [int 0]);
        assert_run_vm!("INC", [int int257_max() - 1] => [int int257_max()]);
        assert_run_vm!("INC", [int int257_min()] => [int int257_min() + 1]);
        // neg
        assert_run_vm!("INC", [] => [int 0], exit_code: 2);
        assert_run_vm!("INC", [nan] => [int 0], exit_code: 4);
        assert_run_vm!("INC", [int int257_max()] => [int 0], exit_code: 4);

        // pos
        assert_run_vm!("QINC", [int 10] => [int 11]);
        assert_run_vm!("QINC", [int -1] => [int 0]);
        assert_run_vm!("QINC", [int int257_max() - 1] => [int int257_max()]);
        assert_run_vm!("QINC", [int int257_min()] => [int int257_min() + 1]);
        assert_run_vm!("QINC", [nan] => [nan]);
        assert_run_vm!("QINC", [int int257_max()] => [nan]);
        // neg
        assert_run_vm!("QINC", [] => [int 0], exit_code: 2);

        // === DEC/QDEC ===

        // pos
        assert_run_vm!("DEC", [int 10] => [int 9]);
        assert_run_vm!("DEC", [int 0] => [int -1]);
        assert_run_vm!("DEC", [int int257_min() + 1] => [int int257_min()]);
        assert_run_vm!("DEC", [int int257_max()] => [int int257_max() - 1]);
        // neg
        assert_run_vm!("DEC", [] => [int 0], exit_code: 2);
        assert_run_vm!("DEC", [nan] => [int 0], exit_code: 4);
        assert_run_vm!("DEC", [int int257_min()] => [int 0], exit_code: 4);

        // pos
        assert_run_vm!("QDEC", [int 10] => [int 9]);
        assert_run_vm!("QDEC", [int 0] => [int -1]);
        assert_run_vm!("QDEC", [int int257_min() + 1] => [int int257_min()]);
        assert_run_vm!("QDEC", [int int257_max()] => [int int257_max() - 1]);
        assert_run_vm!("QDEC", [nan] => [nan]);
        assert_run_vm!("QDEC", [int int257_min()] => [nan]);
        // neg
        assert_run_vm!("QDEC", [] => [int 0], exit_code: 2);

        // === MUL/QMUL

        // pos
        assert_run_vm!("MUL", [int 123, int 0] => [int 0]);
        assert_run_vm!("MUL", [int 123, int 1] => [int 123]);
        assert_run_vm!("MUL", [int 123, int 123] => [int 123 * 123]);
        assert_run_vm!("MUL", [int -123, int 0] => [int 0]);
        assert_run_vm!("MUL", [int -123, int 1] => [int -123]);
        assert_run_vm!("MULINT 0", [int -123] => [int 0]);
        assert_run_vm!("MULINT 1", [int -123] => [int -123]);
        assert_run_vm!("MUL", [int -123, int 123] => [int -123 * 123]);
        assert_run_vm!("MULINT 123", [int -123] => [int -123 * 123]);
        assert_run_vm!("MUL", [int -123, int -123] => [int 123 * 123]);
        assert_run_vm!("MULINT -123", [int -123] => [int 123 * 123]);
        assert_run_vm!("MUL", [int int257_min(), int 0] => [int 0]);
        assert_run_vm!("MUL", [int int257_max(), int 0] => [int 0]);
        assert_run_vm!("MUL", [int int257_min(), int 1] => [int int257_min()]);
        assert_run_vm!("MUL", [int int257_max(), int 1] => [int int257_max()]);
        assert_run_vm!("MUL", [int int257_max(), int -1] => [int int257_min() + 1]);
        // neg
        assert_run_vm!("MUL", [] => [int 0], exit_code: 2);
        assert_run_vm!("MUL", [int 2] => [int 0], exit_code: 2);
        assert_run_vm!("MUL", [int 2, nan] => [int 0], exit_code: 4);
        assert_run_vm!("MUL", [nan, int 2] => [int 0], exit_code: 4);
        assert_run_vm!("MUL", [int 2, null] => [int 0], exit_code: 7);
        assert_run_vm!("MUL", [int int257_min(), int -1] => [int 0], exit_code: 4);
        assert_run_vm!("MUL", [int int257_min() / 2, int -2] => [int 0], exit_code: 4);
        assert_run_vm!("MUL", [int int257_max(), int 2] => [int 0], exit_code: 4);

        // pos
        assert_run_vm!("QMUL", [int 123, int 0] => [int 0]);
        assert_run_vm!("QMUL", [int 123, int 1] => [int 123]);
        assert_run_vm!("QMUL", [int 123, int 123] => [int 123 * 123]);
        assert_run_vm!("QMUL", [int -123, int 0] => [int 0]);
        assert_run_vm!("QMUL", [int -123, int 1] => [int -123]);
        assert_run_vm!("QMULINT 0", [int -123] => [int 0]);
        assert_run_vm!("QMULINT 1", [int -123] => [int -123]);
        assert_run_vm!("QMUL", [int -123, int 123] => [int -123 * 123]);
        assert_run_vm!("QMULINT 123", [int -123] => [int -123 * 123]);
        assert_run_vm!("QMUL", [int -123, int -123] => [int 123 * 123]);
        assert_run_vm!("QMULINT -123", [int -123] => [int 123 * 123]);
        assert_run_vm!("QMUL", [int int257_min(), int 0] => [int 0]);
        assert_run_vm!("QMUL", [int int257_max(), int 0] => [int 0]);
        assert_run_vm!("QMUL", [int int257_min(), int 1] => [int int257_min()]);
        assert_run_vm!("QMUL", [int int257_max(), int 1] => [int int257_max()]);
        assert_run_vm!("QMUL", [int int257_max(), int -1] => [int int257_min() + 1]);
        assert_run_vm!("QMUL", [nan, int 2] => [nan]);
        assert_run_vm!("QMUL", [int 2, nan] => [nan]);
        assert_run_vm!("QMUL", [int int257_min(), int -1] => [nan]);
        assert_run_vm!("QMUL", [int int257_min() / 2, int -2] => [nan]);
        assert_run_vm!("QMUL", [int int257_max(), int 2] => [nan]);
        // neg
        assert_run_vm!("QMUL", [] => [int 0], exit_code: 2);
        assert_run_vm!("QMUL", [int 2] => [int 0], exit_code: 2);
        assert_run_vm!("QMUL", [int 2, null] => [int 0], exit_code: 7);
    }

    #[test]
    #[traced_test]
    fn op_divmod() {
        // pos
        assert_run_vm!("DIV", [int 5, int 5] => [int 1]);
        assert_run_vm!("DIV", [int 5, int 2] => [int 2]);
        assert_run_vm!("DIVR", [int 10, int 3] => [int 3]);
        assert_run_vm!("DIVC", [int 10, int 3] => [int 4]);
        // neg
        assert_run_vm!("DIV", [] => [int 0], exit_code: 2);
        assert_run_vm!("DIV", [int 123] => [int 0], exit_code: 2);
        assert_run_vm!("DIV", [int 1, int 0] => [int 0], exit_code: 4);

        // pos
        assert_run_vm!("MOD", [int 5, int 5] => [int 0]);
        assert_run_vm!("MOD", [int 5, int 2] => [int 1]);
        assert_run_vm!("MODR", [int 10, int 3] => [int 1]);
        assert_run_vm!("MODC", [int 10, int 3] => [int -2]);
        // neg
        assert_run_vm!("MOD", [] => [int 0], exit_code: 2);
        assert_run_vm!("MOD", [int 123] => [int 0], exit_code: 2);
        assert_run_vm!("MOD", [int 1, int 0] => [int 0], exit_code: 4);

        assert_run_vm!("DIVMOD", [int 5, int 5] => [int 1, int 0]);
        assert_run_vm!("DIVMOD", [int 5, int 2] => [int 2, int 1]);
        assert_run_vm!("DIVMODR", [int 10, int 3] => [int 3, int 1]);
        assert_run_vm!("DIVMODC", [int 10, int 3] => [int 4, int -2]);
        // neg
        assert_run_vm!("DIVMOD", [] => [int 0], exit_code: 2);
        assert_run_vm!("DIVMOD", [int 123] => [int 0], exit_code: 2);
        assert_run_vm!("DIVMOD", [int 1, int 0] => [int 0], exit_code: 4);
    }

    #[test]
    #[traced_test]
    fn op_shrmod() {
        assert_run_vm!("@inline x{a924}", [int 5, int 2] => [int 1]);
    }

    #[test]
    #[traced_test]
    fn other_ops() {
        // === MIN/MAX/MINMAX/QMIN/QMAX/QMINMAX ===

        // pos
        assert_run_vm!("MIN", [int 123, int 456] => [int 123]);
        assert_run_vm!("MAX", [int 123, int 456] => [int 456]);
        assert_run_vm!("MINMAX", [int 456, int 123] => [int 123, int 456]);
        // neg
        assert_run_vm!("MIN", [] => [int 0], exit_code: 2);
        assert_run_vm!("MIN", [int 123] => [int 0], exit_code: 2);
        assert_run_vm!("MIN", [int 123, nan] => [int 0], exit_code: 4);
        assert_run_vm!("MINMAX", [int 123, nan] => [int 0], exit_code: 4);

        // pos
        assert_run_vm!("QUIET MIN", [int 123, int 456] => [int 123]);
        assert_run_vm!("QUIET MAX", [int 123, int 456] => [int 456]);
        assert_run_vm!("QUIET MINMAX", [int 456, int 123] => [int 123, int 456]);
        assert_run_vm!("QUIET MIN", [int 123, nan] => [nan]);
        assert_run_vm!("QUIET MINMAX", [int 123, nan] => [nan, nan]);
        // neg
        assert_run_vm!("QUIET MIN", [] => [int 0], exit_code: 2);
        assert_run_vm!("QUIET MIN", [int 123] => [int 0], exit_code: 2);

        // === ABS/QABS ===

        // pos
        assert_run_vm!("ABS", [int 0] => [int 0]);
        assert_run_vm!("ABS", [int 123] => [int 123]);
        assert_run_vm!("ABS", [int -123123] => [int 123123]);
        assert_run_vm!("ABS", [int int257_min() + 1] => [int int257_max()]);
        // neg
        assert_run_vm!("ABS", [] => [int 0], exit_code: 2);
        assert_run_vm!("ABS", [nan] => [int 0], exit_code: 4);
        assert_run_vm!("ABS", [int int257_min()] => [int 0], exit_code: 4);
        assert_run_vm!("ABS", [null] => [int 0], exit_code: 7);

        // pos
        assert_run_vm!("QUIET ABS", [int 0] => [int 0]);
        assert_run_vm!("QUIET ABS", [int 123] => [int 123]);
        assert_run_vm!("QUIET ABS", [int -123123] => [int 123123]);
        assert_run_vm!("QUIET ABS", [int int257_min() + 1] => [int int257_max()]);
        assert_run_vm!("QUIET ABS", [nan] => [nan]);
        assert_run_vm!("QUIET ABS", [int int257_min()] => [nan]);
        // neg
        assert_run_vm!("QUIET ABS", [] => [int 0], exit_code: 2);
        assert_run_vm!("QUIET ABS", [null] => [int 0], exit_code: 7);
    }

    fn int257_min() -> BigInt {
        BigInt::from(-1) << 256
    }

    fn int257_max() -> BigInt {
        (BigInt::from(1) << 256) - 1
    }
}
