use std::cmp::Ordering;
use std::rc::Rc;

use everscale_vm_proc::vm_module;
use num_bigint::{BigInt, Sign};
use num_traits::ToPrimitive;

use crate::error::VmResult;
use crate::state::VmState;

pub struct CmpOps;

#[vm_module]
impl CmpOps {
    #[op(code = "b8", fmt = "SGN", args(quiet = false))]
    #[op(code = "b7b8", fmt = "QSGN", args(quiet = true))]
    fn exec_sgn(st: &mut VmState, quiet: bool) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let Some(x) = ok!(stack.pop_int_or_nan()) else {
            vm_ensure!(quiet, IntegerOverflow);
            ok!(stack.push_nan());
            return Ok(0);
        };
        ok!(stack.push_int(match x.sign() {
            Sign::Minus => -1,
            Sign::NoSign => 0,
            Sign::Plus => 1,
        }));
        Ok(0)
    }

    #[op(code = "b9", fmt = "LESS", args(mode = 0x887, quiet = false))]
    #[op(code = "ba", fmt = "EQUAL", args(mode = 0x878, quiet = false))]
    #[op(code = "bb", fmt = "LEQ", args(mode = 0x877, quiet = false))]
    #[op(code = "bc", fmt = "GREATER", args(mode = 0x788, quiet = false))]
    #[op(code = "bd", fmt = "NEQ", args(mode = 0x787, quiet = false))]
    #[op(code = "be", fmt = "GEQ", args(mode = 0x778, quiet = false))]
    #[op(code = "bf", fmt = "CMP", args(mode = 0x987, quiet = false))]
    #[op(code = "b7b9", fmt = "QLESS", args(mode = 0x887, quiet = true))]
    #[op(code = "b7ba", fmt = "QEQUAL", args(mode = 0x878, quiet = true))]
    #[op(code = "b7bb", fmt = "QLEQ", args(mode = 0x877, quiet = true))]
    #[op(code = "b7bc", fmt = "QGREATER", args(mode = 0x788, quiet = true))]
    #[op(code = "b7bd", fmt = "QNEQ", args(mode = 0x787, quiet = true))]
    #[op(code = "b7be", fmt = "QGEQ", args(mode = 0x778, quiet = true))]
    #[op(code = "b7bf", fmt = "QCMP", args(mode = 0x987, quiet = true))]
    fn exec_cmp(st: &mut VmState, mode: i32, quiet: bool) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let y = ok!(stack.pop_int_or_nan());
        let x = ok!(stack.pop_int_or_nan());

        match (x, y) {
            (Some(x), Some(y)) => {
                ok!(stack.push_int(check_cmp(x.cmp(&y), mode)));
            }
            _ if quiet => ok!(stack.push_nan()),
            _ => vm_bail!(IntegerOverflow),
        }

        Ok(0)
    }

    #[op(code = "c0yy", fmt = "EQINT {y}", args(y = args as i8, mode = 0x878, quiet = false))]
    #[op(code = "c1yy", fmt = "LESSINT {y}", args(y = args as i8, mode = 0x887, quiet = false))]
    #[op(code = "c2yy", fmt = "GTINT {y}", args(y = args as i8, mode = 0x788, quiet = false))]
    #[op(code = "c3yy", fmt = "NEQINT {y}", args(y = args as i8, mode = 0x787, quiet = false))]
    #[op(code = "b7c0yy", fmt = "QEQINT {y}", args(y = args as i8, mode = 0x878, quiet = true))]
    #[op(code = "b7c1yy", fmt = "QLESSINT {y}", args(y = args as i8, mode = 0x887, quiet = true))]
    #[op(code = "b7c2yy", fmt = "QGTINT {y}", args(y = args as i8, mode = 0x788, quiet = true))]
    #[op(code = "b7c3yy", fmt = "QNEQINT {y}", args(y = args as i8, mode = 0x787, quiet = true))]
    fn exec_cmp_int(st: &mut VmState, y: i8, mode: i32, quiet: bool) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        match ok!(stack.pop_int_or_nan()) {
            Some(x) => {
                ok!(stack.push_int(check_cmp(as_truncated_i64(&x).cmp(&(y as i64)), mode)));
            }
            _ if quiet => ok!(stack.push_nan()),
            _ => vm_bail!(IntegerOverflow),
        }

        Ok(0)
    }

    #[op(code = "c4", fmt = "ISNAN")]
    fn exec_is_nan(st: &mut VmState) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let x = ok!(stack.pop_int_or_nan());
        ok!(stack.push_bool(x.is_none()));
        Ok(0)
    }

    #[op(code = "c5", fmt = "CHKNAN")]
    fn exec_chk_nan(st: &mut VmState) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let int = ok!(stack.pop_int());
        ok!(stack.push_raw(int));
        Ok(0)
    }
}

/// Casts to i64 truncating the value to `i64::MIN..=i64::MAX` bounds.
fn as_truncated_i64(x: &BigInt) -> i64 {
    match x.to_i64() {
        Some(x) => x,
        None => match x.sign() {
            Sign::Minus => i64::MIN,
            Sign::NoSign => 0,
            Sign::Plus => i64::MAX,
        },
    }
}

/// `mode` contains a packed expression result, `cmp` selects the hex digit
/// and expression `(7..=9) - 8` gives values in range `-1..=1`.
const fn check_cmp(cmp: Ordering, mode: i32) -> i32 {
    ((mode >> (4 + cmp as i8 * 4)) & 15) - 8
}

#[cfg(test)]
mod tests {
    use tracing_test::traced_test;

    #[test]
    #[traced_test]
    fn check_sign() {
        assert_run_vm!(
            r#"
            INT -5 SGN
            INT -1123 SGN
            INT -123123123 SGN
            INT 0 SGN
            INT 10 SGN
            INT 123132123123 SGN
            "#,
            [] => [int -1, int -1, int -1, int 0, int 1, int 1],
        );

        // NaN
        assert_run_vm!("PUSHNAN SGN", [] => [int 0], exit_code: 4);
        assert_run_vm!("PUSHNAN QSGN", [] => [nan]);
    }

    #[test]
    #[traced_test]
    fn check_nan() {
        assert_run_vm!("INT 0 ISNAN INT 123 ISNAN PUSHNAN ISNAN", [] => [int 0, int 0, int -1]);
        assert_run_vm!("INT 123 CHKNAN INT 0 CHKNAN", [] => [int 123, int 0]);
        assert_run_vm!("PUSHNAN CHKNAN", [] => [int 0], exit_code: 4);
    }

    #[test]
    #[traced_test]
    fn cmp_works() {
        assert_run_vm!(
            r#"
            INT 0 INT 0 LESS
            INT 0 INT 0 EQUAL
            INT 0 INT 0 LEQ
            INT 0 INT 0 GREATER
            INT 0 INT 0 NEQ
            INT 0 INT 0 GEQ
            INT 0 INT 0 CMP
            "#,
            [] => [int 0, int -1, int -1, int 0, int 0, int -1, int 0]
        );

        assert_run_vm!(
            r#"
            INT 123123 INT 0 LESS
            INT 123123 INT 0 EQUAL
            INT 123123 INT 0 LEQ
            INT 123123 INT 0 GREATER
            INT 123123 INT 0 NEQ
            INT 123123 INT 0 GEQ
            INT 123123 INT 0 CMP
            "#,
            [] => [int 0, int 0, int 0, int -1, int -1, int -1, int 1]
        );

        assert_run_vm!(
            r#"
            INT -1 INT 123 LESS
            INT -1 INT 123 EQUAL
            INT -1 INT 123 LEQ
            INT -1 INT 123 GREATER
            INT -1 INT 123 NEQ
            INT -1 INT 123 GEQ
            INT -1 INT 123 CMP
            "#,
            [] => [int -1, int 0, int -1, int 0, int -1, int 0, int -1]
        );

        // NaN
        assert_run_vm!("INT 123 PUSHNAN CMP", [] => [int 0], exit_code: 4);
        assert_run_vm!("PUSHNAN INT 123 CMP", [] => [int 0], exit_code: 4);

        assert_run_vm!("INT 1 INT 2 QCMP", [] => [int -1]);
        assert_run_vm!("INT 123 PUSHNAN QCMP", [] => [nan]);
        assert_run_vm!("PUSHNAN INT 123 QCMP", [] => [nan]);
    }

    #[test]
    #[traced_test]
    fn cmp_int_works() {
        assert_run_vm!(
            r#"
            INT 0 EQINT 0
            INT 0 LESSINT 0
            INT 0 GTINT 0
            INT 0 NEQINT 0
            "#,
            [] => [int -1, int 0, int 0, int 0],
        );

        assert_run_vm!(
            r#"
            INT 123 EQINT -123
            INT 123 LESSINT -123
            INT 123 GTINT -123
            INT 123 NEQINT -123
            "#,
            [] => [int 0, int 0, int -1, int -1],
        );

        assert_run_vm!(
            r#"
            INT -123 EQINT -20
            INT -123 LESSINT -20
            INT -123 GTINT -20
            INT -123 NEQINT -20
            "#,
            [] => [int 0, int -1, int 0, int -1],
        );

        // Big numbers
        assert_run_vm!(
            r#"
            PUSHPOW2 100 EQINT -20
            PUSHPOW2 100 LESSINT -20
            PUSHPOW2 100 GTINT -20
            PUSHPOW2 100 NEQINT -20
            "#,
            [] => [int 0, int 0, int -1, int -1],
        );
        assert_run_vm!(
            r#"
            PUSHNEGPOW2 100 EQINT -20
            PUSHNEGPOW2 100 LESSINT -20
            PUSHNEGPOW2 100 GTINT -20
            PUSHNEGPOW2 100 NEQINT -20
            "#,
            [] => [int 0, int -1, int 0, int -1],
        );

        // NaN
        assert_run_vm!("PUSHNAN EQINT 1", [] => [int 0], exit_code: 4);

        assert_run_vm!("INT 2 QEQINT 2", [] => [int -1]);
        assert_run_vm!("PUSHNAN QEQINT 2", [] => [nan]);
    }
}
