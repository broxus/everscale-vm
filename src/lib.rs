#[cfg(test)]
#[macro_use]
extern crate everscale_asm_macros;
extern crate self as tycho_vm;

/// Prevents using `From::from` for plain error conversion.
macro_rules! ok {
    ($e:expr $(,)?) => {
        match $e {
            core::result::Result::Ok(val) => val,
            core::result::Result::Err(err) => return core::result::Result::Err(err),
        }
    };
}

#[cfg(feature = "tracing")]
macro_rules! vm_log_op {
    ($($tt:tt)*) => { $crate::__log_op(format_args!($($tt)*)) };
}

#[cfg(feature = "tracing")]
fn __log_op(args: std::fmt::Arguments<'_>) {
    tracing::trace!("execute {args}");
}

#[cfg(feature = "tracing")]
macro_rules! vm_log_trace {
    ($($tt:tt)*) => { tracing::trace!($($tt)*) };
}

#[cfg(not(feature = "tracing"))]
macro_rules! vm_log_op {
    ($($tt:tt)*) => {{}};
}

#[cfg(not(feature = "tracing"))]
macro_rules! vm_log_trace {
    ($($tt:tt)*) => {{}};
}

macro_rules! vm_ensure {
    ($cond:expr, $($tt:tt)+) => {
        if $crate::__private::not($cond) {
            return Err(Box::new($crate::error::VmError::$($tt)+));
        }
    };
}

macro_rules! vm_bail {
    ($($tt:tt)*) => {
        return Err(Box::new($crate::error::VmError::$($tt)*))
    };
}

/// Tuple builder.
#[macro_export]
macro_rules! tuple {
    ($($tt:tt)*) => {
        $crate::tuple_impl!(@v [] $($tt)*)
    };
}

#[doc(hidden)]
#[macro_export]
macro_rules! tuple_impl {
    (@v [$($values:tt)*] null $(, $($tt:tt)* )?) => {
        $crate::tuple_impl!(@v [$($values)* $crate::Stack::make_null(), ] $($($tt)*)?)
    };

    (@v [$($values:tt)*] nan $(, $($tt:tt)* )?) => {
        $crate::tuple_impl!(@v [$($values)* $crate::Stack::make_nan(), ] $($($tt)*)?)
    };

    (@v [$($values:tt)*] int $value:expr $(, $($tt:tt)* )?) => {
        $crate::tuple_impl!(@v [
            $($values)* $crate::RcStackValue::new_dyn_value(
                $crate::__export::num_bigint::BigInt::from($value)
            ),
        ] $($($tt)*)?)
    };

    (@v [$($values:tt)*] cell $value:expr $(, $($tt:tt)* )?) => {
        $crate::tuple_impl!(@v [
            $($values)* $crate::RcStackValue::new_dyn_value(
                $value
            ),
        ] $($($tt)*)?)
    };

    (@v [$($values:tt)*] slice $value:expr $(, $($tt:tt)* )?) => {
        $crate::tuple_impl!(@v [
            $($values)* $crate::RcStackValue::new_dyn_value(
                $crate::OwnedCellSlice::from($value)
            ),
        ] $($($tt)*)?)
    };

    (@v [$($values:tt)*] [ $($inner:tt)* ] $(, $($tt:tt)* )?) => {
        $crate::tuple_impl!(@v [
            $($values)* $crate::RcStackValue::new_dyn_value(
                $crate::tuple!($($inner)*)
            ),
        ] $($($tt)*)?)
    };

    (@v [$($values:tt)*] raw $value:expr $(, $($tt:tt)* )?) => {
        $crate::tuple_impl!(@v [
            $($values)* $crate::SafeRc::into_dyn_value($value),
        ] $($($tt)*)?)
    };

    (@v [$($values:tt)*] $(,)?) => {
        vec![$($values)*]
    };
}

#[cfg(test)]
#[macro_export]
macro_rules! assert_run_vm {
    (
        $($code:literal),+,
        $(c7: $c7_params:expr,)?
        $(gas: $gas_limit:expr,)?
        [$($origin_stack:tt)*] => [$($expected_stack:tt)*]
        $(, exit_code: $exit_code:literal)?
        $(,)?
    ) => {{
        let (exit_code, vm) = $crate::tests::run_vm_with_stack(
            tvmasm!($($code),+),
            $crate::assert_run_vm!(@c7 $($c7_params)?),
            $crate::tuple![$($origin_stack)*],
            $crate::assert_run_vm!(@gas $($gas_limit)?),
        );
        $crate::assert_run_vm!(@check_exit_code exit_code $($exit_code)?);

        let expected_stack = $crate::tuple![$($expected_stack)*];

        let expected = format!("{}", (&expected_stack as &dyn $crate::stack::StackValue).display_list());
        let actual = format!("{}", (&vm.stack.items as &dyn $crate::stack::StackValue).display_list());
        assert_eq!(actual, expected);

        $crate::tests::compare_stack(&vm.stack.items, &expected_stack);
    }};
    (@check_exit_code $ident:ident) => {
        assert_eq!($ident, 0, "non-zero exit code")
    };
    (@check_exit_code $ident:ident $exit_code:literal) => {
        assert_eq!($ident, $exit_code, "exit code mismatch")
    };
    (@c7) => {
        $crate::tuple![]
    };
    (@c7 $c7_params:expr) => {
        $c7_params
    };
    (@gas) => {
        1000000
    };
    (@gas $gas_limit:expr) => {
        $gas_limit
    };
}

pub use self::cont::{
    AgainCont, ArgContExt, Cont, ControlData, ControlRegs, ExcQuitCont, OrdCont, PushIntCont,
    QuitCont, RcCont, RepeatCont, UntilCont, WhileCont,
};
pub use self::dispatch::{
    DispatchTable, FnExecInstrArg, FnExecInstrFull, FnExecInstrSimple, Opcode, Opcodes,
};
pub use self::error::{VmError, VmException, VmResult};
pub use self::gas::{GasConsumer, GasParams, LibraryProvider, NoLibraries};
pub use self::instr::{codepage, codepage0};
pub use self::saferc::{SafeDelete, SafeRc, SafeRcMakeMut};
pub use self::smc_info::{
    CustomSmcInfo, SmcInfo, SmcInfoBase, SmcInfoTonV4, SmcInfoTonV6, VmVersion,
};
pub use self::stack::{
    NaN, RcStackValue, Stack, StackValue, StackValueType, StaticStackValue, Tuple, TupleExt,
};
pub use self::state::{
    BehaviourModifiers, CommitedState, InitSelectorParams, SaveCr, VmState, VmStateBuilder,
};
pub use self::util::OwnedCellSlice;

mod cont;
mod dispatch;
mod error;
mod gas;
mod instr;
mod saferc;
mod smc_info;
mod stack;
mod state;
mod util;

#[doc(hidden)]
pub mod __export {
    pub use {everscale_types, num_bigint};
}

#[doc(hidden)]
mod __private {
    use self::not::Bool;

    #[doc(hidden)]
    #[inline]
    pub fn not(cond: impl Bool) -> bool {
        cond.not()
    }

    mod not {
        #[doc(hidden)]
        pub trait Bool {
            fn not(self) -> bool;
        }

        impl Bool for bool {
            #[inline]
            fn not(self) -> bool {
                !self
            }
        }

        impl Bool for &bool {
            #[inline]
            fn not(self) -> bool {
                !*self
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use everscale_types::prelude::*;
    use tracing_test::traced_test;

    use super::*;
    use crate::stack::{RcStackValue, Tuple};

    pub fn run_vm_with_stack<I>(
        code: &[u8],
        c7_params: Tuple,
        original_stack: I,
        gas_limit: u64,
    ) -> (i32, VmState)
    where
        I: IntoIterator<Item = RcStackValue>,
    {
        let code = Boc::decode(code).unwrap();
        let mut vm = VmState::builder()
            .with_code(code)
            .with_smc_info(CustomSmcInfo {
                version: VmState::DEFAULT_VERSION,
                c7: SafeRc::new(c7_params),
            })
            .with_debug(TracingOutput::default())
            .with_stack(original_stack)
            .with_gas(GasParams {
                max: u64::MAX,
                limit: gas_limit,
                credit: 0,
            })
            .build();

        let exit_code = !vm.run();

        (exit_code, vm)
    }

    #[track_caller]
    pub fn compare_stack(actual: &Tuple, expected: &Tuple) {
        let cx = &mut Cell::empty_context();

        let actual_stack = {
            let mut b = CellBuilder::new();
            actual.store_as_stack_value(&mut b, cx).unwrap();
            b.build_ext(cx).unwrap()
        };

        let expected_stack = {
            let mut b = CellBuilder::new();
            expected.store_as_stack_value(&mut b, cx).unwrap();
            b.build_ext(cx).unwrap()
        };

        assert_eq!(actual_stack, expected_stack, "stack mismatch");
    }

    #[test]
    #[traced_test]
    fn dispatch_works() {
        let code = Boc::decode(tvmasm!(
            "PUSHINT 0",
            "PUSHINT 1",
            "PUSHINT 2",
            "NOP",
            "PUSHNAN",
            "DEBUG 0",
            "XCHG s0, s3",
            "XCHG s1, s3",
            "PUXC s1, s2",
            "DUP",
            "OVER",
            "PUSH s3",
            "DROP",
            "NIP",
            "POP s3",
            "XCHG3 s1, s2, s3",
            "XCHG2 s1, s2",
            "XCPU s1, s2",
            "PUXC s1, s0",
            "PUSH2 s3, s4",
            "XCHG3 s3, s4, s0",
            "PUXC2 s3, s1, s0",
            "PUSH3 s1, s2, s3",
            "PU2XC s1, s2, s(-2)",
            "BLKSWAP 1, 2",
            "DEBUG 0",
            "DEBUGSTR x{48454c50313233}",
        ))
        .unwrap();

        let mut vm = VmState::builder()
            .with_code(code)
            .with_debug(TracingOutput::default())
            .build();
        let exit_code = !vm.run();
        println!("Exit code: {exit_code}");
    }

    #[derive(Default)]
    pub struct TracingOutput {
        buffer: String,
    }

    impl std::fmt::Write for TracingOutput {
        fn write_str(&mut self, mut s: &str) -> std::fmt::Result {
            while !s.is_empty() {
                match s.split_once('\n') {
                    None => {
                        self.buffer.push_str(s);
                        return Ok(());
                    }
                    Some((prefix, rest)) => {
                        tracing::debug!("{}{prefix}", self.buffer);
                        self.buffer.clear();
                        s = rest;
                    }
                }
            }
            Ok(())
        }
    }
}
