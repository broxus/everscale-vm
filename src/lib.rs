extern crate self as everscale_vm;

#[cfg(test)]
#[macro_use]
extern crate everscale_asm_macros;

/// Prevents using `From::from` for plain error conversion.
macro_rules! ok {
    ($e:expr $(,)?) => {
        match $e {
            core::result::Result::Ok(val) => val,
            core::result::Result::Err(err) => return core::result::Result::Err(err),
        }
    };
}

macro_rules! vm_log {
    ($($tt:tt)*) => {
        #[cfg(feature = "tracing")]
        tracing::trace!($($tt)*)
    };
}

#[macro_export]
macro_rules! stack {
    ($($item_ty:tt $($value:expr)?),*$(,)?) => {
        vec![$(crate::stack!(@v $item_ty $($value)?)),*]
    };
    (@v null) => {
        crate::stack::Stack::make_null()
    };
    (@v nan) => {
        crate::stack::Stack::make_nan()
    };
    (@v int $value:expr) => {
        ::std::rc::Rc::new(num_bigint::BigInt::from($value)) as crate::stack::RcStackValue
    };
}

#[cfg(test)]
#[macro_export]
macro_rules! assert_run_vm {
    (
        $($code:literal),+,
        [$($origin_stack:tt)*] => [$($expected_stack:tt)*]
        $(, exit_code: $exit_code:literal)?
        $(,)?
    ) => {{
        let (exit_code, vm) = crate::tests::run_vm_with_stack(
            tvmasm!($($code),+),
            crate::stack![$($origin_stack)*],
        );
        crate::assert_run_vm!(@check_exit_code exit_code $($exit_code)?);

        let expected_stack = format!("{}", (&crate::stack![$($expected_stack)*] as &dyn crate::stack::StackValue).display_list());
        let vm_stack = format!("{}", (&vm.stack.items as &dyn crate::stack::StackValue).display_list());

        assert_eq!(vm_stack, expected_stack);
    }};
    (@check_exit_code $ident:ident) => {
        assert_eq!($ident, 0, "non-zero exit code")
    };
    (@check_exit_code $ident:ident $exit_code:literal) => {
        assert_eq!($ident, $exit_code, "exit code mismatch")
    };
}

pub use self::state::VmState;

pub mod cont;
pub mod dispatch;
pub mod error;
pub mod instr;
pub mod stack;
pub mod state;
pub mod util;

#[cfg(test)]
mod tests {
    use everscale_types::prelude::*;
    use tracing_test::traced_test;

    use super::*;
    use crate::stack::RcStackValue;

    pub fn run_vm_with_stack<I>(code: &[u8], original_stack: I) -> (i32, VmState)
    where
        I: IntoIterator<Item = RcStackValue>,
    {
        let code = Boc::decode(code).unwrap();
        let mut vm = VmState::builder()
            .with_code(code)
            .with_debug(TracingOutput::default())
            .with_stack(original_stack)
            .build()
            .unwrap();

        let exit_code = !vm.run();
        (exit_code, vm)
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
            .build()
            .unwrap();
        let exit_code = vm.run();
        println!("Exit code: {exit_code}");
    }

    #[derive(Default)]
    struct TracingOutput {
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
