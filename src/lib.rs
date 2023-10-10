extern crate self as everscale_vm;

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

    #[test]
    #[traced_test]
    fn dispatch_works() {
        let code = Boc::decode_base64(
            "te6ccgEBAQEANgAAaHBxcgCD//4AAxNSEyAhIzAxM0EjUBJRElIRUzRDQFRDIVRxI1RhMFUB/gD+9khFTFAxMjM=",
        )
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
