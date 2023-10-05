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
            "te6ccgEBAQEAJgAASHBxcgCD/wMTUhMgISMwMTNBI1ASURJSEVM0Q0VUQyFUcSNVAQ==",
        )
        .unwrap();

        let mut vm = VmState::builder().with_code(code).build().unwrap();
        let exit_code = vm.run();
        println!("Exit code: {exit_code}");
    }
}
