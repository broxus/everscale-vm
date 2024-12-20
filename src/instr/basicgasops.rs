use std::rc::Rc;

use everscale_vm_proc::vm_module;
use num_traits::{Signed, ToPrimitive};

use crate::cont::QuitCont;
use crate::error::VmResult;
use crate::VmState;

pub struct BasicGasOps;

#[vm_module]
impl BasicGasOps {
    #[instr(code = "f800", fmt = "ACCEPT")]
    fn exec_accept(st: &mut VmState) -> VmResult<i32> {
        exec_set_gas(st, u64::MAX)
    }

    #[instr(code = "f801", fmt = "SETGASLIMIT")]
    fn exec_set_gas_limit(st: &mut VmState) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let x = ok!(stack.pop_int());
        let limit = if x.is_positive() {
            x.to_u64().unwrap_or(u64::MAX)
        } else {
            0u64
        };

        exec_set_gas(st, limit)
    }

    #[instr(code = "f807", fmt = "GASCONSUMED")]
    fn exec_gas_consumed(st: &mut VmState) -> VmResult<i32> {
        ok!(st.version.require_ton(4..));

        let stack = Rc::make_mut(&mut st.stack);
        ok!(stack.push_int(st.gas.gas_consumed()));
        Ok(0)
    }

    #[instr(code = "f80f", fmt = "COMMIT")]
    fn exec_commit(st: &mut VmState) -> VmResult<i32> {
        st.force_commit()?;
        Ok(0)
    }
}

fn exec_set_gas(st: &mut VmState, gas_limit: u64) -> VmResult<i32> {
    if gas_limit < st.gas.gas_consumed() {
        vm_bail!(OutOfGas)
    }
    st.gas.set_limit(gas_limit);

    if st.modifiers.stop_on_accept {
        st.jump(Rc::new(QuitCont { exit_code: 0 }))
    } else {
        Ok(0)
    }
}
