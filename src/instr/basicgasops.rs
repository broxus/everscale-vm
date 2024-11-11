use crate::cont::QuitCont;
use crate::error::VmResult;
use crate::VmState;
use everscale_vm_proc::vm_module;
use num_bigint::BigInt;
use num_traits::{Signed, ToPrimitive};
use std::rc::Rc;

pub struct BasicGasOps;

#[vm_module]
impl BasicGasOps {
    const MAX_GAS_LIMIT: u64 = (1u64 << 63) - 1;

    #[instr(code = "f800", fmt = "ACCEPT")]
    fn exec_accept(st: &mut VmState) -> VmResult<i32> {
        exec_set_gas(st, MAX_GAS_LIMIT)
    }

    fn exec_set_gas(st: &mut VmState, gas_limit: u64) -> VmResult<i32> {
        if gas_limit < st.gas.gas_consumed() {
            vm_bail!(OutOfGas)
        }
        st.gas.set_limit(gas_limit);

        //TODO: should check if we stop on accept message
        if false {
            return st.jump(Rc::new(QuitCont { exit_code: 0 }));
        }

        Ok(0)
    }

    #[instr(code = "f801", fmt = "SETGASLIMIT")]
    fn exec_set_gas_limit(st: &mut VmState) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let g: Rc<BigInt> = ok!(stack.pop_int());
        let limit = if g.is_positive() {
            g.to_u64().unwrap_or(MAX_GAS_LIMIT)
        } else {
            0u64
        };

        exec_set_gas(st, limit)
    }

    //TODO: require version?
    #[instr(code = "f807", fmt = "GASCONSUMED")]
    fn exec_gas_consumed(st: &mut VmState) -> VmResult<i32> {
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
