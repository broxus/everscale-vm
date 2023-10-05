use std::rc::Rc;

use anyhow::Result;
use everscale_vm_proc::vm_module;

use crate::VmState;

pub struct Arithmetic;

#[vm_module]
impl Arithmetic {
    #[instr(code = "7x", fmt = "PUSHINT {x}", args(x = ((args as i32 + 5) & 0xf) - 5))]
    fn exec_push_tinyint4(st: &mut VmState, x: i32) -> Result<i32> {
        ok!(Rc::make_mut(&mut st.stack).push_int(x));
        Ok(0)
    }

    #[instr(code = "83ff", fmt = "PUSHNAN")]
    fn exec_push_nan(st: &mut VmState) -> Result<i32> {
        ok!(Rc::make_mut(&mut st.stack).push_nan());
        Ok(0)
    }
}
