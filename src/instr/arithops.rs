use std::rc::Rc;

use anyhow::Result;
use everscale_types::prelude::*;

use crate::dispatch::Opcodes;
use crate::VmState;

pub fn register_arith_ops(cp0: &mut Opcodes) -> Result<()> {
    register_int_const_ops(cp0)
}

#[rustfmt::skip]
fn register_int_const_ops(cp0: &mut Opcodes) -> Result<()> {
    cp0.add_fixed(0x7, 4, 4, Box::new(dump_push_tinyint4), Box::new(exec_push_tinyint4))?;

    cp0.add_simple(0x83ff, 16, "PUSHNAN", exec_push_nan)?;

    Ok(())
}

fn exec_push_tinyint4(st: &mut VmState, args: u32) -> Result<i32> {
    let x = ((args as i32 + 5) & 0xf) - 5;
    vm_log!("execute PUSHINT {x}");
    ok!(Rc::make_mut(&mut st.stack).push_int(x));
    Ok(0)
}

fn dump_push_tinyint4(_: &mut CellSlice<'_>, args: u32, f: &mut dyn std::fmt::Write) -> Result<()> {
    let x = ((args as i32 + 5) & 0xf) - 5;
    write!(f, "PUSHINT {x}")?;
    Ok(())
}

fn exec_push_nan(st: &mut VmState) -> Result<i32> {
    vm_log!("execute PUSHNAN");
    ok!(Rc::make_mut(&mut st.stack).push_nan());
    Ok(0)
}
