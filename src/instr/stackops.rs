use std::rc::Rc;

use anyhow::Result;
use everscale_types::prelude::*;

use crate::dispatch::Opcodes;
use crate::error::VmError;
use crate::instr::dump::*;
use crate::state::VmState;

pub fn register_stack_ops(cp0: &mut Opcodes) -> Result<()> {
    cp0.add_simple(0x00, 8, "NOP", exec_nop)?;
    cp0.add_simple(0x01, 8, "SWAP", exec_swap)?;
    cp0.add_fixed_range(0x02, 0x10, 8, 4, dump_1sr("XCHG "), Box::new(exec_xchg0))?;
    cp0.add_fixed(0x10, 8, 8, Box::new(dump_xchg), Box::new(exec_xchg))?;
    cp0.add_fixed(0x11, 8, 8, dump_1sr_l("XCHG "), Box::new(exec_xchg0_l))?;
    cp0.add_fixed_range(0x12, 0x20, 8, 4, dump_1sr("XCHG s1,"), Box::new(exec_xchg1))?;
    cp0.add_simple(0x20, 8, "DUP", exec_dup)?;

    Ok(())
}

fn exec_nop(_: &mut VmState) -> Result<i32> {
    vm_log!("execute NOP");
    Ok(0)
}

fn exec_swap(st: &mut VmState) -> Result<i32> {
    vm_log!("execute SWAP");
    ok!(Rc::make_mut(&mut st.stack).swap(0, 1));
    Ok(0)
}

fn exec_xchg0(st: &mut VmState, args: u32) -> Result<i32> {
    let x = args & 0xf;
    vm_log!("execute XCHG s{x}");
    ok!(Rc::make_mut(&mut st.stack).swap(0, x as _));
    Ok(0)
}

fn exec_xchg(st: &mut VmState, args: u32) -> Result<i32> {
    let x = (args >> 4) & 0xf;
    let y = args & 0xf;
    anyhow::ensure!(x != 0 && x < y, VmError::InvalidOpcode);
    vm_log!("execute XCHG s{x},s{y}");
    ok!(Rc::make_mut(&mut st.stack).swap(x as _, y as _));
    Ok(0)
}

fn dump_xchg(_: &mut CellSlice<'_>, args: u32, f: &mut dyn std::fmt::Write) -> Result<()> {
    let x = (args >> 4) & 0xf;
    let y = args & 0xf;
    if x != 0 && x < y {
        write!(f, "XCHG s{x},s{y}")?
    }
    Ok(())
}

fn exec_xchg0_l(st: &mut VmState, args: u32) -> Result<i32> {
    let x = args & 0xff;
    vm_log!("execute XCHG s{x}");
    ok!(Rc::make_mut(&mut st.stack).swap(0, x as _));
    Ok(0)
}

fn exec_xchg1(st: &mut VmState, args: u32) -> Result<i32> {
    let x = args & 0xf;
    debug_assert!(x >= 2); // opcode range must cover this (0x12..0x20)
    vm_log!("execute XCHG s1,s{x}");
    ok!(Rc::make_mut(&mut st.stack).swap(1, x as _));
    Ok(0)
}

fn exec_dup(st: &mut VmState) -> Result<i32> {
    vm_log!("execute DUP");
    let stack = Rc::make_mut(&mut st.stack);
    ok!(stack.push_raw(ok!(stack.fetch(0))));
    Ok(0)
}
