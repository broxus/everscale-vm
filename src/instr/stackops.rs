use std::rc::Rc;

use anyhow::Result;
use everscale_vm_proc::vm_module;

use crate::dispatch::Opcodes;
use crate::error::VmError;
use crate::state::VmState;

pub struct Stackops;

#[vm_module]
impl Stackops {
    #[instr(code = "00", fmt = "NOP")]
    fn exec_nop(_: &mut VmState) -> Result<i32> {
        Ok(0)
    }

    #[instr(code = "01", fmt = "SWAP")]
    fn exec_swap(st: &mut VmState) -> Result<i32> {
        ok!(Rc::make_mut(&mut st.stack).swap(0, 1));
        Ok(0)
    }

    #[instr(code = "0i", range_from = "02", fmt = "XCHG s{i}")]
    #[instr(code = "11ii", fmt = "XCHG s{i}")]
    fn exec_xchg0(st: &mut VmState, i: u32) -> Result<i32> {
        ok!(Rc::make_mut(&mut st.stack).swap(0, i as _));
        Ok(0)
    }

    #[instr(code = "10ij", fmt = "XCHG s{i},s{j}")]
    fn exec_xchg(st: &mut VmState, i: u32, j: u32) -> Result<i32> {
        anyhow::ensure!(i != 0 && i < j, VmError::InvalidOpcode);
        ok!(Rc::make_mut(&mut st.stack).swap(i as _, j as _));
        Ok(0)
    }

    #[instr(code = "1i", range_from = "12", fmt = "XCHG s1,s{i}")]
    fn exec_xchg1(st: &mut VmState, x: u32) -> Result<i32> {
        debug_assert!(x >= 2); // opcode range must cover this (0x12..0x20)
        ok!(Rc::make_mut(&mut st.stack).swap(1, x as _));
        Ok(0)
    }
}

#[rustfmt::skip]
pub fn register_stack_ops(t: &mut Opcodes) -> Result<()> {
    t.add_fixed_range(0x12, 0x20, 8, 4, dump_fn!("XCHG s1," @s), exec_xchg1)?;
    t.add_simple(0x20, 8, "DUP", exec_dup)?;
    t.add_simple(0x21, 8, "OVER", exec_over)?;
    t.add_fixed_range(0x22, 0x30, 8, 4, dump_fn!("PUSH " @s), exec_push)?;
    t.add_simple(0x30, 8, "DROP", exec_drop)?;
    t.add_simple(0x31, 8, "NIP", exec_nip)?;
    t.add_fixed_range(0x32, 0x40, 8, 4, dump_fn!("POP " @s), exec_pop)?;
    t.add_fixed(0x4, 4, 12, dump_fn!("XCHG3 " @s @s @s), exec_xchg3)?;
    t.add_fixed(0x50, 8, 8, dump_fn!("XCHG2 " @s @s), exec_xchg2)?;
    t.add_fixed(0x51, 8, 8, dump_fn!("XCPU " @s @s), exec_xcpu)?;
    t.add_fixed(0x52, 8, 8, dump_fn!("PUXC " @s @s -1), exec_puxc)?;
    t.add_fixed(0x53, 8, 8, dump_fn!("PUSH2 " @s @s), exec_push2)?;
    t.add_fixed(0x540, 12, 12, dump_fn!("XCHG3 " @s @s @s), exec_xchg3)?;
    t.add_fixed(0x541, 12, 12, dump_fn!("XC2PU " @s @s @s), exec_xc2pu)?;
    t.add_fixed(0x542, 12, 12, dump_fn!("XCPUXC " @s @s @s -1), exec_xcpuxc)?;
    t.add_fixed(0x543, 12, 12, dump_fn!("XCPU2 " @s @s @s), exec_xcpu2)?;
    t.add_fixed(0x544, 12, 12, dump_fn!("PUXC2 " @s @s @s -0x11), exec_puxc2)?;
    t.add_fixed(0x545, 12, 12, dump_fn!("PUXCPU " @s @s @s -0x11), exec_puxcpu)?;
    t.add_fixed(0x546, 12, 12, dump_fn!("PU2XC " @s @s @s -0x12), exec_pu2xc)?;
    t.add_fixed(0x547, 12, 12, dump_fn!("PUSH3 " @s @s @s), exec_push3)?;
    t.add_fixed(0x55, 8, 8, dump_fn!("BLKSWAP " @c "," @c +0x11), exec_blkswap)?;
    t.add_fixed(0x56, 8, 8, dump_fn!("PUSH " @sl), exec_push_l)?;
    t.add_fixed(0x57, 8, 8, dump_fn!("POP " @sl), exec_pop_l)?;
    t.add_simple(0x58, 8, "ROT", exec_rot)?;
    t.add_simple(0x59, 8, "ROTREV", exec_rotrev)?;
    t.add_simple(0x5a, 8, "2SWAP", exec_2swap)?;
    t.add_simple(0x5b, 8, "2DROP", exec_2drop)?;
    t.add_simple(0x5c, 8, "2DUP", exec_2dup)?;
    t.add_simple(0x5d, 8, "2OVER", exec_2over)?;


    Ok(())
}

// fn exec_nop(_: &mut VmState) -> Result<i32> {
//     vm_log!("execute NOP");
//     Ok(0)
// }

// fn exec_swap(st: &mut VmState) -> Result<i32> {
//     vm_log!("execute SWAP");
//     ok!(Rc::make_mut(&mut st.stack).swap(0, 1));
//     Ok(0)
// }

// fn exec_xchg0(st: &mut VmState, args: u32) -> Result<i32> {
//     args!(let x = args);
//     vm_log!("execute XCHG s{x}");
//     ok!(Rc::make_mut(&mut st.stack).swap(0, x as _));
//     Ok(0)
// }

// fn exec_xchg(st: &mut VmState, args: u32) -> Result<i32> {
//     args!(let (x, y) = args);
//     anyhow::ensure!(x != 0 && x < y, VmError::InvalidOpcode);
//     vm_log!("execute XCHG s{x},s{y}");
//     ok!(Rc::make_mut(&mut st.stack).swap(x as _, y as _));
//     Ok(0)
// }

fn dump_xchg(args: u32, f: &mut dyn std::fmt::Write) -> Result<()> {
    args!(let (x, y) = args);
    if x != 0 && x < y {
        write!(f, "XCHG s{x},s{y}")?
    }
    Ok(())
}

// fn exec_xchg0_l(st: &mut VmState, args: u32) -> Result<i32> {
//     args!(let x(l) = args);
//     vm_log!("execute XCHG s{x}");
//     ok!(Rc::make_mut(&mut st.stack).swap(0, x as _));
//     Ok(0)
// }

fn exec_dup(st: &mut VmState) -> Result<i32> {
    vm_log!("execute DUP");
    let stack = Rc::make_mut(&mut st.stack);
    ok!(stack.push_raw(ok!(stack.fetch(0))));
    Ok(0)
}

fn exec_over(st: &mut VmState) -> Result<i32> {
    vm_log!("execute OVER");
    let stack = Rc::make_mut(&mut st.stack);
    ok!(stack.push_raw(ok!(stack.fetch(1))));
    Ok(0)
}

fn exec_push(st: &mut VmState, args: u32) -> Result<i32> {
    args!(let x = args);
    vm_log!("execute PUSH s{x}");
    let stack = Rc::make_mut(&mut st.stack);
    ok!(stack.push_raw(ok!(stack.fetch(x as _))));
    Ok(0)
}

fn exec_drop(st: &mut VmState) -> Result<i32> {
    vm_log!("execute DROP");
    ok!(Rc::make_mut(&mut st.stack).pop());
    Ok(0)
}

fn exec_nip(st: &mut VmState) -> Result<i32> {
    vm_log!("execute NIP");
    let stack = Rc::make_mut(&mut st.stack);
    ok!(stack.swap(0, 1));
    ok!(stack.pop());
    Ok(0)
}

fn exec_pop(st: &mut VmState, args: u32) -> Result<i32> {
    args!(let x = args);
    vm_log!("execute POP s{x}");
    let stack = Rc::make_mut(&mut st.stack);
    ok!(stack.swap(0, x as _));
    ok!(stack.pop());
    Ok(0)
}

fn exec_xchg3(st: &mut VmState, args: u32) -> Result<i32> {
    args!(let (x, y, z) = args);
    vm_log!("execute XCHG3 s{x},s{y},s{z}");
    let stack = Rc::make_mut(&mut st.stack);
    ok!(stack.swap(2, x as _));
    ok!(stack.swap(1, y as _));
    ok!(stack.swap(0, z as _));
    Ok(0)
}

fn exec_xchg2(st: &mut VmState, args: u32) -> Result<i32> {
    args!(let (x, y) = args);
    vm_log!("execute XCHG2 s{x},s{y}");
    let stack = Rc::make_mut(&mut st.stack);
    ok!(stack.swap(1, x as _));
    ok!(stack.swap(0, y as _));
    Ok(0)
}

fn exec_xcpu(st: &mut VmState, args: u32) -> Result<i32> {
    args!(let (x, y) = args);
    vm_log!("execute XCPU s{x},s{y}");
    let stack = Rc::make_mut(&mut st.stack);
    ok!(stack.swap(0, x as _));
    ok!(stack.push_raw(ok!(stack.fetch(y as _))));
    Ok(0)
}

fn exec_puxc(st: &mut VmState, args: u32) -> Result<i32> {
    args!(let (x, y) = args);
    vm_log!("execute PUXC s{x},s{}", y - 1);
    let stack = Rc::make_mut(&mut st.stack);
    ok!(stack.push_raw(ok!(stack.fetch(x as _))));
    ok!(stack.swap(0, 1));
    ok!(stack.swap(0, y as _));
    Ok(0)
}

fn exec_push2(st: &mut VmState, args: u32) -> Result<i32> {
    args!(let (x, y) = args);
    vm_log!("execute PUSH2 s{x},s{y}");
    let stack = Rc::make_mut(&mut st.stack);
    ok!(stack.push_raw(ok!(stack.fetch(x as _))));
    ok!(stack.push_raw(ok!(stack.fetch(1 + y as usize))));
    Ok(0)
}

fn exec_xc2pu(st: &mut VmState, args: u32) -> Result<i32> {
    args!(let (x, y, z) = args);
    vm_log!("execute XC2PU s{x},s{y},s{z}");
    let stack = Rc::make_mut(&mut st.stack);
    ok!(stack.swap(1, x as _));
    ok!(stack.swap(0, y as _));
    ok!(stack.push_raw(ok!(stack.fetch(z as _))));
    Ok(0)
}

fn exec_xcpuxc(st: &mut VmState, args: u32) -> Result<i32> {
    args!(let (x, y, z) = args);
    vm_log!("execute XCPUXC s{x},s{y},s{}", z - 1);
    let stack = Rc::make_mut(&mut st.stack);
    ok!(stack.swap(1, x as _));
    ok!(stack.push_raw(ok!(stack.fetch(y as _))));
    ok!(stack.swap(0, 1));
    ok!(stack.swap(0, z as _));
    Ok(0)
}

fn exec_xcpu2(st: &mut VmState, args: u32) -> Result<i32> {
    args!(let (x, y, z) = args);
    vm_log!("execute XCPU2 s{x},s{y},s{z}");
    let stack = Rc::make_mut(&mut st.stack);
    ok!(stack.swap(0, x as _));
    ok!(stack.push_raw(ok!(stack.fetch(y as _))));
    ok!(stack.push_raw(ok!(stack.fetch(1 + z as usize))));
    Ok(0)
}

fn exec_puxc2(st: &mut VmState, args: u32) -> Result<i32> {
    args!(let (x, y, z) = args);
    vm_log!("execute PUXC2 s{x},s{},s{}", y - 1, z - 1);
    let stack = Rc::make_mut(&mut st.stack);
    ok!(stack.push_raw(ok!(stack.fetch(x as _))));
    ok!(stack.swap(2, 0));
    ok!(stack.swap(1, y as _));
    ok!(stack.swap(0, z as _));
    Ok(0)
}

fn exec_puxcpu(st: &mut VmState, args: u32) -> Result<i32> {
    args!(let (x, y, z) = args);
    vm_log!("execute PUXCPU s{x},s{},s{}", y - 1, z - 1);
    let stack = Rc::make_mut(&mut st.stack);
    ok!(stack.push_raw(ok!(stack.fetch(x as _))));
    ok!(stack.swap(0, 1));
    ok!(stack.swap(0, y as _));
    ok!(stack.push_raw(ok!(stack.fetch(z as _))));
    Ok(0)
}

fn exec_pu2xc(st: &mut VmState, args: u32) -> Result<i32> {
    args!(let (x, y, z) = args);
    vm_log!("execute PU2XC s{x},s{},s{}", y - 1, z - 2);
    let stack = Rc::make_mut(&mut st.stack);
    ok!(stack.push_raw(ok!(stack.fetch(x as _))));
    ok!(stack.swap(1, 0));
    ok!(stack.push_raw(ok!(stack.fetch(y as _))));
    ok!(stack.swap(1, 0));
    ok!(stack.swap(0, z as _));
    Ok(0)
}

fn exec_push3(st: &mut VmState, args: u32) -> Result<i32> {
    args!(let (x, y, z) = args);
    vm_log!("execute PUSH3 s{x},s{y},s{z}");
    let stack = Rc::make_mut(&mut st.stack);
    ok!(stack.push_raw(ok!(stack.fetch(x as _))));
    ok!(stack.push_raw(ok!(stack.fetch(1 + y as usize))));
    ok!(stack.push_raw(ok!(stack.fetch(2 + z as usize))));
    Ok(0)
}

fn exec_blkswap(st: &mut VmState, args: u32) -> Result<i32> {
    args!(let (x + 1, y + 1) = args);
    vm_log!("execute BLKSWAP {x},{y}");
    let stack = Rc::make_mut(&mut st.stack);
    ok!(stack.reverse_range((x + y) as _, y as _));
    ok!(stack.reverse_range(0, y as _));
    ok!(stack.reverse_range(0, (x + y) as _));
    Ok(0)
}

fn exec_push_l(st: &mut VmState, args: u32) -> Result<i32> {
    args!(let x(l) = args);
    vm_log!("execute PUSH s{x}");
    let stack = Rc::make_mut(&mut st.stack);
    ok!(stack.push_raw(ok!(stack.fetch(x as _))));
    Ok(0)
}

fn exec_pop_l(st: &mut VmState, args: u32) -> Result<i32> {
    args!(let x(l) = args);
    vm_log!("execute POP s{x}");
    let stack = Rc::make_mut(&mut st.stack);
    ok!(stack.swap(0, x as _));
    ok!(stack.pop());
    Ok(0)
}

fn exec_rot(st: &mut VmState) -> Result<i32> {
    vm_log!("execute ROT");
    let stack = Rc::make_mut(&mut st.stack);
    ok!(stack.swap(1, 2));
    ok!(stack.swap(0, 1));
    Ok(0)
}

fn exec_rotrev(st: &mut VmState) -> Result<i32> {
    vm_log!("execute ROTREV");
    let stack = Rc::make_mut(&mut st.stack);
    ok!(stack.swap(0, 1));
    ok!(stack.swap(1, 2));
    Ok(0)
}

fn exec_2swap(st: &mut VmState) -> Result<i32> {
    vm_log!("execute 2SWAP");
    let stack = Rc::make_mut(&mut st.stack);
    ok!(stack.swap(1, 3));
    ok!(stack.swap(0, 2));
    Ok(0)
}

fn exec_2drop(st: &mut VmState) -> Result<i32> {
    vm_log!("execute 2DROP");
    let stack = Rc::make_mut(&mut st.stack);
    ok!(stack.pop());
    ok!(stack.pop());
    Ok(0)
}

fn exec_2dup(st: &mut VmState) -> Result<i32> {
    vm_log!("execute 2DUP");
    let stack = Rc::make_mut(&mut st.stack);
    ok!(stack.push_raw(ok!(stack.fetch(1))));
    ok!(stack.push_raw(ok!(stack.fetch(1))));
    Ok(0)
}

fn exec_2over(st: &mut VmState) -> Result<i32> {
    vm_log!("execute 2OVER");
    let stack = Rc::make_mut(&mut st.stack);
    ok!(stack.push_raw(ok!(stack.fetch(3))));
    ok!(stack.push_raw(ok!(stack.fetch(3))));
    Ok(0)
}
