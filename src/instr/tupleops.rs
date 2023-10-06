use std::rc::Rc;

use anyhow::Result;
use everscale_vm_proc::vm_module;

use crate::error::VmError;
use crate::stack::{RcStackValue, Stack};
use crate::state::VmState;

pub struct Tupleops;

#[vm_module]
impl Tupleops {
    #[instr(code = "6d", fmt = "PUSHNULL")]
    fn exec_push_null(st: &mut VmState) -> Result<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        ok!(stack.push_null());
        Ok(0)
    }

    #[instr(code = "6e", fmt = "ISNULL")]
    fn exec_is_null(st: &mut VmState) -> Result<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let top = ok!(stack.pop());
        ok!(stack.push_bool(top.is_null()));
        Ok(0)
    }

    #[instr(code = "6f0i", fmt = "TUPLE {i}")]
    fn exec_mktuple(st: &mut VmState, i: u32) -> Result<i32> {
        mktuple(st, i as _)
    }

    #[instr(code = "6f1i", fmt = "INDEX {i}")]
    fn exec_tuple_index(st: &mut VmState, i: u32) -> Result<i32> {
        tuple_index(st, i as _)
    }

    #[instr(code = "6f2i", fmt = "UNTUPLE {i}")]
    fn exec_untuple(st: &mut VmState, i: u32) -> Result<i32> {
        untuple(st, i)
    }

    #[instr(code = "6f3i", fmt = "UNPACKFIRST {i}")]
    fn exec_untuple_first(st: &mut VmState, i: u32) -> Result<i32> {
        untuple_first(st, i)
    }

    #[instr(code = "6f4i", fmt = "EXPLODE {i}")]
    fn exec_explode_tuple(st: &mut VmState, i: u32) -> Result<i32> {
        explode_tuple(st, i)
    }

    #[instr(code = "6f5i", fmt = "SETINDEX {i}")]
    fn exec_tuple_set_index(st: &mut VmState, i: u32) -> Result<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        ok!(tuple_set_index_impl(stack, i as _));
        Ok(0)
    }
}

fn mktuple(st: &mut VmState, n: usize) -> Result<i32> {
    let stack = Rc::make_mut(&mut st.stack);
    let Some(offset) = stack.items.len().checked_sub(n) else {
        anyhow::bail!(VmError::StackUnderflow(n));
    };
    let tuple = Rc::new(stack.items.drain(offset..offset + n).collect::<Vec<_>>());
    // TODO: consume tuple gas
    ok!(stack.push_raw(tuple));
    Ok(0)
}

fn tuple_index(st: &mut VmState, n: usize) -> Result<i32> {
    let stack = Rc::make_mut(&mut st.stack);
    let tuple = ok!(stack.pop_tuple_range(0, 255));
    anyhow::ensure!(
        n < tuple.len(),
        VmError::IntegerOutOfRange {
            actual: n.to_string(),
            min: tuple.len(),
            max: tuple.len(),
        }
    );
    ok!(stack.push_raw(tuple[n].clone()));
    Ok(0)
}

fn tuple_index_quiet(st: &mut VmState, n: usize) -> Resu

fn untuple(st: &mut VmState, n: u32) -> Result<i32> {
    let stack = Rc::make_mut(&mut st.stack);
    let tuple = ok!(stack.pop_tuple_range(n, n));
    ok!(explode_tuple_impl(stack, tuple, n as _));
    Ok(0)
}

fn untuple_first(st: &mut VmState, n: u32) -> Result<i32> {
    let stack = Rc::make_mut(&mut st.stack);
    let tuple = ok!(stack.pop_tuple_range(n, 255));
    ok!(explode_tuple_impl(stack, tuple, n as _));
    Ok(0)
}

fn explode_tuple(st: &mut VmState, n: u32) -> Result<i32> {
    let stack = Rc::make_mut(&mut st.stack);
    let tuple = ok!(stack.pop_tuple_range(0, n));
    let tuple_len = tuple.len();
    ok!(explode_tuple_impl(stack, tuple, tuple_len));
    ok!(stack.push_int(tuple_len));
    Ok(0)
}

fn tuple_set_index_impl(stack: &mut Stack, n: usize) -> Result<()> {
    let x = ok!(stack.pop());
    let mut tuple = ok!(stack.pop_tuple_range(0, 255));
    anyhow::ensure!(
        n < tuple.len(),
        VmError::IntegerOutOfRange {
            min: tuple.len(),
            max: tuple.len(),
            actual: n.to_string()
        }
    );
    Rc::make_mut(&mut tuple)[n] = x;
    // TODO: consume tuple gas
    ok!(stack.push_raw(tuple));
    Ok(())
}

fn explode_tuple_impl(stack: &mut Stack, tuple: Rc<Vec<RcStackValue>>, n: usize) -> Result<i32> {
    match Rc::try_unwrap(tuple) {
        Ok(tuple) => {
            for item in tuple.into_iter().take(n) {
                ok!(stack.push_raw(item));
            }
        }
        Err(tuple) => {
            for item in tuple.iter().take(n) {
                ok!(stack.push_raw(item.clone()));
            }
        }
    }
    // TODO: consume tuple gas n
    Ok(())
}
