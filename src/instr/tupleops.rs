use std::rc::Rc;

use anyhow::Result;
use everscale_vm_proc::vm_module;
use num_traits::Zero;

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
        let stack = Rc::make_mut(&mut st.stack);
        make_tuple_impl(stack, i as _)
    }

    #[instr(code = "6f1i", fmt = "INDEX {i}")]
    fn exec_tuple_index(st: &mut VmState, i: u32) -> Result<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        tuple_index_impl(stack, i as _)
    }

    #[instr(code = "6f2i", fmt = "UNTUPLE {i}")]
    fn exec_untuple(st: &mut VmState, i: u32) -> Result<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        untuple_impl(stack, i)
    }

    #[instr(code = "6f3i", fmt = "UNPACKFIRST {i}")]
    fn exec_untuple_first(st: &mut VmState, i: u32) -> Result<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        untuple_first_impl(stack, i)
    }

    #[instr(code = "6f4i", fmt = "EXPLODE {i}")]
    fn exec_explode_tuple(st: &mut VmState, i: u32) -> Result<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        explode_tuple_impl(stack, i)
    }

    #[instr(code = "6f5i", fmt = "SETINDEX {i}")]
    fn exec_tuple_set_index(st: &mut VmState, i: u32) -> Result<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        tuple_set_index_impl(stack, i as _)
    }

    #[instr(code = "6f6i", fmt = "INDEXQ {i}")]
    fn exec_tuple_quiet_index(st: &mut VmState, i: u32) -> Result<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        tuple_index_quiet_impl(stack, i as _)
    }

    #[instr(code = "6f7i", fmt = "SETINDEXQ {i}")]
    fn exec_tuple_quiet_set_index(st: &mut VmState, i: u32) -> Result<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        tuple_set_index_quiet_impl(stack, i as _)
    }

    #[instr(code = "6f80", fmt = "TUPLEVAR")]
    fn exec_mktuple_var(st: &mut VmState) -> Result<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let n = ok!(stack.pop_smallint_range(0, 255));
        make_tuple_impl(stack, n as _)
    }

    #[instr(code = "6f81", fmt = "INDEXVAR")]
    fn exec_tuple_index_var(st: &mut VmState) -> Result<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let i = ok!(stack.pop_smallint_range(0, 254));
        tuple_index_impl(stack, i as _)
    }

    #[instr(code = "6f82", fmt = "UNTUPLEVAR")]
    fn exec_untuple_var(st: &mut VmState) -> Result<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let n = ok!(stack.pop_smallint_range(0, 255));
        untuple_impl(stack, n as _)
    }

    #[instr(code = "6f83", fmt = "UNPACKFIRSTVAR")]
    fn exec_untuple_first_var(st: &mut VmState) -> Result<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let n = ok!(stack.pop_smallint_range(0, 255));
        untuple_first_impl(stack, n)
    }

    #[instr(code = "6f84", fmt = "EXPLODEVAR")]
    fn exec_explode_tuple_var(st: &mut VmState) -> Result<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let n = ok!(stack.pop_smallint_range(0, 255));
        explode_tuple_impl(stack, n)
    }

    #[instr(code = "6f85", fmt = "SETINDEXVAR")]
    fn exec_tuple_set_index_var(st: &mut VmState) -> Result<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let i = ok!(stack.pop_smallint_range(0, 254));
        tuple_set_index_impl(stack, i as usize)
    }

    #[instr(code = "6f86", fmt = "INDEXVARQ")]
    fn exec_tuple_quiet_index_var(st: &mut VmState) -> Result<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let i = ok!(stack.pop_smallint_range(0, 254));
        tuple_index_quiet_impl(stack, i as _)
    }

    #[instr(code = "6f87", fmt = "SETINDEXVARQ")]
    fn exec_tuple_quiet_set_index_var(st: &mut VmState) -> Result<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let i = ok!(stack.pop_smallint_range(0, 254));
        tuple_set_index_quiet_impl(stack, i as _)
    }

    #[instr(code = "6f88", fmt = "TLEN")]
    fn exec_tuple_length(st: &mut VmState) -> Result<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let tuple = ok!(stack.pop_tuple_range(0, 255));
        ok!(stack.push_int(tuple.len()));
        Ok(0)
    }

    #[instr(code = "6f89", fmt = "QTLEN")]
    fn exec_tuple_length_quiet(st: &mut VmState) -> Result<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let value = ok!(stack.pop());
        ok!(if let Some(value) = value.as_tuple() {
            stack.push_int(value.len())
        } else {
            stack.push_int(-1)
        });
        Ok(0)
    }

    #[instr(code = "6f8a", fmt = "ISTUPLE")]
    fn exec_is_tuple(st: &mut VmState) -> Result<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let is_tuple = ok!(stack.pop()).is_tuple();
        ok!(stack.push_bool(is_tuple));
        Ok(0)
    }

    #[instr(code = "6f8b", fmt = "LAST")]
    fn exec_tuple_last(st: &mut VmState) -> Result<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let tuple = ok!(stack.pop_tuple_range(1, 255));
        ok!(stack.push_raw(Rc::clone(
            tuple.last().expect("Should not fail due to range check")
        )));
        Ok(0)
    }

    #[instr(code = "6f8c", fmt = "TPUSH")]
    fn exec_tuple_push(st: &mut VmState) -> Result<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let x = ok!(stack.pop());
        let mut tuple = ok!(stack.pop_tuple_range(0, 254));
        Rc::make_mut(&mut tuple).push(x);
        // TODO: consume gas of tuple len
        ok!(stack.push_raw(tuple));
        Ok(0)
    }

    #[instr(code = "6f8d", fmt = "TPOP")]
    fn exec_tuple_pop(st: &mut VmState) -> Result<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let mut tuple = ok!(stack.pop_tuple_range(1, 255));
        let x = Rc::make_mut(&mut tuple)
            .pop()
            .expect("Should not fail due to range check");
        // TODO: consume gas of tuple len
        ok!(stack.push_raw(tuple));
        ok!(stack.push_raw(x));
        Ok(0)
    }

    #[instr(code = "6fa0", fmt = "NULLSWAPIF", args(c = true, d = false))]
    #[instr(code = "6fa1", fmt = "NULLSWAPIFNOT", args(c = false, d = false))]
    #[instr(code = "6fa2", fmt = "NULLROTRIF", args(c = true, d = true))]
    #[instr(code = "6fa3", fmt = "NULLROTRIFNOT", args(c = false, d = true))]
    fn exec_null_swap_if(st: &mut VmState, c: bool, d: bool) -> Result<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let x = ok!(stack.pop_int());
        if !x.is_zero() != c {
            ok!(stack.push_null());
            if d {
                ok!(stack.swap(0, 1));
            }
        }
        ok!(stack.push_raw(x));
        Ok(0)
    }

    #[instr(code = "6fa4", fmt = "NULLSWAPIF2", args(c = true, d = false))]
    #[instr(code = "6fa5", fmt = "NULLSWAPIFNOT2", args(c = false, d = false))]
    #[instr(code = "6fa6", fmt = "NULLROTRIF2", args(c = true, d = true))]
    #[instr(code = "6fa7", fmt = "NULLROTRIFNOT2", args(c = false, d = true))]
    fn exec_null_swap_if2(st: &mut VmState, c: bool, d: bool) -> Result<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let x = ok!(stack.pop_int());
        if !x.is_zero() != c {
            ok!(stack.push_null());
            ok!(stack.push_null());
            if d {
                ok!(stack.swap(0, 2));
            }
        }
        ok!(stack.push_raw(x));
        Ok(0)
    }
}

fn make_tuple_impl(stack: &mut Stack, n: usize) -> Result<i32> {
    let Some(offset) = stack.items.len().checked_sub(n) else {
        anyhow::bail!(VmError::StackUnderflow(n));
    };
    let tuple = Rc::new(stack.items.drain(offset..offset + n).collect::<Vec<_>>());
    // TODO: consume tuple gas
    ok!(stack.push_raw(tuple));
    Ok(0)
}

fn tuple_index_impl(stack: &mut Stack, i: usize) -> Result<i32> {
    let tuple = ok!(stack.pop_tuple_range(0, 255));
    anyhow::ensure!(
        i < tuple.len(),
        VmError::IntegerOutOfRange {
            actual: i.to_string(),
            min: tuple.len(),
            max: tuple.len(),
        }
    );
    ok!(stack.push_raw(tuple[i].clone()));
    Ok(0)
}

fn tuple_index_quiet_impl(stack: &mut Stack, i: usize) -> Result<i32> {
    let value = 'value: {
        let Some(tuple) = ok!(stack.pop_opt_tuple_range(0, 255)) else {
            break 'value None;
        };
        tuple.get(i).cloned()
    };
    ok!(match value {
        None => stack.push_null(),
        Some(value) => stack.push_raw(value),
    });
    Ok(0)
}

fn untuple_impl(stack: &mut Stack, n: u32) -> Result<i32> {
    let tuple = ok!(stack.pop_tuple_range(n, n));
    ok!(do_explode_tuple(stack, tuple, n as _));
    Ok(0)
}

fn untuple_first_impl(stack: &mut Stack, n: u32) -> Result<i32> {
    let tuple = ok!(stack.pop_tuple_range(n, 255));
    ok!(do_explode_tuple(stack, tuple, n as _));
    Ok(0)
}

fn explode_tuple_impl(stack: &mut Stack, n: u32) -> Result<i32> {
    let tuple = ok!(stack.pop_tuple_range(0, n));
    let tuple_len = tuple.len();
    ok!(do_explode_tuple(stack, tuple, tuple_len));
    ok!(stack.push_int(tuple_len));
    Ok(0)
}

fn do_explode_tuple(stack: &mut Stack, tuple: Rc<Vec<RcStackValue>>, n: usize) -> Result<()> {
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

fn tuple_set_index_impl(stack: &mut Stack, i: usize) -> Result<i32> {
    let x = ok!(stack.pop());
    let mut tuple = ok!(stack.pop_tuple_range(0, 255));
    anyhow::ensure!(
        i < tuple.len(),
        VmError::IntegerOutOfRange {
            min: 0,
            max: tuple.len(),
            actual: i.to_string()
        }
    );
    Rc::make_mut(&mut tuple)[i] = x;
    // TODO: consume tuple gas
    ok!(stack.push_raw(tuple));
    Ok(0)
}

fn tuple_set_index_quiet_impl(stack: &mut Stack, i: usize) -> Result<i32> {
    let x = ok!(stack.pop());
    let mut tuple = ok!(stack.pop_opt_tuple_range(0, 255));
    anyhow::ensure!(
        i < 255,
        VmError::IntegerOutOfRange {
            min: 0,
            max: 255,
            actual: i.to_string()
        }
    );

    let _updated_items = match &mut tuple {
        None if x.is_null() => 0,
        None => {
            let mut items = vec![Stack::make_null(); i + 1];
            items[i] = x;
            tuple = Some(Rc::new(items));
            i + 1
        }
        Some(items) if i < items.len() => {
            Rc::make_mut(items)[i] = x;
            items.len()
        }
        Some(_) if x.is_null() => 0,
        Some(items) => {
            let items = Rc::make_mut(items);
            items.resize(i + 1, Stack::make_null());
            items[i] = x;
            i + 1
        }
    };

    // TODO: consume gas of tuple with length `_updated_items``

    ok!(match tuple {
        None => stack.push_null(),
        Some(value) => stack.push_raw(value),
    });

    Ok(0)
}
