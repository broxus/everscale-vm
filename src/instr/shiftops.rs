use std::ops::{BitOr, Deref};
use std::rc::Rc;
use num_bigint::BigInt;
use everscale_vm_proc::vm_module;
use crate::error::VmResult;
use crate::VmState;


pub struct Shiftops;


#[vm_module]
impl Shiftops {
    #[instr(code = "b1", fmt = "OR", args(quiet = false))]
    #[instr(code = "b7b1", fmt = "QOR", args(quiet = false))]
    fn exec_or(st: &mut VmState, quiet: bool) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let y: Rc<BigInt> = ok!(stack.pop_int());
        let x: Option<Rc<BigInt>> = ok!(stack.pop_int_or_nan());
        match x {
            Some(f) => {
                let result = f.deref().bitor(y.deref());
                ok!(stack.push_int(result));
            }
            _ if quiet => ok!(stack.push_nan()),
            _ => vm_bail!(IntegerOverflow),
        }

        Ok(0)
    }
}