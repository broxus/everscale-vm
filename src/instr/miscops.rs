use crate::error::VmResult;
use crate::stack::RcStackValue;
use crate::VmState;
use everscale_types::cell::StorageStat;
use everscale_types::error::Error;
use everscale_vm::stack::StackValueType;
use everscale_vm_proc::vm_module;
use num_bigint::BigInt;
use num_traits::{Signed, ToPrimitive};
use std::rc::Rc;

pub struct Miscops;

#[vm_module]
impl Miscops {
    #[instr(
        code = "f940",
        fmt = "CDATASIZEQ",
        args(is_slice = false, quiet = true)
    )]
    #[instr(
        code = "f941",
        fmt = "CDATASIZE",
        args(is_slice = false, quiet = false)
    )]
    #[instr(code = "f942", fmt = "SDATASIZEQ", args(is_slice = true, quiet = true))]
    #[instr(code = "f943", fmt = "SDATASIZE", args(is_slice = true, quiet = false))]
    pub fn exec_compute_data_size(st: &mut VmState, is_slice: bool, quiet: bool) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let bound: Option<Rc<BigInt>> = ok!(stack.pop_int_or_nan());

        let value: RcStackValue = if is_slice {
            ok!(stack.pop_cs())
        } else {
            ok!(stack.pop_cell())
        };
        let bound = match bound {
            Some(bound) if !bound.is_negative() => Rc::unwrap_or_clone(bound),
            _ => vm_bail!(IntegerOverflow),
        };
        let limit = bound.to_u64().unwrap_or_else(|| (1 << 63) - 1);
        let mut storage = StorageStat::with_limit(limit as usize);

        let ok = if is_slice {
            let Some(slice) = value.as_slice() else {
                vm_bail!(InvalidType {
                    expected: StackValueType::Slice,
                    actual: value.ty()
                })
            };
            let cs = slice.apply()?;
            storage.add_slice(&cs)
        } else {
            let Some(cell) = value.as_cell() else {
                vm_bail!(InvalidType {
                    expected: StackValueType::Slice,
                    actual: value.ty()
                })
            };
            storage.add_cell(cell.as_ref())
        };

        if ok {
            ok!(stack.push_int(storage.stats().cell_count));
            ok!(stack.push_int(storage.stats().bit_count));
            ok!(stack.push_int(0)); //TODO: add refs count to storage??
        } else if !quiet {
            vm_bail!(CellError(Error::CellOverflow));
        }

        if quiet {
            ok!(stack.push_bool(ok))
        }

        Ok(0)
    }
}
