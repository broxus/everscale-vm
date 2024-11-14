use crate::cont::ControlRegs;
use crate::error::VmResult;
use crate::VmState;
use everscale_types::cell::{CellBuilder, HashBytes};
use everscale_types::num::Tokens;
use everscale_types::prelude::{Cell, CellFamily, Store};
use everscale_vm_proc::vm_module;
use num_bigint::BigInt;
use num_traits::ToPrimitive;
use std::fmt::Formatter;
use std::rc::Rc;

pub struct MessageOps;

const OUTPUT_ACTIONS_IDX: usize = 5;
#[vm_module]
impl MessageOps {
    //TODO: add new SENDMSG opcode
    #[instr(code = "fb00", fmt = "SENDRAWMSG")]
    fn exec_send_message_raw(st: &mut VmState) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let f = ok!(stack.pop_smallint_range(0, 255));
        let cell: Rc<Cell> = ok!(stack.pop_cell());

        let mut cb = CellBuilder::new();
        let Some(actions) = st.cr.get_d(OUTPUT_ACTIONS_IDX) else {
            vm_bail!(ControlRegisterOutOfRange(5))
        };
        cb.store_reference(actions)?;
        cb.store_uint(0x0ec3c86d, 32)?;
        cb.store_uint(f as u64, 8)?;
        cb.store_reference(cell.as_ref().clone())?;

        install_output_actions(&mut st.cr, cb.build()?)
    }

    #[instr(code = "fbss", range_from = "fb02", range_to = "fb04", fmt = ("{}", s.display()), args(s = ReserveArgs(args)))]
    fn exec_reserve_raw(st: &mut VmState, s: ReserveArgs) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let f = ok!(stack.pop_smallint_range(0, 15));

        let mut cell: Option<Rc<Cell>> = None;
        if s.is_x() {
            cell = ok!(stack.pop_cell_opt());
        }

        let amount: Rc<BigInt> = ok!(stack.pop_int());
        let Some(uamount) = amount.to_u128() else {
            vm_bail!(IntegerOutOfRange {
                min: 0,
                max: u128::MAX as isize,
                actual: amount.to_string()
            })
        };

        let tokens = Tokens::new(uamount);
        if !tokens.is_valid() {
            vm_bail!(IntegerOutOfRange {
                min: 0,
                max: Tokens::MAX.into_inner() as isize,
                actual: amount.to_string()
            })
        }

        let mut cb = CellBuilder::new();
        let Some(actions) = st.cr.get_d(OUTPUT_ACTIONS_IDX) else {
            vm_bail!(ControlRegisterOutOfRange(5))
        };
        cb.store_reference(actions)?;
        cb.store_uint(0x36e6b809, 32)?;
        cb.store_uint(f as u64, 8)?;
        tokens.store_into(&mut cb, &mut Cell::empty_context())?;
        if let Some(cell) = cell {
            cb.store_bit_one()?;
            cb.store_reference(cell.as_ref().clone())?;
        } else {
            cb.store_bit_zero()?;
        }

        install_output_actions(&mut st.cr, cb.build()?)
    }

    #[instr(code = "fb04", fmt = "SETCODE")]
    fn exec_set_code(st: &mut VmState) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let code = ok!(stack.pop_cell());
        let mut cb = CellBuilder::new();

        let Some(actions) = st.cr.get_d(OUTPUT_ACTIONS_IDX) else {
            vm_bail!(ControlRegisterOutOfRange(5))
        };

        cb.store_reference(actions)?;
        cb.store_uint(0x36e6b809, 32)?;
        cb.store_reference(code.as_ref().clone())?;

        install_output_actions(&mut st.cr, cb.build()?)
    }

    #[instr(code = "fb06", fmt = "SETLIBCODE")]
    fn exec_set_lib_code(st: &mut VmState) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let mode = ok!(stack.pop_smallint_range(0, 2));
        let code = ok!(stack.pop_cell());

        let mut cb = CellBuilder::new();
        let Some(actions) = st.cr.get_d(OUTPUT_ACTIONS_IDX) else {
            vm_bail!(ControlRegisterOutOfRange(5))
        };

        cb.store_reference(actions)?;
        cb.store_uint(0x26fa1dd4, 32)?;
        cb.store_uint((mode * 2 + 1) as u64, 8)?;
        cb.store_reference(code.as_ref().clone())?;

        install_output_actions(&mut st.cr, cb.build()?)
    }

    #[instr(code = "fb07", fmt = "CHANGELIB")]
    fn exec_change_lib(st: &mut VmState) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let mode = ok!(stack.pop_smallint_range(0, 2));
        let hash: Rc<BigInt> = ok!(stack.pop_int());
        let mut hash_bytes = [0u8; 32];
        if hash_bytes.len() < hash.to_bytes_be().1.len() {
            vm_bail!(IntegerOverflow)
        }
        hash_bytes.copy_from_slice(hash.to_bytes_be().1.as_ref());
        let hash_bytes = HashBytes::from(hash_bytes);

        let mut cb = CellBuilder::new();

        let Some(actions) = st.cr.get_d(OUTPUT_ACTIONS_IDX) else {
            vm_bail!(ControlRegisterOutOfRange(5))
        };
        cb.store_reference(actions)?;
        cb.store_uint(0x26fa1dd4, 32)?;
        cb.store_uint((mode * 2) as u64, 8)?;
        cb.store_u256(&hash_bytes)?;
        install_output_actions(&mut st.cr, cb.build()?)
    }
}

pub struct ReserveArgs(u32);
impl ReserveArgs {
    fn is_x(&self) -> bool {
        self.0 & 0b1 != 0
    }

    fn display(&self) -> DisplayReserveArgs {
        DisplayReserveArgs(self.0)
    }
}

pub struct DisplayReserveArgs(u32);
impl std::fmt::Display for DisplayReserveArgs {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let args = ReserveArgs(self.0);
        let is_x = if args.is_x() { "X" } else { "" };
        write!(f, "RAWRESERVE{is_x}")
    }
}
fn install_output_actions(regs: &mut ControlRegs, action_head: Cell) -> VmResult<i32> {
    vm_log!("installing an output action");
    regs.set_d(OUTPUT_ACTIONS_IDX, action_head);
    Ok(0)
}
