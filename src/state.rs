use std::rc::Rc;

use ahash::HashSet;
use anyhow::Result;
use everscale_types::cell::*;
use everscale_types::error::Error;

use crate::cont::{ControlRegs, QuitCont, RcCont};
use crate::error::VmError;
use crate::stack::Stack;
use crate::util::OwnedCellSlice;

pub struct VmState {
    pub code: OwnedCellSlice,
    pub stack: Rc<Stack>,
    pub cr: ControlRegs,
    pub commited_state: Option<CommitedState>,
    pub cp: u16,
    pub steps: u64,
    pub quit0: Rc<QuitCont>,
    pub quit1: Rc<QuitCont>,
    pub gas: GasConsumer,
}

impl VmState {
    pub fn jump(&mut self, cont: RcCont) -> Result<i32> {
        if let Some(cont_data) = cont.get_control_data() {
            if cont_data.stack.is_some() || cont_data.nargs.is_some() {
                return self.jump_ext(cont, None);
            }
        }

        cont.jump(self)
    }

    pub fn jump_ext(&mut self, mut cont: RcCont, pass_args: Option<u16>) -> Result<i32> {
        if let Some(control_data) = cont.get_control_data() {
            let depth = self.stack.items.len();
            anyhow::ensure!(
                pass_args.unwrap_or_default() as usize <= depth
                    && control_data.nargs.unwrap_or_default() as usize <= depth,
                VmError::StackUnderflow(std::cmp::max(
                    pass_args.unwrap_or_default(),
                    control_data.nargs.unwrap_or_default()
                ) as usize)
            );

            if let Some(pass_args) = pass_args {
                anyhow::ensure!(
                    control_data.nargs.unwrap_or_default() <= pass_args,
                    VmError::StackUnderflow(pass_args as usize)
                );
            }

            self.preclear_cr(&control_data.save);

            let copy = control_data.nargs.or(pass_args);

            let cont_stack = match Rc::get_mut(&mut cont) {
                None => cont
                    .get_control_data()
                    .and_then(|control_data| control_data.stack.clone()),
                Some(cont) => cont
                    .get_control_data_mut()
                    .and_then(|control_data| control_data.stack.take()),
            };

            match cont_stack {
                Some(mut cont_stack) if !cont_stack.items.is_empty() => {
                    let copy = copy.unwrap_or(cont_stack.items.len() as u16);
                    // TODO: don't copy `self.stack` here
                    ok!(Rc::make_mut(&mut cont_stack)
                        .move_from_stack(Rc::make_mut(&mut self.stack), copy as usize));
                    // TODO: consume_stack_gas(cont_stack)

                    self.stack = cont_stack;
                }
                _ => {
                    if let Some(copy) = copy {
                        if depth > copy as usize {
                            ok!(Rc::make_mut(&mut self.stack).drop_bottom(depth - copy as usize));
                            // TODO: consume_stack_gas(copy)
                        }
                    }
                }
            }
        } else if let Some(pass_args) = pass_args {
            let depth = self.stack.items.len();
            anyhow::ensure!(
                pass_args as usize <= depth,
                VmError::StackUnderflow(pass_args as usize)
            );
            if depth > pass_args as usize {
                ok!(Rc::make_mut(&mut self.stack).drop_bottom(depth - pass_args as usize));
                // TODO: consume_stack_gas(pass_args)
            }
        }

        cont.jump(self)
    }

    pub fn adjust_cr(&mut self, save: &ControlRegs) {
        self.cr.merge(save)
    }

    pub fn preclear_cr(&mut self, save: &ControlRegs) {
        self.cr.preclear(save)
    }

    pub fn set_c0(&mut self, cont: RcCont) {
        self.cr.c[0] = Some(cont);
    }

    pub fn set_code(&mut self, code: OwnedCellSlice, cp: u16) -> Result<()> {
        self.code = code;
        self.force_cp(cp)
    }

    pub fn force_cp(&mut self, cp: u16) -> Result<()> {
        // TODO: add better CP check and probably update dispatch table
        anyhow::ensure!(cp == 0, VmError::InvalidOpcode);
        Ok(())
    }
}

pub struct CommitedState {
    pub c4: Option<Cell>,
    pub c5: Option<Cell>,
}

pub struct GasConsumer {
    pub gas_max: u64,
    pub gas_limit: u64,
    pub gas_credit: u64,
    pub gas_remaining: u64,
    pub loaded_cells: HashSet<HashBytes>,
    pub empty_context: <Cell as CellFamily>::EmptyCellContext,
}

impl GasConsumer {
    const BUILD_CELL_GAS: u64 = 500;
    const NEW_CELL_GAS: u64 = 100;
    const OLD_CELL_GAS: u64 = 25;

    pub fn try_consume(&mut self, amount: u64) -> Result<(), Error> {
        if let Some(remaining) = self.gas_remaining.checked_sub(amount) {
            self.gas_remaining = remaining;
            Ok(())
        } else {
            Err(Error::Cancelled)
        }
    }

    pub fn context(&mut self) -> GasConsumerContext<'_> {
        GasConsumerContext(self)
    }
}

pub struct GasConsumerContext<'a>(&'a mut GasConsumer);

impl GasConsumerContext<'_> {
    fn consume_load_cell(&mut self, cell: &DynCell, mode: LoadMode) -> Result<(), Error> {
        if mode.use_gas() {
            let gas = if self.0.loaded_cells.insert(*cell.repr_hash()) {
                GasConsumer::NEW_CELL_GAS
            } else {
                GasConsumer::OLD_CELL_GAS
            };
            ok!(self.0.try_consume(gas));
        }
        Ok(())
    }
}

impl CellContext for GasConsumerContext<'_> {
    fn finalize_cell(&mut self, cell: CellParts<'_>) -> Result<Cell, Error> {
        ok!(self.0.try_consume(GasConsumer::BUILD_CELL_GAS));
        self.0.empty_context.finalize_cell(cell)
    }

    fn load_cell(&mut self, cell: Cell, mode: LoadMode) -> Result<Cell, Error> {
        ok!(self.consume_load_cell(cell.as_ref(), mode));
        Ok(cell)
    }

    fn load_dyn_cell<'a>(
        &mut self,
        cell: &'a DynCell,
        mode: LoadMode,
    ) -> Result<&'a DynCell, Error> {
        ok!(self.consume_load_cell(cell, mode));
        Ok(cell)
    }
}
