use std::rc::Rc;

use ahash::HashSet;
use anyhow::Result;
use everscale_types::cell::*;
use everscale_types::error::Error;

use crate::cont::{ControlRegs, QuitCont, RcCont};
use crate::stack::Stack;

pub struct VmState<'a> {
    pub code: CellSlice<'a>,
    pub stack: Rc<Stack>,
    pub cr: ControlRegs,
    pub commited_state: Option<CommitedState>,
    pub cp: u16,
    pub steps: u64,
    pub quit0: Rc<QuitCont>,
    pub quit1: Rc<QuitCont>,
    pub gas: GasConsumer,
}

impl VmState<'_> {
    pub fn jump(&mut self, cont: RcCont) -> Result<i32> {
        if let Some(cont_data) = cont.get_control_data() {
            if cont_data.stack.is_some() || cont_data.nargs.is_some() {
                todo!()
            }
        }

        cont.jump(self)
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
