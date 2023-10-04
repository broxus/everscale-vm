use std::rc::Rc;

use ahash::HashSet;
use anyhow::Result;
use everscale_types::cell::*;
use everscale_types::error::Error;
use num_bigint::BigInt;
use num_traits::Zero;

use crate::cont::{ControlRegs, OrdCont, QuitCont, RcCont};
use crate::error::{VmError, VmException};
use crate::stack::{RcStackValue, Stack, StackValue};
use crate::util::OwnedCellSlice;

#[derive(Default)]
pub struct VmStateBuilder {
    pub code: OwnedCellSlice,
    pub data: Cell,
    pub stack: Vec<RcStackValue>,
    pub c7: Option<Vec<RcStackValue>>,
}

impl VmStateBuilder {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn build(self) -> Result<VmState> {
        VmState::new(self.code, self.data)
    }

    pub fn with_code<T: Into<OwnedCellSlice>>(mut self, code: T) -> Self {
        self.code = code.into();
        self
    }

    pub fn with_data(mut self, data: Cell) -> Self {
        self.data = data;
        self
    }

    pub fn with_stack<I: IntoIterator<Item = RcStackValue>>(mut self, values: I) -> Self {
        self.stack = values.into_iter().collect();
        self
    }

    pub fn push<T: StackValue + 'static>(mut self, value: T) -> Self {
        self.stack.push(Rc::new(value));
        self
    }

    pub fn push_raw(mut self, value: RcStackValue) -> Self {
        self.stack.push(value);
        self
    }

    pub fn with_c7(mut self, c7: Vec<RcStackValue>) -> Self {
        self.c7 = Some(c7);
        self
    }
}

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
    pub const MAX_DATA_DEPTH: u16 = 512;

    thread_local! {
        static QUIT0: Rc<QuitCont> = Rc::new(QuitCont { exit_code: 0 });
        static QUIT1: Rc<QuitCont> = Rc::new(QuitCont { exit_code: 1 });
    }

    fn new(code: OwnedCellSlice, data: Cell) -> Result<Self> {
        let mut result = Self {
            code,
            stack: Default::default(),
            cr: ControlRegs::default(),
            commited_state: None,
            cp: 0,
            steps: 0,
            quit0: Self::QUIT0.with(Rc::clone),
            quit1: Self::QUIT1.with(Rc::clone),
            gas: Default::default(), // TODO: pass gas limits as argument
        };

        // TODO

        Ok(result)
    }

    pub fn step(&mut self) -> Result<i32> {
        self.steps += 1;
        if !self.code.range().is_data_empty() {
            // TODO: dispatch
            todo!()
        } else if !self.code.range().is_refs_empty() {
            let next_cell = self.code.apply()?.get_reference_cloned(0)?;

            // TODO: consume implicit_jmpref_gas_price
            let code = self
                .gas
                .context()
                .load_cell(next_cell, LoadMode::Full)?
                .into();

            let cont = Rc::new(OrdCont::simple(code, self.cp));
            self.jump(cont)
        } else {
            // TODO: consume implicit_ret_gas_price
            self.ret()
        }
    }

    pub fn run(&mut self) -> i32 {
        loop {
            let res = match self.step() {
                Ok(res) => res,
                Err(e) => {
                    self.steps += 1;
                    match self.throw_exception(VmException::from(&e) as i32) {
                        Ok(res) => res,
                        Err(e) => break VmException::from(&e).as_exit_code(),
                    }
                }
            };

            // TODO: handle out of gas

            if res != 0 {
                // Try commit on ~(0) and ~(-1) exit codes
                if res | 1 == -1 && !self.try_commit() {
                    self.stack = Rc::new(Stack {
                        items: vec![Rc::new(BigInt::default())],
                    });
                    break VmException::CellOverflow.as_exit_code();
                }
                break res;
            }
        }
    }

    pub fn try_commit(&mut self) -> bool {
        if let (Some(c4), Some(c5)) = (&self.cr.d[0], &self.cr.d[1]) {
            if c4.level() == 0
                && c5.level() == 0
                && c4.repr_depth() <= Self::MAX_DATA_DEPTH
                && c5.repr_depth() <= Self::MAX_DATA_DEPTH
            {
                self.commited_state = Some(CommitedState {
                    c4: c4.clone(),
                    c5: c5.clone(),
                });
                return true;
            }
        }
        return false;
    }

    pub fn force_commit(&mut self) -> Result<()> {
        if self.try_commit() {
            Ok(())
        } else {
            anyhow::bail!(Error::CellOverflow)
        }
    }

    pub fn throw_exception(&mut self, n: i32) -> Result<i32> {
        self.stack = Rc::new(Stack {
            items: vec![Rc::new(BigInt::zero()), Rc::new(BigInt::from(n))],
        });
        self.code = Default::default();
        // TODO: try consume exception_gas_price
        let Some(c2) = self.cr.c[2].clone() else {
            anyhow::bail!(VmError::InvalidOpcode);
        };
        self.jump(c2)
    }

    pub fn throw_exception_with_arg(&mut self, n: i32, arg: RcStackValue) -> Result<i32> {
        self.stack = Rc::new(Stack {
            items: vec![arg, Rc::new(BigInt::from(n))],
        });
        self.code = Default::default();
        // TODO: try consume exception_gas_price
        let Some(c2) = self.cr.c[2].clone() else {
            anyhow::bail!(VmError::InvalidOpcode);
        };
        self.jump(c2)
    }

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

    pub fn ret(&mut self) -> Result<i32> {
        let cont = ok!(self.take_c0());
        self.jump(cont)
    }

    pub fn ret_ext(&mut self, ret_args: Option<u16>) -> Result<i32> {
        let cont = ok!(self.take_c0());
        self.jump_ext(cont, ret_args)
    }

    pub fn ret_alt(&mut self) -> Result<i32> {
        let cont = ok!(self.take_c1());
        self.jump(cont)
    }

    pub fn ret_alt_ext(&mut self, ret_args: Option<u16>) -> Result<i32> {
        let cont = ok!(self.take_c1());
        self.jump_ext(cont, ret_args)
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

    fn take_c0(&mut self) -> Result<RcCont> {
        let Some(cont) = std::mem::replace(&mut self.cr.c[0], Some(self.quit0.clone())) else {
            anyhow::bail!(VmError::InvalidOpcode);
        };
        Ok(cont)
    }

    fn take_c1(&mut self) -> Result<RcCont> {
        let Some(cont) = std::mem::replace(&mut self.cr.c[1], Some(self.quit1.clone())) else {
            anyhow::bail!(VmError::InvalidOpcode);
        };
        Ok(cont)
    }
}

pub struct CommitedState {
    pub c4: Cell,
    pub c5: Cell,
}

// TODO: remove default
#[derive(Default)]
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
