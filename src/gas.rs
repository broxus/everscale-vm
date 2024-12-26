use std::hash::BuildHasher;
use std::rc::Rc;
use std::sync::Arc;

use ahash::HashSet;
use everscale_types::cell::{CellParts, LoadMode};
use everscale_types::error::Error;
use everscale_types::models::SimpleLib;
use everscale_types::prelude::*;

use crate::stack::Stack;

/// Initialization params for [`GasConsumer`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct GasParams {
    /// Maximum possible value of the `limit`.
    pub max: u64,
    /// Gas limit for the out-of-gas exception.
    pub limit: u64,
    /// Free gas (e.g. for external messages without any balance).
    pub credit: u64,
}

impl GasParams {
    pub const fn unlimited() -> Self {
        Self {
            max: u64::MAX,
            limit: u64::MAX,
            credit: 0,
        }
    }

    pub const fn getter() -> Self {
        Self {
            max: 1000000,
            limit: 1000000,
            credit: 0,
        }
    }
}

impl Default for GasParams {
    #[inline]
    fn default() -> Self {
        Self::unlimited()
    }
}

/// Library cells resolver.
pub trait LibraryProvider {
    fn find(&self, library_hash: &HashBytes) -> Result<Option<Cell>, Error>;
}

impl<T: LibraryProvider> LibraryProvider for &'_ T {
    fn find(&self, library_hash: &HashBytes) -> Result<Option<Cell>, Error> {
        T::find(self, library_hash)
    }
}

impl<T: LibraryProvider> LibraryProvider for Box<T> {
    fn find(&self, library_hash: &HashBytes) -> Result<Option<Cell>, Error> {
        T::find(self, library_hash)
    }
}

impl<T: LibraryProvider> LibraryProvider for Rc<T> {
    fn find(&self, library_hash: &HashBytes) -> Result<Option<Cell>, Error> {
        T::find(self, library_hash)
    }
}

impl<T: LibraryProvider> LibraryProvider for Arc<T> {
    fn find(&self, library_hash: &HashBytes) -> Result<Option<Cell>, Error> {
        T::find(self, library_hash)
    }
}

/// Empty libraries provider.
#[derive(Default, Debug, Clone, Copy)]
pub struct NoLibraries;

impl LibraryProvider for NoLibraries {
    #[inline]
    fn find(&self, _library_hash: &HashBytes) -> Result<Option<Cell>, Error> {
        Ok(None)
    }
}

impl LibraryProvider for Vec<Dict<HashBytes, SimpleLib>> {
    fn find(&self, library_hash: &HashBytes) -> Result<Option<Cell>, Error> {
        for lib in self {
            match lib.get(library_hash)? {
                Some(lib) => return Ok(Some(lib.root.clone())),
                None => continue,
            }
        }
        Ok(None)
    }
}

impl<S: BuildHasher> LibraryProvider for std::collections::HashMap<HashBytes, SimpleLib, S> {
    fn find(&self, library_hash: &HashBytes) -> Result<Option<Cell>, Error> {
        Ok(self.get(library_hash).map(|lib| lib.root.clone()))
    }
}

/// Gas tracking context.
pub struct GasConsumer {
    /// Maximum possible value of the `limit`.
    pub gas_max: u64,
    /// Gas limit for the out-of-gas exception.
    pub gas_limit: u64,
    /// Free gas (e.g. for external messages without any balance).
    pub gas_credit: u64,
    /// Initial gas to compute the consumed amount.
    pub gas_base: u64,
    /// Remaining gas available.
    pub gas_remaining: u64,

    /// A set of visited cells.
    pub loaded_cells: HashSet<HashBytes>,
    /// Libraries provider.
    pub libraries: Box<dyn LibraryProvider>,

    /// Number of signature checks.
    pub chksign_counter: u64,

    /// Fallback cell context.
    pub empty_context: <Cell as CellFamily>::EmptyCellContext,
}

impl GasConsumer {
    pub const BUILD_CELL_GAS: u64 = 500;
    pub const NEW_CELL_GAS: u64 = 100;
    pub const OLD_CELL_GAS: u64 = 25;

    pub const FREE_STACK_DEPTH: u64 = 32;
    pub const FREE_SIGNATURE_CHECKS: u64 = 10;

    pub const STACK_VALUE_GAS_PRICE: u64 = 1;
    pub const TUPLE_ENTRY_GAS_PRICE: u64 = 1;
    pub const HASH_EXT_ENTRY_GAS_PRICE: u64 = 1;
    pub const CHK_SGN_GAS_PRICE: u64 = 4000;
    pub const IMPLICIT_JMPREF_GAS_PRICE: u64 = 10;
    pub const IMPLICIT_RET_GAS_PRICE: u64 = 5;
    pub const EXCEPTION_GAS_PRICE: u64 = 50;

    pub fn new(params: GasParams) -> Self {
        Self::with_libraries(params, Box::new(NoLibraries))
    }

    pub fn with_libraries(params: GasParams, libraries: Box<dyn LibraryProvider>) -> Self {
        let gas_remaining = params.limit.saturating_add(params.credit);

        Self {
            gas_max: params.max,
            gas_limit: params.limit,
            gas_credit: params.credit,
            gas_base: gas_remaining,
            gas_remaining,
            loaded_cells: Default::default(),
            libraries,
            chksign_counter: 0,
            empty_context: Default::default(),
        }
    }

    pub fn try_consume_exception_gas(&mut self) -> Result<(), Error> {
        self.try_consume(Self::EXCEPTION_GAS_PRICE)
    }

    pub fn try_consume_implicit_jmpref_gas(&mut self) -> Result<(), Error> {
        self.try_consume(Self::IMPLICIT_JMPREF_GAS_PRICE)
    }

    pub fn try_consume_implicit_ret_gas(&mut self) -> Result<(), Error> {
        self.try_consume(Self::IMPLICIT_RET_GAS_PRICE)
    }

    pub fn try_consume_check_signature_gas(&mut self) -> Result<(), Error> {
        self.chksign_counter += 1;
        if self.chksign_counter > Self::FREE_SIGNATURE_CHECKS {
            self.try_consume(Self::CHK_SGN_GAS_PRICE)?;
        }
        Ok(())
    }

    pub fn try_consume_stack_gas(&mut self, stack: Option<&Rc<Stack>>) -> Result<(), Error> {
        if let Some(stack) = stack {
            self.try_consume_stack_depth_gas(stack.depth() as u64)?;
        }
        Ok(())
    }

    pub fn try_consume_tuple_gas(&mut self, tuple_len: u64) -> Result<(), Error> {
        self.try_consume(tuple_len * Self::TUPLE_ENTRY_GAS_PRICE)?;
        Ok(())
    }

    pub fn try_consume_stack_depth_gas(&mut self, depth: u64) -> Result<(), Error> {
        self.try_consume(
            (std::cmp::max(depth, Self::FREE_STACK_DEPTH) - Self::FREE_STACK_DEPTH)
                * Self::STACK_VALUE_GAS_PRICE,
        )
    }

    pub fn try_consume(&mut self, amount: u64) -> Result<(), Error> {
        if let Some(remaining) = self.gas_remaining.checked_sub(amount) {
            self.gas_remaining = remaining;
            Ok(())
        } else {
            Err(Error::Cancelled)
        }
    }

    pub fn gas_consumed(&self) -> u64 {
        self.gas_base - self.gas_remaining
    }

    pub fn set_limit(&mut self, limit: u64) {
        let limit = std::cmp::min(limit, self.gas_max);
        vm_log_trace!(limit, "changing gas limit");

        self.gas_credit = 0;
        self.gas_limit = limit;
        self.set_base(limit);
    }

    fn set_base(&mut self, base: u64) {
        self.gas_remaining += base - self.gas_base;
        self.gas_base = base;
    }

    // TODO: Update gas
    pub fn load_library(&mut self, library_hash: &HashBytes) -> Result<Option<Cell>, Error> {
        self.libraries.find(library_hash)
    }

    fn consume_load_cell(&mut self, cell: &DynCell, mode: LoadMode) -> Result<(), Error> {
        if mode.use_gas() {
            let gas = if self.loaded_cells.insert(*cell.repr_hash()) {
                GasConsumer::NEW_CELL_GAS
            } else {
                GasConsumer::OLD_CELL_GAS
            };
            ok!(self.try_consume(gas));
        }
        Ok(())
    }
}

impl CellContext for GasConsumer {
    fn finalize_cell(&mut self, cell: CellParts<'_>) -> Result<Cell, Error> {
        ok!(self.try_consume(GasConsumer::BUILD_CELL_GAS));
        self.empty_context.finalize_cell(cell)
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
