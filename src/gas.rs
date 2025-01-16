use std::hash::BuildHasher;
use std::rc::Rc;
use std::sync::Arc;

use ahash::HashSet;
use everscale_types::cell::{CellParts, LoadMode};
use everscale_types::error::Error;
use everscale_types::error::Error::CellUnderflow;
use everscale_types::models::{LibDescr, SimpleLib};
use everscale_types::prelude::*;

use crate::saferc::SafeRc;
use crate::stack::Stack;
use crate::{OwnedCellSlice, VmVersion};

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

    fn find_ref<'a>(&'a self, library_hash: &HashBytes) -> Result<Option<&'a DynCell>, Error>;
}

impl<T: LibraryProvider> LibraryProvider for &'_ T {
    fn find(&self, library_hash: &HashBytes) -> Result<Option<Cell>, Error> {
        T::find(self, library_hash)
    }

    fn find_ref<'a>(&'a self, library_hash: &HashBytes) -> Result<Option<&'a DynCell>, Error> {
        T::find_ref(self, library_hash)
    }
}

impl<T1: LibraryProvider, T2: LibraryProvider> LibraryProvider for (T1, T2) {
    fn find(&self, library_hash: &HashBytes) -> Result<Option<Cell>, Error> {
        if let res @ Some(_) = ok!(T1::find(&self.0, library_hash)) {
            return Ok(res);
        }
        T2::find(&self.1, library_hash)
    }

    fn find_ref<'a>(&'a self, library_hash: &HashBytes) -> Result<Option<&'a DynCell>, Error> {
        if let res @ Some(_) = ok!(T1::find_ref(&self.0, library_hash)) {
            return Ok(res);
        }
        T2::find_ref(&self.1, library_hash)
    }
}

impl<T: LibraryProvider> LibraryProvider for Box<T> {
    fn find(&self, library_hash: &HashBytes) -> Result<Option<Cell>, Error> {
        T::find(self, library_hash)
    }
    fn find_ref<'a>(&'a self, library_hash: &HashBytes) -> Result<Option<&'a DynCell>, Error> {
        T::find_ref(self, library_hash)
    }
}

impl<T: LibraryProvider> LibraryProvider for Rc<T> {
    fn find(&self, library_hash: &HashBytes) -> Result<Option<Cell>, Error> {
        T::find(self, library_hash)
    }
    fn find_ref<'a>(&'a self, library_hash: &HashBytes) -> Result<Option<&'a DynCell>, Error> {
        T::find_ref(self, library_hash)
    }
}

impl<T: LibraryProvider> LibraryProvider for Arc<T> {
    fn find(&self, library_hash: &HashBytes) -> Result<Option<Cell>, Error> {
        T::find(self, library_hash)
    }

    fn find_ref<'a>(&'a self, library_hash: &HashBytes) -> Result<Option<&'a DynCell>, Error> {
        T::find_ref(self, library_hash)
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

    fn find_ref<'a>(&'a self, library_hash: &HashBytes) -> Result<Option<&'a DynCell>, Error> {
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
    fn find_ref<'a>(&'a self, library_hash: &HashBytes) -> Result<Option<&'a DynCell>, Error> {
        for lib in self {
            match lib
                .cast_ref::<HashBytes, SimpleLibRef<'_>>()
                .get(library_hash)?
            {
                Some(lib) => return Ok(Some(lib.root)),
                None => continue,
            }
        }
        Ok(None)
    }
}

impl LibraryProvider for Dict<HashBytes, LibDescr> {
    fn find(&self, library_hash: &HashBytes) -> Result<Option<Cell>, Error> {
        Ok(self.get(library_hash)?.map(|lib| lib.lib.clone()))
    }

    fn find_ref<'a>(&'a self, library_hash: &HashBytes) -> Result<Option<&'a DynCell>, Error> {

        struct LibDescrRef<'tlb> {
            lib: &'tlb DynCell,
        }

        impl<'a> Load<'a> for LibDescrRef<'a> {
            fn load_from(slice: &mut CellSlice<'a>) -> Result<Self, Error> {
                if slice.load_small_uint(2)? != 0 {
                    return Err(Error::InvalidTag);
                }
                Ok(Self {lib: slice.load_reference()?})
            }
        }

        impl EquivalentRepr<LibDescr> for LibDescrRef<'_> {}

        Ok(self
            .cast_ref::<HashBytes, LibDescrRef<'a>>()
            .get(library_hash)?
            .map(|lib| lib.lib))
    }
}

impl<S: BuildHasher> LibraryProvider for std::collections::HashMap<HashBytes, SimpleLib, S> {
    fn find(&self, library_hash: &HashBytes) -> Result<Option<Cell>, Error> {
        Ok(self.get(library_hash).map(|lib| lib.root.clone()))
    }

    fn find_ref<'a>(&'a self, library_hash: &HashBytes) -> Result<Option<&'a DynCell>, Error> {
        Ok(self
            .get(library_hash)
            .map(|lib| lib.root.as_ref()))
    }
}

struct SimpleLibRef<'tlb> {
    root: &'tlb DynCell,
}

impl<'a> Load<'a> for SimpleLibRef<'a> {
    fn load_from(slice: &mut CellSlice<'a>) -> Result<Self, Error> {
        slice.load_bit()?;
        Ok(Self { root: slice.load_reference()? })
    }
}

impl EquivalentRepr<SimpleLib> for SimpleLibRef<'_> {}

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

    vm_version: VmVersion,
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

    pub fn new(params: GasParams, vm_version: VmVersion) -> Self {
        Self::with_libraries(params, Box::new(NoLibraries), vm_version)
    }

    pub fn with_libraries(
        params: GasParams,
        libraries: Box<dyn LibraryProvider>,
        vm_version: VmVersion,
    ) -> Self {
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
            vm_version,
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

    pub fn try_consume_stack_gas(&mut self, stack: Option<&SafeRc<Stack>>) -> Result<(), Error> {
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

    pub fn load_library_ref<'a>(&'a mut self, library_hash: &HashBytes) -> Result<Option<&'a DynCell>, Error> {
        self.libraries.find_ref(library_hash)
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


    // fn consume_load_impl_cell<'a>(&mut self, cell: Cell, load_mode: LoadMode) -> Result<Cell, Error> {
    //     self.consume_load_cell(cell.as_ref(), load_mode)?;
    //
    //     if matches!(cell.cell_type(), CellType::PrunedBranch) {
    //         // check virtualizaion and throw an exception if needed
    //     }
    //
    //     if !load_mode.resolve() {
    //         return Ok(cell);
    //     }
    //
    //     match cell.cell_type() {
    //         CellType::LibraryReference => {
    //             if cell.bit_len() != 8 + 256 {
    //                 return Err(CellUnderflow);
    //             }
    //
    //             let library_cell = self.load_library(cell.repr_hash())?;
    //             if let Some(library) = library_cell {
    //                 if matches!(library.cell_type(), CellType::LibraryReference) {
    //                     return Err(CellUnderflow);
    //                 }
    //                 Ok(library)
    //             } else {
    //                 Err(CellUnderflow)
    //             }
    //         }
    //         CellType::PrunedBranch => {
    //             // TODO: check virtualizaion and throw an exception if needed
    //             Ok(cell)
    //         }
    //         _ => Err(CellUnderflow),
    //     }
    // }


    fn consume_load_dyn_cell<'a>(
        &'a mut self,
        container: CellContainer<'a>,
        load_mode: LoadMode,
    ) -> Result<CellContainer<'a>, Error> {
        self.consume_load_cell(container.as_dyn(), load_mode)?;

        if matches!(container.cell_type(), CellType::PrunedBranch) {
            // check virtualizaion and throw an exception if needed
        }

        if !load_mode.resolve() {
            return Ok(container);
        }

        match container.cell_type() {
            CellType::LibraryReference => {
                if container.bit_len() != 8 + 256 {
                    return Err(CellUnderflow);
                }

                let library_cell= if container.is_cell() {
                    self.load_library(container.repr_hash())?.map(CellContainer::OwnedCell)
                } else {
                    self.load_library_ref(container.repr_hash())?.map(CellContainer::RefCell)
                };

                if let Some(library) = library_cell {
                    if matches!(library.cell_type(), CellType::LibraryReference) {
                        return Err(CellUnderflow);
                    }
                    Ok(library)
                } else {
                    Err(CellUnderflow)
                }
            }
            CellType::PrunedBranch => {
                // TODO: check virtualizaion and throw an exception if needed
                Ok(container)
            }
            _ => Err(CellUnderflow),
        }
    }
}

// trait CellContainer<'a> {
//     fn is_cell(&self) -> bool;
//     fn as_dyn(&self) -> &'a DynCell;
//     fn to_cell(self) -> Result<Cell, Error>;
//     fn repr_hash(&self) -> &HashBytes;
//     fn bit_len(&self) -> u16;
//     fn cell_type(&self) -> CellType;
// }

enum CellContainer<'a> {
    OwnedCell(Cell),
    RefCell(&'a DynCell),
}

impl<'a> CellContainer<'a> {
    fn is_cell(&self) -> bool {
        match self {
            CellContainer::OwnedCell(_) => true,
            CellContainer::RefCell(_) => false,
        }
    }

    fn as_dyn(&'a self) -> &'a DynCell {
        match self {
            CellContainer::OwnedCell(cell) => cell.as_ref(),
            CellContainer::RefCell(r) => *r,
        }
    }

    fn to_cell(self) -> Result<Cell, Error> {
        match self {
            CellContainer::OwnedCell(cell) => Ok(cell),
            CellContainer::RefCell(r) => Err(CellUnderflow),
        }
    }

    fn repr_hash(&self) -> &HashBytes {
        match self {
            CellContainer::OwnedCell(cell) => cell.repr_hash(),
            CellContainer::RefCell(r) => r.repr_hash(),
        }
    }

    fn bit_len(&self) -> u16 {
        match self {
            CellContainer::OwnedCell(cell) => cell.bit_len(),
            CellContainer::RefCell(r) => r.bit_len(),
        }
    }

    fn cell_type(&self) -> CellType {
        match self {
            CellContainer::OwnedCell(cell) => cell.cell_type(),
            CellContainer::RefCell(r) => r.cell_type(),
        }
    }
}

// impl CellContainer for Cell {
//     fn is_cell(&self) -> bool {true}
//     fn as_dyn(&self) -> &DynCell {
//         self.as_ref()
//     }
//     fn to_cell(self) -> Result<Cell, Error> { Ok(self) }
//     fn repr_hash(&self) -> &HashBytes { self.repr_hash() }
//     fn bit_len(&self) -> u16 { self.bit_len() }
//     fn cell_type(&self) -> CellType { self.cell_type() }
// }
//
// impl CellContainer for &DynCell {
//     fn is_cell(&self) -> bool {false}
//     fn as_dyn(&self) -> &DynCell {&self}
//
//     fn to_cell(self) -> Result<Cell, Error> { Err(CellUnderflow) }
//     fn repr_hash(&self) -> &HashBytes { self.repr_hash() }
//     fn bit_len(&self) -> u16 { self.bit_len() }
//     fn cell_type(&self) -> CellType { self.cell_type() }
// }

impl CellContext for GasConsumer {
    fn finalize_cell(&mut self, cell: CellParts<'_>) -> Result<Cell, Error> {
        ok!(self.try_consume(GasConsumer::BUILD_CELL_GAS));
        self.empty_context.finalize_cell(cell)
    }

    fn load_cell(&mut self, cell: Cell, mode: LoadMode) -> Result<Cell, Error> {
        let container = self.consume_load_dyn_cell(CellContainer::OwnedCell(cell), mode)?;
        container.to_cell()
    }

    fn load_dyn_cell<'a>(
        &mut self,
        cell: &'a DynCell,
        mode: LoadMode,
    ) -> Result<&'a DynCell, Error> {
        let container = self.consume_load_dyn_cell(CellContainer::RefCell(cell), mode)?;
        Ok(container.as_dyn())
    }
}
