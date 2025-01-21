use std::hash::BuildHasher;
use std::rc::Rc;
use std::sync::Arc;

use ahash::HashSet;
use everscale_types::cell::{CellParts, LoadMode};
use everscale_types::error::Error;
use everscale_types::models::{LibDescr, SimpleLib};
use everscale_types::prelude::*;

use crate::saferc::SafeRc;
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

impl<T1, T2> LibraryProvider for (T1, T2)
where
    T1: LibraryProvider,
    T2: LibraryProvider,
{
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

impl<T1, T2, T3> LibraryProvider for (T1, T2, T3)
where
    T1: LibraryProvider,
    T2: LibraryProvider,
    T3: LibraryProvider,
{
    fn find(&self, library_hash: &HashBytes) -> Result<Option<Cell>, Error> {
        if let res @ Some(_) = ok!(T1::find(&self.0, library_hash)) {
            return Ok(res);
        }
        if let res @ Some(_) = ok!(T2::find(&self.1, library_hash)) {
            return Ok(res);
        }
        T3::find(&self.2, library_hash)
    }

    fn find_ref<'a>(&'a self, library_hash: &HashBytes) -> Result<Option<&'a DynCell>, Error> {
        if let res @ Some(_) = ok!(T1::find_ref(&self.0, library_hash)) {
            return Ok(res);
        }
        if let res @ Some(_) = ok!(T2::find_ref(&self.1, library_hash)) {
            return Ok(res);
        }
        T3::find_ref(&self.2, library_hash)
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

    fn find_ref<'a>(&'a self, _library_hash: &HashBytes) -> Result<Option<&'a DynCell>, Error> {
        Ok(None)
    }
}

impl LibraryProvider for Dict<HashBytes, SimpleLib> {
    fn find(&self, library_hash: &HashBytes) -> Result<Option<Cell>, Error> {
        match self.get(library_hash)? {
            Some(lib) => Ok(Some(lib.root)),
            None => Ok(None),
        }
    }

    fn find_ref<'a>(&'a self, library_hash: &HashBytes) -> Result<Option<&'a DynCell>, Error> {
        match self
            .cast_ref::<HashBytes, SimpleLibRef<'_>>()
            .get(library_hash)?
        {
            Some(lib) => Ok(Some(lib.root)),
            None => Ok(None),
        }
    }
}

impl LibraryProvider for Vec<Dict<HashBytes, SimpleLib>> {
    fn find(&self, library_hash: &HashBytes) -> Result<Option<Cell>, Error> {
        for lib in self {
            match lib.get(library_hash)? {
                Some(lib) => return Ok(Some(lib.root)),
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
                Ok(Self {
                    lib: slice.load_reference()?,
                })
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
        Ok(self.get(library_hash).map(|lib| lib.root.as_ref()))
    }
}

struct SimpleLibRef<'tlb> {
    root: &'tlb DynCell,
}

impl<'a> Load<'a> for SimpleLibRef<'a> {
    fn load_from(slice: &mut CellSlice<'a>) -> Result<Self, Error> {
        slice.load_bit()?;
        Ok(Self {
            root: slice.load_reference()?,
        })
    }
}

impl EquivalentRepr<SimpleLib> for SimpleLibRef<'_> {}

/// Gas tracking context.
pub struct GasConsumer<'l> {
    /// Maximum possible value of the `limit`.
    gas_max: u64,
    /// Gas limit for the out-of-gas exception.
    gas_limit: std::cell::Cell<u64>,
    /// Free gas (e.g. for external messages without any balance).
    gas_credit: std::cell::Cell<u64>,
    /// Initial gas to compute the consumed amount.
    gas_base: std::cell::Cell<u64>,
    /// Remaining gas available.
    gas_remaining: std::cell::Cell<u64>,

    /// A set of visited cells.
    loaded_cells: std::cell::UnsafeCell<HashSet<HashBytes>>,
    /// Libraries provider.
    libraries: &'l dyn LibraryProvider,

    /// Number of signature checks.
    chksign_counter: std::cell::Cell<usize>,

    // Missing library in case of resolving error occured.
    missing_library: std::cell::Cell<Option<HashBytes>>,
}

impl<'l> GasConsumer<'l> {
    pub const BUILD_CELL_GAS: u64 = 500;
    pub const NEW_CELL_GAS: u64 = 100;
    pub const OLD_CELL_GAS: u64 = 25;

    pub const FREE_STACK_DEPTH: usize = 32;
    pub const FREE_SIGNATURE_CHECKS: usize = 10;
    pub const FREE_NESTED_CONT_JUMP: usize = 8;

    pub const STACK_VALUE_GAS_PRICE: u64 = 1;
    pub const TUPLE_ENTRY_GAS_PRICE: u64 = 1;
    pub const HASH_EXT_ENTRY_GAS_PRICE: u64 = 1;
    pub const CHK_SGN_GAS_PRICE: u64 = 4000;
    pub const IMPLICIT_JMPREF_GAS_PRICE: u64 = 10;
    pub const IMPLICIT_RET_GAS_PRICE: u64 = 5;
    pub const EXCEPTION_GAS_PRICE: u64 = 50;

    pub fn new(params: GasParams) -> Self {
        static NO_LIBRARIES: NoLibraries = NoLibraries;

        Self::with_libraries(params, &NO_LIBRARIES)
    }

    pub fn with_libraries(params: GasParams, libraries: &'l dyn LibraryProvider) -> Self {
        let gas_remaining = params.limit.saturating_add(params.credit);

        Self {
            gas_max: params.max,
            gas_limit: std::cell::Cell::new(params.limit),
            gas_credit: std::cell::Cell::new(params.credit),
            gas_base: std::cell::Cell::new(gas_remaining),
            gas_remaining: std::cell::Cell::new(gas_remaining),
            loaded_cells: Default::default(),
            libraries,
            chksign_counter: std::cell::Cell::new(0),
            missing_library: std::cell::Cell::new(None),
        }
    }

    pub fn libraries(&self) -> &'l dyn LibraryProvider {
        self.libraries
    }

    pub fn credit(&self) -> u64 {
        self.gas_credit.get()
    }

    pub fn consumed(&self) -> u64 {
        self.gas_base.get() - self.gas_remaining.get()
    }

    pub fn limit(&self) -> u64 {
        self.gas_limit.get()
    }

    pub fn set_limit(&self, limit: u64) {
        let limit = std::cmp::min(limit, self.gas_max);
        vm_log_trace!(limit, "changing gas limit");

        self.gas_credit.set(0);
        self.gas_limit.set(limit);
        self.set_base(limit);
    }

    fn set_base(&self, base: u64) {
        let base_diff = base - self.gas_base.get();
        self.gas_remaining.set(self.gas_remaining.get() + base_diff);
        self.gas_base.set(base);
    }

    pub fn try_consume_exception_gas(&self) -> Result<(), Error> {
        self.try_consume(Self::EXCEPTION_GAS_PRICE)
    }

    pub fn try_consume_implicit_jmpref_gas(&self) -> Result<(), Error> {
        self.try_consume(Self::IMPLICIT_JMPREF_GAS_PRICE)
    }

    pub fn try_consume_implicit_ret_gas(&self) -> Result<(), Error> {
        self.try_consume(Self::IMPLICIT_RET_GAS_PRICE)
    }

    pub fn try_consume_check_signature_gas(&self) -> Result<(), Error> {
        self.chksign_counter.set(self.chksign_counter.get() + 1);
        if self.chksign_counter.get() > Self::FREE_SIGNATURE_CHECKS {
            self.try_consume(Self::CHK_SGN_GAS_PRICE)?;
        }
        Ok(())
    }

    pub fn try_consume_stack_gas(&self, stack: Option<&SafeRc<Stack>>) -> Result<(), Error> {
        if let Some(stack) = stack {
            self.try_consume_stack_depth_gas(stack.depth())?;
        }
        Ok(())
    }

    pub fn try_consume_tuple_gas(&self, tuple_len: u64) -> Result<(), Error> {
        self.try_consume(tuple_len * Self::TUPLE_ENTRY_GAS_PRICE)?;
        Ok(())
    }

    pub fn try_consume_stack_depth_gas(&self, depth: usize) -> Result<(), Error> {
        self.try_consume(
            (std::cmp::max(depth, Self::FREE_STACK_DEPTH) - Self::FREE_STACK_DEPTH) as u64
                * Self::STACK_VALUE_GAS_PRICE,
        )
    }

    pub fn try_consume(&self, amount: u64) -> Result<(), Error> {
        if let Some(remaining) = self.gas_remaining.get().checked_sub(amount) {
            self.gas_remaining.set(remaining);
            Ok(())
        } else {
            Err(Error::Cancelled)
        }
    }

    pub fn missing_library(&self) -> Option<HashBytes> {
        self.missing_library.get()
    }

    pub fn set_missing_library(&self, hash: &HashBytes) {
        self.missing_library.set(Some(*hash));
    }

    fn load_cell_impl<'s: 'a, 'a, T: LoadLibrary<'a>>(
        &'s self,
        mut cell: T,
        mode: LoadMode,
    ) -> Result<T, Error> {
        let mut library_loaded = false;
        loop {
            if mode.use_gas() {
                // SAFETY: This is the only place where we borrow `loaded_cells` as mut.
                let is_new =
                    unsafe { (*self.loaded_cells.get()).insert(*cell.as_ref().repr_hash()) };

                ok!(self.try_consume(if is_new {
                    GasConsumer::NEW_CELL_GAS
                } else {
                    GasConsumer::OLD_CELL_GAS
                }));
            }

            if !mode.resolve() {
                return Ok(cell);
            }

            match cell.as_ref().cell_type() {
                CellType::Ordinary => return Ok(cell),
                CellType::LibraryReference if !library_loaded => {
                    // Library data structure is enforced by `CellContext::finalize_cell`.
                    debug_assert_eq!(cell.as_ref().bit_len(), 8 + 256);

                    // Find library by hash.
                    let mut library_hash = HashBytes::ZERO;
                    ok!(cell
                        .as_ref()
                        .as_slice_allow_pruned()
                        .get_raw(8, &mut library_hash.0, 256));

                    let Some(library_cell) = ok!(T::load_library(self, &library_hash)) else {
                        self.missing_library.set(Some(library_hash));
                        return Err(Error::CellUnderflow);
                    };

                    cell = library_cell;
                    library_loaded = true;
                }
                _ => return Err(Error::CellUnderflow),
            }
        }
    }
}

impl CellContext for GasConsumer<'_> {
    fn finalize_cell(&self, cell: CellParts<'_>) -> Result<Cell, Error> {
        ok!(self.try_consume(GasConsumer::BUILD_CELL_GAS));
        Cell::empty_context().finalize_cell(cell)
    }

    fn load_cell(&self, cell: Cell, mode: LoadMode) -> Result<Cell, Error> {
        self.load_cell_impl(cell, mode)
    }

    fn load_dyn_cell<'s: 'a, 'a>(
        &'s self,
        cell: &'a DynCell,
        mode: LoadMode,
    ) -> Result<&'a DynCell, Error> {
        self.load_cell_impl(cell, mode)
    }
}

trait LoadLibrary<'a>: AsRef<DynCell> + 'a {
    fn load_library(gas: &'a GasConsumer, library_hash: &HashBytes) -> Result<Option<Self>, Error>
    where
        Self: Sized;
}

impl<'a> LoadLibrary<'a> for &'a DynCell {
    fn load_library(gas: &'a GasConsumer, library_hash: &HashBytes) -> Result<Option<Self>, Error>
    where
        Self: Sized,
    {
        gas.libraries.find_ref(library_hash)
    }
}

impl LoadLibrary<'_> for Cell {
    fn load_library(gas: &'_ GasConsumer, library_hash: &HashBytes) -> Result<Option<Self>, Error>
    where
        Self: Sized,
    {
        gas.libraries.find(library_hash)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn find_lib_dict_ref() {
        let lib1 = Boc::decode(tvmasm!("NOP")).unwrap();
        let lib2 = Boc::decode(tvmasm!("NOP NOP")).unwrap();

        // Dict with SimpleLib
        let mut libraries = vec![
            (*lib1.repr_hash(), SimpleLib {
                public: true,
                root: lib1.clone(),
            }),
            (*lib2.repr_hash(), SimpleLib {
                public: true,
                root: lib2.clone(),
            }),
        ];
        libraries.sort_unstable_by(|(l, _), (r, _)| l.cmp(r));
        let libraries = Dict::<HashBytes, SimpleLib>::try_from_sorted_slice(&libraries).unwrap();

        assert!(libraries.find(&HashBytes::ZERO).unwrap().is_none());
        assert!(libraries.find_ref(&HashBytes::ZERO).unwrap().is_none());

        assert_eq!(
            libraries.find(lib1.repr_hash()).unwrap().unwrap().as_ref(),
            libraries.find_ref(lib1.repr_hash()).unwrap().unwrap()
        );
        assert_eq!(
            libraries.find(lib2.repr_hash()).unwrap().unwrap().as_ref(),
            libraries.find_ref(lib2.repr_hash()).unwrap().unwrap()
        );

        // Dict with LibDescr
        let mut publishers = Dict::new();
        publishers.add(HashBytes::ZERO, ()).unwrap();

        {
            let lib = LibDescr {
                lib: lib1.clone(),
                publishers: publishers.clone(),
            };
            let c = CellBuilder::build_from(&lib).unwrap();
            let parsed = c.parse::<LibDescr>().unwrap();

            assert_eq!(lib, parsed);
        }

        let mut libraries = vec![
            (*lib1.repr_hash(), LibDescr {
                lib: lib1.clone(),
                publishers: publishers.clone(),
            }),
            (*lib2.repr_hash(), LibDescr {
                lib: lib2.clone(),
                publishers,
            }),
        ];
        libraries.sort_unstable_by(|(l, _), (r, _)| l.cmp(r));

        let libraries = Dict::<HashBytes, LibDescr>::try_from_sorted_slice(&libraries).unwrap();

        assert!(libraries.find(&HashBytes::ZERO).unwrap().is_none());
        assert!(libraries.find_ref(&HashBytes::ZERO).unwrap().is_none());

        assert_eq!(
            libraries.find(lib1.repr_hash()).unwrap().unwrap().as_ref(),
            libraries.find_ref(lib1.repr_hash()).unwrap().unwrap()
        );
        assert_eq!(
            libraries.find(lib2.repr_hash()).unwrap().unwrap().as_ref(),
            libraries.find_ref(lib2.repr_hash()).unwrap().unwrap()
        );
    }
}
