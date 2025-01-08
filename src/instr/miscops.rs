use everscale_types::cell::RefsIter;
use everscale_types::error::Error;
use everscale_types::prelude::*;
use everscale_vm::stack::StackValueType;
use everscale_vm_proc::vm_module;
use num_traits::{Signed, ToPrimitive};

use crate::error::VmResult;
use crate::saferc::SafeRc;
use crate::state::VmState;

pub struct Miscops;

#[vm_module]
impl Miscops {
    #[op(code = "f940", fmt = "CDATASIZEQ", args(is_slice = false, q = true))]
    #[op(code = "f941", fmt = "CDATASIZE", args(is_slice = false, q = false))]
    #[op(code = "f942", fmt = "SDATASIZEQ", args(is_slice = true, q = true))]
    #[op(code = "f943", fmt = "SDATASIZE", args(is_slice = true, q = false))]
    pub fn exec_compute_data_size(st: &mut VmState, is_slice: bool, q: bool) -> VmResult<i32> {
        let stack = SafeRc::make_mut(&mut st.stack);
        let bound = ok!(stack.pop_int_or_nan());

        let value = if is_slice {
            ok!(stack.pop_cs()).into_dyn_value()
        } else {
            ok!(stack.pop_cell()).into_dyn_value()
        };
        let bound = match bound {
            Some(bound) if !bound.is_negative() => SafeRc::unwrap_or_clone(bound),
            _ => vm_bail!(IntegerOverflow),
        };
        let limit = bound.to_u64().unwrap_or(u64::MAX);
        let mut storage = StorageStatExt::with_limit(limit);

        let ok = if is_slice {
            let Some(slice) = value.as_cell_slice() else {
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
                    expected: StackValueType::Cell,
                    actual: value.ty()
                })
            };
            storage.add_cell(cell.as_ref())
        };

        if ok {
            ok!(stack.push_int(storage.stats.cell_count));
            ok!(stack.push_int(storage.stats.bit_count));
            ok!(stack.push_int(storage.stats.ref_count));
        } else if !q {
            vm_bail!(CellError(Error::CellOverflow));
        }

        if q {
            ok!(stack.push_bool(ok))
        }

        Ok(0)
    }
}

struct StorageStatExt<'a> {
    visited: ahash::HashSet<&'a HashBytes>,
    stack: Vec<RefsIter<'a>>,
    stats: CellTreeStatsExt,
    limit: u64,
}

impl<'a> StorageStatExt<'a> {
    pub fn with_limit(limit: u64) -> Self {
        Self {
            visited: Default::default(),
            stack: Vec::new(),
            stats: Default::default(),
            limit,
        }
    }

    fn add_cell(&mut self, cell: &'a DynCell) -> bool {
        if !self.visited.insert(cell.repr_hash()) {
            return true;
        }

        let refs = cell.references();

        self.stats.bit_count += cell.bit_len() as u64;
        self.stats.ref_count += refs.len() as u64;
        self.stats.cell_count += 1;

        self.stack.clear();
        self.stack.push(refs);
        self.reduce_stack()
    }

    fn add_slice(&mut self, slice: &CellSlice<'a>) -> bool {
        let refs = slice.references();

        self.stats.bit_count += slice.size_bits() as u64;
        self.stats.ref_count += refs.len() as u64;

        self.stack.clear();
        self.stack.push(refs);
        self.reduce_stack()
    }

    fn reduce_stack(&mut self) -> bool {
        'outer: while let Some(item) = self.stack.last_mut() {
            for cell in item.by_ref() {
                if !self.visited.insert(cell.repr_hash()) {
                    continue;
                }

                if self.stats.cell_count >= self.limit {
                    return false;
                }

                let next = cell.references();
                let ref_count = next.len();

                self.stats.bit_count += cell.bit_len() as u64;
                self.stats.ref_count += ref_count as u64;
                self.stats.cell_count += 1;

                if ref_count > 0 {
                    self.stack.push(next);
                    continue 'outer;
                }
            }

            self.stack.pop();
        }

        true
    }
}

#[derive(Default)]
struct CellTreeStatsExt {
    bit_count: u64,
    ref_count: u64,
    cell_count: u64,
}
