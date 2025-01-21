use everscale_types::cell::{CellSlice, CellTreeStats, DynCell, HashBytes};
use everscale_types::models::ShardIdent;

pub const fn shift_ceil_price(value: u128) -> u128 {
    let r = value & 0xffff != 0;
    (value >> 16) + r as u128
}

pub const fn is_masterchain(workchain: i32) -> bool {
    workchain == ShardIdent::MASTERCHAIN.workchain()
}

#[derive(Default)]
pub struct ExtStorageStat<'a> {
    visited: ahash::HashMap<&'a HashBytes, u8>,
    limits: CellTreeStats,
    max_merkle_depth: u8,
    cells: u64,
    bits: u64,
}

impl<'a> ExtStorageStat<'a> {
    pub fn compute_for_slice(
        cs: &CellSlice<'a>,
        max_merkle_depth: u8,
        limits: CellTreeStats,
    ) -> Option<CellTreeStats> {
        let mut state = Self {
            visited: ahash::HashMap::default(),
            limits,
            max_merkle_depth,
            cells: 0,
            bits: cs.size_bits() as u64,
        };

        for cell in cs.references() {
            state.add_cell(cell)?;
        }

        Some(CellTreeStats {
            bit_count: state.bits,
            cell_count: state.cells,
        })
    }

    fn add_cell(&mut self, cell: &'a DynCell) -> Option<u8> {
        if let Some(merkle_depth) = self.visited.get(cell.repr_hash()).copied() {
            return Some(merkle_depth);
        }

        self.cells = self.cells.checked_add(1)?;
        self.bits = self.bits.checked_add(cell.bit_len() as u64)?;

        if self.cells > self.limits.cell_count || self.bits > self.limits.bit_count {
            return None;
        }

        let mut max_merkle_depth = 0u8;
        for cell in cell.references() {
            max_merkle_depth = std::cmp::max(self.add_cell(cell)?, max_merkle_depth);
        }
        max_merkle_depth = max_merkle_depth.saturating_add(cell.cell_type().is_merkle() as u8);

        (max_merkle_depth <= self.max_merkle_depth).then_some(max_merkle_depth)
    }
}
