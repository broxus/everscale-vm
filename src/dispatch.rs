use std::collections::BTreeMap;

use anyhow::Result;
use everscale_types::prelude::*;

use crate::error::VmError;
use crate::state::VmState;

pub trait Opcode: Send + Sync {
    fn range(&self) -> (u32, u32);

    fn dispatch(&self, st: &mut VmState, opcode: u32, bits: u16) -> Result<i32>;

    fn load_dump(
        &self,
        slice: &mut CellSlice<'_>,
        opcode: u32,
        bits: u16,
        f: &mut dyn std::fmt::Write,
    ) -> Result<()>;

    fn compute_len(&self, slice: &CellSlice<'_>, opcode: u32, bits: u16) -> Option<(u16, u8)>;
}

pub struct DispatchTable {
    id: u16,
    opcodes: Vec<(u32, Box<dyn Opcode>)>,
}

impl DispatchTable {
    pub fn builder(id: u16) -> DispatchTableBuilder {
        DispatchTableBuilder {
            id,
            opcodes: Default::default(),
        }
    }

    #[inline]
    pub fn id(&self) -> u16 {
        self.id
    }

    pub fn lookup(&self, opcode: u32) -> &dyn Opcode {
        debug_assert!(!self.opcodes.is_empty());

        let mut i = 0;
        let mut j = self.opcodes.len();
        while j - i > 1 {
            let k = (j + i) >> 1;
            if self.opcodes[k].0 <= opcode {
                i = k;
            } else {
                j = k;
            }
        }
        self.opcodes[i].1.as_ref()
    }

    pub fn dispatch(&self, st: &mut VmState) -> Result<i32> {
        let (opcode, bits) = Self::get_opcode_from_slice(&st.code.apply()?);
        let op = self.lookup(opcode);
        op.dispatch(st, opcode, bits)
    }

    pub fn load_dump(&self, slice: &mut CellSlice<'_>, f: &mut dyn std::fmt::Write) -> Result<()> {
        let (opcode, bits) = Self::get_opcode_from_slice(slice);
        let op = self.lookup(opcode);
        op.load_dump(slice, opcode, bits, f)
    }

    pub fn compute_len(&self, slice: &CellSlice<'_>) -> Option<(u16, u8)> {
        let (opcode, bits) = Self::get_opcode_from_slice(slice);
        let op = self.lookup(opcode);
        op.compute_len(slice, opcode, bits)
    }

    fn get_opcode_from_slice(slice: &CellSlice<'_>) -> (u32, u16) {
        let bits = std::cmp::min(MAX_OPCODE_BITS, slice.remaining_bits());
        let opcode = (slice.get_uint(0, bits).unwrap() as u32) << (MAX_OPCODE_BITS - bits);
        (opcode, bits)
    }
}

pub struct DispatchTableBuilder {
    id: u16,
    opcodes: BTreeMap<u32, Box<dyn Opcode>>,
}

impl DispatchTableBuilder {
    pub fn build(self) -> DispatchTable {
        let mut opcodes = Vec::with_capacity(self.opcodes.len() * 2 + 1);

        let mut upto = 0;
        for (k, opcode) in self.opcodes {
            let (min, max) = opcode.range();
            if min > upto {
                opcodes.push((
                    upto,
                    Box::new(DummyOpcode {
                        opcode_min: upto,
                        opcode_max: min,
                    }) as Box<_>,
                ));
            }

            opcodes.push((k, opcode));
            upto = max;
        }

        if upto < MAX_OPCODE {
            opcodes.push((
                upto,
                Box::new(DummyOpcode {
                    opcode_min: upto,
                    opcode_max: MAX_OPCODE,
                }),
            ));
        }

        opcodes.shrink_to_fit();

        DispatchTable {
            id: self.id,
            opcodes,
        }
    }

    pub fn add_simple(
        &mut self,
        opcode: u32,
        bits: u16,
        name: &'static str,
        exec: FnExecInstrSimple,
    ) -> Result<()> {
        let remaining_bits = MAX_OPCODE_BITS - bits;
        self.add_opcode(Box::new(SimpleOpcode {
            name,
            opcode_min: opcode << remaining_bits,
            opcode_max: (opcode + 1) << remaining_bits,
            opcode_bits: bits,
            exec,
        }))
    }

    pub fn add_fixed(
        &mut self,
        opcode: u32,
        opcode_bits: u16,
        arg_bits: u16,
        dump: Box<FnDumpArgInstr>,
        exec: Box<FnExecInstrArg>,
    ) -> Result<()> {
        let remaining_bits = MAX_OPCODE_BITS - opcode_bits;
        self.add_opcode(Box::new(FixedOpcode {
            exec,
            dump,
            opcode_min: opcode << remaining_bits,
            opcode_max: (opcode + 1) << remaining_bits,
            total_bits: opcode_bits + arg_bits,
        }))
    }

    pub fn add_fixed_range(
        &mut self,
        opcode_min: u32,
        opcode_max: u32,
        total_bits: u16,
        _arg_bits: u16,
        dump: Box<FnDumpArgInstr>,
        exec: Box<FnExecInstrArg>,
    ) -> Result<()> {
        let remaining_bits = MAX_OPCODE_BITS - total_bits;
        self.add_opcode(Box::new(FixedOpcode {
            exec,
            dump,
            opcode_min: opcode_min << remaining_bits,
            opcode_max: opcode_max << remaining_bits,
            total_bits,
        }))
    }

    pub fn add_ext(
        &mut self,
        opcode: u32,
        opcode_bits: u16,
        arg_bits: u16,
        dump: Box<FnDumpInstr>,
        exec: Box<FnExecInstrFull>,
        instr_len: Box<FnComputeInstrLen>,
    ) -> Result<()> {
        let remaining_bits = MAX_OPCODE_BITS - opcode_bits;
        self.add_opcode(Box::new(ExtOpcode {
            exec,
            dump,
            instr_len,
            opcode_min: opcode << remaining_bits,
            opcode_max: (opcode + 1) << remaining_bits,
            total_bits: opcode_bits + arg_bits,
        }))
    }

    pub fn add_ext_range(
        &mut self,
        opcode_min: u32,
        opcode_max: u32,
        total_bits: u16,
        dump: Box<FnDumpInstr>,
        exec: Box<FnExecInstrFull>,
        instr_len: Box<FnComputeInstrLen>,
    ) -> Result<()> {
        let remaining_bits = MAX_OPCODE_BITS - total_bits;
        self.add_opcode(Box::new(ExtOpcode {
            exec,
            dump,
            instr_len,
            opcode_min: opcode_min << remaining_bits,
            opcode_max: opcode_max << remaining_bits,
            total_bits,
        }))
    }

    pub fn add_opcode(&mut self, opcode: Box<dyn Opcode>) -> Result<()> {
        let (min, max) = opcode.range();
        debug_assert!(min < max);
        debug_assert!(max <= MAX_OPCODE);

        if let Some((other_min, _)) = self.opcodes.range(min..).next() {
            anyhow::ensure!(
                max <= *other_min,
                "Opcode overlaps with next min: {other_min:06x}"
            );
        }

        if let Some((k, prev)) = self.opcodes.range(..=min).next_back() {
            let (prev_min, prev_max) = prev.range();
            debug_assert!(prev_min < prev_max);
            debug_assert!(prev_min == *k);
            anyhow::ensure!(
                prev_max <= min,
                "Opcode overlaps with prev max: {prev_max:06x}"
            );
        }

        self.opcodes.insert(min, opcode);
        Ok(())
    }
}

// === Opcodes ===

struct DummyOpcode {
    opcode_min: u32,
    opcode_max: u32,
}

impl Opcode for DummyOpcode {
    fn range(&self) -> (u32, u32) {
        (self.opcode_min, self.opcode_max)
    }

    fn dispatch(&self, _: &mut VmState, _: u32, _: u16) -> Result<i32> {
        // TODO: consume gas_per_instr
        anyhow::bail!(VmError::InvalidOpcode);
    }

    fn load_dump(
        &self,
        _: &mut CellSlice<'_>,
        _: u32,
        _: u16,
        _: &mut dyn std::fmt::Write,
    ) -> Result<()> {
        Ok(())
    }

    fn compute_len(&self, _: &CellSlice<'_>, _: u32, _: u16) -> Option<(u16, u8)> {
        None
    }
}

struct SimpleOpcode {
    exec: FnExecInstrSimple,
    name: &'static str,
    opcode_min: u32,
    opcode_max: u32,
    opcode_bits: u16,
}

impl Opcode for SimpleOpcode {
    fn range(&self) -> (u32, u32) {
        (self.opcode_min, self.opcode_max)
    }

    fn dispatch(&self, st: &mut VmState, _: u32, bits: u16) -> Result<i32> {
        // TODO: consume gas_per_instr + opcode_bits * gas_per_bit
        anyhow::ensure!(bits >= self.opcode_bits, VmError::InvalidOpcode);
        st.code.range_mut().advance(self.opcode_bits, 0)?;
        (self.exec)(st)
    }

    fn load_dump(
        &self,
        slice: &mut CellSlice<'_>,
        _: u32,
        bits: u16,
        f: &mut dyn std::fmt::Write,
    ) -> Result<()> {
        if bits >= self.opcode_bits {
            slice.try_advance(self.opcode_bits, 0);
            f.write_str(self.name)?;
        }
        Ok(())
    }

    fn compute_len(&self, _: &CellSlice<'_>, _: u32, bits: u16) -> Option<(u16, u8)> {
        (bits >= self.opcode_bits).then_some((self.opcode_bits, 0))
    }
}

struct FixedOpcode {
    exec: Box<FnExecInstrArg>,
    dump: Box<FnDumpArgInstr>,
    opcode_min: u32,
    opcode_max: u32,
    total_bits: u16,
}

impl Opcode for FixedOpcode {
    fn range(&self) -> (u32, u32) {
        (self.opcode_min, self.opcode_max)
    }

    fn dispatch(&self, st: &mut VmState, opcode: u32, bits: u16) -> Result<i32> {
        // TODO: consume gas_per_instr + total_bits * gas_per_bit
        anyhow::ensure!(bits >= self.total_bits, VmError::InvalidOpcode);
        st.code.range_mut().advance(self.total_bits, 0)?;
        (self.exec)(st, opcode >> (MAX_OPCODE_BITS - self.total_bits))
    }

    fn load_dump(
        &self,
        slice: &mut CellSlice<'_>,
        opcode: u32,
        bits: u16,
        f: &mut dyn std::fmt::Write,
    ) -> Result<()> {
        if bits >= self.total_bits {
            slice.try_advance(self.total_bits, 0);
            (self.dump)(slice, opcode >> (MAX_OPCODE_BITS - self.total_bits), f)?;
        }
        Ok(())
    }

    fn compute_len(&self, _: &CellSlice<'_>, _: u32, bits: u16) -> Option<(u16, u8)> {
        (bits >= self.total_bits).then_some((self.total_bits, 0))
    }
}

struct ExtOpcode {
    exec: Box<FnExecInstrFull>,
    dump: Box<FnDumpInstr>,
    instr_len: Box<FnComputeInstrLen>,
    opcode_min: u32,
    opcode_max: u32,
    total_bits: u16,
}

impl Opcode for ExtOpcode {
    fn range(&self) -> (u32, u32) {
        (self.opcode_min, self.opcode_max)
    }

    fn dispatch(&self, st: &mut VmState, opcode: u32, bits: u16) -> Result<i32> {
        // TODO: consume gas_per_instr + total_bits * gas_per_bit
        anyhow::ensure!(bits >= self.total_bits, VmError::InvalidOpcode);
        (self.exec)(
            st,
            opcode >> (MAX_OPCODE_BITS - self.total_bits),
            self.total_bits,
        )
    }

    fn load_dump(
        &self,
        slice: &mut CellSlice<'_>,
        opcode: u32,
        bits: u16,
        f: &mut dyn std::fmt::Write,
    ) -> Result<()> {
        if bits >= self.total_bits {
            (self.dump)(
                slice,
                opcode >> (MAX_OPCODE_BITS - self.total_bits),
                self.total_bits,
                f,
            )?;
        }
        Ok(())
    }

    fn compute_len(&self, slice: &CellSlice<'_>, opcode: u32, bits: u16) -> Option<(u16, u8)> {
        if bits >= self.total_bits {
            Some((self.instr_len)(
                slice,
                opcode >> (MAX_OPCODE_BITS - self.total_bits),
                self.total_bits,
            ))
        } else {
            None
        }
    }
}

type FnExecInstrSimple = fn(&mut VmState) -> Result<i32>;

type FnExecInstrArg = dyn Fn(&mut VmState, u32) -> Result<i32> + Send + Sync + 'static;

type FnExecInstrFull = dyn Fn(&mut VmState, u32, u16) -> Result<i32> + Send + Sync + 'static;

type FnDumpArgInstr =
    dyn Fn(&mut CellSlice<'_>, u32, &mut dyn std::fmt::Write) -> Result<()> + Send + Sync + 'static;

type FnDumpInstr = dyn Fn(&mut CellSlice<'_>, u32, u16, &mut dyn std::fmt::Write) -> Result<()>
    + Send
    + Sync
    + 'static;

type FnComputeInstrLen = dyn Fn(&CellSlice<'_>, u32, u16) -> (u16, u8) + Send + Sync + 'static;

const MAX_OPCODE_BITS: u16 = 24;
const MAX_OPCODE: u32 = 1 << MAX_OPCODE_BITS;
