use std::rc::Rc;

use everscale_types::cell::LoadMode;
use everscale_types::error::Error;
use everscale_types::prelude::*;
use num_bigint::BigInt;

use crate::cont::RcCont;
use crate::util::{store_int_to_builder, OwnedCellSlice};

#[derive(Default)]
pub struct Stack {
    pub items: Vec<RcStackValue>,
}

impl Stack {
    pub fn make_null() -> RcStackValue {
        thread_local! {
            static NULL: RcStackValue = Rc::new(());
        }
        NULL.with(Rc::clone)
    }

    pub fn make_nan() -> RcStackValue {
        thread_local! {
            static NAN: RcStackValue = Rc::new(NaN);
        }
        NAN.with(Rc::clone)
    }
}

// TODO: impl store with limit
impl Store for Stack {
    fn store_into(
        &self,
        builder: &mut CellBuilder,
        context: &mut dyn CellContext,
    ) -> Result<(), Error> {
        let depth = self.items.len();
        if depth > 0xffffff {
            return Err(Error::IntOverflow);
        }
        ok!(builder.store_uint(depth as _, 24));

        if let Some((last, items)) = self.items.split_last() {
            let mut rest = Cell::empty_cell();
            for item in items {
                let mut builder = CellBuilder::new();
                ok!(builder.store_reference(rest));
                ok!(item.store_as_stack_value(&mut builder, context));
                rest = ok!(builder.build_ext(context));
            }

            ok!(builder.store_reference(rest));
            ok!(last.store_as_stack_value(builder, context));
        }
        Ok(())
    }
}

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub enum StackValueType {
    Null,
    NaN,
    Int,
    Cell,
    Slice,
    Builder,
    Cont,
    Tuple,
}

pub trait StackValue {
    fn ty(&self) -> StackValueType;

    fn store_as_stack_value(
        &self,
        builder: &mut CellBuilder,
        context: &mut dyn CellContext,
    ) -> Result<(), Error>;

    fn as_int(&self) -> Option<&BigInt> {
        None
    }

    fn into_int(self: Rc<Self>) -> Option<Rc<BigInt>> {
        None
    }

    fn as_cell(&self) -> Option<&Cell> {
        None
    }

    fn into_cell(self: Rc<Self>) -> Option<Rc<Cell>> {
        None
    }

    fn as_slice(&self) -> Option<&OwnedCellSlice> {
        None
    }

    fn into_slice(self: Rc<Self>) -> Option<Rc<OwnedCellSlice>> {
        None
    }

    fn as_builder(&self) -> Option<&CellBuilder> {
        None
    }

    fn into_builder(self: Rc<Self>) -> Option<Rc<CellBuilder>> {
        None
    }

    fn as_cont(&self) -> Option<&RcCont> {
        None
    }

    fn into_cont(self: Rc<Self>) -> Option<Rc<RcCont>> {
        None
    }

    fn as_tuple(&self) -> Option<&[RcStackValue]> {
        None
    }

    fn into_tuple(self: Rc<Self>) -> Option<Rc<Vec<RcStackValue>>> {
        None
    }
}

pub type RcStackValue = Rc<dyn StackValue>;

pub fn load_stack_value(
    slice: &mut CellSlice,
    context: &mut dyn CellContext,
) -> Result<RcStackValue, Error> {
    let ty = ok!(slice.load_u8());
    Ok(match ty {
        0 => Stack::make_null(),
        // NOTE: tinyint is skipped as unused
        2 => {
            let t = ok!(slice.load_u8());
            if t == 0xff {
                Stack::make_nan()
            } else {
                todo!()
            }
        }
        3 => Rc::new(ok!(slice.load_reference_cloned())),
        4 => Rc::new(ok!(load_slice_as_stack_value(slice, context))),
        5 => {
            let cell = ok!(context
                .load_dyn_cell(ok!(slice.load_reference()), LoadMode::Full)
                .and_then(CellSlice::new));

            let mut builder = CellBuilder::new();
            ok!(builder.store_slice(cell));
            Rc::new(builder)
        }
        7 => {
            let len = ok!(slice.load_u16()) as usize;
            let mut tuple = Vec::with_capacity(std::cmp::min(len, 128));

            if len > 1 {
                let mut head = ok!(slice.load_reference());
                let mut tail = ok!(slice.load_reference());
                tuple.push(ok!(load_stack_value_from_cell(tail, context)));

                for _ in 0..len - 2 {
                    let slice = &mut ok!(context
                        .load_dyn_cell(head, LoadMode::Full)
                        .and_then(CellSlice::new));
                    head = ok!(slice.load_reference());
                    tail = ok!(slice.load_reference());
                    ok!(ensure_empty(slice));
                    tuple.push(ok!(load_stack_value_from_cell(tail, context)));
                }

                tuple.push(ok!(load_stack_value_from_cell(head, context)));
                tuple.reverse();
            } else if len == 1 {
                tuple.push(ok!(load_stack_value_from_cell(
                    ok!(slice.load_reference()),
                    context
                )));
            }

            Rc::new(tuple)
        }
        _ => return Err(Error::InvalidTag),
    })
}

fn load_stack_value_from_cell(
    cell: &DynCell,
    context: &mut dyn CellContext,
) -> Result<RcStackValue, Error> {
    let slice = &mut ok!(context
        .load_dyn_cell(cell, LoadMode::Full)
        .and_then(CellSlice::new));
    let res = ok!(load_stack_value(slice, context));
    ok!(ensure_empty(slice));
    Ok(res)
}

fn ensure_empty(slice: &CellSlice) -> Result<(), Error> {
    if slice.is_data_empty() && slice.is_refs_empty() {
        Ok(())
    } else {
        Err(Error::InvalidData)
    }
}

impl StackValue for () {
    fn ty(&self) -> StackValueType {
        StackValueType::Null
    }

    fn store_as_stack_value(
        &self,
        builder: &mut CellBuilder,
        _: &mut dyn CellContext,
    ) -> Result<(), Error> {
        builder.store_zeros(8)
    }
}

#[derive(Debug, Clone, Copy)]
pub struct NaN;

impl StackValue for NaN {
    fn ty(&self) -> StackValueType {
        StackValueType::NaN
    }

    fn store_as_stack_value(
        &self,
        builder: &mut CellBuilder,
        _: &mut dyn CellContext,
    ) -> Result<(), Error> {
        builder.store_u16(0x02ff)
    }
}

impl StackValue for BigInt {
    fn ty(&self) -> StackValueType {
        StackValueType::Int
    }

    fn store_as_stack_value(
        &self,
        builder: &mut CellBuilder,
        _: &mut dyn CellContext,
    ) -> Result<(), Error> {
        ok!(builder.store_uint(0x0200 >> 1, 15));
        store_int_to_builder(self, 257, builder)
    }

    fn as_int(&self) -> Option<&BigInt> {
        Some(self)
    }

    fn into_int(self: Rc<Self>) -> Option<Rc<BigInt>> {
        Some(self)
    }
}

impl StackValue for Cell {
    fn ty(&self) -> StackValueType {
        StackValueType::Cell
    }

    fn store_as_stack_value(
        &self,
        builder: &mut CellBuilder,
        _: &mut dyn CellContext,
    ) -> Result<(), Error> {
        ok!(builder.store_u8(0x03));
        builder.store_reference(self.clone())
    }

    fn as_cell(&self) -> Option<&Cell> {
        Some(self)
    }

    fn into_cell(self: Rc<Self>) -> Option<Rc<Cell>> {
        Some(self)
    }
}

impl StackValue for OwnedCellSlice {
    fn ty(&self) -> StackValueType {
        StackValueType::Slice
    }

    fn store_as_stack_value(
        &self,
        builder: &mut CellBuilder,
        _: &mut dyn CellContext,
    ) -> Result<(), Error> {
        ok!(builder.store_u8(0x04));
        store_slice_as_stack_value(self, builder)
    }

    fn as_slice(&self) -> Option<&OwnedCellSlice> {
        Some(self)
    }

    fn into_slice(self: Rc<Self>) -> Option<Rc<OwnedCellSlice>> {
        Some(self)
    }
}
impl StackValue for CellBuilder {
    fn ty(&self) -> StackValueType {
        StackValueType::Builder
    }

    fn store_as_stack_value(
        &self,
        builder: &mut CellBuilder,
        context: &mut dyn CellContext,
    ) -> Result<(), Error> {
        ok!(builder.store_u8(0x05));
        builder.store_reference(ok!(self.clone().build_ext(context)))
    }

    fn as_builder(&self) -> Option<&CellBuilder> {
        Some(self)
    }

    fn into_builder(self: Rc<Self>) -> Option<Rc<CellBuilder>> {
        Some(self)
    }
}

impl StackValue for RcCont {
    fn ty(&self) -> StackValueType {
        StackValueType::Cont
    }

    fn store_as_stack_value(
        &self,
        builder: &mut CellBuilder,
        context: &mut dyn CellContext,
    ) -> Result<(), Error> {
        ok!(builder.store_u8(0x06));
        self.as_ref().store_into(builder, context)
    }

    fn as_cont(&self) -> Option<&RcCont> {
        Some(self)
    }

    fn into_cont(self: Rc<Self>) -> Option<Rc<RcCont>> {
        Some(self)
    }
}

impl StackValue for Vec<RcStackValue> {
    fn ty(&self) -> StackValueType {
        StackValueType::Tuple
    }

    fn store_as_stack_value(
        &self,
        builder: &mut CellBuilder,
        context: &mut dyn CellContext,
    ) -> Result<(), Error> {
        if self.len() > u16::MAX as usize {
            return Err(Error::IntOverflow);
        }

        let mut head = None::<Cell>;
        let mut tail = None::<Cell>;

        for item in self {
            std::mem::swap(&mut head, &mut tail);

            if tail.is_some() && head.is_some() {
                if let (Some(t), Some(h)) = (tail.take(), head.take()) {
                    head = Some(ok!(CellBuilder::build_from_ext((t, h), context)));
                }
            }

            let mut builder = CellBuilder::new();
            ok!(item.store_as_stack_value(&mut builder, context));
            tail = Some(ok!(builder.build_ext(context)));
        }

        ok!(builder.store_u8(0x07));
        ok!(builder.store_u16(self.len() as _));
        if let Some(head) = head {
            ok!(builder.store_reference(head));
        }
        if let Some(tail) = tail {
            ok!(builder.store_reference(tail));
        }
        Ok(())
    }

    fn as_tuple(&self) -> Option<&[RcStackValue]> {
        Some(self)
    }

    fn into_tuple(self: Rc<Self>) -> Option<Rc<Vec<RcStackValue>>> {
        Some(self)
    }
}

pub fn store_slice_as_stack_value(
    slice: &OwnedCellSlice,
    builder: &mut CellBuilder,
) -> Result<(), Error> {
    ok!(builder.store_reference(slice.cell().clone()));

    let range = slice.range();
    let value = ((range.bits_offset() as u64) << 16)
        | (((range.bits_offset() + range.remaining_bits()) as u64) << 6)
        | ((range.refs_offset() as u64) << 3)
        | (range.refs_offset() + range.remaining_refs()) as u64;
    builder.store_uint(value, 26)
}

pub fn load_slice_as_stack_value(
    slice: &mut CellSlice,
    context: &mut dyn CellContext,
) -> Result<OwnedCellSlice, Error> {
    let cell = ok!(slice.load_reference_cloned());
    let range = ok!(slice.load_uint(26));

    let bits_start = (range >> 16) as u16;
    let bits_end = (range >> 6) as u16 & 0x3ff;
    let refs_start = (range >> 3) as u8 & 0b111;
    let refs_end = range as u8 & 0b111;

    if bits_start > bits_end || refs_start > refs_end || refs_end > 4 {
        return Err(Error::InvalidData);
    }

    // TODO: is it ok to resolve library cell for stack?
    let cell = ok!(context.load_cell(cell, LoadMode::Full));

    if bits_end > cell.bit_len() || refs_end > cell.reference_count() {}

    let mut range = CellSliceRange::empty();
    range.try_advance(bits_start, refs_end);
    range = range.get_prefix(bits_end - bits_start, refs_end - refs_start);

    Ok(OwnedCellSlice::from((cell, range)))
}
