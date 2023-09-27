/// Prevents using `From::from` for plain error conversion.
macro_rules! ok {
    ($e:expr $(,)?) => {
        match $e {
            core::result::Result::Ok(val) => val,
            core::result::Result::Err(err) => return core::result::Result::Err(err),
        }
    };
}

use std::rc::Rc;

use everscale_types::error::Error;
use everscale_types::prelude::*;
use num_bigint::BigInt;

use crate::util::{store_int_to_builder, OwnedCellSlice};

mod util;

#[derive(Default)]
pub struct Stack {
    pub itmes: Vec<RcStackValue>,
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
        ok!(builder.store_small_uint(0x0200 >> 1, 15));
        store_int_to_builder(self, 257, true, builder)
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
        // TODO: add flag
        ok!(builder.store_u8(0x04));
        ok!(builder.store_reference(self.cell().clone()));

        let range = self.range();
        let value = ((range.bits_offset() as u64) << 16)
            | (((range.bits_offset() + range.remaining_bits()) as u64) << 6)
            | ((range.refs_offset() as u64) << 3)
            | (range.refs_offset() + range.remaining_refs()) as u64;
        builder.store_uint(value, 26)
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

    fn as_cont(&self) -> Option<&Rc<dyn Cont>> {
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
        let mut result = CellBuilder::new();

        for item in self {
            std::mem::swap(&mut head, &mut tail);

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

pub trait Cont {}

pub type RcCont = Rc<dyn Cont>;

pub struct ControlRegs {
    pub c: [Rc<dyn Cont>; Self::CONT_REG_COUNT],
    pub d: [Cell; Self::DATA_REG_COUNT],
}

impl ControlRegs {
    const CONT_REG_COUNT: usize = 4;
    const DATA_REG_COUNT: usize = 2;
}

pub struct QuitCont {
    pub exit_code: i32,
}

pub struct ExtQuitCont;

pub struct PushIntCont {
    pub value: i32,
    pub next: Rc<dyn Cont>,
}

pub struct RepeatCont {
    pub count: u64,
    pub body: Rc<dyn Cont>,
    pub after: Rc<dyn Cont>,
}

pub struct AgainCont {
    pub body: Rc<dyn Cont>,
}

pub struct UntilCont {
    pub body: Rc<dyn Cont>,
    pub after: Rc<dyn Cont>,
}

pub struct WhileCont {
    pub cont: Rc<dyn Cont>,
    pub body: Rc<dyn Cont>,
    pub after: Rc<dyn Cont>,
    pub check_cond: bool,
}
