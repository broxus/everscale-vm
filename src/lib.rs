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

use everscale_types::dict::DictKey;
use everscale_types::error::Error;
use everscale_types::prelude::*;
use num_bigint::BigInt;

use crate::util::{store_int_to_builder, OwnedCellSlice};

mod util;

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
        ok!(builder.store_uint(0x0200 >> 1, 15));
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
        ok!(builder.store_u8(0x04));
        store_slice(self, builder)
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

fn store_slice(slice: &OwnedCellSlice, builder: &mut CellBuilder) -> Result<(), Error> {
    ok!(builder.store_reference(slice.cell().clone()));

    let range = slice.range();
    let value = ((range.bits_offset() as u64) << 16)
        | (((range.bits_offset() + range.remaining_bits()) as u64) << 6)
        | ((range.refs_offset() as u64) << 3)
        | (range.refs_offset() + range.remaining_refs()) as u64;
    builder.store_uint(value, 26)
}

pub trait Cont: Store {}

pub type RcCont = Rc<dyn Cont>;

pub struct ControlRegs {
    pub c: [Option<RcCont>; Self::CONT_REG_COUNT],
    pub d: [Option<Cell>; Self::DATA_REG_COUNT],
    pub c7: Option<Rc<Vec<RcStackValue>>>,
}

impl ControlRegs {
    const CONT_REG_COUNT: usize = 4;
    const DATA_REG_OFFSET: usize = Self::CONT_REG_COUNT;
    const DATA_REG_COUNT: usize = 2;
}

impl Store for ControlRegs {
    fn store_into(
        &self,
        builder: &mut CellBuilder,
        context: &mut dyn CellContext,
    ) -> Result<(), Error> {
        #[repr(transparent)]
        struct Uint4(usize);

        impl Store for Uint4 {
            fn store_into(
                &self,
                builder: &mut CellBuilder,
                _: &mut dyn CellContext,
            ) -> Result<(), Error> {
                if self.0 > 0xf {
                    return Err(Error::IntOverflow);
                }
                builder.store_small_uint(self.0 as _, 4)
            }
        }

        impl DictKey for Uint4 {
            const BITS: u16 = 4;

            fn from_raw_data(raw_data: &[u8; 128]) -> Option<Self> {
                Some(Self((raw_data[0] & 0xf) as usize))
            }
        }

        #[repr(transparent)]
        struct AsDictValue<'a>(&'a dyn StackValue);

        impl Store for AsDictValue<'_> {
            #[inline]
            fn store_into(
                &self,
                builder: &mut CellBuilder,
                context: &mut dyn CellContext,
            ) -> Result<(), Error> {
                self.0.store_as_stack_value(builder, context)
            }
        }

        // TODO: optimize by building dict manually

        let mut dict = Dict::<Uint4, AsDictValue>::new();

        for (i, c) in self.c.iter().enumerate() {
            if let Some(c) = c {
                ok!(dict.set_ext(Uint4(i), AsDictValue(c), context));
            }
        }
        for (i, d) in self.d.iter().enumerate() {
            if let Some(d) = d {
                ok!(dict.set_ext(Uint4(i + Self::DATA_REG_OFFSET), AsDictValue(d), context));
            }
        }
        if let Some(c7) = &self.c7 {
            ok!(dict.set_ext(Uint4(7), AsDictValue(c7.as_ref()), context));
        }

        dict.store_into(builder, context)
    }
}

pub struct QuitCont {
    pub exit_code: i32,
}

impl Cont for QuitCont {}

impl Store for QuitCont {
    fn store_into(&self, builder: &mut CellBuilder, _: &mut dyn CellContext) -> Result<(), Error> {
        ok!(builder.store_small_uint(0b1000, 4));
        builder.store_u32(self.exit_code as u32)
    }
}

pub struct ExtQuitCont;

impl Cont for ExtQuitCont {}

impl Store for ExtQuitCont {
    fn store_into(&self, builder: &mut CellBuilder, _: &mut dyn CellContext) -> Result<(), Error> {
        builder.store_small_uint(0b1001, 4)
    }
}

pub struct PushIntCont {
    pub value: i32,
    pub next: Rc<dyn Cont>,
}

impl Cont for PushIntCont {}

impl Store for PushIntCont {
    fn store_into(
        &self,
        builder: &mut CellBuilder,
        context: &mut dyn CellContext,
    ) -> Result<(), Error> {
        ok!(builder.store_small_uint(0b1111, 4));
        ok!(builder.store_u32(self.value as u32));
        builder.store_reference(ok!(CellBuilder::build_from_ext(&self.next, context)))
    }
}

pub struct RepeatCont {
    pub count: u64,
    pub body: Rc<dyn Cont>,
    pub after: Rc<dyn Cont>,
}

impl Store for RepeatCont {
    fn store_into(
        &self,
        builder: &mut CellBuilder,
        context: &mut dyn CellContext,
    ) -> Result<(), Error> {
        if self.count >= 0x8000000000000000 {
            return Err(Error::IntOverflow);
        }
        ok!(builder.store_small_uint(0b1010, 4));
        ok!(builder.store_u64(self.count));
        ok!(builder.store_reference(ok!(CellBuilder::build_from_ext(&self.body, context))));
        builder.store_reference(ok!(CellBuilder::build_from_ext(&self.after, context)))
    }
}

pub struct AgainCont {
    pub body: Rc<dyn Cont>,
}

impl Cont for AgainCont {}

impl Store for AgainCont {
    fn store_into(
        &self,
        builder: &mut CellBuilder,
        context: &mut dyn CellContext,
    ) -> Result<(), Error> {
        ok!(builder.store_small_uint(0b110001, 6));
        builder.store_reference(ok!(CellBuilder::build_from_ext(&self.body, context)))
    }
}

pub struct UntilCont {
    pub body: Rc<dyn Cont>,
    pub after: Rc<dyn Cont>,
}

impl Cont for UntilCont {}

impl Store for UntilCont {
    fn store_into(
        &self,
        builder: &mut CellBuilder,
        context: &mut dyn CellContext,
    ) -> Result<(), Error> {
        ok!(builder.store_small_uint(0b110000, 6));
        ok!(builder.store_reference(ok!(CellBuilder::build_from_ext(&self.body, context))));
        builder.store_reference(ok!(CellBuilder::build_from_ext(&self.after, context)))
    }
}

pub struct WhileCont {
    pub cond: Rc<dyn Cont>,
    pub body: Rc<dyn Cont>,
    pub after: Rc<dyn Cont>,
    pub check_cond: bool,
}

impl Cont for WhileCont {}

impl Store for WhileCont {
    fn store_into(
        &self,
        builder: &mut CellBuilder,
        context: &mut dyn CellContext,
    ) -> Result<(), Error> {
        let tag = 0b110010u8 | !self.check_cond as u8;
        ok!(builder.store_small_uint(tag, 6));
        ok!(builder.store_reference(ok!(CellBuilder::build_from_ext(&self.cond, context))));
        ok!(builder.store_reference(ok!(CellBuilder::build_from_ext(&self.body, context))));
        builder.store_reference(ok!(CellBuilder::build_from_ext(&self.after, context)))
    }
}

pub struct ControlData {
    pub stack: Option<Rc<Stack>>,
    pub save: ControlRegs,
    pub nargs: Option<u16>,
    pub cp: Option<u16>,
}

impl Store for ControlData {
    fn store_into(
        &self,
        builder: &mut CellBuilder,
        context: &mut dyn CellContext,
    ) -> Result<(), Error> {
        match self.nargs {
            None => ok!(builder.store_bit_zero()),
            Some(nargs) if nargs <= 0x1fff => {
                ok!(builder.store_bit_one());
                ok!(builder.store_uint(nargs as _, 13));
            }
            Some(_) => return Err(Error::IntOverflow),
        }

        ok!(self.stack.store_into(builder, context));
        ok!(self.save.store_into(builder, context));
        ok!(self.cp.store_into(builder, context));
        Ok(())
    }
}

pub struct OrdCont {
    pub data: ControlData,
    pub code: OwnedCellSlice,
}

impl Cont for OrdCont {}

impl Store for OrdCont {
    fn store_into(
        &self,
        builder: &mut CellBuilder,
        context: &mut dyn CellContext,
    ) -> Result<(), Error> {
        ok!(builder.store_zeros(2));
        ok!(self.data.store_into(builder, context));
        store_slice(&self.code, builder)
    }
}
