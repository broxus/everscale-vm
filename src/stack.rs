use std::rc::Rc;

use everscale_types::cell::LoadMode;
use everscale_types::error::Error;
use everscale_types::prelude::*;
use num_bigint::BigInt;
use num_traits::{One, ToPrimitive, Zero};

use crate::cont::{load_cont, DynCont, RcCont};
use crate::error::{VmError, VmResult};
use crate::util::{bitsize, ensure_empty_slice, store_int_to_builder, OwnedCellSlice};

#[derive(Debug, Default, Clone)]
pub struct Stack {
    pub items: Vec<RcStackValue>,
}

impl Stack {
    const MAX_DEPTH: usize = 0xffffff;

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

    pub fn make_empty_tuple() -> RcStackValue {
        thread_local! {
            static EMPTY_TUPLE: RcStackValue = Rc::new(Vec::new());
        }
        EMPTY_TUPLE.with(Rc::clone)
    }

    pub fn depth(&self) -> usize {
        self.items.len()
    }

    pub fn push<T: StackValue + 'static>(&mut self, item: T) -> VmResult<()> {
        self.push_raw(Rc::new(item))
    }

    pub fn push_raw(&mut self, item: Rc<dyn StackValue>) -> VmResult<()> {
        vm_ensure!(
            self.depth() < Self::MAX_DEPTH,
            StackUnderflow(Self::MAX_DEPTH)
        );

        self.items.push(item);
        Ok(())
    }

    pub fn push_opt<T: StackValue + 'static>(&mut self, value: Option<T>) -> VmResult<()> {
        match value {
            None => self.push_null(),
            Some(value) => self.push(value),
        }
    }

    pub fn push_opt_raw(&mut self, item: Option<Rc<dyn StackValue>>) -> VmResult<()> {
        match item {
            None => self.push_null(),
            Some(item) => self.push_raw(item),
        }
    }

    pub fn push_nth(&mut self, idx: usize) -> VmResult<()> {
        let depth = self.depth();
        vm_ensure!(idx < depth, StackUnderflow(idx));
        vm_ensure!(depth + 1 < Self::MAX_DEPTH, StackUnderflow(Self::MAX_DEPTH));
        self.items.push(self.items[depth - idx - 1].clone());
        Ok(())
    }

    pub fn push_null(&mut self) -> VmResult<()> {
        self.push_raw(Self::make_null())
    }

    pub fn push_nan(&mut self) -> VmResult<()> {
        self.push_raw(Self::make_nan())
    }

    pub fn push_bool(&mut self, value: bool) -> VmResult<()> {
        thread_local! {
            static TRUE: RcStackValue = Rc::new(-BigInt::one());
            static FALSE: RcStackValue = Rc::new(BigInt::zero());
        }

        self.push_raw(if value {
            TRUE.with(Rc::clone)
        } else {
            FALSE.with(Rc::clone)
        })
    }

    pub fn push_int<T: Into<BigInt>>(&mut self, value: T) -> VmResult<()> {
        // TODO: Inline some numbers as thread-local constants to avoid some allocations
        self.push(value.into())
    }

    pub fn push_raw_int(&mut self, value: Rc<BigInt>, quiet: bool) -> VmResult<()> {
        if bitsize(&value, true) <= 257 {
            self.push_raw(value)
        } else if quiet {
            self.push_nan()
        } else {
            vm_bail!(IntegerOverflow)
        }
    }

    pub fn move_from_stack(&mut self, other: &mut Self, n: usize) -> VmResult<()> {
        let Some(new_other_len) = other.depth().checked_sub(n) else {
            vm_bail!(StackUnderflow(n));
        };
        self.items.extend(other.items.drain(new_other_len..));
        Ok(())
    }

    pub fn split_top(&mut self, n: usize) -> VmResult<Rc<Self>> {
        let Some(new_depth) = self.depth().checked_sub(n) else {
            vm_bail!(StackUnderflow(n));
        };
        Ok(Rc::new(Self {
            items: self.items.drain(new_depth..).collect(),
        }))
    }

    pub fn split_top_ext(&mut self, n: usize, drop: usize) -> VmResult<Rc<Self>> {
        let Some(new_depth) = self.depth().checked_sub(n + drop) else {
            vm_bail!(StackUnderflow(n + drop));
        };
        let res = Rc::new(Self {
            items: self.items.drain(new_depth + drop..).collect(),
        });
        self.items.truncate(new_depth);
        Ok(res)
    }

    pub fn pop(&mut self) -> VmResult<Rc<dyn StackValue>> {
        let Some(item) = self.items.pop() else {
            vm_bail!(StackUnderflow(0));
        };
        Ok(item)
    }

    pub fn pop_bool(&mut self) -> VmResult<bool> {
        Ok(!ok!(self.pop_int()).is_zero())
    }

    pub fn pop_int(&mut self) -> VmResult<Rc<BigInt>> {
        ok!(self.pop()).into_int()
    }

    pub fn pop_int_or_nan(&mut self) -> VmResult<Option<Rc<BigInt>>> {
        let value = ok!(self.pop());
        if value.ty() == StackValueType::Int && value.as_int().is_none() {
            Ok(None)
        } else {
            value.into_int().map(Some)
        }
    }

    pub fn pop_smallint_range(&mut self, min: u32, max: u32) -> VmResult<u32> {
        let item = self.pop_int()?;
        if let Some(item) = item.to_u32() {
            if item >= min && item <= max {
                return Ok(item);
            }
        }
        vm_bail!(IntegerOutOfRange {
            min: min as isize,
            max: max as isize,
            actual: item.to_string(),
        })
    }

    pub fn pop_smallint_signed_range(&mut self, min: i32, max: i32) -> VmResult<i32> {
        let item = self.pop_int()?;
        if let Some(item) = item.to_i32() {
            if item >= min && item <= max {
                return Ok(item);
            }
        }
        vm_bail!(IntegerOutOfRange {
            min: min as isize,
            max: max as isize,
            actual: item.to_string(),
        })
    }

    pub fn pop_tuple(&mut self) -> VmResult<Rc<Tuple>> {
        self.pop()?.into_tuple()
    }

    pub fn pop_tuple_range(&mut self, min_len: u32, max_len: u32) -> VmResult<Rc<Tuple>> {
        let tuple = self.pop()?.into_tuple()?;
        vm_ensure!(
            (min_len as usize..=max_len as usize).contains(&tuple.len()),
            InvalidType {
                expected: StackValueType::Tuple,
                actual: StackValueType::Tuple,
            }
        );
        Ok(tuple)
    }

    pub fn pop_opt_tuple_range(
        &mut self,
        min_len: u32,
        max_len: u32,
    ) -> VmResult<Option<Rc<Tuple>>> {
        let tuple = {
            let value = self.pop()?;
            if value.is_null() {
                return Ok(None);
            }
            value.into_tuple()?
        };

        vm_ensure!(
            (min_len as usize..=max_len as usize).contains(&tuple.len()),
            InvalidType {
                expected: StackValueType::Tuple,
                actual: StackValueType::Tuple,
            }
        );
        Ok(Some(tuple))
    }

    pub fn pop_cont(&mut self) -> VmResult<RcCont> {
        self.pop()?.into_cont()
    }

    pub fn pop_cs(&mut self) -> VmResult<Rc<OwnedCellSlice>> {
        self.pop()?.into_slice()
    }

    pub fn pop_builder(&mut self) -> VmResult<Rc<CellBuilder>> {
        self.pop()?.into_builder()
    }

    pub fn pop_cell(&mut self) -> VmResult<Rc<Cell>> {
        self.pop()?.into_cell()
    }

    pub fn pop_many(&mut self, n: usize) -> VmResult<()> {
        let Some(new_len) = self.depth().checked_sub(n) else {
            vm_bail!(StackUnderflow(n));
        };
        self.items.truncate(new_len);
        Ok(())
    }

    pub fn drop_bottom(&mut self, n: usize) -> VmResult<()> {
        vm_ensure!(n <= self.depth(), StackUnderflow(n));
        self.items.drain(..n);
        Ok(())
    }

    pub fn swap(&mut self, lhs: usize, rhs: usize) -> VmResult<()> {
        let depth = self.depth();
        vm_ensure!(lhs < depth, StackUnderflow(lhs));
        vm_ensure!(rhs < depth, StackUnderflow(rhs));
        self.items.swap(depth - lhs - 1, depth - rhs - 1);
        //eprintln!("AFTER SWAP: {}", self.display_dump());
        Ok(())
    }

    pub fn reverse_range(&mut self, offset: usize, n: usize) -> VmResult<()> {
        let depth = self.depth();
        vm_ensure!(offset < depth, StackUnderflow(offset));
        vm_ensure!(offset + n <= depth, StackUnderflow(offset + n));
        self.items[depth - offset - n..depth - offset].reverse();
        Ok(())
    }

    pub fn fetch(&self, idx: usize) -> VmResult<Rc<dyn StackValue>> {
        let depth = self.depth();
        vm_ensure!(idx < depth, StackUnderflow(idx));
        Ok(self.items[depth - idx - 1].clone())
    }
}

// TODO: impl store with limit
impl Store for Stack {
    fn store_into(
        &self,
        builder: &mut CellBuilder,
        context: &mut dyn CellContext,
    ) -> Result<(), Error> {
        let depth = self.depth();
        if depth > Self::MAX_DEPTH {
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

pub fn load_stack(slice: &mut CellSlice, context: &mut dyn CellContext) -> Result<Stack, Error> {
    let depth = ok!(slice.load_uint(24)) as usize;
    if depth == 0 {
        return Ok(Stack::default());
    }

    let mut result = Stack {
        items: Vec::with_capacity(std::cmp::min(depth, 128)),
    };

    let mut rest = ok!(slice.load_reference());
    result.items.push(ok!(load_stack_value(slice, context)));

    if depth > 1 {
        for _ in 0..depth - 2 {
            let slice = &mut ok!(context
                .load_dyn_cell(rest, LoadMode::Full)
                .and_then(CellSlice::new));
            rest = ok!(slice.load_reference());
            result.items.push(ok!(load_stack_value(slice, context)));
            ok!(ensure_empty_slice(slice));
        }

        ok!(ensure_empty_slice(&ok!(context
            .load_dyn_cell(rest, LoadMode::Full)
            .and_then(CellSlice::new))));

        result.items.reverse();
    }

    Ok(result)
}

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub enum StackValueType {
    Null,
    Int,
    Cell,
    Slice,
    Builder,
    Cont,
    Tuple,
}

pub trait StackValue: std::fmt::Debug {
    fn ty(&self) -> StackValueType;

    fn store_as_stack_value(
        &self,
        builder: &mut CellBuilder,
        context: &mut dyn CellContext,
    ) -> Result<(), Error>;

    fn fmt_dump(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result;

    fn as_int(&self) -> Option<&BigInt> {
        None
    }

    fn into_int(self: Rc<Self>) -> VmResult<Rc<BigInt>> {
        Err(invalid_type(self.ty(), StackValueType::Int))
    }

    fn as_cell(&self) -> Option<&Cell> {
        None
    }

    fn into_cell(self: Rc<Self>) -> VmResult<Rc<Cell>> {
        Err(invalid_type(self.ty(), StackValueType::Cell))
    }

    fn as_slice(&self) -> Option<&OwnedCellSlice> {
        None
    }

    fn into_slice(self: Rc<Self>) -> VmResult<Rc<OwnedCellSlice>> {
        Err(invalid_type(self.ty(), StackValueType::Slice))
    }

    fn as_builder(&self) -> Option<&CellBuilder> {
        None
    }

    fn into_builder(self: Rc<Self>) -> VmResult<Rc<CellBuilder>> {
        Err(invalid_type(self.ty(), StackValueType::Builder))
    }

    fn as_cont(&self) -> Option<&DynCont> {
        None
    }

    fn into_cont(self: Rc<Self>) -> VmResult<RcCont> {
        Err(invalid_type(self.ty(), StackValueType::Cont))
    }

    fn as_tuple(&self) -> Option<&[RcStackValue]> {
        None
    }

    fn into_tuple(self: Rc<Self>) -> VmResult<Rc<Tuple>> {
        Err(invalid_type(self.ty(), StackValueType::Tuple))
    }
}

impl dyn StackValue + '_ {
    pub fn is_null(&self) -> bool {
        self.ty() == StackValueType::Null
    }

    pub fn is_tuple(&self) -> bool {
        self.ty() == StackValueType::Tuple
    }

    pub fn as_tuple_range(&self, min_len: u32, max_len: u32) -> Option<&[RcStackValue]> {
        let tuple = self.as_tuple()?;
        (min_len as usize..=max_len as usize)
            .contains(&tuple.len())
            .then_some(tuple)
    }

    pub fn as_pair(&self) -> Option<(&dyn StackValue, &dyn StackValue)> {
        match self.as_tuple()? {
            [first, second] => Some((first.as_ref(), second.as_ref())),
            _ => None,
        }
    }

    pub fn as_list(&self) -> Option<(&dyn StackValue, &dyn StackValue)> {
        let (head, tail) = self.as_pair()?;

        let mut next = tail;
        while !next.is_null() {
            let (_, tail) = next.as_pair()?;
            next = tail;
        }

        Some((head, tail))
    }

    pub fn display_list(&self) -> impl std::fmt::Display + '_ {
        pub struct DisplayList<'a>(&'a dyn StackValue);

        impl std::fmt::Display for DisplayList<'_> {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                self.0.fmt_list(f)
            }
        }

        DisplayList(self)
    }

    fn fmt_list(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.is_null() {
            f.write_str("()")
        } else if let Some(tuple) = self.as_tuple() {
            if let Some((head, tail)) = self.as_list() {
                f.write_str("(")?;
                head.fmt_list(f)?;
                tail.fmt_list_tail(f)?;
                return Ok(());
            }

            f.write_str("[")?;
            let mut first = true;
            for item in tuple {
                if !std::mem::take(&mut first) {
                    f.write_str(" ")?;
                }
                item.as_ref().fmt_list(f)?;
            }
            f.write_str("]")?;

            Ok(())
        } else {
            self.fmt_dump(f)
        }
    }

    fn fmt_list_tail(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut item = self;
        while !item.is_null() {
            let Some((head, tail)) = item.as_pair() else {
                f.write_str(" . ")?;
                item.fmt_list(f)?;
                break;
            };

            f.write_str(" ")?;
            head.fmt_list(f)?;
            item = tail;
        }
        f.write_str(")")
    }
}

fn invalid_type(actual: StackValueType, expected: StackValueType) -> Box<VmError> {
    Box::new(VmError::InvalidType { expected, actual })
}

pub type RcStackValue = Rc<dyn StackValue>;
pub type Tuple = Vec<RcStackValue>;

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
        6 => ok!(load_cont(slice, context)).into_stack_value(),
        7 => {
            let len = ok!(slice.load_u16()) as usize;
            let mut tuple = Vec::with_capacity(std::cmp::min(len, 128));

            match tuple.len() {
                0 => {}
                1 => {
                    tuple.push(ok!(load_stack_value_from_cell(
                        ok!(slice.load_reference()),
                        context
                    )));
                }
                _ => {
                    let mut head = ok!(slice.load_reference());
                    let mut tail = ok!(slice.load_reference());
                    tuple.push(ok!(load_stack_value_from_cell(tail, context)));

                    for _ in 0..len - 2 {
                        let slice = &mut ok!(context
                            .load_dyn_cell(head, LoadMode::Full)
                            .and_then(CellSlice::new));
                        head = ok!(slice.load_reference());
                        tail = ok!(slice.load_reference());
                        ok!(ensure_empty_slice(slice));
                        tuple.push(ok!(load_stack_value_from_cell(tail, context)));
                    }

                    tuple.push(ok!(load_stack_value_from_cell(head, context)));
                    tuple.reverse();
                }
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
    ok!(ensure_empty_slice(slice));
    Ok(res)
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

    fn fmt_dump(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("(null)")
    }
}

#[derive(Debug, Clone, Copy)]
pub struct NaN;

impl StackValue for NaN {
    fn ty(&self) -> StackValueType {
        StackValueType::Int
    }

    fn store_as_stack_value(
        &self,
        builder: &mut CellBuilder,
        _: &mut dyn CellContext,
    ) -> Result<(), Error> {
        builder.store_u16(0x02ff)
    }

    fn fmt_dump(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("NaN")
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

    fn fmt_dump(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(self, f)
    }

    fn as_int(&self) -> Option<&BigInt> {
        Some(self)
    }

    fn into_int(self: Rc<Self>) -> VmResult<Rc<BigInt>> {
        Ok(self)
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

    fn fmt_dump(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "C{{{}}}", self.repr_hash())
    }

    fn as_cell(&self) -> Option<&Cell> {
        Some(self)
    }

    fn into_cell(self: Rc<Self>) -> VmResult<Rc<Cell>> {
        Ok(self)
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

    fn fmt_dump(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(self, f)
    }

    fn as_slice(&self) -> Option<&OwnedCellSlice> {
        Some(self)
    }

    fn into_slice(self: Rc<Self>) -> VmResult<Rc<OwnedCellSlice>> {
        Ok(self)
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

    fn fmt_dump(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "BC{{{}}}", self.display_data())
    }

    fn as_builder(&self) -> Option<&CellBuilder> {
        Some(self)
    }

    fn into_builder(self: Rc<Self>) -> VmResult<Rc<CellBuilder>> {
        Ok(self)
    }
}

impl StackValue for DynCont {
    fn ty(&self) -> StackValueType {
        StackValueType::Cont
    }

    fn store_as_stack_value(
        &self,
        builder: &mut CellBuilder,
        context: &mut dyn CellContext,
    ) -> Result<(), Error> {
        ok!(builder.store_u8(0x06));
        self.store_into(builder, context)
    }

    fn fmt_dump(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Cont{{{:?}}}", self as *const _ as *const ())
    }

    fn as_cont(&self) -> Option<&DynCont> {
        Some(self)
    }

    fn into_cont(self: Rc<Self>) -> VmResult<RcCont> {
        Ok(self)
    }
}

impl StackValue for Tuple {
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

    fn fmt_dump(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.is_empty() {
            return f.write_str("[]");
        }
        f.write_str("[ ")?;
        let mut first = true;
        for item in self {
            if !std::mem::take(&mut first) {
                f.write_str(" ")?;
            }
            StackValue::fmt_dump(item.as_ref(), f)?;
        }
        f.write_str(" ]")
    }

    fn as_tuple(&self) -> Option<&[RcStackValue]> {
        Some(self)
    }

    fn into_tuple(self: Rc<Self>) -> VmResult<Rc<Tuple>> {
        Ok(self)
    }
}

pub fn store_slice_as_stack_value(
    slice: &OwnedCellSlice,
    builder: &mut CellBuilder,
) -> Result<(), Error> {
    ok!(builder.store_reference(slice.cell().clone()));

    let range = slice.range();
    let value = ((range.offset_bits() as u64) << 16)
        | (((range.offset_bits() + range.size_bits()) as u64) << 6)
        | ((range.offset_refs() as u64) << 3)
        | (range.offset_refs() + range.size_refs()) as u64;
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

    if bits_end > cell.bit_len() || refs_end > cell.reference_count() {
        return Err(Error::InvalidData);
    }

    let mut range = CellSliceRange::full(cell.as_ref());
    let ok = range.skip_first(bits_start, refs_end).is_ok();
    debug_assert!(ok);

    let bits = bits_end - bits_start;
    let refs = refs_end - refs_start;
    let ok = range.only_first(bits, refs).is_ok();
    debug_assert!(ok);

    Ok(OwnedCellSlice::from((cell, range)))
}
