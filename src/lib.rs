use std::rc::Rc;

use everscale_types::prelude::*;
use num_bigint::BigInt;

pub trait StackValue {
    fn ty(&self) -> StackValueType;

    fn as_int(&self) -> Option<&BigInt> {
        None
    }

    fn as_cell(&self) -> Option<&Cell> {
        None
    }

    fn as_builder(&self) -> Option<&CellBuilder> {
        None
    }

    fn as_slice(&self) -> Option<&CellSliceParts> {
        None
    }

    fn as_cont(&self) -> Option<&Rc<dyn Continuation>> {
        None
    }

    fn as_tuple(&self) -> Option<&[Rc<dyn StackValue>]> {
        None
    }
}

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub enum StackValueType {
    Null,
    NaN,
    Int,
    Cell,
    Builder,
    Slice,
    Cont,
    Tuple,
}

impl StackValue for () {
    fn ty(&self) -> StackValueType {
        StackValueType::Null
    }
}

#[derive(Debug, Clone, Copy)]
pub struct NaN;

impl StackValue for NaN {
    fn ty(&self) -> StackValueType {
        StackValueType::NaN
    }
}

impl StackValue for BigInt {
    fn ty(&self) -> StackValueType {
        StackValueType::Int
    }

    fn as_int(&self) -> Option<&BigInt> {
        Some(self)
    }
}

impl StackValue for Cell {
    fn ty(&self) -> StackValueType {
        StackValueType::Cell
    }

    fn as_cell(&self) -> Option<&Cell> {
        Some(self)
    }
}

impl StackValue for CellBuilder {
    fn ty(&self) -> StackValueType {
        StackValueType::Builder
    }

    fn as_builder(&self) -> Option<&CellBuilder> {
        Some(self)
    }
}

impl StackValue for CellSliceParts {
    fn ty(&self) -> StackValueType {
        StackValueType::Slice
    }

    fn as_slice(&self) -> Option<&CellSliceParts> {
        Some(self)
    }
}

impl StackValue for Rc<dyn Continuation> {
    fn ty(&self) -> StackValueType {
        StackValueType::Cont
    }

    fn as_cont(&self) -> Option<&Rc<dyn Continuation>> {
        Some(self)
    }
}

impl StackValue for Vec<Rc<dyn StackValue>> {
    fn ty(&self) -> StackValueType {
        StackValueType::Tuple
    }

    fn as_tuple(&self) -> Option<&[Rc<dyn StackValue>]> {
        Some(self)
    }
}

pub trait Continuation {}

pub struct ControlRegs {
    pub c: [Rc<dyn Continuation>; Self::CONT_REG_COUNT],
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
    pub next: Rc<dyn Continuation>,
}

pub struct RepeatCont {
    pub count: u64,
    pub body: Rc<dyn Continuation>,
    pub after: Rc<dyn Continuation>,
}

pub struct AgainCont {
    pub body: Rc<dyn Continuation>,
}

pub struct UntilCont {
    pub body: Rc<dyn Continuation>,
    pub after: Rc<dyn Continuation>,
}

pub struct WhileCont {
    pub cont: Rc<dyn Continuation>,
    pub body: Rc<dyn Continuation>,
    pub after: Rc<dyn Continuation>,
    pub check_cond: bool,
}
