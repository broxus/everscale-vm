use std::rc::Rc;

use everscale_types::dict::DictKey;
use everscale_types::error::Error;
use everscale_types::prelude::*;

use crate::stack::{store_slice_as_stack_value, RcStackValue, Stack, StackValue};
use crate::util::OwnedCellSlice;

pub trait Cont: Store {}

pub type RcCont = Rc<dyn Cont>;

pub fn load_cont(slice: &mut CellSlice, context: &mut dyn CellContext) -> Result<RcCont, Error> {
    todo!()
}

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
        store_slice_as_stack_value(&self.code, builder)
    }
}
