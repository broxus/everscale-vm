use std::rc::Rc;

use anyhow::Result;
use everscale_types::error::Error;
use everscale_types::prelude::*;

use crate::error::VmException;
use crate::stack::{
    load_slice_as_stack_value, load_stack, load_stack_value, store_slice_as_stack_value,
    RcStackValue, Stack, StackValue,
};
use crate::state::VmState;
use crate::util::{ensure_empty_slice, OwnedCellSlice, Uint4};

#[derive(Debug)]
pub struct ControlData {
    pub nargs: Option<u16>,
    pub stack: Option<Rc<Stack>>,
    pub save: ControlRegs,
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

fn load_control_data(
    slice: &mut CellSlice,
    context: &mut dyn CellContext,
) -> Result<ControlData, Error> {
    Ok(ControlData {
        nargs: match ok!(slice.load_bit()) {
            false => None,
            true => Some(ok!(slice.load_uint(13)) as u16),
        },
        stack: match ok!(slice.load_bit()) {
            false => None,
            true => Some(ok!(load_stack(slice, context).map(Rc::new))),
        },
        save: ok!(load_control_regs(slice, context)),
        cp: ok!(Load::load_from(slice)),
    })
}

#[derive(Default, Debug)]
pub struct ControlRegs {
    pub c: [Option<RcCont>; 4],
    pub d: [Option<Cell>; 2],
    pub c7: Option<Rc<Vec<RcStackValue>>>,
}

impl ControlRegs {
    const CONT_REG_COUNT: usize = 4;
    const DATA_REG_OFFSET: usize = Self::CONT_REG_COUNT;
    const DATA_REG_COUNT: usize = 2;

    // TODO: use `&dyn StackValue` for value?
    pub fn set(&mut self, i: usize, value: Rc<dyn StackValue>) -> bool {
        if i < Self::CONT_REG_COUNT {
            if let Some(cont) = value.as_cont() {
                self.c[i] = Some(cont.clone());
                return true;
            }
        } else if i >= Self::DATA_REG_OFFSET && i < Self::DATA_REG_OFFSET + Self::DATA_REG_COUNT {
            if let Some(cell) = value.as_cell() {
                self.d[i - Self::DATA_REG_OFFSET] = Some(cell.clone());
                return true;
            }
        } else if i == 7 {
            // TODO: add `as_tuple_ref` to `StackValue`?
            if let Ok(tuple) = value.into_tuple() {
                self.c7 = Some(tuple);
                return true;
            }
        }

        false
    }

    pub fn set_c(&mut self, i: usize, cont: RcCont) -> bool {
        if i < Self::CONT_REG_COUNT {
            self.c[i] = Some(cont);
            true
        } else {
            false
        }
    }

    pub fn set_d(&mut self, mut i: usize, cell: Cell) -> bool {
        i = i.wrapping_sub(Self::DATA_REG_OFFSET);
        if i < Self::DATA_REG_COUNT {
            self.d[i] = Some(cell);
            true
        } else {
            false
        }
    }

    pub fn set_c7(&mut self, tuple: Rc<Vec<RcStackValue>>) {
        self.c7 = Some(tuple);
    }
}

impl Store for ControlRegs {
    fn store_into(
        &self,
        builder: &mut CellBuilder,
        context: &mut dyn CellContext,
    ) -> Result<(), Error> {
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

fn load_control_regs(
    slice: &mut CellSlice,
    context: &mut dyn CellContext,
) -> Result<ControlRegs, Error> {
    let dict = ok!(Dict::<Uint4, CellSlice<'_>>::load_from(slice));

    let mut result = ControlRegs::default();
    for entry in dict.iter() {
        let (key, ref mut slice) = ok!(entry);
        let value = ok!(load_stack_value(slice, context));
        ok!(ensure_empty_slice(&slice));
        if !result.set(key.0, value) {
            return Err(Error::InvalidData);
        }
    }

    Ok(result)
}

pub trait Cont: Store + std::fmt::Debug {
    fn jump(self: Rc<Self>, state: &mut VmState) -> Result<i32>;

    fn get_control_data(&self) -> Option<&ControlData> {
        None
    }
}

pub type RcCont = Rc<dyn Cont>;

trait LoadWithContext<'a>: Sized {
    fn load_with_context(
        slice: &mut CellSlice<'_>,
        context: &mut dyn CellContext,
    ) -> Result<Self, Error>;
}

pub fn load_cont(slice: &mut CellSlice, context: &mut dyn CellContext) -> Result<RcCont, Error> {
    const MASK: u64 = 0x1_007_01_1_1_0001_0001;

    // Prefetch slice prefix aligned to 6 bits
    let slice_bits = slice.remaining_bits();
    let n = if slice_bits < 6 {
        ok!(slice.get_small_uint(0, slice_bits)) << (6 - slice_bits)
    } else {
        ok!(slice.get_small_uint(0, 6))
    };

    // Count ones in first N bits of mask
    let n = (MASK & (2u64 << n).wrapping_sub(1)).count_ones() - 1;

    // Match bit count with tag ranges
    Ok(match n {
        // 00xxxx -> 0 (16)
        0 => Rc::new(ok!(OrdCont::load_with_context(slice, context))),
        // 01xxxx -> 1 (16)
        1 => Rc::new(ok!(ArgContExt::load_with_context(slice, context))),
        // 1000xx -> 2 (4)
        2 => Rc::new(ok!(QuitCont::load_with_context(slice, context))),
        // 1001xx -> 3 (4)
        3 => Rc::new(ok!(ExcQuitCont::load_with_context(slice, context))),
        // 10100x -> 4 (2)
        4 => Rc::new(ok!(RepeatCont::load_with_context(slice, context))),
        // 110000 -> 5 (1)
        5 => Rc::new(ok!(UntilCont::load_with_context(slice, context))),
        // 110001 -> 6 (1)
        6 => Rc::new(ok!(AgainCont::load_with_context(slice, context))),
        // 11001x -> 7 (2)
        7 => Rc::new(ok!(WhileCont::load_with_context(slice, context))),
        // 1111xx -> 8 (4)
        8 => Rc::new(ok!(PushIntCont::load_with_context(slice, context))),
        // all other
        _ => return Err(Error::InvalidTag),
    })
}

#[derive(Debug)]
pub struct QuitCont {
    pub exit_code: i32,
}

impl QuitCont {
    const TAG: u8 = 0b1000;
}

impl Cont for QuitCont {
    fn jump(self: Rc<Self>, state: &mut VmState) -> Result<i32> {
        Ok(!self.exit_code)
    }
}

impl Store for QuitCont {
    fn store_into(&self, builder: &mut CellBuilder, _: &mut dyn CellContext) -> Result<(), Error> {
        ok!(builder.store_small_uint(Self::TAG, 4));
        builder.store_u32(self.exit_code as u32)
    }
}

impl LoadWithContext<'_> for QuitCont {
    fn load_with_context(
        slice: &mut CellSlice<'_>,
        _: &mut dyn CellContext,
    ) -> Result<Self, Error> {
        if ok!(slice.load_small_uint(4)) != Self::TAG {
            return Err(Error::InvalidTag);
        }

        Ok(Self {
            exit_code: ok!(slice.load_u32()) as i32,
        })
    }
}

#[derive(Debug)]
pub struct ExcQuitCont;

impl ExcQuitCont {
    const TAG: u8 = 0b1001;
}

impl Cont for ExcQuitCont {
    fn jump(self: Rc<Self>, state: &mut VmState) -> Result<i32> {
        let n = state
            .stack
            .pop_smallint_range(0, 0xffff)
            .unwrap_or_else(|e| VmException::from(e) as u32);
        Ok(!(n as i32))
    }
}

impl Store for ExcQuitCont {
    fn store_into(&self, builder: &mut CellBuilder, _: &mut dyn CellContext) -> Result<(), Error> {
        builder.store_small_uint(Self::TAG, 4)
    }
}

impl LoadWithContext<'_> for ExcQuitCont {
    #[inline]
    fn load_with_context(
        slice: &mut CellSlice<'_>,
        _: &mut dyn CellContext,
    ) -> Result<Self, Error> {
        if ok!(slice.load_small_uint(4)) == Self::TAG {
            Ok(Self)
        } else {
            Err(Error::InvalidTag)
        }
    }
}

#[derive(Debug)]
pub struct PushIntCont {
    pub value: i32,
    pub next: Rc<dyn Cont>,
}

impl PushIntCont {
    const TAG: u8 = 0b1111;
}

impl Cont for PushIntCont {
    fn jump(mut self: Rc<Self>, state: &mut VmState) -> Result<i32> {
        ok!(state.stack.push_int(self.value));
        state.jump(match Rc::try_unwrap(self) {
            Ok(this) => this.next,
            Err(this) => this.next.clone(),
        })
    }
}

impl Store for PushIntCont {
    fn store_into(
        &self,
        builder: &mut CellBuilder,
        context: &mut dyn CellContext,
    ) -> Result<(), Error> {
        ok!(builder.store_small_uint(Self::TAG, 4));
        ok!(builder.store_u32(self.value as u32));
        builder.store_reference(ok!(CellBuilder::build_from_ext(&self.next, context)))
    }
}

impl LoadWithContext<'_> for PushIntCont {
    fn load_with_context(
        slice: &mut CellSlice<'_>,
        context: &mut dyn CellContext,
    ) -> Result<Self, Error> {
        if ok!(slice.load_small_uint(4)) != Self::TAG {
            return Err(Error::InvalidTag);
        }

        Ok(Self {
            value: ok!(slice.load_u32()) as i32,
            next: ok!(load_cont(slice, context)),
        })
    }
}

#[derive(Debug)]
pub struct RepeatCont {
    pub count: u64,
    pub body: Rc<dyn Cont>,
    pub after: Rc<dyn Cont>,
}

impl RepeatCont {
    const TAG: u8 = 0b1010;
    const MAX_COUNT: u64 = 0x8000000000000000;
}

impl Cont for RepeatCont {
    fn jump(self: Rc<Self>, state: &mut VmState) -> Result<i32> {
        match Rc::try_unwrap(self) {
            Ok(this) => {
                if this.count <= 0 {
                    return state.jump(this.after);
                }
            }
        }
    }
}

impl Store for RepeatCont {
    fn store_into(
        &self,
        builder: &mut CellBuilder,
        context: &mut dyn CellContext,
    ) -> Result<(), Error> {
        if self.count >= Self::MAX_COUNT {
            return Err(Error::IntOverflow);
        }
        ok!(builder.store_small_uint(Self::TAG, 4));
        ok!(builder.store_u64(self.count));
        ok!(builder.store_reference(ok!(CellBuilder::build_from_ext(&self.body, context))));
        builder.store_reference(ok!(CellBuilder::build_from_ext(&self.after, context)))
    }
}

impl LoadWithContext<'_> for RepeatCont {
    fn load_with_context(
        slice: &mut CellSlice<'_>,
        context: &mut dyn CellContext,
    ) -> Result<Self, Error> {
        if ok!(slice.load_small_uint(4)) != Self::TAG {
            return Err(Error::InvalidTag);
        }

        Ok(Self {
            count: ok!(slice.load_u64()),
            body: ok!(load_cont(slice, context)),
            after: ok!(load_cont(slice, context)),
        })
    }
}

#[derive(Debug)]
pub struct AgainCont {
    pub body: Rc<dyn Cont>,
}

impl AgainCont {
    const TAG: u8 = 0b110001;
}

impl Cont for AgainCont {}

impl Store for AgainCont {
    fn store_into(
        &self,
        builder: &mut CellBuilder,
        context: &mut dyn CellContext,
    ) -> Result<(), Error> {
        ok!(builder.store_small_uint(Self::TAG, 6));
        builder.store_reference(ok!(CellBuilder::build_from_ext(&self.body, context)))
    }
}

impl LoadWithContext<'_> for AgainCont {
    fn load_with_context(
        slice: &mut CellSlice<'_>,
        context: &mut dyn CellContext,
    ) -> Result<Self, Error> {
        if ok!(slice.load_small_uint(6)) != Self::TAG {
            return Err(Error::InvalidTag);
        }

        Ok(Self {
            body: ok!(load_cont(slice, context)),
        })
    }
}

#[derive(Debug)]
pub struct UntilCont {
    pub body: Rc<dyn Cont>,
    pub after: Rc<dyn Cont>,
}

impl UntilCont {
    const TAG: u8 = 0b110000;
}

impl Cont for UntilCont {}

impl Store for UntilCont {
    fn store_into(
        &self,
        builder: &mut CellBuilder,
        context: &mut dyn CellContext,
    ) -> Result<(), Error> {
        ok!(builder.store_small_uint(Self::TAG, 6));
        ok!(builder.store_reference(ok!(CellBuilder::build_from_ext(&self.body, context))));
        builder.store_reference(ok!(CellBuilder::build_from_ext(&self.after, context)))
    }
}

impl LoadWithContext<'_> for UntilCont {
    fn load_with_context(
        slice: &mut CellSlice<'_>,
        context: &mut dyn CellContext,
    ) -> Result<Self, Error> {
        if ok!(slice.load_small_uint(6)) != Self::TAG {
            return Err(Error::InvalidTag);
        }

        Ok(Self {
            body: ok!(load_cont(slice, context)),
            after: ok!(load_cont(slice, context)),
        })
    }
}

#[derive(Debug)]
pub struct WhileCont {
    pub check_cond: bool,
    pub cond: Rc<dyn Cont>,
    pub body: Rc<dyn Cont>,
    pub after: Rc<dyn Cont>,
}

impl WhileCont {
    const TAG: u8 = 0b11001;
}

impl Cont for WhileCont {}

impl Store for WhileCont {
    fn store_into(
        &self,
        builder: &mut CellBuilder,
        context: &mut dyn CellContext,
    ) -> Result<(), Error> {
        let tag = (Self::TAG << 1) | !self.check_cond as u8;
        ok!(builder.store_small_uint(tag, 6));
        ok!(builder.store_reference(ok!(CellBuilder::build_from_ext(&self.cond, context))));
        ok!(builder.store_reference(ok!(CellBuilder::build_from_ext(&self.body, context))));
        builder.store_reference(ok!(CellBuilder::build_from_ext(&self.after, context)))
    }
}

impl LoadWithContext<'_> for WhileCont {
    fn load_with_context(
        slice: &mut CellSlice<'_>,
        context: &mut dyn CellContext,
    ) -> Result<Self, Error> {
        if ok!(slice.load_small_uint(5)) != Self::TAG {
            return Err(Error::InvalidTag);
        }

        Ok(Self {
            check_cond: ok!(slice.load_bit()),
            cond: ok!(load_cont(slice, context)),
            body: ok!(load_cont(slice, context)),
            after: ok!(load_cont(slice, context)),
        })
    }
}

#[derive(Debug)]
pub struct ArgContExt {
    pub data: ControlData,
    pub ext: RcCont,
}

impl ArgContExt {
    const TAG: u8 = 0b01;
}

impl Cont for ArgContExt {
    fn jump(mut self: Rc<Self>, state: &mut VmState) -> Result<i32> {
        // TODO: set control regs and codepage
        let ext = match Rc::try_unwrap(self) {
            Ok(this) => this.ext,
            Err(this) => this.ext.clone(),
        };
        ext.jump(state)
    }

    fn get_control_data(&self) -> Option<&ControlData> {
        Some(&self.data)
    }
}

impl Store for ArgContExt {
    fn store_into(
        &self,
        builder: &mut CellBuilder,
        context: &mut dyn CellContext,
    ) -> Result<(), Error> {
        ok!(builder.store_small_uint(Self::TAG, 2));
        self.ext.store_into(builder, context)
    }
}

impl LoadWithContext<'_> for ArgContExt {
    fn load_with_context(
        slice: &mut CellSlice<'_>,
        context: &mut dyn CellContext,
    ) -> Result<Self, Error> {
        if ok!(slice.load_small_uint(2)) != Self::TAG {
            return Err(Error::InvalidTag);
        }

        Ok(Self {
            data: ok!(load_control_data(slice, context)),
            ext: ok!(load_cont(slice, context)),
        })
    }
}

#[derive(Debug)]
pub struct OrdCont {
    pub data: ControlData,
    pub code: OwnedCellSlice,
}

impl OrdCont {
    const TAG: u8 = 0b00;
}

impl Cont for OrdCont {
    fn jump(self: Rc<Self>, state: &mut VmState) -> Result<i32> {
        // TODO: adjust control regs
        Ok(0)
    }

    fn get_control_data(&self) -> Option<&ControlData> {
        Some(&self.data)
    }
}

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

impl LoadWithContext<'_> for OrdCont {
    fn load_with_context(
        slice: &mut CellSlice<'_>,
        context: &mut dyn CellContext,
    ) -> Result<Self, Error> {
        if ok!(slice.load_small_uint(2)) != Self::TAG {
            return Err(Error::InvalidTag);
        }

        Ok(Self {
            data: ok!(load_control_data(slice, context)),
            code: ok!(load_slice_as_stack_value(slice, context)),
        })
    }
}
