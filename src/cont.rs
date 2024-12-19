use std::rc::Rc;

use everscale_types::error::Error;
use everscale_types::prelude::*;
#[cfg(feature = "tracing")]
use tracing::instrument;

use crate::error::VmResult;
use crate::stack::{
    load_slice_as_stack_value, load_stack, load_stack_value, store_slice_as_stack_value,
    RcStackValue, Stack, StackValue, StackValueType, Tuple, TupleExt,
};
use crate::state::VmState;
use crate::util::{ensure_empty_slice, rc_ptr_eq, OwnedCellSlice, Uint4};

#[derive(Debug, Default, Clone)]
pub struct ControlData {
    pub nargs: Option<u16>,
    pub stack: Option<Rc<Stack>>,
    pub save: ControlRegs,
    pub cp: Option<u16>,
}

impl ControlData {
    pub fn require_nargs(&self, copy: usize) -> VmResult<()> {
        if matches!(self.nargs, Some(nargs) if (nargs as usize) < copy) {
            vm_bail!(StackUnderflow(copy as _))
        }
        Ok(())
    }
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

#[derive(Default, Debug, Clone)]
pub struct ControlRegs {
    pub c: [Option<RcCont>; 4],
    pub d: [Option<Cell>; 2],
    pub c7: Option<Rc<Tuple>>,
}

impl ControlRegs {
    const CONT_REG_COUNT: usize = 4;
    const DATA_REG_OFFSET: usize = Self::CONT_REG_COUNT;
    const DATA_REG_COUNT: usize = 2;
    const DATA_REG_RANGE: std::ops::Range<usize> =
        Self::DATA_REG_OFFSET..Self::DATA_REG_OFFSET + Self::DATA_REG_COUNT;

    pub fn is_valid_idx(i: usize) -> bool {
        i < Self::CONT_REG_COUNT || Self::DATA_REG_RANGE.contains(&i) || i == 7
    }

    pub fn merge(&mut self, other: &ControlRegs) {
        for (c, other_c) in std::iter::zip(&mut self.c, &other.c) {
            Self::merge_stack_value(c, other_c);
        }
        for (d, other_d) in std::iter::zip(&mut self.d, &other.d) {
            Self::merge_cell_value(d, other_d)
        }
        Self::merge_stack_value(&mut self.c7, &other.c7)
    }

    pub fn preclear(&mut self, other: &ControlRegs) {
        for (c, other_c) in std::iter::zip(&mut self.c, &other.c) {
            if other_c.is_some() {
                *c = None;
            }
        }
        for (d, other_d) in std::iter::zip(&mut self.d, &other.d) {
            if other_d.is_some() {
                *d = None;
            }
        }
        if other.c7.is_some() {
            self.c7 = None;
        }
    }

    // TODO: use `&dyn StackValue` for value?
    pub fn set(&mut self, i: usize, value: Rc<dyn StackValue>) -> VmResult<()> {
        if i < Self::CONT_REG_COUNT {
            self.c[i] = Some(ok!(value.into_cont()));
        } else if Self::DATA_REG_RANGE.contains(&i) {
            let cell = ok!(value.into_cell());
            self.d[i - Self::DATA_REG_OFFSET] = Some(Rc::unwrap_or_clone(cell));
        } else if i == 7 {
            self.c7 = Some(ok!(value.into_tuple()));
        } else {
            vm_bail!(ControlRegisterOutOfRange(i))
        }
        Ok(())
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

    pub fn get_d(&mut self, mut i: usize) -> Option<Cell> {
        i = i.wrapping_sub(Self::DATA_REG_OFFSET);
        if i < Self::DATA_REG_COUNT {
            self.d[i].clone()
        } else {
            None
        }
    }

    pub fn set_c7(&mut self, tuple: Rc<Tuple>) {
        self.c7 = Some(tuple);
    }

    pub fn get_as_stack_value(&self, i: usize) -> Option<Rc<dyn StackValue>> {
        if i < Self::CONT_REG_COUNT {
            self.c.get(i)?.clone().map(|cont| cont.into_stack_value())
        } else if Self::DATA_REG_RANGE.contains(&i) {
            self.d[i - Self::DATA_REG_OFFSET]
                .clone()
                .map(|cell| Rc::new(cell) as _)
        } else if i == 7 {
            self.c7.clone().map(|tuple| tuple.clone() as _)
        } else {
            None
        }
    }

    pub fn define_c0(&mut self, cont: &Option<RcCont>) {
        if self.c[0].is_none() {
            self.c[0].clone_from(cont)
        }
    }

    pub fn define_c1(&mut self, cont: &Option<RcCont>) {
        if self.c[1].is_none() {
            self.c[1].clone_from(cont)
        }
    }

    pub fn define_c2(&mut self, cont: &Option<RcCont>) {
        if self.c[2].is_none() {
            self.c[2].clone_from(cont)
        }
    }

    pub fn define(&mut self, i: usize, value: Rc<dyn StackValue>) -> VmResult<()> {
        if i < Self::CONT_REG_COUNT {
            let cont = ok!(value.into_cont());
            vm_ensure!(self.c[i].is_none(), ControlRegisterRedefined);
            self.c[i] = Some(cont);
        } else if Self::DATA_REG_RANGE.contains(&i) {
            let cell = ok!(value.into_cell());
            let d = &mut self.d[i - Self::DATA_REG_OFFSET];
            vm_ensure!(d.is_none(), ControlRegisterRedefined);
            *d = Some(Rc::unwrap_or_clone(cell));
        } else if i == 7 {
            let tuple = ok!(value.into_tuple());

            // NOTE: Value is ignored on redefinition
            if self.c7.is_none() {
                self.c7 = Some(tuple);
            }
        } else {
            vm_bail!(ControlRegisterOutOfRange(i))
        }
        Ok(())
    }

    pub fn get_c7_params(&self) -> VmResult<&[RcStackValue]> {
        let Some(c7) = self.c7.as_ref() else {
            vm_bail!(ControlRegisterOutOfRange(7))
        };

        c7.try_get_tuple_range(0, 0..=255)
    }

    fn merge_cell_value(lhs: &mut Option<Cell>, rhs: &Option<Cell>) {
        if let Some(rhs) = rhs {
            if let Some(lhs) = lhs {
                let lhs = lhs.as_ref() as *const _ as *const ();
                let rhs = rhs.as_ref() as *const _ as *const ();
                if std::ptr::eq(lhs, rhs) {
                    return;
                }
            }
            *lhs = Some(rhs.clone())
        }
    }

    fn merge_stack_value<T: ?Sized>(lhs: &mut Option<Rc<T>>, rhs: &Option<Rc<T>>) {
        if let Some(rhs) = rhs {
            if let Some(lhs) = lhs {
                if rc_ptr_eq(lhs, rhs) {
                    return;
                }
            }
            *lhs = Some(rhs.clone())
        }
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
                ok!(dict.set_ext(Uint4(i), AsDictValue(c.as_stack_value()), context));
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
        ok!(ensure_empty_slice(slice));
        if result.set(key.0, value).is_err() {
            return Err(Error::InvalidData);
        }
    }

    Ok(result)
}

pub type DynCont = dyn Cont;

pub trait Cont: Store + dyn_clone::DynClone + std::fmt::Debug {
    fn into_stack_value(self: Rc<Self>) -> Rc<dyn StackValue>;

    fn as_stack_value(&self) -> &dyn StackValue;

    fn jump(self: Rc<Self>, state: &mut VmState) -> VmResult<i32>;

    fn get_control_data(&self) -> Option<&ControlData> {
        None
    }

    fn get_control_data_mut(&mut self) -> Option<&mut ControlData> {
        None
    }
}

impl<T: Cont + 'static> StackValue for T {
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

pub type RcCont = Rc<DynCont>;

impl DynCont {
    pub fn has_c0(&self) -> bool {
        if let Some(control) = self.get_control_data() {
            control.save.c[0].is_some()
        } else {
            false
        }
    }
}

trait LoadWithContext<'a>: Sized {
    fn load_with_context(
        slice: &mut CellSlice<'_>,
        context: &mut dyn CellContext,
    ) -> Result<Self, Error>;
}

pub fn load_cont(slice: &mut CellSlice, context: &mut dyn CellContext) -> Result<RcCont, Error> {
    #[allow(clippy::unusual_byte_groupings)]
    const MASK: u64 = 0x1_007_01_1_1_0001_0001;

    // Prefetch slice prefix aligned to 6 bits
    let slice_bits = slice.size_bits();
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

#[derive(Debug, Copy, Clone)]
pub struct QuitCont {
    pub exit_code: i32,
}

impl QuitCont {
    const TAG: u8 = 0b1000;
}

impl Cont for QuitCont {
    fn into_stack_value(self: Rc<Self>) -> Rc<dyn StackValue> {
        self
    }

    fn as_stack_value(&self) -> &dyn StackValue {
        self
    }

    #[cfg_attr(
        feature = "tracing",
        instrument(level = "trace", name = "quit_cont", skip_all)
    )]
    fn jump(self: Rc<Self>, _: &mut VmState) -> VmResult<i32> {
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

#[derive(Debug, Copy, Clone)]
pub struct ExcQuitCont;

impl ExcQuitCont {
    const TAG: u8 = 0b1001;
}

impl Cont for ExcQuitCont {
    fn into_stack_value(self: Rc<Self>) -> Rc<dyn StackValue> {
        self
    }

    fn as_stack_value(&self) -> &dyn StackValue {
        self
    }

    #[cfg_attr(
        feature = "tracing",
        instrument(level = "trace", name = "exc_quit_cont", skip_all)
    )]
    fn jump(self: Rc<Self>, state: &mut VmState) -> VmResult<i32> {
        let n = Rc::make_mut(&mut state.stack)
            .pop_smallint_range(0, 0xffff)
            .unwrap_or_else(|e| e.as_exception() as u32);
        vm_log!(n, "terminating vm in the default exception handler");
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

#[derive(Debug, Clone)]
pub struct PushIntCont {
    pub value: i32,
    pub next: Rc<DynCont>,
}

impl PushIntCont {
    const TAG: u8 = 0b1111;
}

impl Cont for PushIntCont {
    fn into_stack_value(self: Rc<Self>) -> Rc<dyn StackValue> {
        self
    }

    fn as_stack_value(&self) -> &dyn StackValue {
        self
    }

    #[cfg_attr(
        feature = "tracing",
        instrument(
            level = "trace",
            name = "push_int_cont",
            fields(value = self.value),
            skip_all,
        )
    )]
    fn jump(self: Rc<Self>, state: &mut VmState) -> VmResult<i32> {
        ok!(Rc::make_mut(&mut state.stack).push_int(self.value));
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

#[derive(Debug, Clone)]
pub struct RepeatCont {
    pub count: u64,
    pub body: Rc<DynCont>,
    pub after: Rc<DynCont>,
}

impl RepeatCont {
    const TAG: u8 = 0b1010;
    const MAX_COUNT: u64 = 0x8000000000000000;
}

impl Cont for RepeatCont {
    fn into_stack_value(self: Rc<Self>) -> Rc<dyn StackValue> {
        self
    }

    fn as_stack_value(&self) -> &dyn StackValue {
        self
    }

    #[cfg_attr(
        feature = "tracing",
        instrument(
            level = "trace",
            name = "repeat_cont",
            fields(value = self.count),
            skip_all,
        )
    )]
    fn jump(mut self: Rc<Self>, state: &mut VmState) -> VmResult<i32> {
        if self.count == 0 {
            return state.jump(self.after.clone());
        }
        if self.body.has_c0() {
            return state.jump(self.body.clone());
        }

        let body = self.body.clone();
        match Rc::get_mut(&mut self) {
            Some(this) => {
                this.count -= 1;
                state.set_c0(self)
            }
            None => state.set_c0(Rc::new(RepeatCont {
                count: self.count - 1,
                body: self.body.clone(),
                after: self.after.clone(),
            })),
        }

        state.jump(body)
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

#[derive(Debug, Clone)]
pub struct AgainCont {
    pub body: Rc<DynCont>,
}

impl AgainCont {
    const TAG: u8 = 0b110001;
}

impl Cont for AgainCont {
    fn into_stack_value(self: Rc<Self>) -> Rc<dyn StackValue> {
        self
    }

    fn as_stack_value(&self) -> &dyn StackValue {
        self
    }

    #[cfg_attr(
        feature = "tracing",
        instrument(level = "trace", name = "again_cont", skip_all)
    )]
    fn jump(self: Rc<Self>, state: &mut VmState) -> VmResult<i32> {
        if !self.body.has_c0() {
            state.set_c0(self.clone())
        }
        state.jump(self.body.clone())
    }
}

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

#[derive(Debug, Clone)]
pub struct UntilCont {
    pub body: Rc<DynCont>,
    pub after: Rc<DynCont>,
}

impl UntilCont {
    const TAG: u8 = 0b110000;
}

impl Cont for UntilCont {
    fn into_stack_value(self: Rc<Self>) -> Rc<dyn StackValue> {
        self
    }

    fn as_stack_value(&self) -> &dyn StackValue {
        self
    }

    #[cfg_attr(
        feature = "tracing",
        instrument(level = "trace", name = "until_cont", skip_all)
    )]
    fn jump(self: Rc<Self>, state: &mut VmState) -> VmResult<i32> {
        vm_log!("until loop condition end");
        let terminated = ok!(Rc::make_mut(&mut state.stack).pop_bool());
        if terminated {
            vm_log!("until loop terminated");
            return state.jump(self.after.clone());
        }
        if !self.body.has_c0() {
            state.set_c0(self.clone());
        }
        state.jump(self.body.clone())
    }
}

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

#[derive(Debug, Clone)]
pub struct WhileCont {
    pub check_cond: bool,
    pub cond: Rc<DynCont>,
    pub body: Rc<DynCont>,
    pub after: Rc<DynCont>,
}

impl WhileCont {
    const TAG: u8 = 0b11001;
}

impl Cont for WhileCont {
    fn into_stack_value(self: Rc<Self>) -> Rc<dyn StackValue> {
        self
    }

    fn as_stack_value(&self) -> &dyn StackValue {
        self
    }

    #[cfg_attr(
        feature = "tracing",
        instrument(
            level = "trace",
            name = "while_cont",
            fields(check_cond = self.check_cond),
            skip_all,
        )
    )]
    fn jump(mut self: Rc<Self>, state: &mut VmState) -> VmResult<i32> {
        let next = if self.check_cond {
            vm_log!("while loop condition end");
            if !ok!(Rc::make_mut(&mut state.stack).pop_bool()) {
                vm_log!("while loop terminated");
                return state.jump(self.after.clone());
            }
            self.body.clone()
        } else {
            vm_log!("while loop body end");
            self.cond.clone()
        };

        if !next.has_c0() {
            match Rc::get_mut(&mut self) {
                Some(this) => {
                    this.check_cond = !this.check_cond;
                    state.set_c0(self);
                }
                None => state.set_c0(Rc::new(WhileCont {
                    check_cond: !self.check_cond,
                    cond: self.cond.clone(),
                    body: self.body.clone(),
                    after: self.after.clone(),
                })),
            }
        }

        state.jump(next)
    }
}

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

#[derive(Debug, Clone)]
pub struct ArgContExt {
    pub data: ControlData,
    pub ext: RcCont,
}

impl ArgContExt {
    const TAG: u8 = 0b01;
}

impl Cont for ArgContExt {
    fn into_stack_value(self: Rc<Self>) -> Rc<dyn StackValue> {
        self
    }

    fn as_stack_value(&self) -> &dyn StackValue {
        self
    }

    #[cfg_attr(
        feature = "tracing",
        instrument(level = "trace", name = "arg_cont", skip_all)
    )]
    fn jump(self: Rc<Self>, state: &mut VmState) -> VmResult<i32> {
        state.adjust_cr(&self.data.save);
        if let Some(cp) = self.data.cp {
            ok!(state.force_cp(cp));
        }

        let ext = match Rc::try_unwrap(self) {
            Ok(this) => this.ext,
            Err(this) => this.ext.clone(),
        };
        ext.jump(state)
    }

    fn get_control_data(&self) -> Option<&ControlData> {
        Some(&self.data)
    }

    fn get_control_data_mut(&mut self) -> Option<&mut ControlData> {
        Some(&mut self.data)
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

#[derive(Debug, Clone)]
pub struct OrdCont {
    pub data: ControlData,
    pub code: OwnedCellSlice,
}

impl OrdCont {
    const TAG: u8 = 0b00;

    pub fn simple(code: OwnedCellSlice, cp: u16) -> Self {
        Self {
            data: ControlData {
                cp: Some(cp),
                ..Default::default()
            },
            code,
        }
    }
}

impl Cont for OrdCont {
    fn into_stack_value(self: Rc<Self>) -> Rc<dyn StackValue> {
        self
    }

    fn as_stack_value(&self) -> &dyn StackValue {
        self
    }

    #[cfg_attr(
        feature = "tracing",
        instrument(level = "trace", name = "ord_cont", skip_all)
    )]
    fn jump(self: Rc<Self>, state: &mut VmState) -> VmResult<i32> {
        state.adjust_cr(&self.data.save);
        let Some(cp) = self.data.cp else {
            vm_bail!(InvalidOpcode);
        };
        ok!(state.set_code(self.code.clone(), cp));
        Ok(0)
    }

    fn get_control_data(&self) -> Option<&ControlData> {
        Some(&self.data)
    }

    fn get_control_data_mut(&mut self) -> Option<&mut ControlData> {
        Some(&mut self.data)
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
