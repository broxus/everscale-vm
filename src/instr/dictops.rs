use crate::error::{VmError, VmResult};
use crate::util::{ store_int_to_builder, OwnedCellSlice};
use crate::VmState;
use everscale_types::cell::{CellBuilder};
use everscale_types::error::Error;
use everscale_types::prelude::{Cell, CellFamily, Store};
use everscale_vm_proc::vm_module;
use std::fmt::Formatter;
use std::rc::Rc;
use everscale_types::dict;
use everscale_types::dict::{SetMode};
use crate::stack::{RcStackValue, StackValueType};

pub struct Dictops;

#[vm_module]
impl Dictops {
    #[instr(code = "f400", fmt = "STDICT")]
    fn exec_stdict(st: &mut VmState) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);

        let mut builder = ok!(stack.pop_builder());
        let cell = ok!(stack.pop_cell_opt());

        cell.store_into(Rc::make_mut(&mut builder), &mut Cell::empty_context())?;
        ok!(stack.push_raw(builder));
        Ok(0)
    }

    // #[instr(code = "f402", fmt = "LDDICT", args(preload = true, quite = false))]
    // //#[instr(code = "f402", fmt = "PLDDICT", args(preload = true, quite = true))]
    // //#[instr(code = "f402", fmt = "LDDICTQ", args(preload = true, quite = true))]
    // fn exec_load_dict(st: &mut VmState, preload: bool, quite: bool) -> VmResult<i32> {
    //     let stack = Rc::make_mut(&mut st.stack);
    //     let owned_cs = stack.pop_cs()?;
    //     let range = owned_cs.range();
    //     let mut cs = owned_cs.apply()?;
    //
    //     if !range.has_remaining(1, 0) {
    //         if !quite {
    //             vm_bail!(CellError(Error::CellUnderflow))
    //         }
    //         if !preload {
    //             ok!(stack.push_raw(owned_cs));
    //         }
    //     } else {
    //         if preload {
    //             let subslice = Rc::new(cs.get_prefix(1, !range.is_empty() as u8));
    //             ok!(stack.push_raw(subslice));
    //         } else {
    //             let mut bytes = Vec::new();
    //             let loaded = cs.load_raw(&mut bytes, 1)?;
    //             ok!(stack.push_raw(Rc::new(loaded)));
    //             ok!(stack.push_raw(Rc::new(cs)));
    //         }
    //     }
    //
    //     if quite {
    //         ok!(stack.push_bool(!range.is_empty()));
    //     };
    //
    //     Ok(0)
    // }

    #[instr(code = "f40s", range_from = "f40a", range_to = "f40f", fmt = ("{}", s.display()), args(s = DictOpArgs(args)))]
    fn exec_dict_get(st: &mut VmState, s: DictOpArgs) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let n = ok!(stack.pop_smallint_range(0, 1023)) as u16;
        let dict: Option<Rc<Cell>> = ok!(stack.pop_cell_opt());

        let key_slice;
        let mut builder;

        let key = if s.is_int() {
            let int = ok!(stack.pop_int());
            builder = CellBuilder::new();
            store_int_to_builder(&int, n, &mut builder)?;
            builder.as_data_slice()
        } else {
            key_slice = stack.pop_cs()?;
            key_slice.apply()?
        };

        let cs = everscale_types::dict::dict_get_owned(
            dict.as_deref(),
            n,
            key,
            &mut Cell::empty_context(),
        )?
            .map(OwnedCellSlice::from);

        if s.is_ref() {
            match cs {
                None => ok!(stack.push_bool(false)),
                Some(slice) => {
                    let slice = slice.apply()?;
                    let cell = slice.get_reference_cloned(0)?;
                    ok!(stack.push_raw(Rc::new(cell)));
                    ok!(stack.push_bool(true));
                }
            }
        } else {
            match cs {
                None => ok!(stack.push_bool(false)),
                Some(slice) => {
                    ok!(stack.push_raw(Rc::new(slice)));
                    ok!(stack.push_bool(true));
                }
            }
        };

        Ok(0)
    }

    #[instr(code = "f4ss", range_from = "f412", range_to = "f418", fmt = ("{}", format_dict_set("SET", s, bld)), args(s = DictOpArgs(args), mode = SetMode::Set, bld = false))]
    #[instr(code = "f4ss", range_from = "f432", range_to = "f438", fmt = ("{}", format_dict_set("SET", s, bld)), args(s = DictOpArgs(args), mode = SetMode::Set, bld = true))]
    #[instr(code = "f4ss", range_from = "f422", range_to = "f428", fmt = ("{}", format_dict_set("REPLACE", s, bld)), args(s = DictOpArgs(args), mode = SetMode::Replace, bld = false))]
    #[instr(code = "f4ss", range_from = "f449", range_to = "f44c", fmt = ("{}", format_dict_set("REPLACE", s, bld)), args(s = DictOpArgs(args), mode = SetMode::Replace, bld = true))]
    #[instr(code = "f4ss", range_from = "f441", range_to = "f444", fmt = ("{}", format_dict_set("ADD", s, bld)), args(s = DictOpArgs(args), mode = SetMode::Add, bld = false))]
    #[instr(code = "f4ss", range_from = "f451", range_to = "f454", fmt = ("{}", format_dict_set("ADD", s, bld)), args(s = DictOpArgs(args), mode = SetMode::Add, bld = true))]
    fn exec_dict_set(st: &mut VmState, s: DictOpArgs, mode: SetMode, bld: bool) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let n = ok!(stack.pop_smallint_range(0, 1023)) as u16;
        let dict: Option<Rc<Cell>> = ok!(stack.pop_cell_opt());

        let key_slice;
        let mut builder;

        let mut key = if s.is_int() {
            let int = ok!(stack.pop_int());
            builder = CellBuilder::new();
            store_int_to_builder(&int, n, &mut builder)?;
            builder.as_data_slice()
        } else {
            key_slice = stack.pop_cs()?;
            key_slice.apply()?
        };

        if key.is_empty() {
            vm_bail!(CellError(Error::CellUnderflow))
        }

        let value: RcStackValue = ok!(stack.pop());
        let value_slice;


        let value_ref: &dyn Store = match (bld, s.is_ref()) {
            (true, _) => {
                match value.as_builder() {
                    Some(builder) => {
                        value_slice = builder.as_full_slice();
                        &value_slice as &dyn Store
                    }
                    None => vm_bail!(InvalidType {expected: StackValueType::Builder, actual: value.ty() })
                }
            }
            (false, false) => {
                match value.as_slice() {
                    Some(slice) => {
                        value_slice = slice.apply()?;
                        &value_slice as &dyn Store
                    }
                    None => vm_bail!(InvalidType {expected: StackValueType::Slice, actual: value.ty() })
                }
            }
            _ => {
                match value.as_cell() {
                    Some(cell) => cell as &dyn Store,
                    None => vm_bail!(InvalidType {expected: StackValueType::Cell, actual: value.ty() })
                }
            }
        };

        let result = everscale_types::dict::dict_insert(
            &mut dict.as_deref().cloned(),
            &mut key,
            n,
            value_ref,
            mode,
            &mut Cell::empty_context(),
        );

        let Some(dict) = dict else {
            vm_bail!(CellError(Error::CellUnderflow)) //TODO: proper error?
        };

        ok!(stack.push_raw(dict));

        match mode {
            SetMode::Set => {
                if result.is_err() {
                    return Err(Box::new(VmError::CellError(Error::InvalidCell)));
                }
            }
            _ => ok!(stack.push_bool(result.is_ok()))
        }

        Ok(0)
    }

    #[instr(code = "f4ss", range_from = "f41a", range_to = "f420", fmt = ("{}", format_dict_set("SETGET", s, bld)), args(s = DictOpArgs(args), mode = SetMode::Set, bld = false))]
    #[instr(code = "f4ss", range_from = "f445", range_to = "f448", fmt = ("{}", format_dict_set("SETGET", s, bld)), args(s = DictOpArgs(args), mode = SetMode::Set, bld = true))]
    #[instr(code = "f4ss", range_from = "f42a", range_to = "f430", fmt = ("{}", format_dict_set("REPLACEGET", s, bld)), args(s = DictOpArgs(args), mode = SetMode::Replace, bld = false))]
    #[instr(code = "f4ss", range_from = "f44d", range_to = "f450", fmt = ("{}", format_dict_set("REPLACEGET", s, bld)), args(s = DictOpArgs(args), mode = SetMode::Replace, bld = true))]
    #[instr(code = "f4ss", range_from = "f43a", range_to = "f440", fmt = ("{}", format_dict_set("ADDGET", s, bld)), args(s = DictOpArgs(args), mode = SetMode::Add, bld = false))]
    #[instr(code = "f4ss", range_from = "f455", range_to = "f458", fmt = ("{}", format_dict_set("ADDGET", s, bld)), args(s = DictOpArgs(args), mode = SetMode::Add, bld = true))]
    fn exec_dict_set_get(st: &mut VmState, s: DictOpArgs, mode: SetMode, bld: bool) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let n = ok!(stack.pop_smallint_range(0, 1023)) as u16;
        let dict: Option<Rc<Cell>> = ok!(stack.pop_cell_opt());

        let key_slice;
        let mut builder;

        let mut key = if s.is_int() {
            let int = ok!(stack.pop_int());
            builder = CellBuilder::new();
            store_int_to_builder(&int, n, &mut builder)?;
            builder.as_data_slice()
        } else {
            key_slice = stack.pop_cs()?;
            key_slice.apply()?
        };

        if key.is_empty() {
            return Err(Box::new(VmError::CellError(Error::CellUnderflow)));
        }

        let is_not_add = match mode {
            SetMode::Add => false,
            _ => true
        };

        let value: RcStackValue = ok!(stack.pop());
        let value_slice;

        let value_ref: &dyn Store = match (bld, s.is_ref()) {
            (true, _) => {
                match value.as_builder() {
                    Some(builder) => {
                        value_slice = builder.as_full_slice();
                        &value_slice as &dyn Store
                    }
                    None => vm_bail!(InvalidType {expected: StackValueType::Builder, actual: value.ty() })
                }
            }
            (false, false) => {
                match value.as_slice() {
                    Some(slice) => {
                        value_slice = slice.apply()?;
                        &value_slice as &dyn Store
                    }
                    None => vm_bail!(InvalidType {expected: StackValueType::Slice, actual: value.ty() })
                }
            }
            _ => {
                match value.as_cell() {
                    Some(cell) => cell as &dyn Store,
                    None => vm_bail!(InvalidType {expected: StackValueType::Cell, actual: value.ty() })
                }
            }
        };

        let (_, prev) = dict::dict_insert_owned(&mut dict.as_deref().cloned(), &mut key, n, value_ref, mode, &mut Cell::empty_context())?;
        if let Some(dict) = dict {
            ok!(stack.push_raw(dict));
        };

        if let Some(prev) = prev {
            ok!(stack.push_raw(Rc::new(prev.0)));
            ok!(stack.push_bool(is_not_add));
        } else {
            ok!(stack.push_bool(!is_not_add));
        }

        Ok(0)
    }

    #[instr(code = "f4ss", range_from = "f459", range_to = "f45c", fmt = ("{}", format_dict_delete("DEL", s)), args(s = DictOpArgs(args)))]
    fn exec_dict_delete(st: &mut VmState, s: DictOpArgs) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let n = ok!(stack.pop_smallint_range(0, 1023)) as u16;
        let dict: Option<Rc<Cell>> = ok!(stack.pop_cell_opt());


        let key_slice;
        let mut builder;

        let mut key = if s.is_int() {
            let int = ok!(stack.pop_int());
            builder = CellBuilder::new();
            store_int_to_builder(&int, n, &mut builder)?;
            let key = builder.as_data_slice();
            if key.is_empty() {
                match dict {
                    Some(dict) => ok!(stack.push_raw(dict)),
                    None => ok!(stack.push_null()), //TODO: do we need to push null here?
                }
                ok!(stack.push_int(0));
                return Ok(0)
            }
            key
        } else {
            key_slice = stack.pop_cs()?;
            key_slice.apply()?
        };

        let result = dict::dict_remove_owned(
            &mut dict.as_deref().cloned(),
            &mut key,
            n,
            true,
            &mut Cell::empty_context()
        )?;
        match dict {
            Some(dict) => ok!(stack.push_raw(dict)),
            None => ok!(stack.push_null()), //TODO: do we need to push null here?
        }
        ok!(stack.push_bool(result.is_some()));

        Ok(0)
    }


    #[instr(code = "f4ss", range_from = "f462", range_to = "f468", fmt = ("{}", format_dict_delete("DELGET", s)), args(s = DictOpArgs(args)))]
    fn exec_dict_deleteget(st: &mut VmState, s: DictOpArgs) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let n = ok!(stack.pop_smallint_range(0, 1023)) as u16;
        let dict: Option<Rc<Cell>> = ok!(stack.pop_cell_opt());


        let key_slice;
        let mut builder;

        let mut key = if s.is_int() {
            let int = ok!(stack.pop_int());
            builder = CellBuilder::new();
            store_int_to_builder(&int, n, &mut builder)?;
            let key = builder.as_data_slice();
            if key.is_empty() {
                match dict {
                    Some(dict) => ok!(stack.push_raw(dict)),
                    None => ok!(stack.push_null()), //TODO: do we need to push null here?
                }
                ok!(stack.push_int(0));
                return Ok(0)
            }
            key
        } else {
            key_slice = stack.pop_cs()?;
            key_slice.apply()?
        };

        let result = dict::dict_remove_owned(
            &mut dict.as_deref().cloned(),
            &mut key,
            n,
            true,
            &mut Cell::empty_context()
        )?;

        match dict {
            Some(dict) => ok!(stack.push_raw(dict)),
            None => ok!(stack.push_null()), //TODO: do we need to push null here?
        }

        if !s.is_ref() {
            let is_ok = result.is_some();
            if let Some(res) = result {
                ok!(stack.push_raw(Rc::new(res.0)));
            }
            ok!(stack.push_bool(is_ok));

        } else {
            let is_ok = result.is_some();
            if let Some(res) = result {
                if res.0.reference_count() != 1 {
                    vm_bail!(CellError(Error::InvalidCell))
                }

                let Some(cell) = res.0.reference_cloned(0) else {
                    vm_bail!(CellError(Error::InvalidCell))
                };
                ok!(stack.push_raw(Rc::new(cell)));
            }

            ok!(stack.push_bool(is_ok));
        }

        Ok(0)
    }


}

struct DictOpArgs(u32);

impl DictOpArgs {
    pub fn is_unsigned(&self) -> bool {
        self.0 & 0b010 != 0
    }

    pub fn is_int(&self) -> bool {
        self.0 & 0b100 != 0
    }

    pub fn is_ref(&self) -> bool {
        self.0 & 0b001 != 0
    }

    fn display(&self) -> DisplayDictOpArgs {
        DisplayDictOpArgs(self.0)
    }
}

struct DisplayDictOpArgs(u32);
impl std::fmt::Display for DisplayDictOpArgs {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let args = DictOpArgs(self.0);
        let is_unsigned = if args.is_unsigned() { "U" } else { "I" };
        let is_int = if args.is_int() { is_unsigned } else { "" };
        let is_ref = if args.is_ref() { "REF" } else { "" };

        write!(f, "DICT{is_int}GET{is_ref}")
    }
}

fn format_dict_set(name: &str, args: DictOpArgs, bld: bool ) -> String {
    let is_unsigned = if args.is_unsigned() { "U" } else { "I" };
    let is_int = if args.is_int() { is_unsigned } else { "" };
    let is_bld = if bld {"B"} else {""};
    let is_ref = if args.is_ref() { "REF" } else { is_bld };

    format!("DICT{is_int}{name}{is_ref}")
}

fn format_dict_delete(name: &str, args: DictOpArgs ) -> String {
    let is_unsigned = if args.is_unsigned() { "U" } else { "I" };
    let is_int = if args.is_int() { is_unsigned } else { "" };
    let is_ref = if args.is_ref() { "REF" } else { "" };
    format!("DICT{is_int}{name}{is_ref}")
}


