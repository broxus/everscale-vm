use crate::error::{VmError, VmResult};
use crate::stack::{RcStackValue, StackValueType};
use crate::util::{load_int_from_slice, store_int_to_builder, OwnedCellSlice};
use crate::VmState;
use everscale_types::cell::{CellBuilder, CellSlice};
use everscale_types::dict::{DictBound, SetMode};
use everscale_types::error::Error;
use everscale_types::prelude::{Cell, CellFamily, Store};
use everscale_vm_proc::vm_module;
use num_bigint::{BigInt, BigUint, Sign};
use std::fmt::Formatter;
use std::rc::Rc;

pub struct Dictops;

#[vm_module]
impl Dictops {
    #[instr(code = "f400", fmt = "STDICT")]
    fn exec_stdict(st: &mut VmState) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);

        let mut builder = ok!(stack.pop_builder());
        let cell: Option<Rc<Cell>> = ok!(stack.pop_cell_opt());

        cell.store_into(Rc::make_mut(&mut builder), &mut Cell::empty_context())?;
        ok!(stack.push_raw(builder));
        Ok(0)
    }

    #[instr(code = "f401", fmt = "SKIPDICT")]
    fn exec_skip_dict(st: &mut VmState) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let mut owned_cs: Rc<OwnedCellSlice> = ok!(stack.pop_cs());
        let cs = owned_cs.apply()?;
        if cs.is_empty() {
            vm_bail!(CellError(Error::CellUnderflow))
        }

        let prefix = cs.get_prefix(1, cs.size_refs());
        let subslice = cs.strip_data_prefix(&prefix);

        match subslice {
            Some(ss) => {
                let new_range = ss.range();
                Rc::make_mut(&mut owned_cs).set_range(new_range);
                ok!(stack.push_raw(owned_cs))
            }
            None => ok!(stack.push_raw(owned_cs)),
        }

        Ok(0)
    }

    #[instr(code = "f404", fmt = "LDDICT", args(preload = false, quite = false))]
    #[instr(code = "f405", fmt = "PLDDICT", args(preload = true, quite = false))]
    #[instr(code = "f406", fmt = "LDDICTQ", args(preload = false, quite = true))]
    #[instr(code = "f407", fmt = "PLDDICTQ", args(preload = true, quite = true))]
    fn exec_load_dict(st: &mut VmState, preload: bool, quite: bool) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let mut owned_cs = stack.pop_cs()?;
        let range = owned_cs.range();
        let is_empty = range.is_empty();
        let mut cs = owned_cs.apply()?;

        if is_empty {
            if !quite {
                vm_bail!(CellError(Error::CellUnderflow))
            }
            if !preload {
                ok!(stack.push_raw(owned_cs));
            }
        } else {
            let cell_opt = if range.size_refs() > 0 {
                cs.get_reference_cloned(0).ok()
            } else {
                None
            };
            ok!(stack.push_opt(cell_opt));

            if !preload {
                let prefix = cs.get_prefix(1, range.size_refs());
                let subslice = cs.strip_data_prefix(&prefix);

                match subslice {
                    Some(ss) => {
                        let new_range = ss.range();
                        Rc::make_mut(&mut owned_cs).set_range(new_range);
                        ok!(stack.push_raw(owned_cs))
                    }
                    None => ok!(stack.push_raw(owned_cs)),
                }
            }
        }

        if quite {
            ok!(stack.push_bool(!is_empty));
        };

        Ok(0)
    }

    #[instr(code = "f40s", range_from = "f40a", range_to = "f40f", fmt = ("{}", s.display()), args(s = DictOpArgs::new("GET", args)))]
    fn exec_dict_get(st: &mut VmState, s: DictOpArgs) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let n = ok!(stack.pop_smallint_range(0, 1023)) as u16;
        let dict: Option<Rc<Cell>> = ok!(stack.pop_cell_opt());

        let key_slice;
        let mut builder;

        let key = if s.is_int() {
            let int = ok!(stack.pop_int());
            ok!(check_key_sign(s.is_unsigned(), int.clone()));
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

    #[instr(code = "f4ss", range_from = "f412", range_to = "f418", fmt = ("{}", s.display()), args(s = DictOpArgs::new("SET", args), mode = SetMode::Set))]
    #[instr(code = "f4ss", range_from = "f432", range_to = "f438", fmt = ("{}", s.display()), args(s = DictOpArgs::new_bld("SET", args), mode = SetMode::Set))]
    #[instr(code = "f4ss", range_from = "f422", range_to = "f428", fmt = ("{}", s.display()), args(s = DictOpArgs::new("REPLACE", args), mode = SetMode::Replace))]
    #[instr(code = "f4ss", range_from = "f449", range_to = "f44c", fmt = ("{}", s.display()), args(s = DictOpArgs::new_bld("REPLACE", args), mode = SetMode::Replace))]
    #[instr(code = "f4ss", range_from = "f441", range_to = "f444", fmt = ("{}", s.display()), args(s = DictOpArgs::new("ADD", args), mode = SetMode::Add))]
    #[instr(code = "f4ss", range_from = "f451", range_to = "f454", fmt = ("{}", s.display()), args(s = DictOpArgs::new_bld("ADD", args), mode = SetMode::Add))]
    fn exec_dict_set(st: &mut VmState, s: DictOpArgs, mode: SetMode) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let n = ok!(stack.pop_smallint_range(0, 1023)) as u16;
        let dict: Option<Rc<Cell>> = ok!(stack.pop_cell_opt());

        let key_slice;
        let mut builder;

        let mut key = if s.is_int() {
            let int = ok!(stack.pop_int());
            ok!(check_key_sign(s.is_unsigned(), int.clone()));
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

        let value_ref: &dyn Store = match (s.is_bld, s.is_ref()) {
            (true, _) => match value.as_builder() {
                Some(builder) => {
                    value_slice = builder.as_full_slice();
                    &value_slice as &dyn Store
                }
                None => vm_bail!(InvalidType {
                    expected: StackValueType::Builder,
                    actual: value.ty()
                }),
            },
            (false, false) => match value.as_slice() {
                Some(slice) => {
                    value_slice = slice.apply()?;
                    &value_slice as &dyn Store
                }
                None => vm_bail!(InvalidType {
                    expected: StackValueType::Slice,
                    actual: value.ty()
                }),
            },
            _ => match value.as_cell() {
                Some(cell) => cell as &dyn Store,
                None => vm_bail!(InvalidType {
                    expected: StackValueType::Cell,
                    actual: value.ty()
                }),
            },
        };

        let mut dict = dict.as_deref().cloned();

        let result = everscale_types::dict::dict_insert(
            &mut dict,
            &mut key,
            n,
            value_ref,
            mode,
            &mut Cell::empty_context(),
        );

        ok!(stack.push_opt(dict));

        match mode {
            SetMode::Set => {
                if result.is_err() {
                    return Err(Box::new(VmError::CellError(Error::InvalidCell)));
                }
            }
            _ => ok!(stack.push_bool(result.is_ok())),
        }

        Ok(0)
    }

    #[instr(code = "f4ss", range_from = "f41a", range_to = "f420", fmt = ("{}", s.display()), args(s = DictOpArgs::new("SETGET", args), mode = SetMode::Set))]
    #[instr(code = "f4ss", range_from = "f445", range_to = "f448", fmt = ("{}", s.display()), args(s = DictOpArgs::new_bld("SETGET", args), mode = SetMode::Set))]
    #[instr(code = "f4ss", range_from = "f42a", range_to = "f430", fmt = ("{}", s.display()), args(s = DictOpArgs::new("REPLACEGET", args), mode = SetMode::Replace))]
    #[instr(code = "f4ss", range_from = "f44d", range_to = "f450", fmt = ("{}", s.display()), args(s = DictOpArgs::new_bld("REPLACEGET", args), mode = SetMode::Replace))]
    #[instr(code = "f4ss", range_from = "f43a", range_to = "f440", fmt = ("{}", s.display()), args(s = DictOpArgs::new("ADDGET", args), mode = SetMode::Add))]
    #[instr(code = "f4ss", range_from = "f455", range_to = "f458", fmt = ("{}", s.display()), args(s = DictOpArgs::new_bld("ADDGET", args), mode = SetMode::Add))]
    fn exec_dict_setget(st: &mut VmState, s: DictOpArgs, mode: SetMode) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let n = ok!(stack.pop_smallint_range(0, 1023)) as u16;
        let dict: Option<Rc<Cell>> = ok!(stack.pop_cell_opt());

        let key_slice;
        let mut builder;

        let mut key = if s.is_int() {
            let int = ok!(stack.pop_int());
            ok!(check_key_sign(s.is_unsigned(), int.clone()));
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
            _ => true,
        };

        let value: RcStackValue = ok!(stack.pop());
        let value_slice;

        let value_ref: &dyn Store = match (s.is_bld, s.is_ref()) {
            (true, _) => match value.as_builder() {
                Some(builder) => {
                    value_slice = builder.as_full_slice();
                    &value_slice as &dyn Store
                }
                None => vm_bail!(InvalidType {
                    expected: StackValueType::Builder,
                    actual: value.ty()
                }),
            },
            (false, false) => match value.as_slice() {
                Some(slice) => {
                    value_slice = slice.apply()?;
                    &value_slice as &dyn Store
                }
                None => vm_bail!(InvalidType {
                    expected: StackValueType::Slice,
                    actual: value.ty()
                }),
            },
            _ => match value.as_cell() {
                Some(cell) => cell as &dyn Store,
                None => vm_bail!(InvalidType {
                    expected: StackValueType::Cell,
                    actual: value.ty()
                }),
            },
        };

        let (_, prev) = everscale_types::dict::dict_insert_owned(
            &mut dict.as_deref().cloned(),
            &mut key,
            n,
            value_ref,
            mode,
            &mut Cell::empty_context(),
        )?;
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

    #[instr(code = "f4ss", range_from = "f459", range_to = "f45c", fmt = ("{}", s.display()), args(s = DeleteOpArgs(args)))]
    fn exec_dict_delete(st: &mut VmState, s: DeleteOpArgs) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let n = ok!(stack.pop_smallint_range(0, 1023)) as u16;
        let dict: Option<Rc<Cell>> = ok!(stack.pop_cell_opt());
        let mut dict = dict.as_deref().cloned();

        let key_slice;
        let mut builder;

        let mut key = if s.is_int() {
            let int: Rc<BigInt> = ok!(stack.pop_int());
            ok!(check_key_sign(s.is_unsigned(), int.clone()));
            builder = CellBuilder::new();
            store_int_to_builder(&int, n, &mut builder)?;
            let key = builder.as_data_slice();
            if key.is_empty() {
                ok!(stack.push_opt(dict));
                ok!(stack.push_int(0));
                return Ok(0);
            }
            key
        } else {
            key_slice = stack.pop_cs()?;
            println!("slice {:?}", key_slice);
            key_slice.apply()?
        };

        let result = everscale_types::dict::dict_remove_owned(
            &mut dict,
            &mut key,
            n,
            true,
            &mut Cell::empty_context(),
        )?;
        ok!(stack.push_opt(dict));
        ok!(stack.push_bool(result.is_some()));

        Ok(0)
    }

    #[instr(code = "f4ss", range_from = "f462", range_to = "f468", fmt = ("{}", s.display()), args(s = DictOpArgs::new("DELGET", args)))]
    fn exec_dict_deleteget(st: &mut VmState, s: DictOpArgs) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let n = ok!(stack.pop_smallint_range(0, 1023)) as u16;
        let dict: Option<Rc<Cell>> = ok!(stack.pop_cell_opt());

        let key_slice;
        let mut builder;

        let mut key = if s.is_int() {
            let int = ok!(stack.pop_int());
            ok!(check_key_sign(s.is_unsigned(), int.clone()));
            builder = CellBuilder::new();
            store_int_to_builder(&int, n, &mut builder)?;
            let key = builder.as_data_slice();
            if key.is_empty() {
                match dict {
                    Some(dict) => ok!(stack.push_raw(dict)),
                    None => vm_bail!(StackUnderflow(1)),
                }
                ok!(stack.push_int(0));
                return Ok(0);
            }
            key
        } else {
            key_slice = stack.pop_cs()?;
            key_slice.apply()?
        };

        let mut dict = dict.as_deref().cloned();

        let result = everscale_types::dict::dict_remove_owned(
            &mut dict,
            &mut key,
            n,
            false,
            &mut Cell::empty_context(),
        )?;

        match dict {
            Some(dict) => ok!(stack.push_raw(Rc::new(dict))),
            None => vm_bail!(StackUnderflow(1)),
        }

        if !s.is_ref() {
            let is_ok = result.is_some();
            if let Some(res) = result {
                let mut slice = OwnedCellSlice::from(res.0);
                slice.set_range(res.1);
                ok!(stack.push_raw(Rc::new(slice)));
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

    #[instr(code = "f4ss", range_from = "f469", range_to = "f46c", fmt = ("{}", s.display()), args(s = DictOpArgs::new("GETOPTREF", args)))]
    fn exec_dict_get_optref(st: &mut VmState, s: DictOpArgs) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let n = ok!(stack.pop_smallint_range(0, 1023)) as u16;
        let dict: Option<Rc<Cell>> = ok!(stack.pop_cell_opt());

        let key_slice;
        let mut builder;

        let key = if s.is_int() {
            let int = ok!(stack.pop_int());
            ok!(check_key_sign(s.is_unsigned(), int.clone()));
            builder = CellBuilder::new();
            if let Err(e) = store_int_to_builder(&int, n, &mut builder) {
                //vm_log!(e);
                ok!(stack.push_null());
                return Ok(0);
            }
            Ok(builder.as_data_slice())
        } else {
            key_slice = stack.pop_cs()?;
            key_slice.apply()
        };

        let key = match key {
            Ok(key) => key,
            Err(e) => vm_bail!(CellError(e)),
        };

        let cs = everscale_types::dict::dict_get_owned(
            dict.as_deref(),
            n,
            key,
            &mut Cell::empty_context(),
        )?
        .map(OwnedCellSlice::from);

        match cs {
            None => vm_bail!(CellError(Error::CellUnderflow)),
            Some(slice) => {
                let slice = slice.apply()?;
                if slice.size_refs() != 1 {
                    vm_bail!(CellError(Error::InvalidData))
                }
                let cell = slice.get_reference_cloned(0).ok();
                ok!(stack.push_opt(cell));
            }
        }
        Ok(0)
    }
    #[instr(code = "f4ss", range_from = "f46d", range_to = "f470", fmt = ("{}", s.display()), args(s = DictOpArgs::new("SETGETOPTREF", args)))]
    fn exec_dict_setget_optref(st: &mut VmState, s: DictOpArgs) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let n = ok!(stack.pop_smallint_range(0, 1023)) as u16;
        let dict: Option<Rc<Cell>> = ok!(stack.pop_cell_opt());

        let key_slice;
        let mut builder;

        let key = if s.is_int() {
            let int = ok!(stack.pop_int());
            ok!(check_key_sign(s.is_unsigned(), int.clone()));
            builder = CellBuilder::new();
            store_int_to_builder(&int, n, &mut builder).map(|_| builder.as_data_slice())
        } else {
            key_slice = stack.pop_cs()?;
            key_slice.apply()
        };

        let mut key = match key {
            Ok(key) => key,
            Err(e) => vm_bail!(CellError(e)),
        };

        let mut dict = dict.as_deref().cloned();

        let new_value = ok!(stack.pop_cell_opt());
        let value = match new_value {
            Some(cell) => everscale_types::dict::dict_insert_owned(
                &mut dict,
                &mut key,
                n,
                &cell,
                SetMode::Set,
                &mut Cell::empty_context(),
            )
            .map(|res| res.1)?,
            None => everscale_types::dict::dict_remove_owned(
                &mut dict,
                &mut key,
                n,
                false,
                &mut Cell::empty_context(),
            )?,
        };
        match dict {
            Some(dict) => {
                ok!(stack.push_raw(Rc::new(dict)));
                ok!(stack.push_opt(value.map(|x| x.0)));
            }
            None => vm_bail!(CellError(Error::InvalidData)),
        }

        Ok(0)
    }

    #[instr(code = "f470", fmt = "PFXDICTSET", args(mode = SetMode::Set))]
    #[instr(code = "f471", fmt = "PFXDICTREPLACE", args(mode = SetMode::Replace))]
    #[instr(code = "f472", fmt = "PFXDICTADD", args(mode = SetMode::Add))]
    fn exec_pfx_dict_set(st: &mut VmState, mode: SetMode) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let n = ok!(stack.pop_smallint_range(0, 1023)) as u16;
        let dict: Option<Rc<Cell>> = ok!(stack.pop_cell_opt());

        let key_slice_owned = ok!(stack.pop_cs());
        let mut key_slice = key_slice_owned.apply()?;

        let new_value = ok!(stack.pop_cs());
        let mut dict = dict.as_deref().cloned();
        let (result, _) = everscale_types::dict::dict_insert_owned(
            &mut dict,
            &mut key_slice,
            n,
            &new_value.apply()?,
            mode,
            &mut Cell::empty_context(),
        )?;
        ok!(stack.push_opt(dict));
        ok!(stack.push_bool(result));
        Ok(0)
    }

    #[instr(code = "f473", fmt = "PFXDICTDEL")]
    fn exec_pfx_dict_delete(st: &mut VmState) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let n = ok!(stack.pop_smallint_range(0, 1023)) as u16;
        let dict: Option<Rc<Cell>> = ok!(stack.pop_cell_opt());

        let key_slice_owned: Rc<OwnedCellSlice> = ok!(stack.pop_cs());
        let mut key_slice = key_slice_owned.apply()?;
        let mut dict = dict.as_deref().cloned();
        let res = everscale_types::dict::dict_remove_owned(
            &mut dict,
            &mut key_slice,
            n,
            false,
            &mut Cell::empty_context(),
        )?;
        ok!(stack.push_opt(dict));
        ok!(stack.push_bool(res.is_some()));
        Ok(0)
    }

    #[instr(code = "f4ss", range_from = "f482", range_to = "f488", fmt = ("{}", s.display()), args(s = DictOpArgs::new("MIN", args)))]
    #[instr(code = "f4ss", range_from = "f48a", range_to = "f490", fmt = ("{}", s.display()), args(s = DictOpArgs::new("MAX", args)))]
    #[instr(code = "f4ss", range_from = "f492", range_to = "f498", fmt = ("{}", s.display()), args(s = DictOpArgs::new("REMMIN", args)))]
    #[instr(code = "f4ss", range_from = "f49a", range_to = "f4a0", fmt = ("{}", s.display()), args(s = DictOpArgs::new("REMMAX", args)))]
    fn exec_dict_get_min(st: &mut VmState, s: DictOpArgs) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);

        let max_key_bytes = match (s.is_int(), s.is_unsigned()) {
            (true, true) => 256,
            (true, false) => 257,
            _ => 1023,
        };

        let n = ok!(stack.pop_smallint_range(0, max_key_bytes)) as u16;
        let dict: Option<Rc<Cell>> = ok!(stack.pop_cell_opt());
        let mut dict_deref = dict.as_deref().cloned();

        let bound = if s.is_max() {
            DictBound::Max
        } else {
            DictBound::Min
        };

        let mut found_key: CellBuilder;

        let key_value_opt = if s.is_rem() {
            everscale_types::dict::dict_remove_bound_owned(
                &mut dict_deref,
                n,
                bound,
                s.is_signed(),
                &mut Cell::empty_context(),
            )?
        } else {
            everscale_types::dict::dict_find_bound_owned(
                dict_deref.as_ref(),
                n,
                bound,
                s.is_signed(),
                &mut Cell::empty_context(),
            )?
        };

        if s.is_rem() {
            ok!(stack.push_opt(dict_deref));
        }

        if let Some((key, value)) = key_value_opt {
            found_key = key;

            if !s.is_ref() {
                let mut slice = OwnedCellSlice::from(value.0);

                slice.set_range(value.1);
                //println!("{}", slice.cell().display_data());
                ok!(stack.push_raw(Rc::new(slice)));
            } else {
                if value.0.reference_count() != 1 {
                    vm_bail!(CellError(Error::InvalidCell))
                }
                let cell = value.0.reference_cloned(0).unwrap();
                ok!(stack.push_raw(Rc::new(cell)));
            }
        } else {
            ok!(stack.push_bool(false));
            return Ok(0);
        }

        if s.is_int() {
            let int = load_int_from_slice(&mut found_key.as_full_slice(), n, s.is_signed())?;
            ok!(stack.push_int(int));
        } else {
            let cell = found_key.build()?;
            ok!(stack.push_raw(Rc::new(OwnedCellSlice::from(cell))));
        }

        ok!(stack.push_bool(true));
        Ok(0)
    }

    #[instr(code = "f4ss", range_from = "f474", range_to = "f480", fmt = ("{}", s.display()), args(s = DictTraverseArgs::new("GET", args)))]
    fn exec_dict_get_near(st: &mut VmState, s: DictTraverseArgs) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);

        let max_key_bytes = match (s.is_int(), s.is_unsigned()) {
            (true, true) => 256,
            (true, false) => 257,
            _ => 1023,
        };

        let n = ok!(stack.pop_smallint_range(0, max_key_bytes)) as u16;
        let dict: Option<Rc<Cell>> = ok!(stack.pop_cell_opt());
        let mut dict_deref = dict.as_deref().cloned();

        let towards = if s.is_prev() {
            DictBound::Min
        } else {
            DictBound::Max
        };

        if !s.is_int() {
            let slice: Rc<OwnedCellSlice> = ok!(stack.pop_cs());
            let key_slice = slice.apply()?;

            let nearest = everscale_types::dict::dict_find_owned(
                dict_deref.as_ref(),
                n,
                key_slice,
                towards,
                s.is_eq(),
                s.is_signed(),
                &mut Cell::empty_context(),
            )?;

            match nearest {
                None => {
                    ok!(stack.push_bool(false));
                    return Ok(0);
                }
                Some((key, (value_cell, _))) => {
                    ok!(stack.push_raw(Rc::new(OwnedCellSlice::from(value_cell))));
                    let key_cell = key.build()?;
                    ok!(stack.push_raw(Rc::new(OwnedCellSlice::from(key_cell))));
                }
            };
        } else {
            let int = ok!(stack.pop_int());
            ok!(check_key_sign(s.is_unsigned(), int.clone()));
            let mut builder = CellBuilder::new();
            let result = match store_int_to_builder(&int, n, &mut builder)
                .map(|_| builder.as_data_slice())
            {
                Ok(key) => everscale_types::dict::dict_find_owned(
                    dict_deref.as_ref(),
                    n,
                    key,
                    towards,
                    s.is_eq(),
                    s.is_signed(),
                    &mut Cell::empty_context(),
                )?,
                Err(Error::IntOverflow) => {
                    let backwards = match towards {
                        DictBound::Max => DictBound::Min,
                        DictBound::Min => DictBound::Max,
                    };
                    everscale_types::dict::dict_find_bound_owned(
                        dict_deref.as_ref(),
                        n,
                        backwards,
                        s.is_signed(),
                        &mut Cell::empty_context(),
                    )?
                }
                Err(e) => vm_bail!(CellError(e)),
            };

            if let Some((key, (value_cell, _))) = result {
                ok!(stack.push_raw(Rc::new(OwnedCellSlice::from(value_cell))));
                let key_cell = key.build()?;
                ok!(stack.push_raw(Rc::new(OwnedCellSlice::from(key_cell))));
            } else {
                ok!(stack.push_bool(false));
                return Ok(0);
            }
        }
        ok!(stack.push_bool(true));
        Ok(0)
    }
    fn exec_subdict_get(st: &mut VmState, s: SubdictOpArgs) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let n = ok!(stack.pop_smallint_range(0, 1023));
        let dict: Option<Rc<Cell>> = ok!(stack.pop_cell_opt());
        let mut dict_deref = dict.as_deref().cloned();

        let mk = match (s.is_int(), s.is_unsigned()) {
            (true, true) => 256,
            (true, false) => 257,
            _ => 1023,
        };
        let k = ok!(stack.pop_smallint_range(0, std::cmp::min(mk, n))) as u16;

        let key_slice;
        let mut builder;

        let mut key = if s.is_int() {
            let int = ok!(stack.pop_int());
            ok!(check_key_sign(s.is_unsigned(), int.clone()));
            builder = CellBuilder::new();
            store_int_to_builder(&int, k, &mut builder).map(|_| builder.as_data_slice())?
        } else {
            key_slice = stack.pop_cs()?;
            key_slice.apply()?
        };

        let subdict = everscale_types::dict::dict_get_subdict(
            dict_deref.as_ref(),
            k,
            &mut key,
            &mut Cell::empty_context(),
        )?;
        ok!(stack.push_opt(subdict));

        Ok(0)
    }

    fn check_key_sign(is_unsigned: bool, int: Rc<BigInt>) -> VmResult<i32> {
        match (is_unsigned, int.sign()) {
            (true, Sign::Minus) => {
                vm_bail!(IntegerOutOfRange {
                    min: 0,
                    max: u32::MAX as isize,
                    actual: int.to_string()
                })
            }
            _ => Ok(0),
        }
    }
}

struct DictOpArgs {
    name: String,
    args: u32,
    is_bld: bool,
}

impl DictOpArgs {
    pub fn new(name: &str, args: u32) -> Self {
        Self {
            name: name.to_string(),
            args,
            is_bld: false,
        }
    }

    pub fn new_bld(name: &str, args: u32) -> Self {
        Self {
            name: name.to_string(),
            args,
            is_bld: true,
        }
    }

    pub fn new_internal(name: &str, args: u32, is_bld: bool) -> Self {
        Self {
            name: name.to_string(),
            args,
            is_bld,
        }
    }

    pub fn is_unsigned(&self) -> bool {
        self.args & 0b010 != 0
    }

    pub fn is_signed(&self) -> bool {
        !self.is_unsigned()
    }

    pub fn is_int(&self) -> bool {
        self.args & 0b100 != 0
    }

    pub fn is_ref(&self) -> bool {
        self.args & 0b001 != 0
    }

    pub fn is_max(&self) -> bool {
        self.args & 0b1000 != 0
    }

    pub fn is_rem(&self) -> bool {
        self.args & 0b100000 != 0
    }

    fn display(&self) -> DisplayDictOpArgs {
        DisplayDictOpArgs {
            args: self.args,
            name: self.name.to_string(),
            is_bld: self.is_bld,
        }
    }

    fn displa_delete(&self) -> DisplayDictOpArgs {
        DisplayDictOpArgs {
            args: self.args,
            name: self.name.to_string(),
            is_bld: self.is_bld,
        }
    }
}

struct DisplayDictOpArgs {
    args: u32,
    name: String,
    is_bld: bool,
}
impl std::fmt::Display for DisplayDictOpArgs {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let args = DictOpArgs::new_internal(&self.name, self.args, self.is_bld);
        let is_unsigned = if args.is_unsigned() { "U" } else { "I" };
        let is_int = if args.is_int() { is_unsigned } else { "" };
        let is_bld = if args.is_bld { "B" } else { "" };
        let is_ref = if args.is_ref() { "REF" } else { is_bld };

        write!(f, "DICT{is_int}{}{is_ref}", args.name)
    }
}

struct DictTraverseArgs {
    name: String,
    args: u32,
}

impl DictTraverseArgs {
    pub fn new(name: &str, args: u32) -> Self {
        Self {
            name: name.to_string(),
            args,
        }
    }
    pub fn is_prev(&self) -> bool {
        self.args & 0b010 != 0
    }

    pub fn is_signed(&self) -> bool {
        !self.is_unsigned()
    }

    pub fn is_unsigned(&self) -> bool {
        self.args & 0b100 != 0
    }

    pub fn is_eq(&self) -> bool {
        self.args & 0b001 != 0
    }

    pub fn is_int(&self) -> bool {
        self.args & 0b1000 != 0
    }

    fn display(&self) -> DisplayDictTraverseArgs {
        DisplayDictTraverseArgs {
            args: self.args,
            name: self.name.to_string(),
        }
    }
}

struct DisplayDictTraverseArgs {
    args: u32,
    name: String,
}
impl std::fmt::Display for DisplayDictTraverseArgs {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let args = DictTraverseArgs::new(&self.name, self.args);
        let is_unsigned = if args.is_unsigned() { "U" } else { "I" };
        let is_int = if args.is_int() { is_unsigned } else { "" };
        let is_eq = if args.is_eq() { "EQ\n" } else { "\n" };
        let is_prev = if args.is_prev() { "PREV" } else { "NEXT" };

        write!(f, "DICT{is_int}{}{is_prev}{is_eq}", args.name)
    }
}

struct SubdictOpArgs {
    args: u32,
    name: String,
}

impl SubdictOpArgs {
    pub fn is_unsigned(&self) -> bool {
        self.args & 0b001 != 0
    }

    pub fn is_int(&self) -> bool {
        self.args & 0b010 != 0
    }

    pub fn is_rp(&self) -> bool {
        self.args & 0b100 != 0
    }
}

struct DeleteOpArgs(u32);

impl DeleteOpArgs {
    pub fn is_unsigned(&self) -> bool {
        self.0 & 0b001 != 0
    }

    pub fn is_int(&self) -> bool {
        self.0 & 0b010 != 0
    }

    pub fn display(&self) -> DisplayDeleteOpArgs {
        DisplayDeleteOpArgs { args: self.0 }
    }
}

struct DisplayDeleteOpArgs {
    args: u32,
}

impl std::fmt::Display for DisplayDeleteOpArgs {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let args = DeleteOpArgs(self.args);
        let is_unsigned = if args.is_unsigned() { "U" } else { "I" };
        let is_int = if args.is_int() { is_unsigned } else { "" };

        write!(f, "DICT{is_int}DEL")
    }
}

#[cfg(test)]
pub mod tests {
    use crate::cont::load_cont;
    use crate::stack::RcStackValue;
    use crate::util::OwnedCellSlice;
    use everscale_types::cell::{CellBuilder, CellSliceRange};
    use everscale_types::dict::{DictKey, SetMode};
    use everscale_types::prelude::{Cell, CellFamily, Dict, Store};
    use everscale_vm::stack::StackValue;
    use everscale_vm::util::store_int_to_builder;
    use num_bigint::{BigInt, Sign};
    use num_traits::One;
    use std::rc::Rc;
    use tracing_test::traced_test;

    #[test]
    #[traced_test]
    fn stdict_tests() {
        let init_builder: RcStackValue = Rc::new(CellBuilder::new());
        let mut dict = everscale_types::dict::Dict::<u32, u32>::new();
        dict.add(1, 1).unwrap();
        let dictionary: Rc<Cell> = Rc::new(dict.clone().into_root().unwrap());

        let mavalue: RcStackValue = Rc::new({
            let mut builder = CellBuilder::new();
            dict.store_into(&mut builder, &mut Cell::empty_context())
                .unwrap();
            builder
        });

        assert_run_vm!(
            r#"
                STDICT
            "#,
            [raw dictionary, raw init_builder.clone()] => [raw mavalue],
        );

        let mavalue: RcStackValue = Rc::new({
            let mut builder = CellBuilder::new();
            builder.store_bit_zero().unwrap();
            builder
        });

        assert_run_vm!(
            r#"
                STDICT
            "#,
            [null, raw init_builder.clone()] => [raw mavalue],
        );
    }

    // #[test]
    // #[traced_test]
    // fn skipdict_tests() {
    //    let dict = build_dict::<u32, u32, _>(|dict| {
    //        dict.add(1, 1)?;
    //        Ok(())
    //    });
    //
    //     assert_run_vm!(
    //         r#"
    //             SKIPDICT
    //         "#,
    //         [raw dict.clone()] => [raw dict],
    //     );
    // }

    #[test]
    #[traced_test]
    fn get_dict_tests() {
        let dict = build_dict::<u32, u32, _>(|dict| {
            dict.add(1, 1)?;
            Ok(())
        });

        let key_len: RcStackValue = make_int_key_len();
        let int: RcStackValue = make_int_stack_key(1);
        let another_int: RcStackValue = make_new_int_value(3);

        let mut builder = CellBuilder::new();
        store_int_to_builder(&BigInt::one(), int_kbl(), &mut builder).unwrap();
        let result: RcStackValue = Rc::new(builder.build().unwrap());

        assert_run_vm!(
            r#"
                DICTIGET
                SWAP NEWC STSLICE ENDC
                SWAP
            "#,
            [raw int, raw dict.clone(), raw key_len.clone()] => [raw result, int -1],
        );

        assert_run_vm!(
            r#"
                DICTIGET
            "#,
            [raw another_int, raw dict.clone(), raw key_len.clone()] => [int 0],
        );
    }

    #[test]
    #[traced_test]
    fn set_dict_tests() {
        let dict_value = build_dict::<u32, u32, _>(|dict| {
            dict.set(1, 1)?;
            Ok(())
        });
        let new_slice_value = make_new_slice_value(3);
        let new_cell_value = make_new_cell(3);
        let stack_key: RcStackValue = make_int_stack_key(1);
        let key_len: RcStackValue = make_int_key_len();

        let result_dict = build_dict::<u32, u32, _>(|dict| {
            dict.set(1, 3)?;
            Ok(())
        });

        let result_dict_ref = build_dict::<u32, Cell, _>(|dict| {
            dict.add(1, new_cell_value.clone())?;
            Ok(())
        });

        assert_run_vm!(
            r#"
                DICTISET
            "#,
            [raw new_slice_value.clone(), raw stack_key.clone(), raw dict_value.clone(), raw key_len.clone()] => [raw result_dict.clone()],
        );

        assert_run_vm!(
            r#"
                DICTISETREF
            "#,
            [raw Rc::new(new_cell_value), raw stack_key, raw dict_value.clone(), raw key_len.clone()] => [raw result_dict_ref],
        );
    }

    #[test]
    #[traced_test]
    fn delete_dict_tests() {
        let key_len: RcStackValue = make_int_key_len();

        let dict_value = build_dict::<i32, i32, _>(|dict| {
            dict.set(-1, 1)?;
            dict.set(-2, 2)?;
            Ok(())
        });

        let result_dict = build_dict::<i32, i32, _>(|dict| {
            dict.set(-1, 1)?;
            Ok(())
        });

        {
            let stack_slice_key: RcStackValue = make_slice_stack_key(-2);
            let another_slice_key: RcStackValue = make_slice_stack_key(3);

            assert_run_vm!("DICTDEL",
                [raw stack_slice_key.clone(), raw dict_value.clone(), raw key_len.clone()] => [raw result_dict.clone(), int -1],
            );

            assert_run_vm!("DICTDEL",
                [raw another_slice_key.clone(), raw dict_value.clone(), raw key_len.clone()] => [raw dict_value.clone(), int 0],
            );
        }

        {
            let stack_int_key: RcStackValue = make_int_stack_key(-2);
            let another_int_key: RcStackValue = make_int_stack_key(3);

            assert_run_vm!("DICTIDEL",
                [raw another_int_key.clone(), raw dict_value.clone(), raw key_len.clone()] => [raw dict_value.clone(), int 0],
            );

            assert_run_vm!("DICTIDEL",
                [raw stack_int_key.clone(), raw dict_value.clone(), raw key_len.clone()] => [raw result_dict.clone(), int -1],
            );

            assert_run_vm!("DICTUDEL",
                [raw stack_int_key.clone(), raw dict_value.clone(), raw key_len.clone()] => [int 0],
                exit_code: 5
            );
        }
    }

    #[test]
    #[traced_test]
    fn delete_dictget_tests() {
        let key_len: RcStackValue = make_int_key_len();
        let dict_value = build_dict::<i32, i32, _>(|dict| {
            dict.set(1, 1)?;
            dict.set(-2, 2)?;
            Ok(())
        });

        let result_dict = build_dict::<i32, i32, _>(|dict| {
            dict.set(1, 1)?;
            Ok(())
        });

        let mut builder = CellBuilder::new();
        store_int_to_builder(&BigInt::from(2), int_kbl(), &mut builder).unwrap();
        let removed_value: RcStackValue = Rc::new(builder.build().unwrap());

        {
            let stack_slice_key: RcStackValue = make_slice_stack_key(-2);
            let another_slice_key: RcStackValue = make_slice_stack_key(3);

            assert_run_vm!(r#"
                DICTDELGET
                SWAP
                XCHG s1, s2
                NEWC STSLICE ENDC
                XCHG s1, s2
                SWAP
            "#,
                [raw stack_slice_key.clone(), raw dict_value.clone(), raw key_len.clone()] => [raw result_dict.clone(), raw removed_value.clone(), int -1],
            );

            assert_run_vm!(r#"
                DICTDELGET
            "#,
                [raw another_slice_key.clone(), raw dict_value.clone(), raw key_len.clone()] => [raw dict_value.clone(), int 0],
            );
        }

        {
            let stack_slice_key: RcStackValue = make_int_stack_key(-2);
            let another_slice_key: RcStackValue = make_int_stack_key(3);

            let result_dict = build_dict::<i32, i32, _>(|dict| {
                dict.set(1, 1)?;
                Ok(())
            });

            assert_run_vm!(r#"
                DICTIDELGET
                SWAP
                XCHG s1, s2
                NEWC STSLICE ENDC
                XCHG s1, s2
                SWAP
            "#,
                [raw stack_slice_key.clone(), raw dict_value.clone(), raw key_len.clone()] => [raw result_dict.clone(), raw removed_value, int -1],
            );
        }
    }

    #[test]
    #[traced_test]
    fn get_min_max_tests() {
        let key_len: RcStackValue = make_int_key_len();
        let dict_value = build_dict::<i32, i32, _>(|dict| {
            dict.set(1, 1)?;
            dict.set(2, 2)?;
            dict.set(3, 3)?;
            Ok(())
        });

        let mut builder = CellBuilder::new();
        store_int_to_builder(&BigInt::from(1), int_kbl(), &mut builder).unwrap();
        let value: RcStackValue = Rc::new(builder.build().unwrap());

        assert_run_vm!(r#"
                DICTMIN
            "#,
            [raw dict_value.clone(), raw key_len.clone()] => [raw value.clone(), raw value.clone(), int -1],
        );
    }

    fn int_dict_to_cell(dict: Dict<u32, u32>) -> Cell {
        dict.clone().into_root().unwrap()
    }

    const fn int_kbl() -> u16 {
        32
    }

    fn make_int_key_len() -> RcStackValue {
        Rc::new(BigInt::from(int_kbl()))
    }

    fn int_key_slice<const N: u16, T>(arg: T) -> OwnedCellSlice
    where
        T: Into<BigInt>,
    {
        let mut builder = CellBuilder::new();
        store_int_to_builder(&arg.into(), N, &mut builder).unwrap();
        builder.build().unwrap().into()
    }

    fn make_slice_stack_key(value: i32) -> RcStackValue {
        make_new_slice_value(value)
    }
    fn make_int_stack_key(value: i32) -> RcStackValue {
        Rc::new(BigInt::from(value))
    }

    fn make_int_key() -> BigInt {
        BigInt::one()
    }

    fn make_value() -> RcStackValue {
        Rc::new(BigInt::from(2))
    }

    fn make_new_slice_value(value: i32) -> RcStackValue {
        let value = BigInt::from(value);
        let mut builder = CellBuilder::new();
        store_int_to_builder(&value, 32, &mut builder).unwrap();
        Rc::new(OwnedCellSlice::from(builder.build().unwrap()))
    }

    fn make_new_cell_value(value: u32) -> RcStackValue {
        Rc::new(make_new_cell(value))
    }

    fn make_new_cell(value: u32) -> Cell {
        let value = BigInt::from(value);
        let mut builder = CellBuilder::new();
        store_int_to_builder(&value, 32, &mut builder).unwrap();
        builder.build().unwrap()
    }

    fn make_new_int_value(value: u32) -> RcStackValue {
        Rc::new(BigInt::from(value))
    }

    fn make_new_value() -> BigInt {
        BigInt::from(3)
    }

    fn build_dict<K, V, F>(f: F) -> RcStackValue
    where
        K: Store + DictKey,
        V: Store,
        for<'a> F: FnOnce(&'a mut Dict<K, V>) -> anyhow::Result<()>,
    {
        let mut dict = Dict::<K, V>::new();
        f(&mut dict).unwrap();
        Rc::new(dict.into_root().unwrap())
    }
}
