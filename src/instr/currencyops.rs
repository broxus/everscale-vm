use std::env::args;
use everscale_vm_proc::vm_module;
use std::fmt::Formatter;
use std::ops::Deref;
use std::rc::Rc;
use everscale_types::cell::CellBuilder;
use num_bigint::BigInt;
use everscale_vm::error::VmResult;
use everscale_vm::util::OwnedCellSlice;
use everscale_vm::VmState;
use crate::util::{load_int_from_slice, store_int_to_builder};

pub struct CurrencyOps;

#[vm_module]
impl CurrencyOps {
    #[instr(code = "fa00", fmt = ("{}", s.display()), args(s = VarIntegerArgs::new(false, 4, false, false)))]
    #[instr(code = "fa01", fmt = ("{}", s.display()), args(s = VarIntegerArgs::new(false, 4, true, false)))]
    #[instr(code = "fa04", fmt = ("{}", s.display()), args(s = VarIntegerArgs::new(false, 5, false, false)))]
    #[instr(code = "fa05", fmt = ("{}", s.display()), args(s = VarIntegerArgs::new(false, 5, true, false)))]
    fn exec_load_var_integer(st: &mut VmState, s: VarIntegerArgs) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let mut cs: Rc<OwnedCellSlice> = ok!(stack.pop_cs());
        let mut cs = cs.deref().clone();
        let mut slice = cs.apply()?;


        let int_opt = match load_int_from_slice(&mut slice, s.len_bits as u16, s.signed) {
            Ok(int) => Some(int),
            Err(e) => {
                if !s.quite {
                    vm_bail!(CellError(e))
                } else {
                    None
                }
            }
        };

        cs.set_range(slice.range());

        match int_opt {
            Some(int) => {
                ok!(stack.push_int(int));
                ok!(stack.push_raw(Rc::new(cs)));
                if s.quite {
                    ok!(stack.push_bool(true))
                }
            }
            None=> ok!(stack.push_bool(false))

        }
        Ok(0)
    }

    #[instr(code = "fa02", fmt = ("{}", s.display()), args(s = VarIntegerArgs::new(true, 4, false, false)))]
    #[instr(code = "fa03", fmt = ("{}", s.display()), args(s = VarIntegerArgs::new(true, 4, true, false)))]
    #[instr(code = "fa06", fmt = ("{}", s.display()), args(s = VarIntegerArgs::new(true, 5, false, false)))]
    #[instr(code = "fa07", fmt = ("{}", s.display()), args(s = VarIntegerArgs::new(true, 5, true, false)))]
    fn exec_store_var_integer(st: &mut VmState, s: VarIntegerArgs) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let int: Rc<BigInt> = ok!(stack.pop_int());
        let mut builder: Rc<CellBuilder> = ok!(stack.pop_builder());
        let cb_ref = Rc::make_mut(&mut builder);
        match store_int_to_builder(int.as_ref(), s.len_bits as u16, cb_ref){
            Ok(_) => {
                ok!(stack.push_raw(builder));
                if s.quite {
                    ok!(stack.push_bool(true));
                }
            },
            Err(e) => {
                if !s.quite {
                    vm_bail!(CellError(e))
                }
                ok!(stack.push_bool(false));
            }
        }
        Ok(0)
    }

    // fn exec_load_message_addr(st: &mut VmState, quite: bool) -> VmResult<i32> {
    //     let stack = Rc::make_mut(&mut st.stack);
    //     let cs = ok!(stack.pop_cs());
    // }
}

pub struct VarIntegerArgs {
    store: bool,
    len_bits: u32,
    signed: bool,
    quite: bool,
}

impl VarIntegerArgs {
    fn new(store: bool, len_bits: u32, signed: bool, quite: bool) -> Self {
        Self {
            store,
            len_bits,
            signed,
            quite,
        }
    }

    fn display_store(&self) -> DisplayVarIntegerArgs {
        DisplayVarIntegerArgs {
            store: self.store,
            len_bits: self.len_bits,
            signed: self.signed,
            quite: self.quite,
        }
    }
}

pub struct DisplayVarIntegerArgs {
    store: bool,
    len_bits: u32,
    signed: bool,
    quite: bool,
}

impl std::fmt::Display for DisplayVarIntegerArgs {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let mode = if self.store { "ST" } else { "LD" };
        let quite = if self.quite { "Q" } else { "" };

        let log = if self.len_bits == 4 && !self.signed {
            format!("{mode}GRAMS{quite}")
        } else {
            let signed = if self.signed { "" } else { "U" };
            format!("{mode}VAR{signed}INT{}{quite}", 1 << self.len_bits)
        };
        write!(f, "{log}")
    }
}
