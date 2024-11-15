use everscale_vm_proc::vm_module;
use std::fmt::Formatter;

pub struct CurrencyOps;

#[vm_module]
impl CurrencyOps {
    // fn exec_load_var_integer(st: &mut VmState, args: VarIntegerArgs) -> VmResult<i32> {
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
