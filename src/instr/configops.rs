use crate::error::VmResult;
use crate::stack::{RcStackValue, Stack};
use everscale_vm::cont::ControlRegs;
use everscale_vm::stack::StackValueType;
use everscale_vm::VmState;
use everscale_vm_proc::vm_module;
use std::fmt::Formatter;
use std::rc::Rc;

pub struct ConfigOps;

#[vm_module]
impl ConfigOps {
    #[instr(code = "f82s", fmt = ("{}", s.display()), args(s = ConfigOpsArgs(args)))]
    fn exec_get_param(st: &mut VmState, s: ConfigOpsArgs) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        ok!(get_and_push_param(&mut st.cr, stack, s.0 as usize));
        Ok(0)
    }

    #[instr(code = "f830", fmt = "CONFIGDICT")]
    fn exec_get_config_dict(st: &mut VmState) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        ok!(get_and_push_param(&mut st.cr, stack, 9usize));
        ok!(stack.push_int(32));
        Ok(0)
    }

    // fn exec_get_config_param(st: &mut VmState, opt: bool) -> VmResult<i32> {
    //     let stack = Rc::make_mut(&mut st.stack);
    //     let idx = ok!(stack.pop_int());
    //     ok!(get_and_push_param(&mut st.cr, stack, 9usize));
    //     //let dict = ok!(stack.pop_op)
    //     Ok(0)
    // }
}
pub struct ConfigOpsArgs(u32);

impl ConfigOpsArgs {
    fn display(&self) -> DisplayConfigOpsArgs {
        DisplayConfigOpsArgs(self.0)
    }
}
pub struct DisplayConfigOpsArgs(u32);

impl std::fmt::Display for DisplayConfigOpsArgs {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let code = match self.0 {
            3 => "NOW",
            4 => "BLOCKLT",
            5 => "LTIME",
            6 => "RANDCEED",
            7 => "BALANCE",
            8 => "MYADDR",
            9 => "CONFIGROOT",
            10 => "MYCODE",
            11 => "INCOMINGVALUE",
            12 => "STORAGEFEES",
            13 => "PREVBLOCKSINFOTUPLE",
            14 => "UNPACKEDCONFIGTUPLE",
            15 => "DUEPAYMENT",
            i => &format!("GETPARAM {i}"),
        };

        write!(f, "{}", code)
    }
}

fn get_and_push_param(regs: &mut ControlRegs, stack: &mut Stack, index: usize) -> VmResult<i32> {
    let param = ok!(get_param(regs, index));
    ok!(stack.push_raw(param.clone()));
    Ok(0)
}

fn get_param(regs: &mut ControlRegs, index: usize) -> VmResult<&RcStackValue> {
    let c7_opt = &regs.c7;
    let Some(c7) = c7_opt else {
        vm_bail!(ControlRegisterOutOfRange(7))
    };

    let control_params_opt: Option<&RcStackValue> = c7.get(0);
    let Some(control_params) = control_params_opt else {
        vm_bail!(InvalidType {
            expected: StackValueType::Tuple,
            actual: StackValueType::Null
        })
    };

    let intermediate_tuple = control_params.as_tuple_range(0, 255);
    let Some(intermediate_value) = intermediate_tuple else {
        vm_bail!(InvalidType {
            expected: StackValueType::Tuple,
            actual: control_params.ty()
        })
    };

    let param: &RcStackValue = match intermediate_value.get(index) {
        Some(param) => param,
        None => vm_bail!(ControlRegisterOutOfRange(index)),
    };

    Ok(param)
}
