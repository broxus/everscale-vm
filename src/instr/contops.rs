use std::rc::Rc;

use anyhow::Result;
use everscale_vm_proc::vm_module;

use crate::cont::{OrdCont, RcCont};
use crate::dispatch::Opcodes;
use crate::error::VmError;
use crate::state::{SaveCr, VmState};

pub struct Contops;

#[vm_module]
impl Contops {
    // === Jump ops ===

    #[instr(code = "d8", fmt = "EXECUTE")]
    fn exec_execute(st: &mut VmState) -> Result<i32> {
        let cont = ok!(Rc::make_mut(&mut st.stack).pop_cont_owned());
        st.call(cont)
    }

    #[instr(code = "d9", fmt = "JMPX")]
    fn exec_jmpx(st: &mut VmState) -> Result<i32> {
        let cont = ok!(Rc::make_mut(&mut st.stack).pop_cont_owned());
        st.jump(cont)
    }

    #[instr(code = "dapr", fmt = "CALLXARGS {p},{r}")]
    fn exec_callx_args(st: &mut VmState, p: u32, r: u32) -> Result<i32> {
        let cont = ok!(Rc::make_mut(&mut st.stack).pop_cont_owned());
        st.call_ext(cont, Some(p as _), Some(r as _))
    }

    #[instr(code = "db0p", fmt = "CALLXARGS {p},-1")]
    fn exec_callx_args_p(st: &mut VmState, p: u32) -> Result<i32> {
        let cont = ok!(Rc::make_mut(&mut st.stack).pop_cont_owned());
        st.call_ext(cont, Some(p as _), None)
    }

    #[instr(code = "db1p", fmt = "JMPXARGS {p}")]
    fn exec_jmpx_args(st: &mut VmState, p: u32) -> Result<i32> {
        let cont = ok!(Rc::make_mut(&mut st.stack).pop_cont_owned());
        st.jump_ext(cont, Some(p as _))
    }

    #[instr(code = "db2r", fmt = "RETARGS {r}")]
    fn exec_ret_args(st: &mut VmState, r: u32) -> Result<i32> {
        st.ret_ext(Some(r as _))
    }

    #[instr(code = "db30", fmt = "RET")]
    fn exec_ret(st: &mut VmState) -> Result<i32> {
        st.ret()
    }

    #[instr(code = "db31", fmt = "RETALT")]
    fn exec_ret_alt(st: &mut VmState) -> Result<i32> {
        st.ret_alt()
    }

    #[instr(code = "db32", fmt = "RETBOOL")]
    fn exec_ret_bool(st: &mut VmState) -> Result<i32> {
        if ok!(Rc::make_mut(&mut st.stack).pop_bool()) {
            st.ret()
        } else {
            st.ret_alt()
        }
    }

    #[instr(code = "db34", fmt = "CALLCC")]
    fn exec_callcc(st: &mut VmState) -> Result<i32> {
        let cont = ok!(Rc::make_mut(&mut st.stack).pop_cont_owned());
        let cc = ok!(st.extract_cc(SaveCr::C0_C1, None, None));
        ok!(Rc::make_mut(&mut st.stack).push(cc as RcCont));
        st.jump(cont)
    }

    #[instr(code = "db35", fmt = "JMPXDATA")]
    fn exec_jmpx_data(st: &mut VmState) -> Result<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let cont = ok!(stack.pop_cont_owned());
        ok!(stack.push(st.code.clone()));
        st.jump(cont)
    }

    #[instr(code = "db36pr", fmt = "CALLCCARGS {p},{r}", args(r = ((args as i32 + 1) & 0xf) - 1))]
    fn exec_callcc_args(st: &mut VmState, p: u32, r: i32) -> Result<i32> {
        let cont = ok!(Rc::make_mut(&mut st.stack).pop_cont_owned());
        let cc = ok!(st.extract_cc(SaveCr::C0_C1, Some(p as _), (r >= 0).then_some(r as _)));
        ok!(Rc::make_mut(&mut st.stack).push(cc as RcCont));
        st.jump(cont)
    }

    #[instr(code = "db38", fmt = "CALLXVARARGS")]
    fn exec_callx_varargs(st: &mut VmState) -> Result<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let r = ok!(stack.pop_smallint_signed_range(-1, 254));
        let p = ok!(stack.pop_smallint_signed_range(-1, 254));
        let cont = ok!(stack.pop_cont_owned());
        st.call_ext(cont, (p >= 0).then_some(p as _), (r >= 0).then_some(r as _))
    }

    #[instr(code = "db39", fmt = "RETVARARGS")]
    fn exec_ret_varargs(st: &mut VmState) -> Result<i32> {
        let r = ok!(Rc::make_mut(&mut st.stack).pop_smallint_signed_range(-1, 254));
        st.ret_ext((r >= 0).then_some(r as _))
    }

    #[instr(code = "db3a", fmt = "JMPXVARARGS")]
    fn exec_jmpx_varargs(st: &mut VmState) -> Result<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let p = ok!(stack.pop_smallint_signed_range(-1, 254));
        let cont = ok!(stack.pop_cont_owned());
        st.jump_ext(cont, (p >= 0).then_some(p as _))
    }

    #[instr(code = "db3b", fmt = "CALLCCVARARGS")]
    fn exec_callcc_varargs(st: &mut VmState) -> Result<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let r = ok!(stack.pop_smallint_signed_range(-1, 254));
        let p = ok!(stack.pop_smallint_signed_range(-1, 254));
        let cont = ok!(stack.pop_cont_owned());
        let cc = ok!(st.extract_cc(
            SaveCr::C0_C1,
            (p >= 0).then_some(p as _),
            (r >= 0).then_some(r as _)
        ));
        ok!(Rc::make_mut(&mut st.stack).push(cc as RcCont));
        st.jump(cont)
    }

    #[init]
    fn init_do_with_ref(&self, t: &mut Opcodes) -> Result<()> {
        ok!(t.add_ext(0xdb3c, 16, 0, exec_callref));
        ok!(t.add_ext(0xdb3d, 16, 0, exec_jmpref));
        t.add_ext(0xdb3e, 16, 0, exec_jmpref_data)
    }

    fn exec_callref(st: &mut VmState, _: u32, bits: u16) -> Result<i32> {
        let cont = ok!(exec_ref_prefix(st, bits, "CALLREF"));
        st.call(cont)
    }

    fn exec_jmpref(st: &mut VmState, _: u32, bits: u16) -> Result<i32> {
        let cont = ok!(exec_ref_prefix(st, bits, "JMPREF"));
        st.jump(cont)
    }

    fn exec_jmpref_data(st: &mut VmState, _: u32, bits: u16) -> Result<i32> {
        let cont = ok!(exec_ref_prefix(st, bits, "JMPREFDATA"));
        ok!(Rc::make_mut(&mut st.stack).push(st.code.clone()));
        st.jump(cont)
    }

    #[instr(code = "db3f", fmt = "RETDATA")]
    fn exec_ret_data(st: &mut VmState) -> Result<i32> {
        ok!(Rc::make_mut(&mut st.stack).push(st.code.clone()));
        st.ret()
    }
}

fn exec_ref_prefix(st: &mut VmState, bits: u16, name: &str) -> Result<Rc<OrdCont>> {
    let code_range = st.code.range();
    anyhow::ensure!(code_range.has_remaining(bits, 1), VmError::InvalidOpcode);
    st.code.range_mut().try_advance(bits, 0);

    let Some(code) = st.code.cell().reference_cloned(code_range.refs_offset()) else {
        anyhow::bail!(everscale_types::error::Error::CellUnderflow);
    };
    st.code.range_mut().try_advance(0, 1);

    vm_log!("execute {name} ({})", code.repr_hash());
    st.ref_to_cont(code)
}
