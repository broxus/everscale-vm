use std::rc::Rc;

use anyhow::Result;
use everscale_types::prelude::Cell;
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
    fn init_jumps_with_ref(&self, t: &mut Opcodes) -> Result<()> {
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

    // === Conditions and loops ===

    #[instr(code = "dc", fmt = "IFRET")]
    fn exec_ifret(st: &mut VmState) -> Result<i32> {
        if ok!(Rc::make_mut(&mut st.stack).pop_bool()) {
            st.ret()
        } else {
            Ok(0)
        }
    }

    #[instr(code = "dd", fmt = "IFNOTRET")]
    fn exec_ifnotret(st: &mut VmState) -> Result<i32> {
        if ok!(Rc::make_mut(&mut st.stack).pop_bool()) {
            Ok(0)
        } else {
            st.ret()
        }
    }

    #[instr(code = "de", fmt = "IF")]
    fn exec_if(st: &mut VmState) -> Result<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let cont = ok!(stack.pop_cont_owned());
        if ok!(stack.pop_bool()) {
            st.call(cont)
        } else {
            Ok(0)
        }
    }

    #[instr(code = "df", fmt = "IFNOT")]
    fn exec_ifnot(st: &mut VmState) -> Result<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let cont = ok!(stack.pop_cont_owned());
        if ok!(stack.pop_bool()) {
            Ok(0)
        } else {
            st.call(cont)
        }
    }

    #[instr(code = "e0", fmt = "IFJMP")]
    fn exec_if_jmp(st: &mut VmState) -> Result<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let cont = ok!(stack.pop_cont_owned());
        if ok!(stack.pop_bool()) {
            st.jump(cont)
        } else {
            Ok(0)
        }
    }

    #[instr(code = "e1", fmt = "IFNOTJMP")]
    fn exec_ifnot_jmp(st: &mut VmState) -> Result<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let cont = ok!(stack.pop_cont_owned());
        if ok!(stack.pop_bool()) {
            Ok(0)
        } else {
            st.jump(cont)
        }
    }

    #[instr(code = "e2", fmt = "IFELSE")]
    fn exec_if_else(st: &mut VmState) -> Result<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let cont = {
            let cont0 = ok!(stack.pop_cont_owned());
            let cont1 = ok!(stack.pop_cont_owned());
            match ok!(stack.pop_bool()) {
                false => cont0,
                true => cont1,
            }
        };
        st.call(cont)
    }

    #[init]
    fn init_if_with_ref(&self, t: &mut Opcodes) -> Result<()> {
        ok!(t.add_ext(0xe300, 16, 0, exec_ifref));
        ok!(t.add_ext(0xe301, 16, 0, exec_ifnotref));
        ok!(t.add_ext(0xe302, 16, 0, exec_ifjmpref));
        t.add_ext(0xe303, 16, 0, exec_ifnotjmpref)
    }

    fn exec_ifref(st: &mut VmState, _: u32, bits: u16) -> Result<i32> {
        let cell = ok!(exec_cell_prefix(st, bits, "IFREF"));
        if ok!(Rc::make_mut(&mut st.stack).pop_bool()) {
            let cont = ok!(st.ref_to_cont(cell));
            st.call(cont)
        } else {
            Ok(0)
        }
    }

    fn exec_ifnotref(st: &mut VmState, _: u32, bits: u16) -> Result<i32> {
        let cell = ok!(exec_cell_prefix(st, bits, "IFNOTREF"));
        if ok!(Rc::make_mut(&mut st.stack).pop_bool()) {
            Ok(0)
        } else {
            let cont = ok!(st.ref_to_cont(cell));
            st.call(cont)
        }
    }

    fn exec_ifjmpref(st: &mut VmState, _: u32, bits: u16) -> Result<i32> {
        let cell = ok!(exec_cell_prefix(st, bits, "IFJMPREF"));
        if ok!(Rc::make_mut(&mut st.stack).pop_bool()) {
            let cont = ok!(st.ref_to_cont(cell));
            st.jump(cont)
        } else {
            Ok(0)
        }
    }

    fn exec_ifnotjmpref(st: &mut VmState, _: u32, bits: u16) -> Result<i32> {
        let cell = ok!(exec_cell_prefix(st, bits, "IFNOTJMPREF"));
        if ok!(Rc::make_mut(&mut st.stack).pop_bool()) {
            Ok(0)
        } else {
            let cont = ok!(st.ref_to_cont(cell));
            st.jump(cont)
        }
    }

    #[instr(code = "e304", fmt = "CONDSEL")]
    fn exec_condsel(st: &mut VmState) -> Result<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let y = ok!(stack.pop());
        let x = ok!(stack.pop());
        let cond = ok!(stack.pop_bool());
        ok!(stack.push_raw(match cond {
            true => x,
            false => y,
        }));
        Ok(0)
    }

    #[instr(code = "e305", fmt = "CONDSELCHK")]
    fn exec_condsel_chk(st: &mut VmState) -> Result<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let y = ok!(stack.pop());
        let x = ok!(stack.pop());
        anyhow::ensure!(
            x.ty() == y.ty(),
            VmError::InvalidType {
                expected: x.ty(),
                actual: y.ty(),
            }
        );
        let cond = ok!(stack.pop_bool());
        ok!(stack.push_raw(match cond {
            true => x,
            false => y,
        }));
        Ok(0)
    }

    #[instr(code = "e308", fmt = "IFRETALT")]
    fn exec_ifretalt(st: &mut VmState) -> Result<i32> {
        if ok!(Rc::make_mut(&mut st.stack).pop_bool()) {
            st.ret_alt()
        } else {
            Ok(0)
        }
    }

    #[instr(code = "e309", fmt = "IFNOTRETALT")]
    fn exec_ifnotretalt(st: &mut VmState) -> Result<i32> {
        if ok!(Rc::make_mut(&mut st.stack).pop_bool()) {
            Ok(0)
        } else {
            st.ret_alt()
        }
    }

    #[init]
    fn init_ifelse_with_ref(&self, t: &mut Opcodes) -> Result<()> {
        ok!(t.add_ext(0xe30d, 16, 0, exec_ifrefelse));
        ok!(t.add_ext(0xe30e, 16, 0, exec_ifelseref));
        ok!(t.add_ext(0xe30f, 16, 0, exec_ifref_elseref));
        t.add_ext(0xe3c0 >> 6, 10, 0, exec_if_bit_jmpref)
    }

    fn exec_ifrefelse(st: &mut VmState, _: u32, bits: u16) -> Result<i32> {
        exec_ifelse_ref_impl(st, bits, true)
    }

    fn exec_ifelseref(st: &mut VmState, _: u32, bits: u16) -> Result<i32> {
        exec_ifelse_ref_impl(st, bits, false)
    }

    fn exec_ifref_elseref(st: &mut VmState, _: u32, bits: u16) -> Result<i32> {
        let cell = {
            let code = &mut st.code;
            anyhow::ensure!(code.range().has_remaining(bits, 2), VmError::InvalidOpcode);
            code.range_mut().try_advance(bits, 0);

            let Some(cell1) = code.cell().reference_cloned(code.range().refs_offset()) else {
                anyhow::bail!(everscale_types::error::Error::CellUnderflow);
            };
            code.range_mut().try_advance(0, 1);

            let Some(cell0) = code.cell().reference_cloned(code.range().refs_offset()) else {
                anyhow::bail!(everscale_types::error::Error::CellUnderflow);
            };
            code.range_mut().try_advance(0, 1);

            vm_log!(
                "execute IFREFELSEREF ({}) ({})",
                cell1.repr_hash(),
                cell0.repr_hash()
            );

            match ok!(Rc::make_mut(&mut st.stack).pop_bool()) {
                false => cell0,
                true => cell1,
            }
        };
        let cont = ok!(st.ref_to_cont(cell));
        st.call(cont)
    }

    #[instr(code = "e3$10nx#x", fmt = ("IF{}BITJMP {x}", if n != 0 { "N" } else { "" }))]
    fn exec_if_bit_jmp(st: &mut VmState, n: u32, x: u32) -> Result<i32> {
        let negate = n != 0;
        let (cont, bit) = {
            let stack = Rc::make_mut(&mut st.stack);
            let cont = ok!(stack.pop_cont_owned());
            let value = ok!(stack.pop_int());
            let bit = value.bit(x as _);
            ok!(stack.push_raw(value));
            (cont, bit)
        };

        if bit ^ negate {
            st.jump(cont)
        } else {
            Ok(0)
        }
    }

    fn exec_if_bit_jmpref(st: &mut VmState, args: u32, bits: u16) -> Result<i32> {
        let code_range = st.code.range();
        anyhow::ensure!(code_range.has_remaining(bits, 1), VmError::InvalidOpcode);
        st.code.range_mut().try_advance(bits, 0);

        let Some(cell) = st.code.cell().reference_cloned(code_range.refs_offset()) else {
            anyhow::bail!(everscale_types::error::Error::CellUnderflow);
        };
        st.code.range_mut().try_advance(0, 1);

        let negate = (args & 0x20) != 0;
        let bit = args & 0x1f;
        vm_log!(
            "execute {}BITJMPREF {bit} ({})",
            if negate { "N" } else { "" },
            cell.repr_hash()
        );

        let bit = {
            let stack = Rc::make_mut(&mut st.stack);
            let value = ok!(stack.pop_int());
            let bit = value.bit(bit as _);
            ok!(stack.push_raw(value));
            bit
        };

        if bit ^ negate {
            let cont = ok!(st.ref_to_cont(cell));
            st.jump(cont)
        } else {
            Ok(0)
        }
    }

    #[instr(code = "e4", fmt = "REPEAT", args(brk = false))]
    #[instr(code = "e314", fmt = "REPEATBRK", args(brk = true))]
    fn exec_repeat(st: &mut VmState, brk: bool) -> Result<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let body = ok!(stack.pop_cont_owned());
        let n = ok!(stack.pop_smallint_signed_range(i32::MIN, i32::MAX));
        if n <= 0 {
            return Ok(0);
        }

        let cc = ok!(st.extract_cc(SaveCr::C0, None, None));
        let after = st.c1_envelope_if(brk, cc, true);
        st.repeat(body, after, n as _)
    }

    #[instr(code = "e5", fmt = "REPEATEND", args(brk = false))]
    #[instr(code = "e315", fmt = "REPEATENDBRK", args(brk = true))]
    fn exec_repeat_end(st: &mut VmState, brk: bool) -> Result<i32> {
        let n = ok!(Rc::make_mut(&mut st.stack).pop_smallint_signed_range(i32::MIN, i32::MAX));
        if n <= 0 {
            return Ok(0);
        }
        let body = ok!(st.extract_cc(SaveCr::NONE, None, None));
        let Some(c0) = st.cr.c[0].clone() else {
            anyhow::bail!(VmError::InvalidOpcode);
        };
        let after = st.c1_envelope_if(brk, c0, true);
        st.repeat(body, after, n as _)
    }

    #[instr(code = "e6", fmt = "UNTIL", args(brk = false))]
    #[instr(code = "e316", fmt = "UNTILBRK", args(brk = true))]
    fn exec_until(st: &mut VmState, brk: bool) -> Result<i32> {
        let body = ok!(Rc::make_mut(&mut st.stack).pop_cont_owned());
        let cc = ok!(st.extract_cc(SaveCr::C0, None, None));
        let after = st.c1_envelope_if(brk, cc, true);
        st.until(body, after)
    }

    #[instr(code = "e7", fmt = "UNTILEND", args(brk = false))]
    #[instr(code = "e317", fmt = "UNTILENDBRK", args(brk = true))]
    fn exec_until_end(st: &mut VmState, brk: bool) -> Result<i32> {
        let body = ok!(st.extract_cc(SaveCr::NONE, None, None));
        let Some(c0) = st.cr.c[0].clone() else {
            anyhow::bail!(VmError::InvalidOpcode);
        };
        let after = st.c1_envelope_if(brk, c0, true);
        st.until(body, after)
    }

    #[instr(code = "e8", fmt = "WHILE", args(brk = false))]
    #[instr(code = "e318", fmt = "WHILEBRK", args(brk = true))]
    fn exec_while(st: &mut VmState, brk: bool) -> Result<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let body = ok!(stack.pop_cont_owned());
        let cond = ok!(stack.pop_cont_owned());

        let cc = ok!(st.extract_cc(SaveCr::C0, None, None));
        let after = st.c1_envelope_if(brk, cc, true);
        st.loop_while(cond, body, after)
    }

    #[instr(code = "e9", fmt = "WHILEEND", args(brk = false))]
    #[instr(code = "e319", fmt = "WHILEENDBRK", args(brk = true))]
    fn exec_while_end(st: &mut VmState, brk: bool) -> Result<i32> {
        let cond = ok!(Rc::make_mut(&mut st.stack).pop_cont_owned());
        let body = ok!(st.extract_cc(SaveCr::NONE, None, None));
        let Some(c0) = st.cr.c[0].clone() else {
            anyhow::bail!(VmError::InvalidOpcode);
        };
        let after = st.c1_envelope_if(brk, c0, true);
        st.loop_while(cond, body, after)
    }

    #[instr(code = "ea", fmt = "AGAIN", args(brk = false))]
    #[instr(code = "e31a", fmt = "AGAINBRK", args(brk = true))]
    fn exec_again(st: &mut VmState, brk: bool) -> Result<i32> {
        if brk {
            let cc = ok!(st.extract_cc(SaveCr::C0_C1, None, None));
            st.cr.c[1] = Some(cc);
        }
        let body = ok!(Rc::make_mut(&mut st.stack).pop_cont_owned());
        st.again(body)
    }

    #[instr(code = "eb", fmt = "AGAINEND", args(brk = false))]
    #[instr(code = "e31b", fmt = "AGAINENDBRK", args(brk = true))]
    fn exec_again_end(st: &mut VmState, brk: bool) -> Result<i32> {
        if brk {
            st.c1_save_set();
        }
        let cc = ok!(st.extract_cc(SaveCr::NONE, None, None));
        st.again(cc)
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

fn exec_cell_prefix(st: &mut VmState, bits: u16, name: &str) -> Result<Cell> {
    let code_range = st.code.range();
    anyhow::ensure!(code_range.has_remaining(bits, 1), VmError::InvalidOpcode);
    st.code.range_mut().try_advance(bits, 0);

    let Some(cell) = st.code.cell().reference_cloned(code_range.refs_offset()) else {
        anyhow::bail!(everscale_types::error::Error::CellUnderflow);
    };
    st.code.range_mut().try_advance(0, 1);

    vm_log!("execute {name} ({})", cell.repr_hash());
    Ok(cell)
}

fn exec_ifelse_ref_impl(st: &mut VmState, bits: u16, ref_first: bool) -> Result<i32> {
    let cont = {
        let code_range = st.code.range();
        anyhow::ensure!(code_range.has_remaining(bits, 1), VmError::InvalidOpcode);
        st.code.range_mut().try_advance(bits, 0);

        let Some(cell) = st.code.cell().reference_cloned(code_range.refs_offset()) else {
            anyhow::bail!(everscale_types::error::Error::CellUnderflow);
        };
        st.code.range_mut().try_advance(0, 1);

        let name = match ref_first {
            true => "IFREFELSE",
            false => "IFELSEREF",
        };

        vm_log!("execute {name} ({})", cell.repr_hash());

        let stack = Rc::make_mut(&mut st.stack);
        let cont = ok!(stack.pop_cont_owned());

        if ok!(stack.pop_bool()) == ref_first {
            ok!(st.ref_to_cont(cell))
        } else {
            cont
        }
    };
    st.call(cont)
}
