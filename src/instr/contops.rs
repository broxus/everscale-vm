use std::rc::Rc;

use anyhow::Result;
use everscale_types::prelude::Cell;
use everscale_vm_proc::vm_module;

use crate::cont::{ArgContExt, Cont, ControlData, ControlRegs, OrdCont, PushIntCont, RcCont};
use crate::dispatch::Opcodes;
use crate::error::VmResult;
use crate::stack::{Stack, StackValueType};
use crate::state::{SaveCr, VmState};

pub struct Contops;

#[vm_module]
impl Contops {
    // === Jump ops ===

    #[instr(code = "d8", fmt = "EXECUTE")]
    fn exec_execute(st: &mut VmState) -> VmResult<i32> {
        let cont = ok!(Rc::make_mut(&mut st.stack).pop_cont());
        st.call(cont)
    }

    #[instr(code = "d9", fmt = "JMPX")]
    fn exec_jmpx(st: &mut VmState) -> VmResult<i32> {
        let cont = ok!(Rc::make_mut(&mut st.stack).pop_cont());
        st.jump(cont)
    }

    #[instr(code = "dapr", fmt = "CALLXARGS {p},{r}")]
    fn exec_callx_args(st: &mut VmState, p: u32, r: u32) -> VmResult<i32> {
        let cont = ok!(Rc::make_mut(&mut st.stack).pop_cont());
        st.call_ext(cont, Some(p as _), Some(r as _))
    }

    #[instr(code = "db0p", fmt = "CALLXARGS {p},-1")]
    fn exec_callx_args_p(st: &mut VmState, p: u32) -> VmResult<i32> {
        let cont = ok!(Rc::make_mut(&mut st.stack).pop_cont());
        st.call_ext(cont, Some(p as _), None)
    }

    #[instr(code = "db1p", fmt = "JMPXARGS {p}")]
    fn exec_jmpx_args(st: &mut VmState, p: u32) -> VmResult<i32> {
        let cont = ok!(Rc::make_mut(&mut st.stack).pop_cont());
        st.jump_ext(cont, Some(p as _))
    }

    #[instr(code = "db2r", fmt = "RETARGS {r}")]
    fn exec_ret_args(st: &mut VmState, r: u32) -> VmResult<i32> {
        st.ret_ext(Some(r as _))
    }

    #[instr(code = "db30", fmt = "RET")]
    fn exec_ret(st: &mut VmState) -> VmResult<i32> {
        st.ret()
    }

    #[instr(code = "db31", fmt = "RETALT")]
    fn exec_ret_alt(st: &mut VmState) -> VmResult<i32> {
        st.ret_alt()
    }

    #[instr(code = "db32", fmt = "RETBOOL")]
    fn exec_ret_bool(st: &mut VmState) -> VmResult<i32> {
        if ok!(Rc::make_mut(&mut st.stack).pop_bool()) {
            st.ret()
        } else {
            st.ret_alt()
        }
    }

    #[instr(code = "db34", fmt = "CALLCC")]
    fn exec_callcc(st: &mut VmState) -> VmResult<i32> {
        let cont = ok!(Rc::make_mut(&mut st.stack).pop_cont());
        let cc = ok!(st.extract_cc(SaveCr::C0_C1, None, None));
        ok!(Rc::make_mut(&mut st.stack).push_raw(cc.into_stack_value()));
        st.jump(cont)
    }

    #[instr(code = "db35", fmt = "JMPXDATA")]
    fn exec_jmpx_data(st: &mut VmState) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let cont = ok!(stack.pop_cont());
        ok!(stack.push(st.code.clone()));
        st.jump(cont)
    }

    #[instr(code = "db36pr", fmt = "CALLCCARGS {p},{r}", args(r = ((args as i32 + 1) & 0xf) - 1))]
    fn exec_callcc_args(st: &mut VmState, p: u32, r: i32) -> VmResult<i32> {
        let cont = ok!(Rc::make_mut(&mut st.stack).pop_cont());
        let cc = ok!(st.extract_cc(SaveCr::C0_C1, Some(p as _), (r >= 0).then_some(r as _)));
        ok!(Rc::make_mut(&mut st.stack).push_raw(cc.into_stack_value()));
        st.jump(cont)
    }

    #[instr(code = "db38", fmt = "CALLXVARARGS")]
    fn exec_callx_varargs(st: &mut VmState) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let r = ok!(stack.pop_smallint_signed_range(-1, 254));
        let p = ok!(stack.pop_smallint_signed_range(-1, 254));
        let cont = ok!(stack.pop_cont());
        st.call_ext(cont, (p >= 0).then_some(p as _), (r >= 0).then_some(r as _))
    }

    #[instr(code = "db39", fmt = "RETVARARGS")]
    fn exec_ret_varargs(st: &mut VmState) -> VmResult<i32> {
        let r = ok!(Rc::make_mut(&mut st.stack).pop_smallint_signed_range(-1, 254));
        st.ret_ext((r >= 0).then_some(r as _))
    }

    #[instr(code = "db3a", fmt = "JMPXVARARGS")]
    fn exec_jmpx_varargs(st: &mut VmState) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let p = ok!(stack.pop_smallint_signed_range(-1, 254));
        let cont = ok!(stack.pop_cont());
        st.jump_ext(cont, (p >= 0).then_some(p as _))
    }

    #[instr(code = "db3b", fmt = "CALLCCVARARGS")]
    fn exec_callcc_varargs(st: &mut VmState) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let r = ok!(stack.pop_smallint_signed_range(-1, 254));
        let p = ok!(stack.pop_smallint_signed_range(-1, 254));
        let cont = ok!(stack.pop_cont());
        let cc = ok!(st.extract_cc(
            SaveCr::C0_C1,
            (p >= 0).then_some(p as _),
            (r >= 0).then_some(r as _)
        ));
        ok!(Rc::make_mut(&mut st.stack).push_raw(cc.into_stack_value()));
        st.jump(cont)
    }

    #[init]
    fn init_jumps_with_ref(&self, t: &mut Opcodes) -> Result<()> {
        ok!(t.add_ext(0xdb3c, 16, 0, exec_callref));
        ok!(t.add_ext(0xdb3d, 16, 0, exec_jmpref));
        t.add_ext(0xdb3e, 16, 0, exec_jmpref_data)
    }

    fn exec_callref(st: &mut VmState, _: u32, bits: u16) -> VmResult<i32> {
        let cont = ok!(exec_ref_prefix(st, bits, "CALLREF"));
        st.call(cont)
    }

    fn exec_jmpref(st: &mut VmState, _: u32, bits: u16) -> VmResult<i32> {
        let cont = ok!(exec_ref_prefix(st, bits, "JMPREF"));
        st.jump(cont)
    }

    fn exec_jmpref_data(st: &mut VmState, _: u32, bits: u16) -> VmResult<i32> {
        let cont = ok!(exec_ref_prefix(st, bits, "JMPREFDATA"));
        ok!(Rc::make_mut(&mut st.stack).push(st.code.clone()));
        st.jump(cont)
    }

    #[instr(code = "db3f", fmt = "RETDATA")]
    fn exec_ret_data(st: &mut VmState) -> VmResult<i32> {
        ok!(Rc::make_mut(&mut st.stack).push(st.code.clone()));
        st.ret()
    }

    // === Conditions and loops ===

    #[instr(code = "dc", fmt = "IFRET")]
    fn exec_ifret(st: &mut VmState) -> VmResult<i32> {
        if ok!(Rc::make_mut(&mut st.stack).pop_bool()) {
            st.ret()
        } else {
            Ok(0)
        }
    }

    #[instr(code = "dd", fmt = "IFNOTRET")]
    fn exec_ifnotret(st: &mut VmState) -> VmResult<i32> {
        if ok!(Rc::make_mut(&mut st.stack).pop_bool()) {
            Ok(0)
        } else {
            st.ret()
        }
    }

    #[instr(code = "de", fmt = "IF")]
    fn exec_if(st: &mut VmState) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let cont = ok!(stack.pop_cont());
        if ok!(stack.pop_bool()) {
            st.call(cont)
        } else {
            Ok(0)
        }
    }

    #[instr(code = "df", fmt = "IFNOT")]
    fn exec_ifnot(st: &mut VmState) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let cont = ok!(stack.pop_cont());
        if ok!(stack.pop_bool()) {
            Ok(0)
        } else {
            st.call(cont)
        }
    }

    #[instr(code = "e0", fmt = "IFJMP")]
    fn exec_if_jmp(st: &mut VmState) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let cont = ok!(stack.pop_cont());
        if ok!(stack.pop_bool()) {
            st.jump(cont)
        } else {
            Ok(0)
        }
    }

    #[instr(code = "e1", fmt = "IFNOTJMP")]
    fn exec_ifnot_jmp(st: &mut VmState) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let cont = ok!(stack.pop_cont());
        if ok!(stack.pop_bool()) {
            Ok(0)
        } else {
            st.jump(cont)
        }
    }

    #[instr(code = "e2", fmt = "IFELSE")]
    fn exec_if_else(st: &mut VmState) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let cont = {
            let cont0 = ok!(stack.pop_cont());
            let cont1 = ok!(stack.pop_cont());
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

    fn exec_ifref(st: &mut VmState, _: u32, bits: u16) -> VmResult<i32> {
        let cell = ok!(exec_cell_prefix(st, bits, "IFREF"));
        if ok!(Rc::make_mut(&mut st.stack).pop_bool()) {
            let cont = ok!(st.ref_to_cont(cell));
            st.call(cont)
        } else {
            Ok(0)
        }
    }

    fn exec_ifnotref(st: &mut VmState, _: u32, bits: u16) -> VmResult<i32> {
        let cell = ok!(exec_cell_prefix(st, bits, "IFNOTREF"));
        if ok!(Rc::make_mut(&mut st.stack).pop_bool()) {
            Ok(0)
        } else {
            let cont = ok!(st.ref_to_cont(cell));
            st.call(cont)
        }
    }

    fn exec_ifjmpref(st: &mut VmState, _: u32, bits: u16) -> VmResult<i32> {
        let cell = ok!(exec_cell_prefix(st, bits, "IFJMPREF"));
        if ok!(Rc::make_mut(&mut st.stack).pop_bool()) {
            let cont = ok!(st.ref_to_cont(cell));
            st.jump(cont)
        } else {
            Ok(0)
        }
    }

    fn exec_ifnotjmpref(st: &mut VmState, _: u32, bits: u16) -> VmResult<i32> {
        let cell = ok!(exec_cell_prefix(st, bits, "IFNOTJMPREF"));
        if ok!(Rc::make_mut(&mut st.stack).pop_bool()) {
            Ok(0)
        } else {
            let cont = ok!(st.ref_to_cont(cell));
            st.jump(cont)
        }
    }

    #[instr(code = "e304", fmt = "CONDSEL")]
    fn exec_condsel(st: &mut VmState) -> VmResult<i32> {
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
    fn exec_condsel_chk(st: &mut VmState) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let y = ok!(stack.pop());
        let x = ok!(stack.pop());
        vm_ensure!(
            x.ty() == y.ty(),
            InvalidType {
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
    fn exec_ifretalt(st: &mut VmState) -> VmResult<i32> {
        if ok!(Rc::make_mut(&mut st.stack).pop_bool()) {
            st.ret_alt()
        } else {
            Ok(0)
        }
    }

    #[instr(code = "e309", fmt = "IFNOTRETALT")]
    fn exec_ifnotretalt(st: &mut VmState) -> VmResult<i32> {
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

    fn exec_ifrefelse(st: &mut VmState, _: u32, bits: u16) -> VmResult<i32> {
        exec_ifelse_ref_impl(st, bits, true)
    }

    fn exec_ifelseref(st: &mut VmState, _: u32, bits: u16) -> VmResult<i32> {
        exec_ifelse_ref_impl(st, bits, false)
    }

    fn exec_ifref_elseref(st: &mut VmState, _: u32, bits: u16) -> VmResult<i32> {
        let cell = {
            let code = &mut st.code;
            vm_ensure!(code.range().has_remaining(bits, 2), InvalidOpcode);
            let ok = code.range_mut().skip_first(bits, 0).is_ok();
            debug_assert!(ok);

            let Some(cell1) = code.cell().reference_cloned(code.range().offset_refs()) else {
                vm_bail!(CellError(everscale_types::error::Error::CellUnderflow));
            };
            let ok = code.range_mut().skip_first(0, 1).is_ok();
            debug_assert!(ok);

            let Some(cell0) = code.cell().reference_cloned(code.range().offset_refs()) else {
                vm_bail!(CellError(everscale_types::error::Error::CellUnderflow));
            };
            let ok = code.range_mut().skip_first(0, 1).is_ok();
            debug_assert!(ok);

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
    fn exec_if_bit_jmp(st: &mut VmState, n: u32, x: u32) -> VmResult<i32> {
        let negate = n != 0;
        let (cont, bit) = {
            let stack = Rc::make_mut(&mut st.stack);
            let cont = ok!(stack.pop_cont());
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

    fn exec_if_bit_jmpref(st: &mut VmState, args: u32, bits: u16) -> VmResult<i32> {
        let code_range = st.code.range();
        vm_ensure!(code_range.has_remaining(bits, 1), InvalidOpcode);
        let ok = st.code.range_mut().skip_first(bits, 0).is_ok();
        debug_assert!(ok);

        let Some(cell) = st.code.cell().reference_cloned(code_range.offset_refs()) else {
            vm_bail!(CellError(everscale_types::error::Error::CellUnderflow));
        };
        let ok = st.code.range_mut().skip_first(0, 1).is_ok();
        debug_assert!(ok);

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
    fn exec_repeat(st: &mut VmState, brk: bool) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let body = ok!(stack.pop_cont());
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
    fn exec_repeat_end(st: &mut VmState, brk: bool) -> VmResult<i32> {
        let n = ok!(Rc::make_mut(&mut st.stack).pop_smallint_signed_range(i32::MIN, i32::MAX));
        if n <= 0 {
            return Ok(0);
        }
        let body = ok!(st.extract_cc(SaveCr::NONE, None, None));
        let Some(c0) = st.cr.c[0].clone() else {
            vm_bail!(InvalidOpcode);
        };
        let after = st.c1_envelope_if(brk, c0, true);
        st.repeat(body, after, n as _)
    }

    #[instr(code = "e6", fmt = "UNTIL", args(brk = false))]
    #[instr(code = "e316", fmt = "UNTILBRK", args(brk = true))]
    fn exec_until(st: &mut VmState, brk: bool) -> VmResult<i32> {
        let body = ok!(Rc::make_mut(&mut st.stack).pop_cont());
        let cc = ok!(st.extract_cc(SaveCr::C0, None, None));
        let after = st.c1_envelope_if(brk, cc, true);
        st.until(body, after)
    }

    #[instr(code = "e7", fmt = "UNTILEND", args(brk = false))]
    #[instr(code = "e317", fmt = "UNTILENDBRK", args(brk = true))]
    fn exec_until_end(st: &mut VmState, brk: bool) -> VmResult<i32> {
        let body = ok!(st.extract_cc(SaveCr::NONE, None, None));
        let Some(c0) = st.cr.c[0].clone() else {
            vm_bail!(InvalidOpcode);
        };
        let after = st.c1_envelope_if(brk, c0, true);
        st.until(body, after)
    }

    #[instr(code = "e8", fmt = "WHILE", args(brk = false))]
    #[instr(code = "e318", fmt = "WHILEBRK", args(brk = true))]
    fn exec_while(st: &mut VmState, brk: bool) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let body = ok!(stack.pop_cont());
        let cond = ok!(stack.pop_cont());

        let cc = ok!(st.extract_cc(SaveCr::C0, None, None));
        let after = st.c1_envelope_if(brk, cc, true);
        st.loop_while(cond, body, after)
    }

    #[instr(code = "e9", fmt = "WHILEEND", args(brk = false))]
    #[instr(code = "e319", fmt = "WHILEENDBRK", args(brk = true))]
    fn exec_while_end(st: &mut VmState, brk: bool) -> VmResult<i32> {
        let cond = ok!(Rc::make_mut(&mut st.stack).pop_cont());
        let body = ok!(st.extract_cc(SaveCr::NONE, None, None));
        let Some(c0) = st.cr.c[0].clone() else {
            vm_bail!(InvalidOpcode);
        };
        let after = st.c1_envelope_if(brk, c0, true);
        st.loop_while(cond, body, after)
    }

    #[instr(code = "ea", fmt = "AGAIN", args(brk = false))]
    #[instr(code = "e31a", fmt = "AGAINBRK", args(brk = true))]
    fn exec_again(st: &mut VmState, brk: bool) -> VmResult<i32> {
        if brk {
            let cc = ok!(st.extract_cc(SaveCr::C0_C1, None, None));
            st.cr.c[1] = Some(cc);
        }
        let body = ok!(Rc::make_mut(&mut st.stack).pop_cont());
        st.again(body)
    }

    #[instr(code = "eb", fmt = "AGAINEND", args(brk = false))]
    #[instr(code = "e31b", fmt = "AGAINENDBRK", args(brk = true))]
    fn exec_again_end(st: &mut VmState, brk: bool) -> VmResult<i32> {
        if brk {
            st.c1_save_set();
        }
        let cc = ok!(st.extract_cc(SaveCr::NONE, None, None));
        st.again(cc)
    }

    // === Continuation change ===

    #[instr(code = "ecrn", fmt = "SETCONTARGS {r},{n}", args(n = ((args as i32 + 1) & 0xf) - 1))]
    fn exec_setcontargs(st: &mut VmState, r: u32, n: i32) -> VmResult<i32> {
        ok!(exec_setcontargs_common(st, r, n));
        Ok(0)
    }

    #[instr(code = "ed0p", fmt = "RETURNARGS {p}")]
    fn exec_return_args(st: &mut VmState, p: u32) -> VmResult<i32> {
        ok!(exec_return_args_common(st, p));
        Ok(0)
    }

    #[instr(code = "ed10", fmt = "RETURNVARARGS")]
    fn exec_return_varargs(st: &mut VmState) -> VmResult<i32> {
        let count = ok!(Rc::make_mut(&mut st.stack).pop_smallint_range(0, 255));
        ok!(exec_return_args_common(st, count));
        Ok(0)
    }

    #[instr(code = "ed11", fmt = "SETCONTVARARGS")]
    fn exec_setcont_varargs(st: &mut VmState) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let more = ok!(stack.pop_smallint_signed_range(-1, 255));
        let copy = ok!(stack.pop_smallint_range(0, 255));
        ok!(exec_setcontargs_common(st, copy, more));
        Ok(0)
    }

    #[instr(code = "ed12", fmt = "SETNUMVARARGS")]
    fn exec_setnum_varargs(st: &mut VmState) -> VmResult<i32> {
        let more = ok!(Rc::make_mut(&mut st.stack).pop_smallint_signed_range(-1, 255));
        ok!(exec_setcontargs_common(st, 0, more));
        Ok(0)
    }

    #[instr(code = "ed1e", fmt = "BLESS")]
    fn exec_bless(st: &mut VmState) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let code = ok!(stack.pop_cs());
        let cont = Rc::new(OrdCont::simple(Rc::unwrap_or_clone(code), st.cp.id()));
        ok!(stack.push_raw(cont.into_stack_value()));
        Ok(0)
    }

    #[instr(code = "ed1f", fmt = "BLESSVARARGS")]
    fn exec_bless_varargs(st: &mut VmState) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let more = ok!(stack.pop_smallint_signed_range(-1, 255));
        let copy = ok!(stack.pop_smallint_range(0, 255));
        ok!(exec_bless_args_common(st, copy, more));
        Ok(0)
    }

    #[instr(code = "ed4i", fmt = "PUSH c{i}")]
    fn exec_push_ctr(st: &mut VmState, i: u32) -> VmResult<i32> {
        vm_ensure!(ControlRegs::is_valid_idx(i as _), InvalidOpcode);
        ok!(Rc::make_mut(&mut st.stack).push_opt_raw(st.cr.get_as_stack_value(i as _)));
        Ok(0)
    }

    #[instr(code = "ed5i", fmt = "POP c{i}")]
    fn exec_pop_ctr(st: &mut VmState, i: u32) -> VmResult<i32> {
        vm_ensure!(ControlRegs::is_valid_idx(i as _), InvalidOpcode);
        let value = ok!(Rc::make_mut(&mut st.stack).pop());
        ok!(st.cr.set(i as _, value));
        Ok(0)
    }

    #[instr(code = "ed6i", fmt = "SETCONTCTR c{i}")]
    fn exec_setcont_ctr(st: &mut VmState, i: u32) -> VmResult<i32> {
        vm_ensure!(ControlRegs::is_valid_idx(i as _), InvalidOpcode);
        let stack = Rc::make_mut(&mut st.stack);
        let mut cont = ok!(stack.pop_cont());
        let value = ok!(stack.pop());
        ok!(force_cdata(&mut cont).save.define(i as _, value));
        ok!(stack.push_raw(cont.into_stack_value()));
        Ok(0)
    }

    #[instr(code = "ed7i", fmt = "SETRETCTR c{i}")]
    fn exec_setret_ctr(st: &mut VmState, i: u32) -> VmResult<i32> {
        vm_ensure!(ControlRegs::is_valid_idx(i as _), InvalidOpcode);
        let cont = st.cr.c[0].as_mut().expect("c0 should always be set");
        let value = ok!(Rc::make_mut(&mut st.stack).pop());
        ok!(force_cdata(cont).save.define(i as _, value));
        Ok(0)
    }

    #[instr(code = "ed8i", fmt = "SETALTCTR c{i}")]
    fn exec_setalt_ctr(st: &mut VmState, i: u32) -> VmResult<i32> {
        vm_ensure!(ControlRegs::is_valid_idx(i as _), InvalidOpcode);
        // TODO: Check if c1 is always set
        let cont = st.cr.c[1].as_mut().expect("c1 should always be set");
        let value = ok!(Rc::make_mut(&mut st.stack).pop());
        ok!(force_cdata(cont).save.define(i as _, value));
        Ok(0)
    }

    #[instr(code = "ed9i", fmt = "POPSAVE c{i}")]
    fn exec_popsave(st: &mut VmState, i: u32) -> VmResult<i32> {
        vm_ensure!(ControlRegs::is_valid_idx(i as _), InvalidOpcode);
        let stack = Rc::make_mut(&mut st.stack);
        let value = ok!(stack.pop());
        let mut c0 = st.cr.c[0].clone().expect("c0 should always be set");

        vm_ensure!(
            i > 0 || value.ty() == StackValueType::Cont,
            InvalidType {
                expected: StackValueType::Cont,
                actual: value.ty(),
            }
        );

        // NOTE: Is it ok to ignore redefinition errors?
        let prev = st
            .cr
            .get_as_stack_value(i as _)
            .unwrap_or_else(Stack::make_null);
        force_cdata(&mut c0).save.define(i as _, prev).ok();

        // TODO: Check if the order of setting c0 and `cr.set(..)` really matters
        if i == 0 {
            st.cr.c[0] = Some(c0);
            ok!(st.cr.set(i as _, value));
        } else {
            ok!(st.cr.set(i as _, value));
            st.cr.c[0] = Some(c0);
        }

        Ok(0)
    }

    #[instr(code = "edai", fmt = "SAVECTR c{i}")]
    fn exec_savectr(st: &mut VmState, i: u32) -> VmResult<i32> {
        vm_ensure!(ControlRegs::is_valid_idx(i as _), InvalidOpcode);

        let mut c0 = st.cr.c[0].clone().expect("c0 should always be set");

        let value = st
            .cr
            .get_as_stack_value(i as _)
            .unwrap_or_else(Stack::make_null);

        ok!(force_cdata(&mut c0).save.define(i as _, value));
        st.cr.c[0] = Some(c0);
        Ok(0)
    }

    #[instr(code = "edbi", fmt = "SAVEALTCTR c{i}")]
    fn exec_savealt_ctr(st: &mut VmState, i: u32) -> VmResult<i32> {
        vm_ensure!(ControlRegs::is_valid_idx(i as _), InvalidOpcode);

        // TODO: Check if c1 is always set
        let mut c1 = st.cr.c[1].clone().expect("c1 should always be set");

        let value = st
            .cr
            .get_as_stack_value(i as _)
            .unwrap_or_else(Stack::make_null);

        ok!(force_cdata(&mut c1).save.define(i as _, value));
        st.cr.c[1] = Some(c1);
        Ok(0)
    }

    #[instr(code = "edci", fmt = "SAVEBOTHCTR c{i}")]
    fn exec_saveboth_ctr(st: &mut VmState, i: u32) -> VmResult<i32> {
        vm_ensure!(ControlRegs::is_valid_idx(i as _), InvalidOpcode);

        let mut c0 = st.cr.c[0].clone().expect("c0 should always be set");
        let mut c1 = st.cr.c[1].clone().expect("c1 should always be set");

        let value = st
            .cr
            .get_as_stack_value(i as _)
            .unwrap_or_else(Stack::make_null);

        ok!(force_cdata(&mut c0).save.define(i as _, value.clone()));
        ok!(force_cdata(&mut c1).save.define(i as _, value));
        st.cr.c[0] = Some(c0);
        st.cr.c[1] = Some(c1);
        Ok(0)
    }

    #[instr(code = "ede0", fmt = "PUSHCTRX")]
    fn exec_push_ctr_var(st: &mut VmState) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let idx = ok!(stack.pop_smallint_range(0, 16)) as usize;
        let Some(value) = st.cr.get_as_stack_value(idx) else {
            vm_bail!(ControlRegisterOutOfRange(idx));
        };
        ok!(stack.push_raw(value));
        Ok(0)
    }

    #[instr(code = "ede1", fmt = "POPCTRX")]
    fn exec_pop_ctr_var(st: &mut VmState) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let idx = ok!(stack.pop_smallint_range(0, 16)) as usize;
        vm_ensure!(
            ControlRegs::is_valid_idx(idx),
            ControlRegisterOutOfRange(idx)
        );

        let value = ok!(stack.pop());
        ok!(st.cr.set(idx, value));
        Ok(0)
    }

    #[instr(code = "ede2", fmt = "SETCONTCTRX")]
    fn exec_setcont_ctr_var(st: &mut VmState) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let idx = ok!(stack.pop_smallint_range(0, 16)) as usize;
        vm_ensure!(
            ControlRegs::is_valid_idx(idx),
            ControlRegisterOutOfRange(idx)
        );
        let mut cont = ok!(stack.pop_cont());
        let value = ok!(stack.pop());
        ok!(force_cdata(&mut cont).save.define(idx, value));
        ok!(stack.push_raw(cont.into_stack_value()));
        Ok(0)
    }

    #[instr(code = "edf0", fmt = "BOOLAND", args(op = Compose::And))]
    #[instr(code = "edf1", fmt = "BOOLOR", args(op = Compose::Or))]
    #[instr(code = "edf2", fmt = "COMPOSBOTH", args(op = Compose::Both))]
    fn exec_compos(st: &mut VmState, op: Compose) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let value = ok!(stack.pop_cont());
        let mut cont = ok!(stack.pop_cont());
        let refs = &mut force_cdata(&mut cont).save;
        match op {
            Compose::And => refs.define_c0(&Some(value)),
            Compose::Or => refs.define_c1(&Some(value)),
            Compose::Both => {
                refs.define_c0(&Some(value.clone()));
                refs.define_c1(&Some(value));
            }
        }
        ok!(stack.push_raw(cont.into_stack_value()));
        Ok(0)
    }

    #[instr(code = "edf3", fmt = "ATEXIT")]
    fn exec_atexit(st: &mut VmState) -> VmResult<i32> {
        let mut cont = ok!(Rc::make_mut(&mut st.stack).pop_cont());
        force_cdata(&mut cont).save.define_c0(&st.cr.c[0]);
        st.cr.c[0] = Some(cont);
        Ok(0)
    }

    #[instr(code = "edf4", fmt = "ATEXITALT")]
    fn exec_atexit_alt(st: &mut VmState) -> VmResult<i32> {
        let mut cont = ok!(Rc::make_mut(&mut st.stack).pop_cont());
        force_cdata(&mut cont).save.define_c1(&st.cr.c[1]);
        st.cr.c[1] = Some(cont);
        Ok(0)
    }

    #[instr(code = "edf5", fmt = "SETEXITALT")]
    fn exec_setexit_alt(st: &mut VmState) -> VmResult<i32> {
        let mut cont = ok!(Rc::make_mut(&mut st.stack).pop_cont());
        let cr = force_cdata(&mut cont);
        cr.save.define_c0(&st.cr.c[0]);
        cr.save.define_c1(&st.cr.c[1]);
        st.cr.c[1] = Some(cont);
        Ok(0)
    }

    #[instr(code = "edf6", fmt = "THENRET")]
    fn exec_thenret(st: &mut VmState) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let mut cont = ok!(stack.pop_cont());
        force_cdata(&mut cont).save.define_c0(&st.cr.c[0]);
        ok!(stack.push_raw(cont.into_stack_value()));
        Ok(0)
    }

    #[instr(code = "edf7", fmt = "THENRETALT")]
    fn exec_thenret_alt(st: &mut VmState) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let mut cont = ok!(stack.pop_cont());
        force_cdata(&mut cont).save.define_c1(&st.cr.c[1]);
        ok!(stack.push_raw(cont.into_stack_value()));
        Ok(0)
    }

    #[instr(code = "edf8", fmt = "INVERT")]
    fn exec_invert(st: &mut VmState) -> VmResult<i32> {
        st.cr.c.swap(0, 1);
        Ok(0)
    }

    #[instr(code = "edf9", fmt = "BOOLEVAL")]
    fn exec_booleval(st: &mut VmState) -> VmResult<i32> {
        let cont = ok!(Rc::make_mut(&mut st.stack).pop_cont());

        let next = ok!(st.extract_cc(SaveCr::C0_C1, None, None));
        st.cr.c[0] = Some(Rc::new(PushIntCont {
            value: -1,
            next: next.clone(),
        }));
        st.cr.c[1] = Some(Rc::new(PushIntCont { value: 0, next }));

        st.jump(cont)
    }

    #[instr(code = "edfa", fmt = "SAMEALT", args(save = false))]
    #[instr(code = "edfb", fmt = "SAMEALTSAVE", args(save = true))]
    fn exec_samealt(st: &mut VmState, save: bool) -> VmResult<i32> {
        let [c0, c1, ..] = &mut st.cr.c;

        // TODO: Check if there are no ways to leave `None` in c0
        let c0 = c0.as_mut().expect("c0 should be always set");
        if save {
            force_cdata(c0).save.define_c1(c1);
        }

        *c1 = Some(c0.clone());
        Ok(0)
    }

    #[instr(code = "eern", fmt = "BLESSARGS {r},{n}", args(n = ((args as i32 + 1) & 0xf) - 1))]
    fn exec_bless_args(st: &mut VmState, r: u32, n: i32) -> VmResult<i32> {
        ok!(exec_bless_args_common(st, r, n));
        Ok(0)
    }

    // === Dictjump ===

    #[instr(code = "f0nn", fmt = "CALLDICT {n}")]
    #[instr(code = "f1$00nn#n", fmt = "CALLDICT {n}")]
    fn exec_calldict_short(st: &mut VmState, n: u32) -> VmResult<i32> {
        ok!(Rc::make_mut(&mut st.stack).push_int(n));
        let Some(c3) = st.cr.c[3].clone() else {
            vm_bail!(InvalidType {
                expected: StackValueType::Cont,
                actual: StackValueType::Null,
            });
        };
        st.call(c3)
    }

    #[instr(code = "f1$01nn#n", fmt = "JMPDICT {n}")]
    fn exec_jmpdict(st: &mut VmState, n: u32) -> VmResult<i32> {
        ok!(Rc::make_mut(&mut st.stack).push_int(n));
        let Some(c3) = st.cr.c[3].clone() else {
            vm_bail!(InvalidType {
                expected: StackValueType::Cont,
                actual: StackValueType::Null,
            });
        };
        st.jump(c3)
    }

    #[instr(code = "f1$10nn#n", fmt = "PREPAREDICT {n}")]
    fn exec_preparedict(st: &mut VmState, n: u32) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        ok!(stack.push_int(n));

        let c3 = match st.cr.c[3].clone() {
            Some(c3) => c3.into_stack_value(),
            None => Stack::make_null(),
        };
        ok!(stack.push_raw(c3));
        Ok(0)
    }

    // === Exceptions ===

    #[instr(code = "f2$00nn#n", fmt = "THROW {n}", args(mode = ThrowMode::Direct))]
    #[instr(code = "f2$01nn#n", fmt = "THROWIF {n}", args(mode = ThrowMode::Cond(true)))]
    #[instr(code = "f2$10nn#n", fmt = "THROWIFNOT {n}", args(mode = ThrowMode::Cond(false)))]
    #[instr(code = "f2c$0nnn#nn", fmt = "THROW {n}", args(mode = ThrowMode::Direct))]
    #[instr(code = "f2d$0nnn#nn", fmt = "THROWIF {n}", args(mode = ThrowMode::Cond(true)))]
    #[instr(code = "f2e$0nnn#nn", fmt = "THROWIFNOT {n}", args(mode = ThrowMode::Cond(false)))]
    fn exec_throw_fixed(st: &mut VmState, n: u32, mode: ThrowMode) -> VmResult<i32> {
        if let ThrowMode::Cond(cond) = mode {
            if ok!(Rc::make_mut(&mut st.stack).pop_bool()) != cond {
                return Ok(0);
            }
        }

        st.throw_exception(n as i32)
    }

    #[instr(code = "f2c$1nnn#n", fmt = "THROWARG {n}", args(mode = ThrowMode::Direct))]
    #[instr(code = "f2d$1nnn#n", fmt = "THROWARGIF {n}", args(mode = ThrowMode::Cond(true)))]
    #[instr(code = "f2e$1nnn#n", fmt = "THROWARGIFNOT {n}", args(mode = ThrowMode::Cond(false)))]
    fn exec_throw_arg_fixed(st: &mut VmState, n: u32, mode: ThrowMode) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);

        if let ThrowMode::Cond(cond) = mode {
            if ok!(stack.pop_bool()) != cond {
                ok!(stack.pop());
                return Ok(0);
            }
        }

        let arg = ok!(stack.pop());
        st.throw_exception_with_arg(n as i32, arg)
    }

    #[instr(code = "f2fx", range_to = "f2f6", fmt = ("{}", ThrowAnyArgs(x)))]
    fn exec_throw_any(st: &mut VmState, x: u32) -> VmResult<i32> {
        let args = ThrowAnyArgs(x);

        let stack = Rc::make_mut(&mut st.stack);
        let cond = if args.has_cond() {
            ok!(stack.pop_bool())
        } else {
            args.throw_cond()
        };

        let n = ok!(stack.pop_smallint_range(0, 0xffff));
        if cond != args.throw_cond() {
            if args.has_param() {
                ok!(stack.pop());
            }
            Ok(0)
        } else if args.has_param() {
            let arg = ok!(stack.pop());
            st.throw_exception_with_arg(n as i32, arg)
        } else {
            st.throw_exception(n as i32)
        }
    }

    #[instr(code = "f2ff", fmt = "TRY")]
    fn exec_try(st: &mut VmState) -> VmResult<i32> {
        exec_try_common(st, None)
    }

    #[instr(code = "f3pr", fmt = "TRYARGS {p},{r}")]
    fn exec_tryargs(st: &mut VmState, p: u32, r: u32) -> VmResult<i32> {
        exec_try_common(st, Some((p as u16, r as u16)))
    }

    // === Codepage ops ===
    #[instr(code = "fff0", fmt = "SETCPX")]
    fn exec_set_cp_any(st: &mut VmState) -> VmResult<i32> {
        let cp = ok!(Rc::make_mut(&mut st.stack).pop_smallint_signed_range(-0x8000, 0x7fff));
        ok!(st.force_cp(cp as i16 as u16));
        Ok(0)
    }

    #[instr(code = "ff00", fmt = "SETCP0", args(x = 0i16))]
    #[instr(
        code = "ffxx",
        range_from = "ff01",
        range_to = "fff0",
        fmt = "SETCP",
        args(x = (args & 0xff) as i16),
    )]
    #[instr(code = "fffx", range_from = "fff1", fmt = "SETCP {x}", args(x = (args & 0xf) as i16 - 16))]
    fn exec_set_cp(st: &mut VmState, x: i16) -> VmResult<i32> {
        ok!(st.force_cp(x as u16));
        Ok(0)
    }
}

fn exec_ref_prefix(st: &mut VmState, bits: u16, name: &str) -> VmResult<Rc<OrdCont>> {
    let code_range = st.code.range();
    vm_ensure!(code_range.has_remaining(bits, 1), InvalidOpcode);
    let ok = st.code.range_mut().skip_first(bits, 0).is_ok();
    debug_assert!(ok);

    let Some(code) = st.code.cell().reference_cloned(code_range.offset_refs()) else {
        vm_bail!(CellError(everscale_types::error::Error::CellUnderflow));
    };
    let ok = st.code.range_mut().skip_first(0, 1).is_ok();
    debug_assert!(ok);

    vm_log!("execute {name} ({})", code.repr_hash());
    st.ref_to_cont(code)
}

fn exec_cell_prefix(st: &mut VmState, bits: u16, name: &str) -> VmResult<Cell> {
    let code_range = st.code.range();
    vm_ensure!(code_range.has_remaining(bits, 1), InvalidOpcode);
    let ok = st.code.range_mut().skip_first(bits, 0).is_ok();
    debug_assert!(ok);

    let Some(cell) = st.code.cell().reference_cloned(code_range.offset_refs()) else {
        vm_bail!(CellError(everscale_types::error::Error::CellUnderflow));
    };
    let ok = st.code.range_mut().skip_first(0, 1).is_ok();
    debug_assert!(ok);

    vm_log!("execute {name} ({})", cell.repr_hash());
    Ok(cell)
}

fn exec_ifelse_ref_impl(st: &mut VmState, bits: u16, ref_first: bool) -> VmResult<i32> {
    let cont = {
        let code_range = st.code.range();
        vm_ensure!(code_range.has_remaining(bits, 1), InvalidOpcode);
        let ok = st.code.range_mut().skip_first(bits, 0).is_ok();
        debug_assert!(ok);

        let Some(cell) = st.code.cell().reference_cloned(code_range.offset_refs()) else {
            vm_bail!(CellError(everscale_types::error::Error::CellUnderflow));
        };
        let ok = st.code.range_mut().skip_first(0, 1).is_ok();
        debug_assert!(ok);

        let name = match ref_first {
            true => "IFREFELSE",
            false => "IFELSEREF",
        };

        vm_log!("execute {name} ({})", cell.repr_hash());

        let stack = Rc::make_mut(&mut st.stack);
        let cont = ok!(stack.pop_cont());

        if ok!(stack.pop_bool()) == ref_first {
            ok!(st.ref_to_cont(cell))
        } else {
            cont
        }
    };
    st.call(cont)
}

fn exec_setcontargs_common(st: &mut VmState, copy: u32, more: i32) -> VmResult<()> {
    let stack = Rc::make_mut(&mut st.stack);
    let mut cont = ok!(stack.pop_cont());
    if copy > 0 || more >= 0 {
        let cdata = force_cdata(&mut cont);

        if copy > 0 {
            ok!(cdata.require_nargs(copy as _));
            if let Some(cdata_stack) = &mut cdata.stack {
                ok!(Rc::make_mut(cdata_stack).move_from_stack(stack, copy as _));
            } else {
                cdata.stack = Some(ok!(stack.split_top(copy as _)));
            }

            st.gas.try_consume_stack_gas(cdata.stack.as_ref())?;

            if let Some(n) = &mut cdata.nargs {
                *n -= copy as u16;
            }
        }

        if more >= 0 {
            match &mut cdata.nargs {
                Some(n) => {
                    if *n as i32 > more {
                        *n = u16::MAX; // will throw an exception if run
                    }
                }
                None => cdata.nargs = Some(more as _),
            }
        }
    }

    ok!(stack.push_raw(cont.into_stack_value()));
    Ok(())
}

fn exec_return_args_common(st: &mut VmState, count: u32) -> VmResult<()> {
    let (copy, alt_stack) = {
        let stack = Rc::make_mut(&mut st.stack);
        if stack.depth() == count as usize {
            return Ok(());
        }

        let copy = stack.depth() - count as usize;
        let new_stack = ok!(stack.split_top(count as _));

        (copy, std::mem::replace(&mut st.stack, new_stack))
    };

    let cont = st.cr.c[0].as_mut().expect("c0 should always be set");
    let cdata = force_cdata(cont);
    ok!(cdata.require_nargs(copy));

    if let Some(cdata_stack) = &mut cdata.stack {
        ok!(Rc::make_mut(cdata_stack).move_from_stack(&mut Rc::unwrap_or_clone(alt_stack), copy))
    } else {
        cdata.stack = Some(alt_stack);
    }

    st.gas.try_consume_stack_gas(cdata.stack.as_ref())?;

    if let Some(n) = &mut cdata.nargs {
        *n -= copy as u16;
    }
    Ok(())
}

fn exec_bless_args_common(st: &mut VmState, copy: u32, more: i32) -> VmResult<()> {
    let stack = Rc::make_mut(&mut st.stack);
    let cs = ok!(stack.pop_cs());
    let new_stack = ok!(stack.split_top(copy as _));
    st.gas.try_consume_stack_gas(Some(&new_stack))?;
    let cont = Rc::new(OrdCont {
        data: ControlData {
            nargs: (more >= 0).then_some(more as _),
            stack: Some(new_stack),
            save: Default::default(),
            cp: Some(st.cp.id()),
        },
        code: Rc::unwrap_or_clone(cs),
    });
    ok!(stack.push_raw(cont.into_stack_value()));
    Ok(())
}

fn exec_try_common(st: &mut VmState, args: Option<(u16, u16)>) -> VmResult<i32> {
    let stack = Rc::make_mut(&mut st.stack);
    let mut handler_cont = ok!(stack.pop_cont());
    let cont = ok!(stack.pop_cont());
    let old_c2 = st.cr.c[2].clone();

    let (stack_copy, nargs) = args.unzip();
    let cc = ok!(st.extract_cc(SaveCr::FULL, stack_copy, nargs));

    let handler_cr = &mut force_cdata(&mut handler_cont).save;
    handler_cr.define_c2(&old_c2);
    if handler_cr.c[0].is_none() {
        handler_cr.c[0] = Some(cc.clone());
    }

    st.cr.c[0] = Some(cc);
    st.cr.c[2] = Some(handler_cont);
    st.jump(cont)
}

fn force_cdata(cont: &mut RcCont) -> &mut ControlData {
    if cont.get_control_data().is_some() {
        return dyn_clone::rc_make_mut(cont)
            .get_control_data_mut()
            .expect("always has control data");
    }

    *cont = Rc::new(ArgContExt {
        data: Default::default(),
        ext: cont.clone(), // TODO: Somehow reduce this `clone`
    });

    Rc::get_mut(cont)
        .expect("only one instance")
        .get_control_data_mut()
        .expect("always has control data")
}

#[derive(Debug, Clone, Copy)]
enum Compose {
    And,
    Or,
    Both,
}

#[derive(Debug, Clone, Copy)]
enum ThrowMode {
    Direct,
    Cond(bool),
}

#[derive(Clone, Copy)]
struct ThrowAnyArgs(u32);

impl ThrowAnyArgs {
    const fn has_param(self) -> bool {
        self.0 & 0b001 != 0
    }

    const fn has_cond(self) -> bool {
        self.0 & 0b110 != 0
    }

    const fn throw_cond(self) -> bool {
        self.0 & 0b010 != 0
    }
}

impl std::fmt::Display for ThrowAnyArgs {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let arg = if self.has_param() { "ARG" } else { "" };
        let cond = if self.has_cond() {
            if self.throw_cond() {
                "IF"
            } else {
                "IFNOT"
            }
        } else {
            ""
        };

        write!(f, "THROW{arg}ANY{cond}")
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cont::RcCont;
    use crate::stack::RcStackValue;
    use everscale_types::boc::Boc;
    use everscale_vm::cont::{ControlData, ControlRegs};
    use num_bigint::BigInt;
    use tracing_test::traced_test;

    #[test]
    #[traced_test]
    fn argument_contops() {
        assert_run_vm!(
            r#"
            PUSHINT 1
            PUSHCONT {
                PUSHINT 3
                PUSHINT 2
            }
            CALLXARGS 1, 2
            "#,
            [] => [int 3, int 2],
        );

        assert_run_vm!(
            r#"
            PUSHINT 1
            PUSHCONT {
                NOP
            }
            CALLXARGS 1, 1
            "#,
            [] => [int 1],
        );

        assert_run_vm!(
            r#"
            PUSHCONT {
                NOP
            }
            CALLXARGS 1, 0
            "#,
            [] => [int 0],
            exit_code: 2
        );

        assert_run_vm!(
            r#"
            PUSHCONT {
                PUSHINT 3
                PUSHINT 2
            }
            CALLXARGS 0, 3
            "#,
            [] => [int 0],
            exit_code: 2
        );

        assert_run_vm!(
            r#"
            PUSHCONT {
                PUSHINT 3
                PUSHINT 2
            }
            CALLXARGS 0, 3
            "#,
            [] => [int 0],
            exit_code: 2
        );

        assert_run_vm!(
            r#"
            PUSHCONT {
                PUSHINT 3
                PUSHINT 2
            }
            CALLXARGS 0, -1
            "#,
            [] => [int 3, int 2]
        );

        assert_run_vm!(
            r#"
            PUSHINT 1
            PUSHCONT {
                PUSHINT 3
                PUSHINT 2
            }
            CALLXARGS 1, -1
            "#,
            [] => [int 1, int 3, int 2]
        );

        assert_run_vm!(
            r#"
            PUSHINT 1
            PUSHINT 2
            PUSHCONT {
                PUSHINT 3
                PUSHINT 4
            }
            JMPXARGS 1
            PUSHINT 1
            "#,
            [] => [int 2, int 3, int 4]
        );

        assert_run_vm!(
            r#"
            PUSHINT 1
            PUSHINT 2
            PUSHCONT {
                PUSHINT 3
                PUSHINT 4
            }
            JMPXARGS 1
            PUSHINT 1
            "#,
            [] => [int 2, int 3, int 4]
        );

        assert_run_vm!(
            r#"
            PUSHINT 1
            PUSHCONT {
                PUSHINT 123
                PUSHINT 245
                RETARGS 2
            }
            EXECUTE
            "#,
            [] => [int 123, int 245]
        );
    }

    #[test]
    #[traced_test]
    fn basic_contops() {
        let cont: RcStackValue = Rc::new(crate::cont::PushIntCont {
            value: 1,
            next: Rc::new(crate::cont::PushIntCont {
                value: 2,
                next: Rc::new(crate::cont::QuitCont { exit_code: 0 }),
            }),
        });

        assert_run_vm!(
            "EXECUTE",
            [raw cont.clone()] => [int 1, int 2],
        );

        let code = Boc::decode(&everscale_asm_macros::tvmasm! {
            r#"
            PUSHINT 1
            PUSHINT 2
            "#
        })
        .unwrap();

        let cont: RcStackValue = Rc::new(crate::cont::OrdCont::simple(
            code.into(),
            crate::instr::codepage0().id(),
        ));

        assert_run_vm!(
            "EXECUTE",
            [raw cont.clone()] => [int 1, int 2],
        );

        assert_run_vm!(
            "JMPX",
            [raw cont.clone()] => [int 1, int 2],
        );
    }

    #[test]
    #[traced_test]
    fn conditional_contops() {
        let code = Boc::decode(&everscale_asm_macros::tvmasm! {
            r#"
            PUSHINT 1
            PUSHINT 2
            IFRET
            PUSHINT 0
            "#
        })
        .unwrap();

        let cont: RcStackValue = Rc::new(crate::cont::OrdCont::simple(
            code.into(),
            crate::instr::codepage0().id(),
        ));

        assert_run_vm!(
            "EXECUTE",
            [raw cont.clone()] => [int 1]
        );

        //--------

        let code = Boc::decode(&everscale_asm_macros::tvmasm! {
            r#"
            PUSHINT 1
            PUSHINT 0
            IFRET
            PUSHINT 2
            "#
        })
        .unwrap();

        let cont: RcStackValue = Rc::new(crate::cont::OrdCont::simple(
            code.into(),
            crate::instr::codepage0().id(),
        ));

        assert_run_vm!(
            "EXECUTE",
            [raw cont.clone()] => [int 1, int 2]
        );

        assert_run_vm!(
            "IFRET",
            [null] => [int 0],
            exit_code: 7
        );

        //-------

        let code = Boc::decode(&everscale_asm_macros::tvmasm! {
            r#"
            PUSHINT 2
            PUSHINT 0
            IFNOTRET
            PUSHINT 1
            "#
        })
        .unwrap();

        let cont: RcStackValue = Rc::new(crate::cont::OrdCont::simple(
            code.into(),
            crate::instr::codepage0().id(),
        ));

        assert_run_vm!(
            "EXECUTE",
            [raw cont.clone()] => [int 2]
        );

        //--------

        let code = Boc::decode(&everscale_asm_macros::tvmasm! {
            r#"
            PUSHINT 2
            PUSHINT 1
            IFNOTRET
            PUSHINT 1
            "#
        })
        .unwrap();

        let cont: RcStackValue = Rc::new(crate::cont::OrdCont::simple(
            code.into(),
            crate::instr::codepage0().id(),
        ));

        assert_run_vm!(
            "EXECUTE",
            [raw cont.clone()] => [int 2, int 1]
        );

        //-------------

        let code = Boc::decode(&everscale_asm_macros::tvmasm! {
            r#"
            PUSHINT 1
            PUSHINT 2
            "#
        })
        .unwrap();

        let cont: RcStackValue = Rc::new(crate::cont::OrdCont::simple(
            code.into(),
            crate::instr::codepage0().id(),
        ));

        assert_run_vm!(
            "IF",
            [int 0, raw cont.clone()] => [],
        );
        assert_run_vm!(
            "IF",
            [int 123, raw cont.clone()] => [int 1, int 2],
        );

        assert_run_vm!(
            "IFNOT",
            [int 1, raw cont.clone()] => [],
        );

        assert_run_vm!(
            "IFNOT",
            [int 13890, raw cont.clone()] => [],
        );

        assert_run_vm!(
            "IFNOT",
            [int 0, raw cont.clone()] => [int 1, int 2],
        );

        //-------

        let code1 = Boc::decode(&everscale_asm_macros::tvmasm! {
            r#"
            PUSHINT 1
            PUSHINT 2
            "#
        })
        .unwrap();

        let cont1: RcStackValue = Rc::new(crate::cont::OrdCont::simple(
            code1.into(),
            crate::instr::codepage0().id(),
        ));

        let code2 = Boc::decode(&everscale_asm_macros::tvmasm! {
            r#"
            PUSHINT 3
            PUSHINT 4
            "#
        })
        .unwrap();

        let cont2: RcStackValue = Rc::new(crate::cont::OrdCont::simple(
            code2.into(),
            crate::instr::codepage0().id(),
        ));

        assert_run_vm!(
            "IFELSE",
            [int 0, raw cont1.clone(), raw cont2.clone()] => [int 3, int 4]
        );

        assert_run_vm!(
            "IFELSE",
            [int 1, raw cont1.clone(), raw cont2.clone()] => [int 1, int 2]
        );

        assert_run_vm!(
            "IFELSE",
            [null, raw cont1.clone(), raw cont2.clone()] => [int 0],
            exit_code: 7
        );
    }

    #[test]
    #[traced_test]
    fn conditional_refcontops() {
        let code = Boc::decode(&everscale_asm_macros::tvmasm! {
            r#"
            PUSHINT 1
            PUSHINT 2
            "#
        })
        .unwrap();

        let cont: RcStackValue = Rc::new(crate::cont::OrdCont::simple(
            code.into(),
            crate::instr::codepage0().id(),
        ));

        // assert_run_vm!(
        //     "IFREF",
        //     code.as,
        //     [int 0, raw cont.clone()] => [],
        // );

        assert_run_vm!(
            "IF",
            [int 123, raw cont.clone()] => [int 1, int 2],
        );

        assert_run_vm!(
            r#"PUSHCONT { PUSHINT 1 PUSHINT 2 } EXECUTE"#,
            [] => [int 1, int 2],
        );

        assert_run_vm!(
            "IF",
            [int 0, raw cont.clone()] => [],
        );

        assert_run_vm!(
            "IFNOT",
            [int 1, raw cont.clone()] => [],
        );

        assert_run_vm!(
            "IFNOT",
            [int 13890, raw cont.clone()] => [],
        );

        assert_run_vm!(
            "IFNOT",
            [int 0, raw cont.clone()] => [int 1, int 2],
        );
    }

    //#[test]
    //#[traced_test]
    fn conditional_altcontops() {
        //----

        let code_c1 = Boc::decode(&everscale_asm_macros::tvmasm! {
            r#"
            PUSHINT 1
            "#
        })
        .unwrap();
        let cont_c1 = crate::cont::OrdCont::simple(code_c1.into(), crate::instr::codepage0().id());

        let mut cr = ControlRegs::default();
        cr.set_c(1, Rc::new(cont_c1));

        let code_c0 = Boc::decode(&everscale_asm_macros::tvmasm! {
            r#"
            PUSHINT 2
            "#
        })
        .unwrap();

        let cont_c0: RcStackValue = Rc::new(crate::cont::OrdCont {
            data: ControlData {
                nargs: None,
                stack: None,
                save: cr,
                cp: Some(crate::instr::codepage0().id()),
            },
            code: code_c0.into(),
        });

        assert_run_vm!(
            "IFRETALT",
            [int 1, raw cont_c0.clone()] => [int 1]
        );
    }

    #[test]
    #[traced_test]
    fn loops() {
        // REPEAT
        let code = Boc::decode(&everscale_asm_macros::tvmasm! {
            r#"
            PUSHINT 2
            "#
        })
        .unwrap();
        let cont: RcStackValue = Rc::new(crate::cont::OrdCont::simple(
            code.into(),
            crate::instr::codepage0().id(),
        ));

        let code1 = Boc::decode(&everscale_asm_macros::tvmasm! {
            r#"
            PUSHINT 2
            PUSHINT 1
            "#
        })
        .unwrap();
        let cont1: RcStackValue = Rc::new(crate::cont::OrdCont::simple(
            code1.into(),
            crate::instr::codepage0().id(),
        ));

        assert_run_vm!(
            "REPEAT",
            [int 5, raw cont.clone()] => [int 2, int 2,int 2, int 2, int 2 ]
        );

        assert_run_vm!(
            "REPEAT",
            [int -1, raw cont.clone()] => []
        );

        assert_run_vm!(
            "REPEAT",
            [int (BigInt::from(1) << 31), raw cont.clone()] => [int 0],
            exit_code: 5
        );

        // REPEATEND

        assert_run_vm!(
            "REPEATEND PUSHINT 2",
            [int 3] => [int 2, int 2, int 2]
        );

        //UNTIL
        assert_run_vm!(
            "UNTIL",
            [raw cont1.clone()] => [int 2]
        );

        //UNTILEND
        // TODO: case for other branch
        assert_run_vm!(
            "UNTILEND PUSHINT 0 PUSHINT 1",
            [int 3] => [int 3, int 0]
        );

        // WHILE
        let code0 = Boc::decode(&everscale_asm_macros::tvmasm! {
            r#"
            PUSHINT 2
            "#
        })
        .unwrap();
        let c0: RcStackValue = Rc::new(crate::cont::OrdCont::simple(
            code0.into(),
            crate::instr::codepage0().id(),
        ));

        let code1 = Boc::decode(&everscale_asm_macros::tvmasm! {
            r#"
            PUSHINT 0
            "#
        })
        .unwrap();
        let c1: RcStackValue = Rc::new(crate::cont::OrdCont::simple(
            code1.into(),
            crate::instr::codepage0().id(),
        ));

        assert_run_vm!(
            "WHILE",
            [int 2, raw c1.clone(), raw c0.clone()] => [int 2]
        );

        // WHILEEND
        // TODO: case for other branch
        assert_run_vm!(
            "WHILEEND PUSHINT 1",
            [int 2, raw c1.clone()] => [int 2]
        );

        // AGAIN
        // TODO: TEST MORE CASES

        let code_c0 = Boc::decode(&everscale_asm_macros::tvmasm! {
            r#"
            PUSHINT 2
            RETALT
            "#
        })
        .unwrap();

        let cont_c0: RcStackValue = Rc::new(crate::cont::OrdCont::simple(
            code_c0.into(),
            crate::instr::codepage0().id(),
        ));

        //TODO: probably this behaviour with exit code 1 is okay. Add more cases with more loops

        assert_run_vm!(
            "AGAIN",
            [int 2, raw cont_c0.clone()] => [int 2, int 2],
            exit_code: 1
        );

        // AGAINEND
        assert_run_vm!(
            "AGAINEND PUSHINT 2 RETALT",
            [int 2] => [int 2, int 2],
            exit_code: 1
        );

        //REPEATBRK

        let code_c0 = Boc::decode(&everscale_asm_macros::tvmasm! {
            r#"
            PUSHINT 0
            DUMPSTK
            SWAP
            DEC
            DUP
            PUSHCONT {
                DROP
                RETALT
            }
            IFNOT
            "#
        })
        .unwrap();

        let cont_c0: RcStackValue = Rc::new(crate::cont::OrdCont::simple(
            code_c0.into(),
            crate::instr::codepage0().id(),
        ));

        assert_run_vm!(
            "REPEATBRK",
            [int 5, int 10, raw cont_c0.clone()] => [int 0, int 0, int 0, int 0, int 0]
        );

        //REPEATENDBRK

        assert_run_vm!(
            r#"
            PUSHCONT {
                REPEATENDBRK
                PUSHINT 0
                SWAP
                DEC
                DUP
                PUSHCONT {
                    DROP
                    RETALT
                }
                IFNOT
                POP s1
            }
            EXECUTE
            "#,
            [int 5, int 10] => [int 0]
        );

        let code_c0 = Boc::decode(&everscale_asm_macros::tvmasm! {
            r#"
            INC
            SWAP
            DUP
            PUSHCONT {
                DROP
                RETALT
            }
            IFNOT
            SWAP
            DUMPSTK
            "#
        })
        .unwrap();

        let cont_c0: RcStackValue = Rc::new(crate::cont::OrdCont::simple(
            code_c0.into(),
            crate::instr::codepage0().id(),
        ));

        assert_run_vm!(
            "UNTILBRK",
            [int 0, int -5, raw cont_c0.clone()] => [int -4]
        );
    }
}
