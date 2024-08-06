use std::borrow::Cow;
use std::rc::Rc;

use everscale_types::cell::{Cell, CellBuilder, CellFamily, CellSlice, DynCell};
use everscale_types::error::Error;
use everscale_vm_proc::vm_module;
use num_bigint::{BigInt, Sign};
use num_traits::{ToPrimitive, Zero};

use crate::error::{VmError, VmResult};
use crate::stack::{RcStackValue, Stack};
use crate::state::VmState;
use crate::util::{bitsize, OwnedCellSlice};

pub struct Cellops;

#[vm_module]
impl Cellops {
    // === Serializer ops ===

    #[instr(code = "c8", fmt = "NEWC")]
    fn exec_new_builder(st: &mut VmState) -> VmResult<i32> {
        ok!(Rc::make_mut(&mut st.stack).push(CellBuilder::new()));
        Ok(0)
    }

    #[instr(code = "c9", fmt = "ENDC")]
    fn exec_builder_to_cell(st: &mut VmState) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let builder = stack.pop_builder()?;

        // TODO: Use `build_ext`
        let cell = Rc::unwrap_or_clone(builder).build()?;
        ok!(stack.push(cell));
        Ok(0)
    }

    #[instr(code = "caxx", fmt = "STI {x}", args(x = (args & 0xff) + 1, signed = true))]
    #[instr(code = "cbxx", fmt = "STU {x}", args(x = (args & 0xff) + 1, signed = false))]
    fn exec_store_int(st: &mut VmState, x: u32, signed: bool) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        exec_store_int_common(stack, x as u16, StoreIntArgs::from_sign(signed))
    }

    #[instr(code = "cc", fmt = "STREF", args(quiet = false))]
    #[instr(code = "cf10", fmt = "STREF", args(quiet = false))]
    #[instr(code = "cf18", fmt = "STREFQ", args(quiet = true))]
    fn exec_store_ref(st: &mut VmState, quiet: bool) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let mut builder = ok!(stack.pop_builder());
        let cell = ok!(stack.pop_cell());

        if !builder.has_capacity(0, 1) {
            return finish_store_overflow(stack, cell, builder, quiet);
        }

        Rc::make_mut(&mut builder).store_reference(Rc::unwrap_or_clone(cell))?;

        finish_store_ok(stack, builder, quiet)
    }

    #[instr(code = "cd", fmt = "ENDCST", args(quiet = false))]
    #[instr(code = "cf15", fmt = "STBREFR", args(quiet = false))]
    #[instr(code = "cf1d", fmt = "STBREFRQ", args(quiet = true))]
    fn exec_store_builder_as_ref_rev(st: &mut VmState, quiet: bool) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let child_builder = ok!(stack.pop_builder());
        let mut builder = ok!(stack.pop_builder());

        if !builder.has_capacity(0, 1) {
            return finish_store_overflow(stack, builder, child_builder, quiet);
        }

        // TODO: Use `build_ext`
        let cell = Rc::unwrap_or_clone(child_builder).build()?;
        Rc::make_mut(&mut builder).store_reference(cell)?;

        finish_store_ok(stack, builder, quiet)
    }

    #[instr(code = "ce", fmt = "STSLICE", args(quiet = false))]
    #[instr(code = "cf12", fmt = "STSLICE", args(quiet = false))]
    #[instr(code = "cf1a", fmt = "STSLICEQ", args(quiet = true))]
    fn exec_store_slice(st: &mut VmState, quiet: bool) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let mut builder = ok!(stack.pop_builder());
        let cs = ok!(stack.pop_cs());

        if !cs.fits_into(&builder) {
            return finish_store_overflow(stack, cs, builder, quiet);
        }

        // TODO: Is it ok to store special cells data as is?
        let slice = cs.apply_allow_special();
        Rc::make_mut(&mut builder).store_slice(slice)?;

        finish_store_ok(stack, builder, quiet)
    }

    #[instr(code = "cf0$0sss", fmt = ("{}", s.display_x()), args(s = StoreIntArgs(args)))]
    fn exec_store_int_var(st: &mut VmState, s: StoreIntArgs) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let bits = ok!(stack.pop_smallint_range(0, 256 + s.is_signed() as u32));
        exec_store_int_common(stack, bits as u16, s)
    }

    #[instr(
        code = "cf0$1sss#n",
        fmt = ("{} {n}", s.display()),
        args(s = StoreIntArgs(args >> 8), n = (args & 0xff) + 1),
    )]
    fn exec_store_int_fixed(st: &mut VmState, s: StoreIntArgs, n: u32) -> VmResult<i32> {
        exec_store_int_common(Rc::make_mut(&mut st.stack), n as _, s)
    }

    #[instr(code = "cf11", fmt = "STBREF", args(quiet = false))]
    #[instr(code = "cf19", fmt = "STBREFQ", args(quiet = true))]
    fn exec_store_builder_as_ref(st: &mut VmState, quiet: bool) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let mut builder = ok!(stack.pop_builder());
        let child_builder = ok!(stack.pop_builder());

        if !builder.has_capacity(0, 1) {
            return finish_store_overflow(stack, child_builder, builder, quiet);
        }

        // TODO: Use `build_ext`
        let cell = Rc::unwrap_or_clone(child_builder).build()?;
        Rc::make_mut(&mut builder).store_reference(cell)?;

        finish_store_ok(stack, builder, quiet)
    }

    #[instr(code = "cf13", fmt = "STB", args(quiet = false))]
    #[instr(code = "cf1b", fmt = "STBQ", args(quiet = true))]
    fn exec_store_builder(st: &mut VmState, quiet: bool) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let mut builder = ok!(stack.pop_builder());
        let other_builder = ok!(stack.pop_builder());

        if !builder.has_capacity(other_builder.bit_len(), other_builder.reference_count()) {
            return finish_store_overflow(stack, other_builder, builder, quiet);
        }

        Rc::make_mut(&mut builder).store_builder(&other_builder)?;

        finish_store_ok(stack, builder, quiet)
    }

    #[instr(code = "cf14", fmt = "STREFR", args(quiet = false))]
    #[instr(code = "cf1c", fmt = "STREFRQ", args(quiet = true))]
    fn exec_store_ref_rev(st: &mut VmState, quiet: bool) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let cell = ok!(stack.pop_cell());
        let mut builder = ok!(stack.pop_builder());

        if !builder.has_capacity(0, 1) {
            return finish_store_overflow(stack, builder, cell, quiet);
        }

        Rc::make_mut(&mut builder).store_reference(Rc::unwrap_or_clone(cell))?;

        finish_store_ok(stack, builder, quiet)
    }

    #[instr(code = "cf16", fmt = "STSLICER", args(quiet = false))]
    #[instr(code = "cf1e", fmt = "STSLICERQ", args(quiet = true))]
    fn exec_store_slice_rev(st: &mut VmState, quiet: bool) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let cs = ok!(stack.pop_cs());
        let mut builder = ok!(stack.pop_builder());

        if !cs.fits_into(&builder) {
            return finish_store_overflow(stack, builder, cs, quiet);
        }

        // TODO: Is it ok to store special cells data as is?
        let slice = cs.apply_allow_special();
        Rc::make_mut(&mut builder).store_slice(slice)?;

        finish_store_ok(stack, builder, quiet)
    }

    #[instr(code = "cf17", fmt = "STBR", args(quiet = false))]
    #[instr(code = "cf1f", fmt = "STBRQ", args(quiet = true))]
    fn exec_store_builder_rev(st: &mut VmState, quiet: bool) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let other_builder = ok!(stack.pop_builder());
        let mut builder = ok!(stack.pop_builder());

        if !builder.has_capacity(other_builder.bit_len(), other_builder.reference_count()) {
            return finish_store_overflow(stack, builder, other_builder, quiet);
        }

        Rc::make_mut(&mut builder).store_builder(&other_builder)?;

        finish_store_ok(stack, builder, quiet)
    }

    // TODO: exec_store_const_ref

    #[instr(code = "cf23", fmt = "ENDXC")]
    fn exec_builder_to_special_cell(st: &mut VmState) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);

        let special = ok!(stack.pop_bool());
        let mut builder = Rc::unwrap_or_clone(ok!(stack.pop_builder()));

        builder.set_exotic(special);

        // TODO: Use `build_ext`
        // TODO: Test if `special` build fails with ordinary cell type in first 8 bits
        let cell = builder.build()?;

        ok!(stack.push(cell));
        Ok(0)
    }

    // TODO: exec_store_le_int

    #[instr(code = "cf30", fmt = "BDEPTH")]
    fn exec_builder_depth(st: &mut VmState) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let builder = ok!(stack.pop_builder());

        let depth = compute_depth(builder.references());
        ok!(stack.push_int(depth));
        Ok(0)
    }

    #[instr(code = "cf31", fmt = "BBITS")]
    fn exec_builder_bits(st: &mut VmState) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let builder = ok!(stack.pop_builder());
        ok!(stack.push_int(builder.bit_len()));
        Ok(0)
    }

    #[instr(code = "cf32", fmt = "BREFS")]
    fn exec_builder_refs(st: &mut VmState) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let builder = ok!(stack.pop_builder());
        ok!(stack.push_int(builder.reference_count()));
        Ok(0)
    }

    #[instr(code = "cf33", fmt = "BBITREFS")]
    fn exec_builder_bits_refs(st: &mut VmState) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let builder = ok!(stack.pop_builder());
        ok!(stack.push_int(builder.bit_len()));
        ok!(stack.push_int(builder.reference_count()));
        Ok(0)
    }

    #[instr(code = "cf35", fmt = "BREMBITS")]
    fn exec_builder_rem_bits(st: &mut VmState) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let builder = ok!(stack.pop_builder());
        ok!(stack.push_int(builder.spare_bits_capacity()));
        Ok(0)
    }

    #[instr(code = "cf36", fmt = "BREMREFS")]
    fn exec_builder_rem_refs(st: &mut VmState) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let builder = ok!(stack.pop_builder());
        ok!(stack.push_int(builder.spare_refs_capacity()));
        Ok(0)
    }

    #[instr(code = "cf37", fmt = "BREMBITREFS")]
    fn exec_builder_rem_bits_refs(st: &mut VmState) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let builder = ok!(stack.pop_builder());
        ok!(stack.push_int(builder.spare_bits_capacity()));
        ok!(stack.push_int(builder.spare_refs_capacity()));
        Ok(0)
    }

    #[instr(code = "cf38xx", fmt = "BCHKBITS {x}", args(x = (args & 0xff) + 1, quiet = false))]
    #[instr(code = "cf3cxx", fmt = "BCHKBITSQ {x}", args(x = (args & 0xff) + 1, quiet = true))]
    fn exec_builder_chk_bits(st: &mut VmState, x: u32, quiet: bool) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let builder = ok!(stack.pop_builder());

        let fits = builder.has_capacity(x as u16, 0);
        if quiet {
            ok!(stack.push_int(if fits { -1 } else { 0 }));
        } else if !fits {
            vm_bail!(CellError(Error::CellOverflow));
        }
        Ok(0)
    }

    #[instr(code = "cf39", fmt = "BCHKBITS", args(mode = CheckMode::Bits, quiet = false))]
    #[instr(code = "cf3a", fmt = "BCHKREFS", args(mode = CheckMode::Refs, quiet = false))]
    #[instr(code = "cf3b", fmt = "BCHKBITREFS", args(mode = CheckMode::BitRefs, quiet = false))]
    #[instr(code = "cf3d", fmt = "BCHKBITSQ", args(mode = CheckMode::Bits, quiet = true))]
    #[instr(code = "cf3e", fmt = "BCHKREFSQ", args(mode = CheckMode::Refs, quiet = true))]
    #[instr(code = "cf3f", fmt = "BCHKBITREFSQ", args(mode = CheckMode::BitRefs, quiet = true))]
    fn exec_builder_chk_bits_refs(st: &mut VmState, mode: CheckMode, quiet: bool) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);

        // TODO: Check why `7` is the max value for refs in the original code
        let (bits, refs) = match mode {
            CheckMode::Bits => (ok!(stack.pop_smallint_range(0, 1023)), 0),
            CheckMode::Refs => (0, ok!(stack.pop_smallint_range(0, 7))),
            CheckMode::BitRefs => {
                let refs = ok!(stack.pop_smallint_range(0, 7));
                let bits = ok!(stack.pop_smallint_range(0, 1023));
                (bits, refs)
            }
        };
        let builder = ok!(stack.pop_builder());

        let fits = builder.has_capacity(bits as u16, refs as u8);
        if quiet {
            ok!(stack.push_int(if fits { -1 } else { 0 }));
        } else if !fits {
            vm_bail!(CellError(Error::CellOverflow));
        }
        Ok(0)
    }

    #[instr(code = "cf40", fmt = "STZEROES", args(value = Some(false)))]
    #[instr(code = "cf41", fmt = "STONES", args(value = Some(true)))]
    #[instr(code = "cf42", fmt = "STSAME", args(value = None))]
    fn exec_store_same(st: &mut VmState, value: Option<bool>) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);

        let value = match value {
            Some(value) => value,
            None => ok!(stack.pop_smallint_range(0, 1)) != 0,
        };
        let bits = ok!(stack.pop_smallint_range(0, 1023));
        let mut builder = ok!(stack.pop_builder());

        vm_ensure!(
            builder.has_capacity(bits as _, 0),
            CellError(Error::CellOverflow)
        );

        {
            let builder = Rc::make_mut(&mut builder);
            match value {
                true => builder.store_ones(bits as _)?,
                false => builder.store_zeros(bits as _)?,
            }
        }

        ok!(stack.push_raw(builder));
        Ok(0)
    }

    // TODO: exec_store_const_slice

    // === Deserializer ops ===

    #[instr(code = "d0", fmt = "CTOS")]
    fn exec_cell_to_slice(st: &mut VmState) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let cell = ok!(stack.pop_cell());

        // TODO: Load with gas consumer
        let cs = OwnedCellSlice::new(Rc::unwrap_or_clone(cell));
        ok!(stack.push(cs));
        Ok(0)
    }

    #[instr(code = "d1", fmt = "ENDS")]
    fn exec_slice_chk_empty(st: &mut VmState) -> VmResult<i32> {
        let cs = ok!(Rc::make_mut(&mut st.stack).pop_cs());
        let range = cs.range();
        vm_ensure!(
            range.remaining_bits() == 0 && range.remaining_refs() == 0,
            CellError(Error::CellUnderflow)
        );
        Ok(0)
    }

    #[instr(code = "d2xx", fmt = "LDI {x}", args(x = (args & 0xff) + 1, signed = true))]
    #[instr(code = "d3xx", fmt = "LDU {x}", args(x = (args & 0xff) + 1, signed = false))]
    fn exec_load_int_fixed(st: &mut VmState, x: u32, signed: bool) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        exec_load_int_common(stack, x as _, LoadIntArgs::from_sign(signed))
    }

    #[instr(code = "d4", fmt = "LDREF")]
    fn exec_load_ref(st: &mut VmState) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let mut cs = ok!(stack.pop_cs());
        vm_ensure!(
            cs.range().remaining_refs() > 0,
            CellError(Error::CellUnderflow)
        );

        let mut slice = cs.apply_allow_special();
        let cell = slice.load_reference_cloned()?;
        ok!(stack.push(cell));

        let range = slice.range();
        Rc::make_mut(&mut cs).set_range(range);
        ok!(stack.push_raw(cs));
        Ok(0)
    }

    #[instr(code = "d5", fmt = "LDREFRTOS")]
    fn exec_load_ref_rev_to_slice(st: &mut VmState) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let mut cs = ok!(stack.pop_cs());
        vm_ensure!(
            cs.range().remaining_refs() > 0,
            CellError(Error::CellUnderflow)
        );

        let mut slice = cs.apply_allow_special();
        let cell = slice.load_reference_cloned()?;
        // TODO: Load with gas consumer
        ok!(stack.push(OwnedCellSlice::new(cell)));

        let range = slice.range();
        Rc::make_mut(&mut cs).set_range(range);
        ok!(stack.push_raw(cs));
        Ok(0)
    }

    #[instr(code = "d6xx", fmt = "LDSLICE {x}", args(x = (args & 0xff) + 1))]
    fn exec_load_slice_fixed(st: &mut VmState, x: u32) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        exec_load_slice_common(stack, x as _, LoadSliceArgs(0))
    }

    #[instr(code = "d70$0sss", fmt = ("{}", s.display_x()), args(s = LoadIntArgs(args)))]
    fn exec_load_int_var(st: &mut VmState, s: LoadIntArgs) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let bits = ok!(stack.pop_smallint_range(0, 256 + s.is_signed() as u32));
        exec_load_int_common(stack, bits as _, s)
    }

    #[instr(
        code = "d70$1sss#n",
        fmt = ("{} {n}", s.display()),
        args(s = LoadIntArgs(args >> 8), n = (args & 0xff) + 1)
    )]
    fn exec_load_int_fixed2(st: &mut VmState, s: LoadIntArgs, n: u32) -> VmResult<i32> {
        exec_load_int_common(Rc::make_mut(&mut st.stack), n as _, s)
    }

    #[instr(code = "d71$0xxx", fmt = "PLDUZ {x}", args(x = ((args & 7) + 1) << 5))]
    fn exec_preload_uint_fixed_0e(st: &mut VmState, x: u32) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let mut cs = ok!(stack.pop_cs());

        let (int, range) = {
            let mut slice = cs.apply_allow_special();

            let ld_bits = std::cmp::min(slice.remaining_bits(), x as _);
            let int = match x {
                0..=64 => {
                    let value = slice
                        .load_uint(ld_bits)?
                        .checked_shl(x - ld_bits as u32)
                        .unwrap_or_default();
                    Some(BigInt::from(value))
                }
                65..=256 => {
                    // Extra bits after loading
                    let rshift = (8 - ld_bits as u32 % 8) % 8;
                    // Zero-padding
                    let lshift = x - ld_bits as u32;

                    let mut buffer = [0u8; 32];
                    let mut int = slice
                        .load_raw(&mut buffer, ld_bits)
                        .map(|buffer| BigInt::from_bytes_be(Sign::Plus, buffer))?;

                    // Combine shifts
                    match rshift.cmp(&lshift) {
                        std::cmp::Ordering::Less => {
                            int <<= lshift - rshift;
                        }
                        std::cmp::Ordering::Greater => {
                            int >>= rshift - lshift;
                        }
                        std::cmp::Ordering::Equal => {}
                    }

                    Some(int)
                }
                _ => None,
            };

            (int, slice.range())
        };

        Rc::make_mut(&mut cs).set_range(range);
        ok!(stack.push_raw(cs));

        ok!(match int {
            Some(int) => stack.push_int(int),
            None => stack.push_nan(),
        });
        Ok(0)
    }

    #[instr(code = "d71$10ss", fmt = ("{}", s.display_x()), args(s = LoadSliceArgs(args)))]
    fn exec_load_slice(st: &mut VmState, s: LoadSliceArgs) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let bits = ok!(stack.pop_smallint_range(0, 1023));
        exec_load_slice_common(stack, bits as _, s)
    }

    #[instr(
        code = "d71$11ss#n",
        fmt = ("{} {n}", s.display()),
        args(s = LoadSliceArgs(args >> 8), n = (args & 0xff) + 1)
    )]
    fn exec_load_slice_fixed2(st: &mut VmState, s: LoadSliceArgs, n: u32) -> VmResult<i32> {
        exec_load_slice_common(Rc::make_mut(&mut st.stack), n as _, s)
    }

    #[instr(code = "d720", fmt = "SDCUTFIRST", args(op = SliceRangeOp::CutFirst))]
    #[instr(code = "d721", fmt = "SDSKIPFIRST", args(op = SliceRangeOp::SkipFirst))]
    #[instr(code = "d722", fmt = "SDCUTLAST", args(op = SliceRangeOp::CutLast))]
    #[instr(code = "d723", fmt = "SDSKIPLAST", args(op = SliceRangeOp::SkipLast))]
    fn exec_slice_range_op(st: &mut VmState, op: SliceRangeOp) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let bits = ok!(stack.pop_smallint_range(0, 1023)) as u16;
        let mut cs = ok!(stack.pop_cs());

        let mut range = cs.range();
        vm_ensure!(
            range.has_remaining(bits, 0),
            CellError(Error::CellUnderflow)
        );

        match op {
            SliceRangeOp::CutFirst => {
                range = range.get_prefix(bits, 0);
            }
            SliceRangeOp::SkipFirst => {
                let ok = range.try_advance(bits, 0);
                debug_assert!(ok);
            }
            SliceRangeOp::CutLast => {
                let ok = range.try_advance(range.remaining_bits() - bits, range.remaining_refs());
                debug_assert!(ok);
            }
            SliceRangeOp::SkipLast => {
                range = range.get_prefix(range.remaining_bits() - bits, range.remaining_refs());
            }
        };

        Rc::make_mut(&mut cs).set_range(range);
        ok!(stack.push_raw(cs));
        Ok(0)
    }

    #[instr(code = "d724", fmt = "SDSUBSTR")]
    fn exec_slice_substr(st: &mut VmState) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let len_bits = ok!(stack.pop_smallint_range(0, 1023)) as u16;
        let offset_bits = ok!(stack.pop_smallint_range(0, 1023)) as u16;
        let mut cs = ok!(stack.pop_cs());

        let mut range = cs.range();
        vm_ensure!(
            range.has_remaining(offset_bits + len_bits, 0),
            CellError(Error::CellUnderflow)
        );

        let ok = range.try_advance(offset_bits, 0);
        debug_assert!(ok);
        range = range.get_prefix(len_bits, 0);

        Rc::make_mut(&mut cs).set_range(range);
        ok!(stack.push_raw(cs));
        Ok(0)
    }

    #[instr(code = "d726", fmt = "SDBEGINSX", args(quiet = false))]
    #[instr(code = "d727", fmt = "SDBEGINSXQ", args(quiet = true))]
    fn exec_slice_begins_with(st: &mut VmState, quiet: bool) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let target = ok!(stack.pop_cs());
        let target = target.apply_allow_special();
        exec_slice_begins_with_common(stack, &target, quiet)
    }

    // TODO: exec_slice_begins_with_const

    #[instr(code = "d730", fmt = "SCUTFIRST", args(op = SliceRangeOp::CutFirst))]
    #[instr(code = "d731", fmt = "SSKIPFIRST", args(op = SliceRangeOp::SkipFirst))]
    #[instr(code = "d732", fmt = "SCUTLAST", args(op = SliceRangeOp::CutLast))]
    #[instr(code = "d733", fmt = "SSKIPLAST", args(op = SliceRangeOp::SkipLast))]
    fn exec_slice_full_range_op(st: &mut VmState, op: SliceRangeOp) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let refs = ok!(stack.pop_smallint_range(0, 4)) as u8;
        let bits = ok!(stack.pop_smallint_range(0, 1023)) as u16;
        let mut cs = ok!(stack.pop_cs());

        let mut range = cs.range();
        vm_ensure!(
            range.has_remaining(bits, refs),
            CellError(Error::CellUnderflow)
        );

        match op {
            SliceRangeOp::CutFirst => {
                range = range.get_prefix(bits, refs);
            }
            SliceRangeOp::SkipFirst => {
                let ok = range.try_advance(bits, refs);
                debug_assert!(ok);
            }
            SliceRangeOp::CutLast => {
                let ok =
                    range.try_advance(range.remaining_bits() - bits, range.remaining_refs() - refs);
                debug_assert!(ok);
            }
            SliceRangeOp::SkipLast => {
                range =
                    range.get_prefix(range.remaining_bits() - bits, range.remaining_refs() - refs);
            }
        };

        Rc::make_mut(&mut cs).set_range(range);
        ok!(stack.push_raw(cs));
        Ok(0)
    }

    #[instr(code = "d734", fmt = "SUBSLICE")]
    fn exec_subslice(st: &mut VmState) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let len_refs = ok!(stack.pop_smallint_range(0, 4)) as u8;
        let len_bits = ok!(stack.pop_smallint_range(0, 1023)) as u16;
        let offset_refs = ok!(stack.pop_smallint_range(0, 4)) as u8;
        let offset_bits = ok!(stack.pop_smallint_range(0, 1023)) as u16;
        let mut cs = ok!(stack.pop_cs());

        let mut range = cs.range();
        vm_ensure!(
            range.has_remaining(offset_bits + len_bits, offset_refs + len_refs),
            CellError(Error::CellUnderflow)
        );

        let ok = range.try_advance(offset_bits, offset_refs);
        debug_assert!(ok);
        range = range.get_prefix(len_bits, len_refs);

        Rc::make_mut(&mut cs).set_range(range);
        ok!(stack.push_raw(cs));
        Ok(0)
    }

    #[instr(code = "d736", fmt = "SPLIT", args(quiet = false))]
    #[instr(code = "d737", fmt = "SPLITQ", args(quiet = true))]
    fn exec_split(st: &mut VmState, quiet: bool) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let refs = ok!(stack.pop_smallint_range(0, 4)) as u8;
        let bits = ok!(stack.pop_smallint_range(0, 1023)) as u16;
        let mut cs = ok!(stack.pop_cs());

        let mut range = cs.range();
        if !range.has_remaining(bits, refs) {
            if !quiet {
                vm_bail!(CellError(Error::CellUnderflow));
            }

            ok!(stack.push_raw(cs));
            ok!(stack.push_int(0));
            return Ok(0);
        }

        let prefix_range = range.get_prefix(bits, refs);
        let ok = range.try_advance(bits, refs);
        debug_assert!(ok);

        ok!(stack.push(OwnedCellSlice::from((cs.cell().clone(), prefix_range))));

        Rc::make_mut(&mut cs).set_range(range);
        ok!(stack.push_raw(cs));

        if quiet {
            ok!(stack.push_int(-1));
        }
        Ok(0)
    }

    #[instr(code = "d739", fmt = "XCTOS")]
    fn exec_cell_to_slice_maybe_special(st: &mut VmState) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let cell = ok!(stack.pop_cell());
        let is_special = cell.descriptor().is_exotic();

        // TODO: Load with gas consumer
        let cs = OwnedCellSlice::new(Rc::unwrap_or_clone(cell));
        ok!(stack.push(cs));
        ok!(stack.push_bool(is_special));
        Ok(0)
    }

    #[instr(code = "d73a", fmt = "XLOAD", args(quiet = false))]
    #[instr(code = "d73b", fmt = "XLOADQ", args(quiet = true))]
    fn exec_load_special_cell(st: &mut VmState, quiet: bool) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let _cell = ok!(stack.pop_cell());
        let _ = quiet;

        todo!();
    }

    #[instr(code = "d741", fmt = "SCHKBITS", args(mode = CheckMode::Bits, quiet = false))]
    #[instr(code = "d742", fmt = "SCHKREFS", args(mode = CheckMode::Refs, quiet = false))]
    #[instr(code = "d743", fmt = "SCHKBITREFS", args(mode = CheckMode::BitRefs, quiet = false))]
    #[instr(code = "d745", fmt = "SCHKBITSQ", args(mode = CheckMode::Bits, quiet = true))]
    #[instr(code = "d746", fmt = "SCHKREFSQ", args(mode = CheckMode::Refs, quiet = true))]
    #[instr(code = "d747", fmt = "SCHKBITREFSQ", args(mode = CheckMode::BitRefs, quiet = true))]
    fn exec_check_slice(st: &mut VmState, mode: CheckMode, quiet: bool) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);

        let (bits, refs) = match mode {
            CheckMode::Bits => (ok!(stack.pop_smallint_range(0, 1023)), 0),
            CheckMode::Refs => (0, ok!(stack.pop_smallint_range(0, 4))),
            CheckMode::BitRefs => {
                let refs = ok!(stack.pop_smallint_range(0, 4));
                let bits = ok!(stack.pop_smallint_range(0, 1023));
                (bits, refs)
            }
        };
        let cs = ok!(stack.pop_cs());

        let fits = cs.range().has_remaining(bits as _, refs as _);
        if quiet {
            ok!(stack.push_int(if fits { -1 } else { 0 }));
        } else if !fits {
            vm_bail!(CellError(Error::CellOverflow));
        }
        Ok(0)
    }

    #[instr(code = "d748", fmt = "PLDREFVAR")]
    fn exec_preload_ref(st: &mut VmState) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let idx = ok!(stack.pop_smallint_range(0, 3)) as u8;
        let cs = ok!(stack.pop_cs());

        let slice = cs.apply_allow_special();
        let cell = slice.get_reference_cloned(idx)?;
        ok!(stack.push(cell));
        Ok(0)
    }

    #[instr(code = "d749", fmt = "SBITS", args(mode = CheckMode::Bits))]
    #[instr(code = "d74a", fmt = "SREFS", args(mode = CheckMode::Refs))]
    #[instr(code = "d74b", fmt = "SBITREFS", args(mode = CheckMode::BitRefs))]
    fn exec_slice_bits_refs(st: &mut VmState, mode: CheckMode) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let cs = ok!(stack.pop_cs());

        let range = cs.range();
        if matches!(mode, CheckMode::Bits | CheckMode::BitRefs) {
            ok!(stack.push_int(range.remaining_bits()));
        }
        if matches!(mode, CheckMode::Refs | CheckMode::BitRefs) {
            ok!(stack.push_int(range.remaining_refs()));
        }
        Ok(0)
    }

    #[instr(code = "d74$11xx", fmt = "PLDREFIDX {x}")]
    fn exec_preload_ref_fixed(st: &mut VmState, x: u32) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let cs = ok!(stack.pop_cs());

        let slice = cs.apply_allow_special();
        let cell = slice.get_reference_cloned(x as _)?;
        ok!(stack.push(cell));
        Ok(0)
    }

    // TODO: exec_load_le_int

    #[instr(code = "d760", fmt = "LDZEROES", args(value = Some(false)))]
    #[instr(code = "d761", fmt = "LDONES", args(value = Some(true)))]
    #[instr(code = "d762", fmt = "LDSAME", args(value = None))]
    fn exec_load_same(st: &mut VmState, value: Option<bool>) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let value = match value {
            Some(value) => value,
            None => ok!(stack.pop_smallint_range(0, 1)) != 0,
        };
        let mut cs = ok!(stack.pop_cs());

        let range = {
            let target = match value {
                false => Cell::all_zeros_ref(),
                true => Cell::all_ones_ref(),
            };
            let target = unsafe { target.as_slice_unchecked() };

            let mut slice = cs.apply_allow_special();
            let prefix = slice.longest_common_data_prefix(&target);
            let ok = slice.try_advance(prefix.remaining_bits(), 0);
            debug_assert!(ok);

            ok!(stack.push_int(prefix.remaining_bits()));

            slice.range()
        };

        Rc::make_mut(&mut cs).set_range(range);
        ok!(stack.push_raw(cs));
        Ok(0)
    }

    #[instr(code = "d764", fmt = "SDEPTH")]
    fn exec_slice_depth(st: &mut VmState) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let cs = ok!(stack.pop_cs());
        let slice = cs.apply_allow_special();

        let depth = compute_depth(slice.references());
        ok!(stack.push_int(depth));
        Ok(0)
    }

    #[instr(code = "d765", fmt = "CDEPTH")]
    fn exec_cell_depth(st: &mut VmState) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);

        let cell = {
            let item = ok!(stack.pop());
            if item.is_null() {
                None
            } else {
                Some(ok!(item.into_cell()))
            }
        };

        ok!(match cell {
            Some(cell) => {
                let depth = compute_depth(cell.references());
                stack.push_int(depth)
            }
            None => stack.push_int(0),
        });
        Ok(0)
    }

    // TODO: Impl other
}

fn exec_store_int_common(stack: &mut Stack, bits: u16, args: StoreIntArgs) -> VmResult<i32> {
    fn finish_store_fail(
        stack: &mut Stack,
        builder: Rc<CellBuilder>,
        x: Rc<BigInt>,
        code: i32,
        args: StoreIntArgs,
    ) -> VmResult<i32> {
        if args.is_reversed() {
            ok!(stack.push_raw_int(x, true));
            ok!(stack.push_raw(builder));
        } else {
            ok!(stack.push_raw(builder));
            ok!(stack.push_raw_int(x, true));
        }
        ok!(stack.push_int(code));
        Ok(0)
    }

    let mut builder;
    let x;
    if args.is_reversed() {
        builder = ok!(stack.pop_builder());
        x = ok!(stack.pop_int());
    } else {
        x = ok!(stack.pop_int());
        builder = ok!(stack.pop_builder());
    }

    if !builder.has_capacity(bits, 0) {
        return if args.is_quiet() {
            finish_store_fail(stack, builder, x, -1, args)
        } else {
            Err(Box::new(VmError::CellError(Error::CellOverflow)))
        };
    }

    let int_bits = bitsize(&x, args.is_signed());
    if bits < int_bits {
        return if args.is_quiet() {
            finish_store_fail(stack, builder, x, 1, args)
        } else {
            Err(Box::new(VmError::IntegerOutOfRange {
                min: 0,
                max: bits as _,
                actual: int_bits.to_string(),
            }))
        };
    }

    {
        let builder = Rc::make_mut(&mut builder);
        match x.to_u64() {
            Some(value) => builder.store_uint(value, bits)?,
            None => {
                let int = if bits % 8 != 0 {
                    let align = 8 - bits % 8;
                    Cow::Owned((*x).clone() << align)
                } else {
                    Cow::Borrowed(x.as_ref())
                };

                let minimal_bytes = ((bits + 7) / 8) as usize;

                let (prefix, mut bytes) = if args.is_signed() {
                    let bytes = int.to_signed_bytes_le();
                    (
                        bytes
                            .last()
                            .map(|first| (first >> 7) * 255)
                            .unwrap_or_default(),
                        bytes,
                    )
                } else {
                    (0, int.to_bytes_le().1)
                };
                bytes.resize(minimal_bytes, prefix);
                bytes.reverse();

                builder.store_raw(&bytes, bits)?;
            }
        }
    }

    finish_store_ok(stack, builder, args.is_quiet())
}

fn finish_store_overflow(
    stack: &mut Stack,
    arg1: RcStackValue,
    arg2: RcStackValue,
    quiet: bool,
) -> VmResult<i32> {
    if quiet {
        ok!(stack.push_raw(arg1));
        ok!(stack.push_raw(arg2));
        ok!(stack.push_int(-1));
        Ok(0)
    } else {
        Err(Box::new(VmError::CellError(Error::CellOverflow)))
    }
}

fn finish_store_ok(stack: &mut Stack, builder: Rc<CellBuilder>, quiet: bool) -> VmResult<i32> {
    ok!(stack.push_raw(builder));
    if quiet {
        ok!(stack.push_int(0));
    }
    Ok(0)
}

#[derive(Clone, Copy)]
struct StoreIntArgs(u32);

impl StoreIntArgs {
    const fn from_sign(signed: bool) -> Self {
        Self((!signed) as u32)
    }

    const fn is_unsigned(self) -> bool {
        self.0 & 0b001 != 0
    }

    const fn is_signed(self) -> bool {
        !self.is_unsigned()
    }

    const fn is_reversed(self) -> bool {
        self.0 & 0b010 != 0
    }

    const fn is_quiet(self) -> bool {
        self.0 & 0b100 != 0
    }

    fn display(&self) -> DisplayStoreIntArgs<false> {
        DisplayStoreIntArgs(self.0)
    }

    fn display_x(self) -> DisplayStoreIntArgs<true> {
        DisplayStoreIntArgs(self.0)
    }
}

struct DisplayStoreIntArgs<const X: bool>(u32);

impl<const X: bool> std::fmt::Display for DisplayStoreIntArgs<X> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let args = StoreIntArgs(self.0);

        let sign = if args.is_signed() { "I" } else { "U" };
        let x = if X { "X" } else { "" };
        let rev = if args.is_reversed() { "R" } else { "" };
        let quiet = if args.is_quiet() { "Q" } else { "" };

        write!(f, "ST{sign}{x}{rev}{quiet}")
    }
}

#[derive(Clone, Copy)]
enum CheckMode {
    Bits,
    Refs,
    BitRefs,
}

impl std::fmt::Display for CheckMode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            Self::Bits => "BITS",
            Self::Refs => "REFS",
            Self::BitRefs => "BITREFS",
        })
    }
}

fn exec_load_int_common(stack: &mut Stack, bits: u16, args: LoadIntArgs) -> VmResult<i32> {
    let mut cs = ok!(stack.pop_cs());

    if !cs.range().has_remaining(bits, 0) {
        if !args.is_quiet() {
            vm_bail!(CellError(Error::CellUnderflow));
        }

        if !args.is_prefetch() {
            ok!(stack.push_raw(cs));
        }

        ok!(stack.push_int(0));
        return Ok(0);
    }

    let range = {
        let mut slice = cs.apply_allow_special();

        let signed = args.is_signed();
        let int = match bits {
            0 => Ok(BigInt::zero()),
            0..=64 if !signed => slice.load_uint(bits).map(BigInt::from),
            0..=64 if signed => slice.load_uint(bits).map(|mut int| {
                if bits < 64 {
                    // Clone sign bit into all high bits
                    int |= ((int >> (bits - 1)) * u64::MAX) << (bits - 1);
                }
                BigInt::from(int as i64)
            }),
            _ => {
                let rem = bits % 8;
                let mut buffer = [0u8; 33];
                slice.load_raw(&mut buffer, bits).map(|buffer| {
                    let mut int = if signed {
                        BigInt::from_signed_bytes_be(buffer)
                    } else {
                        BigInt::from_bytes_be(Sign::Plus, buffer)
                    };
                    if bits % 8 != 0 {
                        int >>= 8 - rem;
                    }
                    int
                })
            }
        }?;

        ok!(stack.push_int(int));

        slice.range()
    };

    if !args.is_prefetch() {
        Rc::make_mut(&mut cs).set_range(range);
        ok!(stack.push_raw(cs));
    }

    if args.is_quiet() {
        ok!(stack.push_int(-1));
    }
    Ok(0)
}

#[derive(Clone, Copy)]
struct LoadIntArgs(u32);

impl LoadIntArgs {
    const fn from_sign(signed: bool) -> Self {
        Self((!signed) as u32)
    }

    const fn is_unsigned(self) -> bool {
        self.0 & 0b001 != 0
    }

    const fn is_signed(self) -> bool {
        !self.is_unsigned()
    }

    const fn is_prefetch(self) -> bool {
        self.0 & 0b010 != 0
    }

    const fn is_quiet(self) -> bool {
        self.0 & 0b100 != 0
    }

    fn display(&self) -> DisplayLoadIntArgs<false> {
        DisplayLoadIntArgs(self.0)
    }

    fn display_x(self) -> DisplayLoadIntArgs<true> {
        DisplayLoadIntArgs(self.0)
    }
}

struct DisplayLoadIntArgs<const X: bool>(u32);

impl<const X: bool> std::fmt::Display for DisplayLoadIntArgs<X> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let args = LoadIntArgs(self.0);

        let prefetch = if args.is_prefetch() { "P" } else { "" };
        let sign = if args.is_signed() { "I" } else { "U" };
        let x = if X { "X" } else { "" };
        let quiet = if args.is_quiet() { "Q" } else { "" };

        write!(f, "{prefetch}LD{sign}{x}{quiet}")
    }
}

fn exec_load_slice_common(stack: &mut Stack, bits: u16, args: LoadSliceArgs) -> VmResult<i32> {
    let mut cs = ok!(stack.pop_cs());

    if !cs.range().has_remaining(bits, 0) {
        if !args.is_quiet() {
            vm_bail!(CellError(Error::CellUnderflow));
        }

        if !args.is_prefetch() {
            ok!(stack.push_raw(cs));
        }

        ok!(stack.push_int(0));
        return Ok(0);
    }

    let range = {
        let mut range = cs.range();
        let slice = OwnedCellSlice::from((cs.cell().clone(), range.get_prefix(bits, 0)));
        ok!(stack.push(slice));

        range.try_advance(bits, 0);
        range
    };

    if !args.is_prefetch() {
        Rc::make_mut(&mut cs).set_range(range);
        ok!(stack.push_raw(cs));
    }

    if args.is_quiet() {
        ok!(stack.push_int(-1));
    }
    Ok(0)
}

#[derive(Clone, Copy)]
struct LoadSliceArgs(u32);

impl LoadSliceArgs {
    const fn is_prefetch(self) -> bool {
        self.0 & 0b01 != 0
    }

    const fn is_quiet(self) -> bool {
        self.0 & 0b10 != 0
    }

    fn display(&self) -> DisplayLoadSliceArgs<false> {
        DisplayLoadSliceArgs(self.0)
    }

    fn display_x(&self) -> DisplayLoadSliceArgs<true> {
        DisplayLoadSliceArgs(self.0)
    }
}

struct DisplayLoadSliceArgs<const X: bool>(u32);

impl<const X: bool> std::fmt::Display for DisplayLoadSliceArgs<X> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let args = LoadSliceArgs(self.0);

        let prefetch = if args.is_prefetch() { "P" } else { "" };
        let x = if X { "X" } else { "" };
        let quiet = if args.is_quiet() { "Q" } else { "" };

        write!(f, "{prefetch}LDSLICE{x}{quiet}")
    }
}

#[derive(Clone, Copy)]
enum SliceRangeOp {
    CutFirst,
    SkipFirst,
    CutLast,
    SkipLast,
}

fn exec_slice_begins_with_common(
    stack: &mut Stack,
    prefix: &CellSlice<'_>,
    quiet: bool,
) -> VmResult<i32> {
    let mut cs = ok!(stack.pop_cs());

    let range = {
        let slice = cs.apply_allow_special();
        let Some(slice) = slice.strip_data_prefix(prefix) else {
            if !quiet {
                vm_bail!(CellError(Error::CellUnderflow));
            }
            ok!(stack.push_raw(cs));
            ok!(stack.push_int(0));
            return Ok(0);
        };
        slice.range()
    };

    Rc::make_mut(&mut cs).set_range(range);
    ok!(stack.push_raw(cs));

    if quiet {
        ok!(stack.push_int(-1));
    }
    Ok(0)
}

#[inline]
fn compute_depth<'a, I: IntoIterator<Item = C>, C: AsRef<DynCell>>(references: I) -> u16 {
    let mut depth = 0;
    for cell in references {
        depth = std::cmp::max(depth, cell.as_ref().repr_depth().saturating_add(1));
    }
    depth
}
