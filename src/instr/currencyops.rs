use crate::stack::{Stack, StackValueType};
use everscale_types::cell::{CellBuilder, CellSlice};
use everscale_types::error::Error;
use everscale_types::num::SplitDepth;
use everscale_vm::error::VmResult;
use everscale_vm::stack::Tuple;
use everscale_vm::util::{load_var_int_from_slice, store_varint_to_builder, OwnedCellSlice};
use everscale_vm::VmState;
use everscale_vm_proc::vm_module;
use num_bigint::{BigInt, Sign};
use num_traits::{One, ToPrimitive, Zero};
use std::fmt::Formatter;
use std::ops::Deref;
use std::rc::Rc;

pub struct CurrencyOps;

#[vm_module]
impl CurrencyOps {
    #[instr(code = "fa00", fmt = ("{}", s.display()), args(s = VarIntegerArgs::new(false, 4, false, false)))]
    #[instr(code = "fa01", fmt = ("{}", s.display()), args(s = VarIntegerArgs::new(false, 4, true, false)))]
    #[instr(code = "fa04", fmt = ("{}", s.display()), args(s = VarIntegerArgs::new(false, 5, false, false)))]
    #[instr(code = "fa05", fmt = ("{}", s.display()), args(s = VarIntegerArgs::new(false, 5, true, false)))]
    fn exec_load_var_integer(st: &mut VmState, s: VarIntegerArgs) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let cs: Rc<OwnedCellSlice> = ok!(stack.pop_cs());
        let mut cs = cs.deref().clone();
        let mut slice = cs.apply()?;

        let int_opt = match load_var_int_from_slice(&mut slice, s.len_bits as u16, s.signed) {
            Ok(int) => Some(int),
            Err(e) => {
                if !s.quiet {
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
                if s.quiet {
                    ok!(stack.push_bool(true))
                }
            }
            None => ok!(stack.push_bool(false)),
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
        match store_varint_to_builder(int.as_ref(), s.len_bits as u16, cb_ref, s.signed, s.quiet) {
            Ok(true) => {
                ok!(stack.push_raw(builder));
                if s.quiet {
                    ok!(stack.push_bool(true));
                }
            }
            Ok(false) => {
                ok!(stack.push_bool(false));
            }
            Err(e) => {
                vm_bail!(CellError(e))
            }
        }
        Ok(0)
    }

    #[instr(code = "fa40", fmt = "LDMSGADDR", args(quiet = false))]
    #[instr(code = "fa41", fmt = "LDMSGADDRQ", args(quiet = true))]
    fn exec_load_message_addr(st: &mut VmState, quiet: bool) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let cs: Rc<OwnedCellSlice> = ok!(stack.pop_cs());
        let cs = cs.deref();
        let mut slice = cs.apply()?;
        let (success, address) = load_message_address_q(&mut slice, quiet)?;

        if success {
            //push address
            let mut cloned = cs.clone();
            cloned.set_range(address.range());
            ok!(stack.push_raw(Rc::new(cloned)));

            //push remainder of cell
            let mut rest = cs.clone();
            rest.set_range(slice.range());
            ok!(stack.push_raw(Rc::new(rest)));
            if quiet {
                ok!(stack.push_bool(true));
            }
        } else {
            //push original cell
            let mut cs = cs.clone();
            cs.set_range(slice.range());
            ok!(stack.push_raw(Rc::new(cs)));
            ok!(stack.push_bool(false))
        }
        Ok(0)
    }

    #[instr(code = "fa42", fmt = "PARSEMSGADDR", args(quiet = false))]
    #[instr(code = "fa43", fmt = "PARSEMSGADDRQ", args(quiet = true))]
    fn exec_parse_message_addr(st: &mut VmState, quiet: bool) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let mut cs: Rc<OwnedCellSlice> = ok!(stack.pop_cs());
        let owned_cell_slice = Rc::make_mut(&mut cs);
        match parse_message_address(owned_cell_slice) {
            Ok((true, tuple)) => {
                ok!(stack.push_raw(Rc::new(tuple)));
                if quiet {
                    ok!(stack.push_bool(true));
                }
            }
            _ => {
                if quiet {
                    ok!(stack.push_bool(false));
                } else {
                    vm_bail!(CellError(Error::CellUnderflow))
                }
            }
        }
        Ok(0)
    }

    #[instr(code = "fa44", fmt = "REWRITESTDADDR", args(allow_var_addr = false, quiet = false))]
    #[instr(code = "fa45", fmt = "REWRITESTDADDRQ", args(allow_var_addr = false, quiet = true))]
    #[instr(code = "fa46", fmt = "REWRITEVARADDR", args(allow_var_addr = true, quiet = false))]
    #[instr(code = "fa47", fmt = "REWRITEVARADDR", args(allow_var_addr = true, quiet = true))]
    fn exec_rewrite_message_addr(st: &mut VmState, allow_var_addr: bool, quiet: bool) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let mut cs: Rc<OwnedCellSlice> = ok!(stack.pop_cs());
        let owned_cell_slice = Rc::make_mut(&mut cs);
        let (result, tuple) = parse_message_address(owned_cell_slice)?;
        if !result && owned_cell_slice.range().is_empty() {
            if quiet {
                ok!(stack.push_bool(false));
                return Ok(0);
            }
            vm_bail!(CellError(Error::CellUnderflow));
        }
        let t_opt = tuple.first();
        let Some(t) = t_opt else {
           vm_bail!(InvalidType { expected: StackValueType::Int, actual: StackValueType::Null})
        };

        let t = match t.as_int().and_then(|x| x.to_u64()) {
            Some(t) => t,
            None => {
                vm_bail!(InvalidType { expected: StackValueType::Int, actual: StackValueType::Null})
            }
        };

        if t != 2 && t != 3 {
            if quiet {
                ok!(stack.push_bool(false));
                return Ok(0);
            }
            vm_bail!(CellError(Error::CellUnderflow));
        }

        let address_opt = tuple.get(3);
        let Some(address_slice) = address_opt else {
            vm_bail!(InvalidType { expected: StackValueType::Slice, actual: StackValueType::Null})
        };
        let Some(address_slice) = address_slice.as_slice() else {
            vm_bail!(InvalidType { expected: StackValueType::Slice, actual: address_slice.ty()})
        };

        let prefix_opt = tuple.get(1);
        let Some(prefix_slice) = prefix_opt else {
            vm_bail!(InvalidType { expected: StackValueType::Slice, actual: StackValueType::Null})
        };

        let prefix_slice = prefix_slice.as_slice();

        if !allow_var_addr {
            match (address_slice.range().size_bits(), quiet) {
                (256, _) => (),
                (_, true) => {
                    ok!(stack.push_bool(false));
                    return Ok(0);
                }
                _ => vm_bail!(CellError(Error::CellUnderflow)),
            }
            let address_slice = address_slice.apply()?;
            let mut rw_addr = address_slice.get_u256(0)?;

            let mut int_address = BigInt::default();

            match prefix_slice {
                Some(prefix) => {
                    let prefix = prefix.apply()?;
                    let prefix = prefix.get_raw(0, &mut rw_addr.0, prefix.range().size_bits())?;
                    int_address = BigInt::from_bytes_be(Sign::Plus, prefix);
                },
                None => ()
            };


            let address_opt = tuple.get(2);
            let Some(address_slice) = address_opt else {
                vm_bail!(InvalidType { expected: StackValueType::Slice, actual: StackValueType::Null})
            };
            ok!(stack.push_raw(address_slice.clone()));
            ok!(stack.push_int(int_address));
        } else {
            let rewrited = do_rewrite_addr(address_slice.clone(), prefix_slice.cloned());
            match rewrited {
                Err(e) => {
                    if quiet {
                        ok!(stack.push_bool(false));
                        return Ok(0);
                    }
                    vm_bail!(CellError(e));
                }
                Ok(slice) => {
                    let address_opt = tuple.get(2);
                    let Some(address_slice) = address_opt else {
                        vm_bail!(InvalidType { expected: StackValueType::Slice, actual: StackValueType::Null})
                    };
                    ok!(stack.push_raw(address_slice.clone()));
                    ok!(stack.push_raw(Rc::new(slice)));
                }
            }
        }

        if quiet {
            ok!(stack.push_bool(true));
        }
        Ok(0)
    }
}

fn do_rewrite_addr<'a>(addr: OwnedCellSlice, prefix: Option<OwnedCellSlice>) -> Result<OwnedCellSlice, Error> {
    let mut addr_slice = addr.apply()?;
    let prefix = match prefix {
        None => return Ok(addr),
        Some(prefix)  => prefix,
    };
    let prefix_slice = prefix.apply()?;
    if prefix_slice.is_empty() {
        return Ok(addr);
    }
    if prefix_slice.size_bits() > addr_slice.size_bits() {
        return Err(Error::InvalidCell)
    }

    if prefix_slice.size_bits() == addr_slice.size_bits() {
        return Ok(prefix)
    }

    let mut cb = CellBuilder::new();
    addr_slice.skip_first(prefix_slice.size_bits(), 0)?;
    cb.store_slice(prefix_slice)?;
    cb.store_slice(addr_slice)?;
    let cell = cb.build()?;

    //TODO: consume gas here ??
    Ok(OwnedCellSlice::from(cell))

}

fn parse_message_address(owned_slice: &mut OwnedCellSlice) -> Result<(bool, Tuple), Error> {
    let slice = owned_slice.clone();
    let mut slice = slice.apply()?;

    let mut tuple = Tuple::new();
    let prefix = slice.load_small_uint(2)?;
    owned_slice.set_range(slice.range());

    match prefix {
        0 => {
            tuple.push(Rc::new(BigInt::zero()));
            Ok((true, tuple))
        }
        1 => {
            let len = slice.load_uint(9)?;
            let address = slice.get_prefix(len as u16, 0);
            slice.skip_first(len as u16, 0)?;
            tuple.push(Rc::new(BigInt::one()));
            owned_slice.set_range(address.range());
            tuple.push(Rc::new(owned_slice.clone()));
            Ok((true, tuple))
        }
        2 => {
            let anycast = parse_maybe_anycast(&mut slice)?;
            let worckchain = slice.load_u8()?;
            let prefix = slice.get_prefix(256, 0);
            slice.skip_first(256, 0)?;

            tuple.push(Rc::new(BigInt::from(2)));
            let value = match anycast {
                Some(anycast) => {
                    owned_slice.set_range(anycast.range());
                    Rc::new(owned_slice.clone())
                }
                None => Stack::make_null(),
            };
            tuple.push(value);
            tuple.push(Rc::new(BigInt::from(worckchain)));
            owned_slice.set_range(prefix.range());
            tuple.push(Rc::new(owned_slice.clone()));
            Ok((true, tuple))
        }
        3 => {
            let anycast = parse_maybe_anycast(&mut slice)?;
            let len = slice.load_uint(9)?;
            let worckchain = slice.load_uint(32)?;
            let prefix = slice.get_prefix(len as u16, 0);
            slice.skip_first(len as u16, 0)?;

            tuple.push(Rc::new(BigInt::from(3)));
            let value = match anycast {
                Some(anycast) => {
                    owned_slice.set_range(anycast.range());
                    Rc::new(owned_slice.clone())
                }
                None => Stack::make_null(),
            };
            tuple.push(value);
            tuple.push(Rc::new(BigInt::from(worckchain)));
            owned_slice.set_range(prefix.range());
            tuple.push(Rc::new(owned_slice.clone()));
            Ok((true, tuple))
        }
        _ => Ok((false, tuple)),
    }
}
fn load_message_address_q<'a>(
    cs: &mut CellSlice<'a>,
    quiet: bool,
) -> VmResult<(bool, CellSlice<'a>)> {
    let mut res = cs.clone();

    if let Err(e) = skip_message_addr(cs) {
        if quiet {
            return Ok((false, res));
        }
        vm_bail!(CellError(e))
    }
    res.skip_last(cs.size_bits(), cs.size_refs())?;

    Ok((true, res))
}

fn skip_message_addr(slice: &mut CellSlice) -> Result<(), Error> {
    let addr_type = slice.load_small_uint(2)?;
    match addr_type {
        0 => Ok(()),
        1 => {
            let len = slice.load_uint(9)? as usize;
            slice.skip_first(len as u16, 0)?;
            Ok(())
        }
        2 => {
            skip_maybe_anycast(slice)?;
            slice.skip_first(8 + 256, 0)?;
            Ok(())
        }
        3 => {
            skip_maybe_anycast(slice)?;
            let len = slice.load_uint(9)?;
            slice.skip_first((32 + len) as u16, 0)
        }

        _ => Err(Error::InvalidData),
    }
}

fn skip_maybe_anycast(cs: &mut CellSlice) -> Result<(), Error> {
    if !cs.load_bit()? {
        return Ok(());
    }
    let depth = SplitDepth::new(load_uint_leq(cs, 30)? as u8)?;
    cs.skip_first(depth.into_bit_len(), 0)?;

    Ok(())
}

fn parse_maybe_anycast<'a>(cs: &mut CellSlice<'a>) -> Result<Option<CellSlice<'a>>, Error> {
    let load_bit = cs.load_bit()?;
    if !load_bit {
        return Ok(None);
    }

    let depth = SplitDepth::new(load_uint_leq(cs, 30)? as u8)?;
    let prefix = cs.get_prefix(depth.into_bit_len(), 0);
    cs.skip_first(depth.into_bit_len(), 0)?;

    Ok(Some(prefix))
}

fn load_uint_leq(cs: &mut CellSlice, upper_bound: u32) -> Result<u64, Error> {
    let leading_zeros = if upper_bound == 0 {
        32
    } else {
        upper_bound.leading_zeros()
    };
    let bits = 32 - leading_zeros;
    if bits > 32 || bits > cs.size_bits() as u32 {
        Err(Error::IntOverflow)
    } else {
        let result = cs.get_uint(cs.offset_bits(), bits as u16)?;
        if result > upper_bound as u64 {
            return Err(Error::IntOverflow);
        };

        cs.skip_first(bits as u16, 0)?;
        Ok(result)
    }
}

pub struct VarIntegerArgs {
    store: bool,
    len_bits: u32,
    signed: bool,
    quiet: bool,
}

impl VarIntegerArgs {
    fn new(store: bool, len_bits: u32, signed: bool, quiet: bool) -> Self {
        Self {
            store,
            len_bits,
            signed,
            quiet,
        }
    }

    fn display(&self) -> DisplayVarIntegerArgs {
        DisplayVarIntegerArgs {
            store: self.store,
            len_bits: self.len_bits,
            signed: self.signed,
            quiet: self.quiet,
        }
    }
}

pub struct DisplayVarIntegerArgs {
    store: bool,
    len_bits: u32,
    signed: bool,
    quiet: bool,
}

impl std::fmt::Display for DisplayVarIntegerArgs {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let mode = if self.store { "ST" } else { "LD" };
        let quiet = if self.quiet { "Q" } else { "" };

        let log = if self.len_bits == 4 && !self.signed {
            format!("{mode}GRAMS{quiet}")
        } else {
            let signed = if self.signed { "" } else { "U" };
            format!("{mode}VAR{signed}INT{}{quiet}", 1 << self.len_bits)
        };
        write!(f, "{log}")
    }
}

#[cfg(test)]
mod test {
    use crate::stack::{RcStackValue, Tuple};
    use crate::util::{store_varint_to_builder, OwnedCellSlice};
    use everscale_types::cell::CellSliceRange;
    use everscale_types::models::StdAddr;
    use everscale_types::prelude::CellBuilder;
    use everscale_vm::stack::Stack;
    use num_bigint::BigInt;
    use std::rc::Rc;
    use std::str::FromStr;
    use tracing_test::traced_test;

    #[test]
    #[traced_test]
    fn load_varint_u16_test() {
        let int = BigInt::from(5);
        let mut builder = CellBuilder::new();
        store_varint_to_builder(&int, 4, &mut builder, true, false).unwrap();
        let mut slice = OwnedCellSlice::from(builder.build().unwrap());
        let value: RcStackValue = Rc::new(slice.clone());
        let mut cs = slice.apply().unwrap();
        cs.skip_first(12, 0).unwrap();
        slice.set_range(cs.range());
        let another_value: RcStackValue = Rc::new(slice);

        assert_run_vm!("LDVARUINT16", [raw value] => [int 5, raw another_value])
        // aka LDGRAMS
    }

    #[test]
    #[traced_test]
    fn load_varint_u32_test() {
        let int = BigInt::from(5);
        let mut builder = CellBuilder::new();
        store_varint_to_builder(&int, 5, &mut builder, true, false).unwrap();
        let mut slice = OwnedCellSlice::from(builder.build().unwrap());
        let value: RcStackValue = Rc::new(slice.clone());
        let mut cs = slice.apply().unwrap();
        cs.skip_first(13, 0).unwrap();
        slice.set_range(cs.range());
        let another_value: RcStackValue = Rc::new(slice);

        assert_run_vm!("LDVARUINT32", [raw value] => [int 5, raw another_value])
    }

    #[test]
    #[traced_test]
    fn parse_message_address() {
        let addr =
            StdAddr::from_str("0:6301b2c75596e6e569a6d13ae4ec70c94f177ece0be19f968ddce73d44e7afc7")
                .unwrap();
        let mut addr = OwnedCellSlice::from(CellBuilder::build_from(addr).unwrap());
        let value: RcStackValue = Rc::new(addr.clone());

        let mut tuple = Tuple::new();
        tuple.push(Rc::new(BigInt::from(2)));
        tuple.push(Stack::make_null());
        tuple.push(Rc::new(BigInt::from(0)));
        let mut cs = addr.apply().unwrap();
        cs.skip_first(11, 0).unwrap();
        addr.set_range(cs.range());
        tuple.push(Rc::new(addr));
        let tuple: RcStackValue = Rc::new(tuple);

        assert_run_vm!("PARSEMSGADDR", [raw value.clone()] => [raw tuple.clone()]);
        assert_run_vm!("PARSEMSGADDRQ", [raw value.clone()] => [raw tuple, int -1]);
    }
}
