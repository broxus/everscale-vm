use std::rc::Rc;

use everscale_types::cell::LoadMode;
use everscale_types::error::Error;
use everscale_types::num::SplitDepth;
use everscale_types::prelude::*;
use everscale_vm::error::VmResult;
use everscale_vm::util::{load_uint_leq, OwnedCellSlice};
use everscale_vm::VmState;
use everscale_vm_proc::vm_module;
use num_bigint::{BigInt, Sign};

use crate::gas::GasConsumer;
use crate::stack::{RcStackValue, Stack, StackValue, Tuple};
use crate::util::{bitsize, load_int_from_slice, store_int_to_builder_unchecked};

pub struct CurrencyOps;

#[vm_module]
impl CurrencyOps {
    #[op(code = "fa00", fmt = "LDGRAMS", args(len_bits = 4, signed = false))]
    #[op(code = "fa01", fmt = "LDVARINT16", args(len_bits = 4, signed = true))]
    #[op(code = "fa04", fmt = "LDVARUINT32", args(len_bits = 5, signed = false))]
    #[op(code = "fa05", fmt = "LDVARINT32", args(len_bits = 5, signed = true))]
    fn exec_load_var_integer(st: &mut VmState, len_bits: u16, signed: bool) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let mut csr = ok!(stack.pop_cs());

        let int;
        let cs_range = {
            let mut cs = csr.apply()?;
            int = load_varint(&mut cs, len_bits, signed)?;
            cs.range()
        };
        Rc::make_mut(&mut csr).set_range(cs_range);

        ok!(stack.push_int(int));
        ok!(stack.push_raw(csr));
        Ok(0)
    }

    #[op(code = "fa02", fmt = "STGRAMS", args(len_bits = 4, signed = false))]
    #[op(code = "fa03", fmt = "STVARINT16", args(len_bits = 4, signed = true))]
    #[op(code = "fa06", fmt = "STVARUINT32", args(len_bits = 5, signed = false))]
    #[op(code = "fa07", fmt = "STVARINT32", args(len_bits = 5, signed = true))]
    fn exec_store_var_integer(st: &mut VmState, len_bits: u16, signed: bool) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let int = ok!(stack.pop_int());
        let mut builder = ok!(stack.pop_builder());

        store_varint(&int, len_bits, signed, Rc::make_mut(&mut builder))?;

        ok!(stack.push_raw(builder));
        Ok(0)
    }

    #[op(code = "fa40", fmt = "LDMSGADDR", args(quiet = false))]
    #[op(code = "fa41", fmt = "LDMSGADDRQ", args(quiet = true))]
    fn exec_load_message_addr(st: &mut VmState, quiet: bool) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let mut csr = ok!(stack.pop_cs());

        let mut cs = csr.apply()?;
        let mut addr = cs;
        match skip_message_addr(&mut cs) {
            Ok(()) => {
                addr.skip_last(cs.size_bits(), cs.size_refs())?;
                let addr_cs = OwnedCellSlice::from((csr.cell().clone(), addr.range()));

                let range = cs.range();
                Rc::make_mut(&mut csr).set_range(range);

                ok!(stack.push(addr_cs));
                ok!(stack.push_raw(csr));
                if quiet {
                    ok!(stack.push_bool(true));
                }
            }
            Err(_) if quiet => {
                ok!(stack.push_raw(csr));
                ok!(stack.push_bool(false));
            }
            Err(e) => vm_bail!(CellError(e)),
        }
        Ok(0)
    }

    #[op(code = "fa42", fmt = "PARSEMSGADDR", args(quiet = false))]
    #[op(code = "fa43", fmt = "PARSEMSGADDRQ", args(quiet = true))]
    fn exec_parse_message_addr(st: &mut VmState, quiet: bool) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let csr = ok!(stack.pop_cs());

        let mut range = csr.range();
        match parse_message_addr(csr.cell(), &mut range) {
            Ok(parts) => {
                ok!(stack.push(parts.into_tuple()));
                if quiet {
                    ok!(stack.push_bool(true));
                }
            }
            Err(_) if quiet => ok!(stack.push_bool(false)),
            Err(e) => vm_bail!(CellError(e)),
        }
        Ok(0)
    }

    #[op(code = "fa44", fmt = "REWRITESTDADDR", args(var = false, q = false))]
    #[op(code = "fa45", fmt = "REWRITESTDADDRQ", args(var = false, q = true))]
    #[op(code = "fa46", fmt = "REWRITEVARADDR", args(var = true, q = false))]
    #[op(code = "fa47", fmt = "REWRITEVARADDR", args(var = true, q = true))]
    fn exec_rewrite_message_addr(st: &mut VmState, var: bool, q: bool) -> VmResult<i32> {
        let handle_error = |stack: &mut Stack, e: Error| {
            if q {
                ok!(stack.push_bool(false));
                Ok(0)
            } else {
                vm_bail!(CellError(e));
            }
        };

        let stack = Rc::make_mut(&mut st.stack);
        let csr = ok!(stack.pop_cs());

        let mut range = csr.range();
        let parts = match parse_message_addr(csr.cell(), &mut range) {
            Ok(parts) => parts,
            Err(e) => return handle_error(stack, e),
        };

        let (pfx, wc, addr) = match parts {
            AddrParts::Std {
                pfx,
                workchain,
                addr,
            } => (pfx, workchain as i32, addr),
            AddrParts::Var {
                pfx,
                workchain,
                addr,
            } => (pfx, workchain, addr),
            _ => return handle_error(stack, Error::CellUnderflow),
        };

        let addr = if var {
            match rewrite_addr_var(addr, pfx, &mut st.gas) {
                Ok(addr) => Rc::new(addr) as RcStackValue,
                Err(e) => return handle_error(stack, e),
            }
        } else {
            match rewrite_addr_std(addr, pfx) {
                Ok(addr) => Rc::new(addr) as RcStackValue,
                Err(e) => return handle_error(stack, e),
            }
        };

        ok!(stack.push_int(wc));
        ok!(stack.push_raw(addr));
        if q {
            ok!(stack.push_bool(true));
        }
        Ok(0)
    }
}

fn rewrite_addr_var(
    addr: OwnedCellSlice,
    pfx: Option<OwnedCellSlice>,
    gas: &mut GasConsumer,
) -> Result<OwnedCellSlice, Error> {
    let Some(pfx) = pfx else {
        return Ok(addr);
    };

    if pfx.range().size_bits() == addr.range().size_bits() {
        return Ok(pfx);
    }

    let mut cs = addr.apply()?;
    let pfx = pfx.apply()?;
    cs.skip_first(pfx.size_bits(), 0)?;

    let mut cb = CellBuilder::new();
    cb.store_slice(pfx)?;
    cb.store_slice(cs)?;
    let cell = cb.build_ext(gas)?;
    let cell = gas.load_cell(cell, LoadMode::UseGas)?;
    Ok(OwnedCellSlice::from(cell))
}

fn rewrite_addr_std(addr: OwnedCellSlice, pfx: Option<OwnedCellSlice>) -> Result<BigInt, Error> {
    let mut addr = addr.apply()?.load_u256()?.0;

    if let Some(pfx) = pfx {
        let mut pfx = pfx.apply()?;
        let pfx_len = pfx.size_bits();

        let mut buffer = [0u8; 4];
        pfx.load_raw(&mut buffer, pfx_len)?;

        let bytes = (pfx_len / 8) as usize;
        addr[..bytes].copy_from_slice(&buffer[..bytes]);

        let bits = pfx_len % 8;
        if bits != 0 {
            addr[bytes] &= (1 << (8 - bits)) - 1;
            addr[bytes] |= buffer[bytes];
        }
    }

    Ok(BigInt::from_bytes_be(Sign::Plus, &addr))
}

fn parse_message_addr(cell: &Cell, range: &mut CellSliceRange) -> Result<AddrParts, Error> {
    let mut cs = range.apply(cell)?;
    match cs.load_small_uint(2)? {
        // addr_none$00 = MsgAddressExt;
        0b00 => Ok(AddrParts::None),
        // addr_extern$01
        0b01 => {
            // len:(## 9)
            let len = cs.load_uint(9)? as u16;
            // external_address:(bits len) = MsgAddressExt;
            let addr = cs.load_prefix(len, 0)?;

            Ok(AddrParts::Ext {
                addr: OwnedCellSlice::from((cell.clone(), addr.range())),
            })
        }
        // addr_std$10
        0b10 => {
            // anycast:(Maybe Anycast)
            let pfx = parse_maybe_anycast(cell, &mut cs)?;
            // workchain_id:int8
            let workchain = cs.load_u8()? as i8;
            // address:bits256 = MsgAddressInt;
            let addr = cs.load_prefix(256, 0)?;

            Ok(AddrParts::Std {
                pfx,
                workchain,
                addr: OwnedCellSlice::from((cell.clone(), addr.range())),
            })
        }
        // addr_var$11
        0b11 => {
            // anycast:(Maybe Anycast)
            let pfx = parse_maybe_anycast(cell, &mut cs)?;
            // addr_len:(## 9)
            let len = cs.load_uint(9)? as u16;
            // workchain_id:int32
            let workchain = cs.load_u32()? as i32;
            // address:(bits addr_len) = MsgAddressInt;
            let addr = cs.load_prefix(len, 0)?;

            Ok(AddrParts::Var {
                pfx,
                workchain,
                addr: OwnedCellSlice::from((cell.clone(), addr.range())),
            })
        }
        _ => Err(Error::InvalidData),
    }
}

fn parse_maybe_anycast(
    cell: &Cell,
    cs: &mut CellSlice<'_>,
) -> Result<Option<OwnedCellSlice>, Error> {
    // just$1
    Ok(if cs.load_bit()? {
        // anycast_info$_ depth:(#<= 30)
        let depth = SplitDepth::new(load_uint_leq(cs, 30)? as u8)?;
        // rewrite_pfx:(bits depth) = Anycast;
        let pfx = cs.load_prefix(depth.into_bit_len(), 0)?;

        Some(OwnedCellSlice::from((cell.clone(), pfx.range())))
    } else {
        None
    })
}

enum AddrParts {
    None,
    Ext {
        addr: OwnedCellSlice,
    },
    Std {
        pfx: Option<OwnedCellSlice>,
        workchain: i8,
        addr: OwnedCellSlice,
    },
    Var {
        pfx: Option<OwnedCellSlice>,
        workchain: i32,
        addr: OwnedCellSlice,
    },
}

impl AddrParts {
    fn into_tuple(self) -> Tuple {
        fn opt_to_value<T: StackValue + 'static>(value: Option<T>) -> RcStackValue {
            match value {
                None => Stack::make_null(),
                Some(value) => Rc::new(value),
            }
        }

        match self {
            Self::None => vec![Rc::new(BigInt::ZERO)],
            Self::Ext { addr } => vec![Rc::new(BigInt::from(1)), Rc::new(addr)],
            Self::Std {
                pfx,
                workchain,
                addr,
            } => vec![
                Rc::new(BigInt::from(2)),
                opt_to_value(pfx),
                Rc::new(BigInt::from(workchain)),
                Rc::new(addr),
            ],
            Self::Var {
                pfx,
                workchain,
                addr,
            } => vec![
                Rc::new(BigInt::from(3)),
                opt_to_value(pfx),
                Rc::new(BigInt::from(workchain)),
                Rc::new(addr),
            ],
        }
    }
}

fn skip_message_addr(cs: &mut CellSlice) -> Result<(), Error> {
    match cs.load_small_uint(2)? {
        // addr_none$00 = MsgAddressExt;
        0b00 => Ok(()),
        // addr_extern$01
        0b01 => {
            // len:(## 9)
            let len = cs.load_uint(9)? as u16;
            // external_address:(bits len) = MsgAddressExt;
            cs.skip_first(len, 0)
        }
        // addr_std$10
        0b10 => {
            // anycast:(Maybe Anycast)
            skip_maybe_anycast(cs)?;
            // workchain_id:int8 address:bits256 = MsgAddressInt;
            cs.skip_first(8 + 256, 0)?;
            Ok(())
        }
        // addr_var$11
        0b11 => {
            // anycast:(Maybe Anycast)
            skip_maybe_anycast(cs)?;
            // addr_len:(## 9)
            let len = cs.load_uint(9)? as u16;
            // workchain_id:int32 address:(bits addr_len) = MsgAddressInt;
            cs.skip_first(32 + len, 0)
        }
        _ => Err(Error::InvalidData),
    }
}

fn skip_maybe_anycast(cs: &mut CellSlice) -> Result<(), Error> {
    // just$1
    if cs.load_bit()? {
        // anycast_info$_ depth:(#<= 30)
        let depth = SplitDepth::new(load_uint_leq(cs, 30)? as u8)?;
        // rewrite_pfx:(bits depth) = Anycast;
        cs.skip_first(depth.into_bit_len(), 0)?;
    }
    Ok(())
}

fn store_varint(
    int: &BigInt,
    len_bits: u16,
    signed: bool,
    builder: &mut CellBuilder,
) -> VmResult<()> {
    let bitsize = bitsize(int, signed);
    let bytes = bitsize.div_ceil(8);
    vm_ensure!(bytes < (1 << len_bits), IntegerOutOfRange {
        min: 0,
        max: (1 << len_bits) - 1,
        actual: bytes.to_string(),
    });
    builder.store_small_uint(bytes as u8, len_bits)?;
    store_int_to_builder_unchecked(int, bytes * 8, signed, builder)?;
    Ok(())
}

fn load_varint(slice: &mut CellSlice<'_>, len_bits: u16, signed: bool) -> Result<BigInt, Error> {
    let len = slice.load_uint(len_bits)? as u16;
    load_int_from_slice(slice, len * 8, signed)
}

#[cfg(test)]
mod test {
    use everscale_types::models::StdAddr;
    use tracing_test::traced_test;

    use super::*;

    #[test]
    #[traced_test]
    fn load_varint_u16_test() -> anyhow::Result<()> {
        let int = BigInt::from(5);
        let mut builder = CellBuilder::new();
        store_varint(&int, 4, true, &mut builder)?;
        let mut slice = OwnedCellSlice::from(builder.build()?);
        let value = Rc::new(slice.clone()) as RcStackValue;

        let mut cs = slice.apply()?;
        cs.skip_first(12, 0)?;
        slice.set_range(cs.range());

        assert_run_vm!("LDVARUINT16", [raw value] => [int 5, slice slice]);
        // aka LDGRAMS

        Ok(())
    }

    #[test]
    #[traced_test]
    fn load_varint_u32_test() -> anyhow::Result<()> {
        let int = BigInt::from(5);
        let mut builder = CellBuilder::new();
        store_varint(&int, 5, true, &mut builder)?;
        let mut slice = OwnedCellSlice::from(builder.build()?);
        let value = Rc::new(slice.clone()) as RcStackValue;

        let mut cs = slice.apply()?;
        cs.skip_first(13, 0)?;
        slice.set_range(cs.range());

        assert_run_vm!("LDVARUINT32", [raw value] => [int 5, slice slice]);

        Ok(())
    }

    #[test]
    #[traced_test]
    fn parse_message_address() -> anyhow::Result<()> {
        let addr = "0:6301b2c75596e6e569a6d13ae4ec70c94f177ece0be19f968ddce73d44e7afc7"
            .parse::<StdAddr>()?;
        let mut addr = OwnedCellSlice::from(CellBuilder::build_from(addr)?);
        let value = Rc::new(addr.clone()) as RcStackValue;

        let mut cs = addr.apply().unwrap();
        cs.skip_first(11, 0).unwrap();
        addr.set_range(cs.range());

        let tuple = Rc::new(tuple![
            int 2,
            null,
            int 0,
            slice addr,
        ]);

        assert_run_vm!("PARSEMSGADDR", [raw value.clone()] => [raw tuple.clone()]);
        assert_run_vm!("PARSEMSGADDRQ", [raw value.clone()] => [raw tuple, int -1]);

        Ok(())
    }
}
