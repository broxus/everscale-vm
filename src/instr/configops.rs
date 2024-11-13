use crate::error::VmResult;
use crate::stack::{RcStackValue, Stack, Tuple};
use crate::util::OwnedCellSlice;
use everscale_types::models::{BlockchainConfig, GasLimitsPrices, StoragePrices};
use everscale_types::prelude::{Cell, CellBuilder, CellFamily, Load};
use everscale_vm::cont::ControlRegs;
use everscale_vm::instr::dictops::check_key_sign;
use everscale_vm::stack::StackValueType;
use everscale_vm::util::{load_int_from_slice, store_int_to_builder};
use everscale_vm::VmState;
use everscale_vm_proc::vm_module;
use num_bigint::BigInt;
use num_integer::Integer;
use num_traits::{Signed, Zero};
use std::fmt::Formatter;
use std::ops::{Mul, Shr, ShrAssign};
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

    #[instr(code = "f832", fmt = "PARAM", args(opt = false))]
    #[instr(code = "f833", fmt = "OPTPARAM", args(opt = true))]
    fn exec_get_config_param(st: &mut VmState, opt: bool) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let idx = ok!(stack.pop_int());
        ok!(get_and_push_param(&mut st.cr, stack, 9usize));
        let dict: Option<Rc<Cell>> = ok!(stack.pop_cell_opt());
        let kbl = 32u16;

        ok!(check_key_sign(false, idx.clone()));

        let mut builder = CellBuilder::new();
        store_int_to_builder(&idx, kbl, &mut builder)?;
        let key = builder.as_data_slice();

        let dict = dict.as_deref();
        let result =
            everscale_types::dict::dict_get_owned(dict, kbl, key, &mut Cell::empty_context())?
                .map(OwnedCellSlice::from);

        let ref_cell = match result {
            Some(slice) => {
                let slice = slice.apply()?;
                Some(slice.get_reference_cloned(0)?)
            }
            None => None,
        };

        match (ref_cell, opt) {
            (ref_cell, true) => ok!(stack.push_opt(ref_cell)),
            (Some(cell), false) => {
                ok!(stack.push_raw(Rc::new(cell)));
                ok!(stack.push_bool(true));
            }
            (None, false) => ok!(stack.push_bool(false)),
        }

        Ok(0)
    }

    #[instr(code = "f83400", fmt = "PREVMCBLOCKS", args(i = 0))]
    #[instr(code = "f83401", fmt = "PREVKEYBLOCK", args(i = 1))]
    fn exec_get_prev_blocks_info(st: &mut VmState, i: u32) -> VmResult<i32> {
        let index = (i & 3) as usize;

        let stack = Rc::make_mut(&mut st.stack);

        let param: &RcStackValue = ok!(get_param(&mut st.cr, 13));

        let Some(t2) = param.as_tuple_range(0, 255) else {
            vm_bail!(InvalidType {
                expected: StackValueType::Tuple,
                actual: param.ty()
            })
        };

        let param: &RcStackValue = match t2.get(index) {
            Some(param) => param,
            None => vm_bail!(ControlRegisterOutOfRange(index)),
        };

        ok!(stack.push_raw(param.clone()));
        Ok(0)
    }

    #[instr(code = "f835", fmt = "GLOBALID")]
    fn exec_get_global_id(st: &mut VmState) -> VmResult<i32> {
        //TODO: add global id as separate parameter

        let param: &RcStackValue = ok!(get_param(&mut st.cr, 13));
        let dict = param.as_cell();
        if dict.is_none() {
            vm_bail!(InvalidType {
                expected: StackValueType::Cell,
                actual: StackValueType::Null
            })
        }

        let kbl = 32u16;

        let mut builder = CellBuilder::new();
        store_int_to_builder(&BigInt::from(19), kbl, &mut builder)?;
        let key = builder.as_data_slice();

        let result =
            everscale_types::dict::dict_get_owned(dict, kbl, key, &mut Cell::empty_context())?
                .map(OwnedCellSlice::from);

        let ref_cell = match result {
            Some(slice) => {
                let slice = slice.apply()?;
                slice.get_reference_cloned(0)?
            }
            None => vm_bail!(Unknown("invalid global_id config".to_string())),
        };

        let mut slice = ref_cell.as_slice()?;
        if slice.size_bits() < kbl {
            vm_bail!(Unknown("invalid global_id config".to_string()))
        }

        let stack = Rc::make_mut(&mut st.stack);
        let id = load_int_from_slice(&mut slice, kbl, true)?;
        ok!(stack.push_int(id));

        Ok(0)
    }

    #[instr(code = "f836", fmt = "GETGASFEE")]
    fn exec_get_gas_fee(st: &mut VmState) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let is_masterchain = ok!(stack.pop_bool());
        let gas = ok!(stack.pop_long_range(0, u64::MAX));
        let unpacked_config: Rc<Tuple> = ok!(get_unpacked_config_tuple(&mut st.cr));

        let index = if is_masterchain { 2 } else { 3 };

        let Some(value) = unpacked_config.get(index as usize) else {
            vm_bail!(InvalidType {
                expected: StackValueType::Tuple,
                actual: StackValueType::Null
            })
        };

        let Some(cell_slice) = value.as_slice() else {
            vm_bail!(InvalidType {
                expected: StackValueType::Slice,
                actual: value.ty()
            })
        };
        let mut slice = &cell_slice.apply()?;
        let config = BlockchainConfig::load_from(&mut slice)?;
        let prices = config.get_gas_prices(is_masterchain)?;

        let gas = if gas <= prices.flat_gas_limit {
            BigInt::from(prices.flat_gas_price)
        } else {
            let value: BigInt = BigInt::from(prices.flat_gas_price) * (gas - prices.flat_gas_limit);
            value.shr(16) + prices.flat_gas_price
        };

        ok!(stack.push_int(gas));
        Ok(0)
    }

    #[instr(code = "f837", fmt = "GETSTORAGEFEE")]
    fn exec_get_storage_fee(st: &mut VmState) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let is_masterchain = ok!(stack.pop_bool());
        let delta: u64 = ok!(stack.pop_long_range(0, u64::MAX));
        let bits: u64 = ok!(stack.pop_long_range(0, u64::MAX));
        let cells: u64 = ok!(stack.pop_long_range(0, u64::MAX));

        let unpacked_config: Rc<Tuple> = ok!(get_unpacked_config_tuple(&mut st.cr));

        let Some(value) = unpacked_config.get(0usize) else {
            vm_bail!(InvalidType {
                expected: StackValueType::Tuple,
                actual: StackValueType::Null
            })
        };

        let Some(cell_slice) = value.as_slice() else {
            vm_bail!(InvalidType {
                expected: StackValueType::Slice,
                actual: value.ty()
            })
        };

        let mut slice = &cell_slice.apply()?;
        let config = BlockchainConfig::load_from(&mut slice)?;
        let prices = config.get_storage_prices()?;
        let mut total = BigInt::zero();
        if let Some(prices) = prices.get(0)? {
            if is_masterchain {
                total = BigInt::from(cells) * prices.mc_cell_price_ps;
                total += BigInt::from(bits) * prices.mc_bit_price_ps;
            } else {
                total = BigInt::from(cells) * prices.cell_price_ps;
                total += BigInt::from(bits) * prices.bit_price_ps;
            }
        }

        ok!(stack.push_int(total));
        Ok(0)
    }

    #[instr(code = "f838", fmt = "GETFORWARDFEE")]
    fn exec_get_forward_fee(st: &mut VmState) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let is_masterchain = ok!(stack.pop_bool());
        let bits: u64 = ok!(stack.pop_long_range(0, u64::MAX));
        let cells: u64 = ok!(stack.pop_long_range(0, u64::MAX));

        let unpacked_config: Rc<Tuple> = ok!(get_unpacked_config_tuple(&mut st.cr));
        let index = if is_masterchain { 4 } else { 5 };

        let Some(value) = unpacked_config.get(index as usize) else {
            vm_bail!(InvalidType {
                expected: StackValueType::Tuple,
                actual: StackValueType::Null
            })
        };

        let Some(cell_slice) = value.as_slice() else {
            vm_bail!(InvalidType {
                expected: StackValueType::Slice,
                actual: value.ty()
            })
        };
        let mut slice = &cell_slice.apply()?;
        let config = BlockchainConfig::load_from(&mut slice)?;
        let prices = config.get_msg_forward_prices(is_masterchain)?;

        let fees = BigInt::from(prices.lump_price)
            * (BigInt::from(prices.bit_price) * bits + BigInt::from(prices.cell_price) * cells)
                .shr(16);

        ok!(stack.push_int(fees));
        Ok(0)
    }

    #[instr(code = "f839", fmt = "GETPRECOMPILEDGAS")]
    fn exec_get_precompiled_gas(st: &mut VmState) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        ok!(get_and_push_param(&mut st.cr, stack, 16usize));
        Ok(0)
    }

    #[instr(code = "f83a", fmt = "GETORIGINALFWDFEE")]
    fn exec_get_original_fwd_fee(st: &mut VmState) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let is_masterchain = ok!(stack.pop_bool());
        let fwd_fee: Rc<BigInt> = ok!(stack.pop_int());
        if fwd_fee.is_negative() {
            vm_bail!(IntegerOutOfRange {
                min: u64::MIN as isize,
                max: u64::MAX as isize,
                actual: fwd_fee.to_string()
            })
        }

        let unpacked_config: Rc<Tuple> = ok!(get_unpacked_config_tuple(&mut st.cr));
        let index = if is_masterchain { 4 } else { 5 };

        let Some(value) = unpacked_config.get(index as usize) else {
            vm_bail!(InvalidType {
                expected: StackValueType::Tuple,
                actual: StackValueType::Null
            })
        };

        let Some(cell_slice) = value.as_slice() else {
            vm_bail!(InvalidType {
                expected: StackValueType::Slice,
                actual: value.ty()
            })
        };
        let mut slice = &cell_slice.apply()?;
        let config = BlockchainConfig::load_from(&mut slice)?;
        let prices = config.get_msg_forward_prices(is_masterchain)?;

        let fees = {
            let tmp = fwd_fee.as_ref().mul(BigInt::from(1 << 16));
            let d = BigInt::from(1 << 16) - prices.first_frac;
            let (quot, rem) = tmp.div_rem(&d);
            quot
        };

        ok!(stack.push_int(fees));

        Ok(0)
    }
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

fn get_unpacked_config_tuple(regs: &mut ControlRegs) -> VmResult<Rc<Tuple>> {
    let param = ok!(get_param(regs, 14));
    param.clone().into_tuple()
}

fn get_param(regs: &mut ControlRegs, index: usize) -> VmResult<&RcStackValue> {
    let Some(c7) = &regs.c7 else {
        vm_bail!(ControlRegisterOutOfRange(7))
    };

    let Some(control_params) = c7.get(0) else {
        vm_bail!(InvalidType {
            expected: StackValueType::Tuple,
            actual: StackValueType::Null
        })
    };

    let Some(intermediate_value) = control_params.as_tuple_range(0, 255) else {
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
