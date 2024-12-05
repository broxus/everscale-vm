use crate::cont::ControlRegs;
use crate::error::VmResult;
use crate::VmState;
use everscale_types::cell::{CellBuilder, HashBytes};
use everscale_types::num::Tokens;
use everscale_types::prelude::{Cell, CellFamily, Store};
use everscale_vm_proc::vm_module;
use num_bigint::BigInt;
use num_traits::ToPrimitive;
use std::fmt::Formatter;
use std::rc::Rc;

pub struct MessageOps;

const OUTPUT_ACTIONS_IDX: usize = 5;
#[vm_module]
impl MessageOps {
    //TODO: add new SENDMSG opcode
    #[instr(code = "fb00", fmt = "SENDRAWMSG")]
    fn exec_send_message_raw(st: &mut VmState) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let f = ok!(stack.pop_smallint_range(0, 255));
        let cell: Rc<Cell> = ok!(stack.pop_cell());

        let mut cb = CellBuilder::new();
        let Some(actions) = st.cr.get_d(OUTPUT_ACTIONS_IDX) else {
            vm_bail!(ControlRegisterOutOfRange(5))
        };
        cb.store_reference(actions)?;
        cb.store_uint(0x0ec3c86d, 32)?;
        cb.store_uint(f as u64, 8)?;
        cb.store_reference(cell.as_ref().clone())?;

        install_output_actions(&mut st.cr, cb.build()?)
    }

    #[instr(code = "fbss", range_from = "fb02", range_to = "fb04", fmt = ("{}", s.display()), args(s = ReserveArgs(args)))]
    fn exec_reserve_raw(st: &mut VmState, s: ReserveArgs) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let f = ok!(stack.pop_smallint_range(0, 15));

        let mut cell: Option<Rc<Cell>> = None;
        if s.is_x() {
            cell = ok!(stack.pop_cell_opt());
        }

        let amount: Rc<BigInt> = ok!(stack.pop_int());
        let Some(uamount) = amount.to_u128() else {
            vm_bail!(IntegerOutOfRange {
                min: 0,
                max: u128::MAX as isize,
                actual: amount.to_string()
            })
        };

        let tokens = Tokens::new(uamount);
        if !tokens.is_valid() {
            vm_bail!(IntegerOutOfRange {
                min: 0,
                max: Tokens::MAX.into_inner() as isize,
                actual: amount.to_string()
            })
        }

        let mut cb = CellBuilder::new();
        let Some(actions) = st.cr.get_d(OUTPUT_ACTIONS_IDX) else {
            vm_bail!(ControlRegisterOutOfRange(5))
        };
        cb.store_reference(actions)?;
        cb.store_uint(0x36e6b809, 32)?;
        cb.store_uint(f as u64, 8)?;
        tokens.store_into(&mut cb, &mut Cell::empty_context())?;
        if let Some(cell) = cell {
            cb.store_bit_one()?;
            cb.store_reference(cell.as_ref().clone())?;
        } else {
            cb.store_bit_zero()?;
        }

        install_output_actions(&mut st.cr, cb.build()?)
    }

    #[instr(code = "fb04", fmt = "SETCODE")]
    fn exec_set_code(st: &mut VmState) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let code = ok!(stack.pop_cell());
        let mut cb = CellBuilder::new();

        let Some(actions) = st.cr.get_d(OUTPUT_ACTIONS_IDX) else {
            vm_bail!(ControlRegisterOutOfRange(5))
        };

        cb.store_reference(actions)?;
        cb.store_uint(0x36e6b809, 32)?;
        cb.store_reference(code.as_ref().clone())?;

        install_output_actions(&mut st.cr, cb.build()?)
    }

    #[instr(code = "fb06", fmt = "SETLIBCODE")]
    fn exec_set_lib_code(st: &mut VmState) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let mode = ok!(stack.pop_smallint_range(0, 2));
        let code = ok!(stack.pop_cell());

        let mut cb = CellBuilder::new();
        let Some(actions) = st.cr.get_d(OUTPUT_ACTIONS_IDX) else {
            vm_bail!(ControlRegisterOutOfRange(5))
        };

        cb.store_reference(actions)?;
        cb.store_uint(0x26fa1dd4, 32)?;
        cb.store_uint((mode * 2 + 1) as u64, 8)?;
        cb.store_reference(code.as_ref().clone())?;

        install_output_actions(&mut st.cr, cb.build()?)
    }

    #[instr(code = "fb07", fmt = "CHANGELIB")]
    fn exec_change_lib(st: &mut VmState) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let mode = ok!(stack.pop_smallint_range(0, 2));
        let hash: Rc<BigInt> = ok!(stack.pop_int());
        let mut hash_bytes = [0u8; 32];
        if hash_bytes.len() < hash.to_bytes_be().1.len() {
            vm_bail!(IntegerOverflow)
        }
        hash_bytes.copy_from_slice(hash.to_bytes_be().1.as_ref());
        let hash_bytes = HashBytes::from(hash_bytes);

        let mut cb = CellBuilder::new();

        let Some(actions) = st.cr.get_d(OUTPUT_ACTIONS_IDX) else {
            vm_bail!(ControlRegisterOutOfRange(5))
        };
        cb.store_reference(actions)?;
        cb.store_uint(0x26fa1dd4, 32)?;
        cb.store_uint((mode * 2) as u64, 8)?;
        cb.store_u256(&hash_bytes)?;
        install_output_actions(&mut st.cr, cb.build()?)
    }
}

pub struct ReserveArgs(u32);
impl ReserveArgs {
    fn is_x(&self) -> bool {
        self.0 & 0b1 != 0
    }

    fn display(&self) -> DisplayReserveArgs {
        DisplayReserveArgs(self.0)
    }
}

pub struct DisplayReserveArgs(u32);
impl std::fmt::Display for DisplayReserveArgs {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let args = ReserveArgs(self.0);
        let is_x = if args.is_x() { "X" } else { "" };
        write!(f, "RAWRESERVE{is_x}")
    }
}
fn install_output_actions(regs: &mut ControlRegs, action_head: Cell) -> VmResult<i32> {
    vm_log!("installing an output action");
    regs.set_d(OUTPUT_ACTIONS_IDX, action_head);
    Ok(0)
}

#[cfg(test)]
mod tests {
    use crate::cont::OrdCont;
    use crate::stack::StackValueType::Cont;
    use crate::stack::{RcStackValue, Stack};
    use crate::util::OwnedCellSlice;
    use crate::VmState;
    use anyhow::Context;
    use everscale_types::cell::{Cell, CellBuilder, CellSlice};
    use everscale_types::dict::{Dict, RawDict};
    use everscale_types::models::{
        ExtInMsgInfo, GlobalCapabilities, GlobalCapability, OwnedMessage, StdAddr,
    };
    use everscale_types::prelude::{Boc, CellFamily, HashBytes, Load, Store};
    use everscale_vm::stack::Tuple;
    use everscale_vm::util::store_int_to_builder;
    use num_bigint::BigInt;
    use std::rc::Rc;
    use std::str::FromStr;
    use tracing_test::traced_test;

    #[test]
    #[traced_test]
    fn send_msg_test() {
        let code = Boc::decode(&everscale_asm_macros::tvmasm! {
            r#"
            SETCP0 DUP IFNOTRET // return if recv_internal
            DUP
            PUSHINT 85143
            EQUAL OVER
            PUSHINT 78748
            EQUAL OR
            // "seqno" and "get_public_key" get-methods
            PUSHCONT {
                PUSHINT 1
                AND
                PUSHCTR c4 CTOS
                LDU 32
                LDU 32
                NIP
                PLDU 256
                CONDSEL
            }
            IFJMP
            // fail unless recv_external
            INC THROWIF 32

            PUSHPOW2 9 LDSLICEX // signature
            DUP
            LDU 32 // subwallet_id
            LDU 32 // valid_until
            LDU 32 // msg_seqno

            NOW
            XCHG s1, s3
            LEQ
            DUMPSTK
            THROWIF 35

            PUSH c4 CTOS
            LDU 32
            LDU 32
            LDU 256
            ENDS

            XCPU s3, s2
            EQUAL
            THROWIFNOT 33

            XCPU s4, s4
            EQUAL
            THROWIFNOT 34

            XCHG s0, s4
            HASHSU
            XC2PU s0, s5, s5
            CHKSIGNU THROWIFNOT 35

            ACCEPT

            PUSHCONT { DUP SREFS }
            PUSHCONT {
                LDU 8
                LDREF
                XCHG s0, s2
                SENDRAWMSG
            }
            WHILE

            ENDS SWAP INC

            NEWC
            STU 32
            STU 32
            STU 256
            ENDC
            POP c4
            "#
        })
        .unwrap();

        let code = OwnedCellSlice::from(code);

        let balance_tuple: Tuple = vec![Rc::new(BigInt::from(10000000000u64)), Stack::make_null()];

        let addr =
            StdAddr::from_str("0:4f4f10cb9a30582792fb3c1e364de5a6fbe6fe04f4167f1f12f83468c767aeb3")
                .unwrap();
        let addr = OwnedCellSlice::from(CellBuilder::build_from(addr).unwrap());

        let c7: Vec<RcStackValue> = vec![
            Rc::new(BigInt::from(0x076ef1ea)),
            Rc::new(BigInt::from(0)),                 //actions
            Rc::new(BigInt::from(0)),                 //msgs_sent
            Rc::new(BigInt::from(1732042729)),        //unix_time
            Rc::new(BigInt::from(55364288000000u64)), //block_logical_time
            Rc::new(BigInt::from(55396331000001u64)), // transaction_logical_time
            Rc::new(BigInt::from(0)),                 //rand_ceed
            Rc::new(balance_tuple),
            Rc::new(addr),
            Stack::make_null(),
            Rc::new(code.clone()),
        ];

        let c4_data = Boc::decode_base64(
            "te6ccgEBAQEAKgAAUAAAAblLqS2KyLDWxgjLA6yhKJfmGLWfXdvRC34pWEXEek1ncgteNXU=",
        )
        .unwrap();

        let message_cell = Boc::decode_base64("te6ccgEBAgEAqQAB34gAnp4hlzRgsE8l9ng8bJvLTffN/AnoLP4+JfBo0Y7PXWYHO+2B5vPMosfjPalLE/qz0rm+wRn9g9sSu0q4Zwo0Lq5vB/YbhvWObr1T6jLdyEU3xEQ2uSP7sKARmIsEqMbIal1JbFM55wEgAAANyBwBAGhCACeniGXNGCwTyX2eDxsm8tN9838Cegs/j4l8GjRjs9dZodzWUAAAAAAAAAAAAAAAAAAA").unwrap();
        let message = OwnedMessage::load_from(
            &mut OwnedCellSlice::from(message_cell.clone()).apply().unwrap(),
        )
        .unwrap();
        let message_body = OwnedCellSlice::from(message.body);

        let stack: Vec<RcStackValue> = vec![
            Rc::new(BigInt::from(1406127106355u64)),
            Rc::new(BigInt::from(0)),
            Rc::new(message_cell),
            Rc::new(message_body),
            Rc::new(BigInt::from(-1)),
        ];

        let mut builder = VmState::builder();
        builder.c7 = Some(vec![Rc::new(c7)]);
        builder.stack = stack;
        builder.code = code;
        let mut vm_state = builder
            .with_gas_base(1000)
            .with_gas_remaining(1000)
            .with_gas_max(u64::MAX)
            .with_debug(TracingOutput::default())
            .build()
            .unwrap();
        vm_state.cr.set(4, Rc::new(c4_data)).unwrap();
        let result = vm_state.run();
        println!("code {result}");
    }

    #[test]
    #[traced_test]
    pub fn e_wallet_send_msg() {
        let code = Boc::decode_base64("te6cckEBBgEA/AABFP8A9KQT9LzyyAsBAgEgAgMABNIwAubycdcBAcAA8nqDCNcY7UTQgwfXAdcLP8j4KM8WI88WyfkAA3HXAQHDAJqDB9cBURO68uBk3oBA1wGAINcBgCDXAVQWdfkQ8qj4I7vyeWa++COBBwiggQPoqFIgvLHydAIgghBM7mRsuuMPAcjL/8s/ye1UBAUAmDAC10zQ+kCDBtcBcdcBeNcB10z4AHCAEASqAhSxyMsFUAXPFlAD+gLLaSLQIc8xIddJoIQJuZgzcAHLAFjPFpcwcQHLABLM4skB+wAAPoIQFp4+EbqOEfgAApMg10qXeNcB1AL7AOjRkzLyPOI+zYS/").unwrap();
        let code = OwnedCellSlice::from(code);

        let balance_tuple: Tuple = vec![Rc::new(BigInt::from(10000000000u64)), Stack::make_null()];

        let addr =
            StdAddr::from_str("0:6301b2c75596e6e569a6d13ae4ec70c94f177ece0be19f968ddce73d44e7afc7")
                .unwrap();
        let addr = OwnedCellSlice::from(CellBuilder::build_from(addr).unwrap());

        let c7: Vec<RcStackValue> = vec![
            Rc::new(BigInt::from(0x076ef1ea)),
            Rc::new(BigInt::from(0)),                 //actions
            Rc::new(BigInt::from(0)),                 //msgs_sent
            Rc::new(BigInt::from(1732048342)),        //unix_time
            Rc::new(BigInt::from(55398352000001u64)), //block_logical_time
            Rc::new(BigInt::from(55398317000004u64)), // transaction_logical_time
            Rc::new(BigInt::from(0)),                 //rand_ceed
            Rc::new(balance_tuple),
            Rc::new(addr),
            Stack::make_null(),
            Rc::new(code.clone()),
        ];

        let c4_data = Boc::decode_base64(
            "te6ccgEBAQEAKgAAUMiw1sYIywOsoSiX5hi1n13b0Qt+KVhFxHpNZ3ILXjV1AAABk0YeykY=",
        )
        .unwrap();

        let message_cell = Boc::decode_base64("te6ccgEBBAEA0gABRYgAxgNljqstzcrTTaJ1ydjhkp4u/ZwXwz8tG7nOeonPX44MAQHhmt2/xQjjwjfYraY7Tv53Ct8o9OAtI8nD7DFB19TrG7W8wYMxQKtbXuvGvaKFoB9D0lMZwnPpZ1fEBWxaXZgtg/IsNbGCMsDrKEol+YYtZ9d29ELfilYRcR6TWdyC141dQAAAZNGIEb+Zzz2EEzuZGyACAWWADGA2WOqy3NytNNonXJ2OGSni79nBfDPy0buc56ic9fjgAAAAAAAAAAAAAAAHc1lAADgDAAA=").unwrap();
        let message = OwnedMessage::load_from(
            &mut OwnedCellSlice::from(message_cell.clone()).apply().unwrap(),
        )
        .unwrap();
        let message_body = OwnedCellSlice::from(message.body);

        let stack: Vec<RcStackValue> = vec![
            Rc::new(BigInt::from(4989195982u64)),
            Rc::new(BigInt::from(0)),
            Rc::new(message_cell),
            Rc::new(message_body),
            Rc::new(BigInt::from(-1)),
        ];

        let mut builder = VmState::builder();
        builder.c7 = Some(vec![Rc::new(c7)]);
        builder.stack = stack;
        builder.code = code;

        let mut vm_state = builder
            .with_gas_base(10000)
            .with_gas_remaining(10000)
            .with_gas_max(u64::MAX)
            .with_debug(TracingOutput::default())
            .build()
            .unwrap();
        vm_state.cr.set(4, Rc::new(c4_data)).unwrap();
        let result = vm_state.run();
        println!("code {result}");
    }

    #[test]
    #[traced_test]
    pub fn jetton() {
        let code = Boc::decode_base64("te6ccgECGgEABQ4AART/APSkE/S88sgLAQIBYgIDAgLLBAUCASAQEQHX0MtDTAwFxsI5EMIAg1yHTHwGCEBeNRRm6kTDhgEDXIfoAMO1E0PoA+kD6QNTU0/8B+GHRUEWhQTT4QchQBvoCUATPFljPFszMy//J7VTg+kD6QDH6ADH0AfoAMfoAATFw+DoC0x8BAdM/ARKBgAdojhkZYOA54tkgUGD+gvABPztRND6APpA+kDU1NP/Afhh0SaCEGQrfQe6jss1NVFhxwXy4EkE+kAh+kQwwADy4U36ANTRINDTHwGCEBeNRRm68uBIgEDXIfoA+kAx+kAx+gAg1wsAmtdLwAEBwAGw8rGRMOJUQxvgOSWCEHvdl9664wIlghAsdrlzuuMCNCQHCAkKAY4hkXKRceL4OSBuk4F4LpEg4iFulDGBfuCRAeJQI6gToHOBBK1w+DygAnD4NhKgAXD4NqBzgQUTghAJZgGAcPg3oLzysCVZfwsB5jUF+gD6QPgo+EEoEDQB2zxvIjD5AHB0yMsCygfL/8nQUAjHBfLgShKhRBRQNvhByFAG+gJQBM8WWM8WzMzL/8ntVPpA0SDXCwHAALOOIsiAEAHLBQHPFnD6AnABy2qCENUydtsByx8BAcs/yYBC+wCRW+IYAdI1XwM0AfpA0gABAdGVyCHPFsmRbeLIgBABywVQBM8WcPoCcAHLaoIQ0XNUAAHLH1AEAcs/I/pEMMAAjp34KPhBEDVBUNs8byIw+QBwdMjLAsoHy//J0BLPFpcxbBJwAcsB4vQAyYBQ+wAYBP6CEGUB81S6jiUwM1FCxwXy4EkC+kDRQAME+EHIUAb6AlAEzxZYzxbMzMv/ye1U4CSCEPuI4Rm6jiQxMwPRUTHHBfLgSYsCQDT4QchQBvoCUATPFljPFszMy//J7VTgJIIQy4YpArrjAjAjghAlCNZquuMCI4IQdDHyIbrjAhA2DA0ODwHAghA7msoAcPsC+Cj4QRA2QVDbPG8iMCD5AHB0yMsCygfL/8iAGAHLBQHPF1j6AgKYWHdQA8trzMyXMAFxWMtqzOLJgBH7AFAFoEMU+EHIUAb6AlAEzxZYzxbMzMv/ye1UGABONDZRRccF8uBJyFADzxbJEDQS+EHIUAb6AlAEzxZYzxbMzMv/ye1UACI2XwMCxwXy4EnU1NEB7VT7BABKM1BCxwXy4EkB0YsCiwJANPhByFAG+gJQBM8WWM8WzMzL/8ntVAAcXwaCENNyFYy63IQP8vACAUgSEwICcRYXAT+10V2omh9AH0gfSBqamn/gPww6IovgnwUfCCJbZ43kUBgCAWoUFQAuq1vtRND6APpA+kDU1NP/Afhh0RAkXwQALqpn7UTQ+gD6QPpA1NTT/wH4YdFfBfhBAVutvPaiaH0AfSB9IGpqaf+A/DDoii+CfBR8IIltnjeRGHyAODpkZYFlA+X/5OhAGACLrxb2omh9AH0gfSBqamn/gPww6L+Z6DbBeDhy69tRTZyXwoO38K5ReQKeK2EZw5RicZ5PRu2PdBPmLHgKOGRlg/oAZKGAQAH2hA9/cCb6RDGr+1MRSUYYBMjLA1AD+gIBzxYBzxbL/yCBAMrIyw8Bzxck+QAl12UlggIBNMjLFxLLD8sPy/+OKQakXAHLCXH5BABScAHL/3H5BACr+yiyUwS5kzQ0I5Ew4iDAICTAALEX5hAjXwMzMyJwA8sJySLIywESGQAU9AD0AMsAyQFvAg==").unwrap();
        let code = OwnedCellSlice::from(code);

        let balance_tuple: Tuple = vec![Rc::new(BigInt::from(1931553923u64)), Stack::make_null()];

        let addr =
            StdAddr::from_str("0:2a0c78148c73416b63250b990efdfbf9d5897bf3b33e2f5498a2fe0617174bb8")
                .unwrap();
        let addr = OwnedCellSlice::from(CellBuilder::build_from(addr).unwrap());

        let default = StdAddr::default();
        let default = OwnedCellSlice::from(CellBuilder::build_from(default).unwrap());

        let c7: Vec<RcStackValue> = vec![
            Rc::new(BigInt::from(0x076ef1ea)),
            Rc::new(BigInt::from(0)),                 //actions
            Rc::new(BigInt::from(0)),                 //msgs_sent
            Rc::new(BigInt::from(1733142533)),        //unix_time
            Rc::new(BigInt::from(50899537000013u64)), //block_logical_time
            Rc::new(BigInt::from(50899537000013u64)), // transaction_logical_time
            Rc::new(BigInt::from(0)),                 //rand_ceed
            Rc::new(balance_tuple),
            Rc::new(addr.clone()),
            Stack::make_null(),
            Rc::new(code.clone()),
        ];

        let c4_data = Boc::decode_base64(
            "te6ccgEBBAEA3gACTmE+QBlNGKCvtRVlwuLLP8LwzhcDJNm1TPewFBFqmlIYet7ln0NupwECCEICDvGeG/QPK6SS/KrDhu7KWb9oJ6OFBwjZ/NmttoOrwzYB5mh0dHBzOi8vZ2lzdC5naXRodWJ1c2VyY29udGVudC5jb20vRW1lbHlhbmVua29LLzI3MWMwYWRhMWRlNDJiOTdjNDU1YWM5MzVjOTcyZjQyL3Jhdy9iN2IzMGMzZTk3MGUwNzdlMTFkMDg1Y2M2NzEzYmUDADAzMTU3YzdjYTA4L21ldGFkYXRhLmpzb24=",
        )
            .unwrap();

        println!("{}", c4_data.repr_hash());

        let stack: Vec<RcStackValue> = vec![
            Rc::new(default),
            Rc::new(BigInt::from(103289)),
            //Rc::new(BigInt::from(106029))
        ];

        let mut builder = VmState::builder();

        let mut vm_state = builder
            .with_c7(vec![Rc::new(c7)])
            .with_stack(stack)
            .with_code(code.clone())
            .with_gas_base(1000000)
            .with_gas_remaining(1000000)
            .with_gas_max(u64::MAX)
            .with_debug(TracingOutput::default())
            .build()
            .unwrap();
        vm_state.cr.set(4, Rc::new(c4_data)).unwrap();
        vm_state
            .cr
            .set(
                3,
                Rc::new(OrdCont::simple(
                    code.clone(),
                    crate::instr::codepage0().id(),
                )),
            )
            .unwrap();

        let result = !vm_state.run();
        println!("code {result}");
    }

    #[derive(Default)]
    struct TracingOutput {
        buffer: String,
    }

    impl std::fmt::Write for TracingOutput {
        fn write_str(&mut self, mut s: &str) -> std::fmt::Result {
            while !s.is_empty() {
                match s.split_once('\n') {
                    None => {
                        self.buffer.push_str(s);
                        return Ok(());
                    }
                    Some((prefix, rest)) => {
                        tracing::debug!("{}{prefix}", self.buffer);
                        self.buffer.clear();
                        s = rest;
                    }
                }
            }
            Ok(())
        }
    }
}
