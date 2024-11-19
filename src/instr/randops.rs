use crate::cont::ControlRegs;
use crate::error::VmResult;
use crate::stack::{RcStackValue, StackValueType};
use crate::VmState;
use everscale_types::cell::HashBytes;
use everscale_vm::stack::{Stack, Tuple};
use everscale_vm_proc::vm_module;
use num_bigint::{BigInt, Sign};
use num_traits::ToBytes;
use sha2::Digest;
use std::ops::ShrAssign;
use std::rc::Rc;

pub struct RandOps;
const RANDCEED_ID: usize = 6;

#[vm_module]
impl RandOps {
    #[instr(code = "f810", fmt = "RANDU256")]
    fn exec_randu256(st: &mut VmState) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let random_bytes: HashBytes = ok!(generate_random_u256(&mut st.cr));
        let random = BigInt::from_bytes_be(Sign::Plus, random_bytes.as_ref());
        ok!(stack.push_int(random));
        Ok(0)
    }
    #[instr(code = "f811", fmt = "RAND")]
    fn exec_rand_int(st: &mut VmState) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let int: Rc<BigInt> = ok!(stack.pop_int());
        let random_bytes: HashBytes = ok!(generate_random_u256(&mut st.cr));
        let random = BigInt::from_bytes_be(Sign::Plus, random_bytes.as_ref());

        let Some(mut temp) = int.checked_mul(&random) else {
            vm_bail!(IntegerOverflow)
        };

        temp.shr_assign(256);
        ok!(stack.push_int(temp));

        Ok(0)
    }

    #[instr(code = "f814", fmt = "SETRAND", args(mix = false))]
    #[instr(code = "f815", fmt = "ADDRAND", args(mix = true))]
    fn exec_set_rand(st: &mut VmState, mix: bool) -> VmResult<i32> {
        let stack = Rc::make_mut(&mut st.stack);
        let mut int: Rc<BigInt> = ok!(stack.pop_int());

        if int.bits() > 256 {
            vm_bail!(IntegerOutOfRange {
                min: 0,
                max: 256,
                actual: int.bits().to_string()
            })
        }

        let Some(c7) = &st.cr.c7 else {
            vm_bail!(ControlRegisterOutOfRange(7))
        };

        let control_params_opt = c7.get(0);
        let Some(control_params) = control_params_opt else {
            vm_bail!(InvalidType {
                expected: StackValueType::Tuple,
                actual: StackValueType::Null
            })
        };

        let intermediate_tuple_opt = control_params.as_tuple_range(0, 255);
        let Some(intermediate_value) = intermediate_tuple_opt else {
            vm_bail!(InvalidType {
                expected: StackValueType::Tuple,
                actual: control_params.ty()
            })
        };

        if mix {
            let value: Option<&RcStackValue> = intermediate_value.get(RANDCEED_ID);

            let ceed: Rc<BigInt> = match value {
                Some(value) => ok!(value.clone().into_int()),
                None => vm_bail!(InvalidType {
                    expected: StackValueType::Int,
                    actual: StackValueType::Null
                }),
            };

            let mut data = [0u8; 64];
            data[0..32].copy_from_slice(&ceed.to_be_bytes());
            data[32..64].copy_from_slice(&int.to_be_bytes());

            let mut hasher = sha2::Sha256::new();
            hasher.update(data);
            let hash = hasher.finalize();
            int = Rc::new(BigInt::from_bytes_be(Sign::Plus, &hash));
        }

        //TODO: should clean c7 first
        let mut new_intermediate = Tuple::from(intermediate_value);
        let to_pay = if RANDCEED_ID < intermediate_value.len() {
            new_intermediate[RANDCEED_ID] = int;
            new_intermediate.len()
        } else {
            new_intermediate.resize(RANDCEED_ID + 1, Stack::make_null());
            new_intermediate[RANDCEED_ID] = int;
            RANDCEED_ID + 1
        };

        if to_pay > 0 {
            //TODO: consume gas tuple in amount of to_pay
        }

        let mut new_c7 = c7.as_ref().clone();
        new_c7[0] = Rc::new(new_intermediate);

        //TODO: consume gas tuple for c7
        st.cr.set_c7(Rc::new(new_c7));

        Ok(0)
    }
}

fn generate_random_u256(regs: &mut ControlRegs) -> VmResult<HashBytes> {
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

    let value: Option<&RcStackValue> = intermediate_value.get(RANDCEED_ID);
    let ceed: Rc<BigInt> = match value {
        Some(value) => ok!(value.clone().into_int()),
        None => vm_bail!(InvalidType {
            expected: StackValueType::Int,
            actual: StackValueType::Null
        }),
    };

    let seed_bytes = ceed.to_be_bytes();
    let mut hasher = sha2::Sha512::new();
    hasher.update(seed_bytes);
    let hash = hasher.finalize();

    let new_ceed = BigInt::from_bytes_be(Sign::Plus, &hash[0..32]);

    let mut random_bytes = [0u8; 32];
    random_bytes.copy_from_slice(&hash[32..64]);
    let random = HashBytes::from(random_bytes);

    //TODO: should clean c7 first

    //TODO: consume gas to set t1 idx 6 in c7
    let mut new_intermediate = Tuple::from(intermediate_value);
    new_intermediate[RANDCEED_ID] = Rc::new(new_ceed);

    let mut new_c7 = c7.as_ref().clone();
    new_c7[0] = Rc::new(new_intermediate);

    //TODO: consume gas tuple for c7
    regs.set_c7(Rc::new(new_c7));
    Ok(random)
}

pub mod test {
    use crate::stack::{RcStackValue, StackValue};
    use everscale_vm::stack::Tuple;
    use num_bigint::{BigInt, Sign};
    use std::rc::Rc;
    use tracing_test::traced_test;

    #[test]
    #[tracing_test::traced_test]
    fn random() {
        let bytes = hex::decode("576f8d6b5ac3bcc80844b7d50b1cc6603444bbe7cfcf8fc0aa1ee3c636d9e339")
            .unwrap();
        let value: RcStackValue = Rc::new(BigInt::from_bytes_be(Sign::Plus, &bytes));

        let result_bytes =
            hex::decode("504C79E96A1A3D91262EDE19D9F064E9752EEA03E21A5E208D7BDCAF2D6610EE")
                .unwrap();
        let result: RcStackValue = Rc::new(BigInt::from_bytes_be(Sign::Plus, &result_bytes));

        let tuple: Tuple = vec![
            value.clone(),
            value.clone(),
            value.clone(),
            value.clone(),
            value.clone(),
            value.clone(),
            value.clone(),
        ];
        let tuple2: Tuple = vec![Rc::new(tuple)];

        assert_run_vm_with_c7!("RAND", [tuple2], [raw value] => [raw result] )
    }

    #[test]
    #[traced_test]
    fn random_u256() {
        let bytes = hex::decode("576f8d6b5ac3bcc80844b7d50b1cc6603444bbe7cfcf8fc0aa1ee3c636d9e339")
            .unwrap();

        let result_bytes =
            hex::decode("EB1A91B388F714F56EE88C7B1B0902FF713FE8EBA39F64FC8F7F2F618601BBF5")
                .unwrap();
        let result: RcStackValue = Rc::new(BigInt::from_bytes_be(Sign::Plus, &result_bytes));

        let value: RcStackValue = Rc::new(BigInt::from_bytes_be(Sign::Plus, &bytes));
        let tuple: Tuple = vec![
            value.clone(),
            value.clone(),
            value.clone(),
            value.clone(),
            value.clone(),
            value.clone(),
            value.clone(),
        ];
        let tuple2: Tuple = vec![Rc::new(tuple)];

        assert_run_vm_with_c7!("RANDU256", [tuple2], [] => [raw result] )
    }
}
