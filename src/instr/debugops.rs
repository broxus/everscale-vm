use anyhow::Result;
use everscale_vm_proc::vm_module;

use crate::dispatch::Opcodes;
use crate::error::VmError;
use crate::VmState;

pub struct Debugops;

#[vm_module]
impl Debugops {
    #[instr(code = "fe00", fmt = "DUMPSTK")]
    fn exec_dump_stack(st: &mut VmState) -> Result<i32> {
        let Some(debug) = &mut st.debug else {
            return Ok(0);
        };

        let mut depth = st.stack.depth();
        write!(&mut *debug, "#DEBUG#: stack({depth} values) :")?;
        if depth > 255 {
            write!(&mut *debug, " ...")?;
            depth = 255;
        }

        for value in st.stack.items.iter().rev().take(depth) {
            write!(&mut *debug, " {}", value.display_list())?;
        }

        writeln!(&mut *debug)?;
        Ok(0)
    }

    #[instr(code = "fexx", range_from = "fe01", range_to = "fe14", fmt = "DEBUG {x}", args(x = args & 0xff))]
    #[instr(code = "fexx", range_from = "fe15", range_to = "fe20", fmt = "DEBUG {x}", args(x = args & 0xff))]
    #[instr(code = "fexx", range_from = "fe30", range_to = "fef0", fmt = "DEBUG {x}", args(x = args & 0xff))]
    fn exec_dummy_debug(_: &mut VmState, x: u32) -> Result<i32> {
        _ = x;
        Ok(0)
    }

    #[instr(code = "fe14", fmt = "STRDUMP")]
    fn exec_dump_string(st: &mut VmState) -> Result<i32> {
        let Some(debug) = &mut st.debug else {
            return Ok(0);
        };

        if let Some(value) = st.stack.items.last() {
            if let Some(slice) = value.as_slice() {
                // TODO: print as string, but why is it needed?
                writeln!(
                    &mut *debug,
                    "#DEBUG#: {}",
                    slice.apply_allow_special().display_data()
                )?;
            } else {
                writeln!(&mut *debug, "#DEBUG#: is not a slice")?;
            }
        } else {
            writeln!(&mut *debug, "#DEBUG#: s0 is absent")?;
        }
        Ok(0)
    }

    #[instr(code = "fe2x", fmt = "DUMP s{x}")]
    fn exec_dump_value(st: &mut VmState, x: u32) -> Result<i32> {
        let Some(debug) = &mut st.debug else {
            return Ok(0);
        };

        let x = x as usize;
        let depth = st.stack.depth();
        if x < depth {
            writeln!(
                &mut *debug,
                "#DEBUG#: s{x} = {}",
                st.stack.items[depth - x - 1].display_list()
            )?;
        } else {
            writeln!(&mut *debug, "#DEBUG#: s{x} is absent")?;
        }

        Ok(0)
    }

    #[init]
    fn init_dummy_debug_str_ext(&self, t: &mut Opcodes) -> Result<()> {
        t.add_ext(0xfef, 12, 4, exec_dummy_debug_str)
    }

    fn exec_dummy_debug_str(st: &mut VmState, args: u32, bits: u16) -> Result<i32> {
        let data_bits = ((args & 0xf) + 1) as u16 * 8;
        anyhow::ensure!(
            st.code.range().has_remaining(bits + data_bits, 0),
            VmError::InvalidOpcode
        );
        st.code.range_mut().try_advance(bits, 0);
        let prefix = st.code.apply_allow_special().get_prefix(data_bits, 0);

        println!("{}", prefix.remaining_bits());
        vm_log!("execute DEBUGSTR {}", prefix.display_data());

        st.code.range_mut().try_advance(data_bits, 0);
        Ok(0)
    }
}
