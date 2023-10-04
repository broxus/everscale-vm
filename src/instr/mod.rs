use std::sync::OnceLock;

use anyhow::Result;

use crate::dispatch::DispatchTable;

mod arithops;
mod dump;
mod stackops;

pub fn codepage(n: u16) -> Option<&'static DispatchTable> {
    match n {
        0 => Some(codepage0()),
        _ => None,
    }
}

pub fn codepage0() -> &'static DispatchTable {
    fn build() -> Result<DispatchTable> {
        let mut cp = DispatchTable::builder(0);
        stackops::register_stack_ops(&mut cp)?;
        arithops::register_arith_ops(&mut cp)?;
        Ok(cp.build())
    }

    static CP0: OnceLock<DispatchTable> = OnceLock::new();
    CP0.get_or_init(|| build().unwrap())
}
