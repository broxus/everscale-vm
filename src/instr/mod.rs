use std::sync::OnceLock;

use anyhow::Result;

use self::arithops::Arithmetic;
use self::stackops::Stackops;
use crate::dispatch::{DispatchTable, Opcodes};

mod arithops;
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
        Arithmetic.init(&mut cp)?;
        Stackops.init(&mut cp)?;
        Ok(cp.build())
    }

    static CP0: OnceLock<DispatchTable> = OnceLock::new();
    CP0.get_or_init(|| build().unwrap())
}

pub trait Module {
    fn init(&self, opcodes: &mut Opcodes) -> Result<()>;
}
