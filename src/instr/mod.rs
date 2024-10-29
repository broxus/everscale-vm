use std::sync::OnceLock;

use anyhow::Result;

use self::arithops::Arithops;
use self::cellops::Cellops;
use self::contops::Contops;
use self::debugops::Debugops;
use self::stackops::Stackops;
use self::tupleops::Tupleops;
use crate::dispatch::{DispatchTable, Opcodes};
use crate::instr::dictops::Dictops;

mod arithops;
mod cellops;
mod contops;
mod debugops;
mod dictops;
mod stackops;
mod tupleops;

pub fn codepage(n: u16) -> Option<&'static DispatchTable> {
    match n {
        0 => Some(codepage0()),
        _ => None,
    }
}

pub fn codepage0() -> &'static DispatchTable {
    fn build() -> Result<DispatchTable> {
        let mut cp = DispatchTable::builder(0);
        Arithops.init(&mut cp)?;
        Cellops.init(&mut cp)?;
        Contops.init(&mut cp)?;
        Stackops.init(&mut cp)?;
        Tupleops.init(&mut cp)?;
        Debugops.init(&mut cp)?;
        Dictops.init(&mut cp)?;
        Ok(cp.build())
    }

    static CP0: OnceLock<DispatchTable> = OnceLock::new();
    CP0.get_or_init(|| build().unwrap())
}

pub trait Module {
    fn init(&self, opcodes: &mut Opcodes) -> Result<()>;
}
