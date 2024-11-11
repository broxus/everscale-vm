use std::sync::OnceLock;

use anyhow::Result;

use self::arithops::Arithops;
use self::basicgasops::BasicGasOps;
use self::cellops::Cellops;
use self::contops::Contops;
use self::debugops::Debugops;
use self::randops::RandOps;
use self::stackops::Stackops;
use self::tupleops::Tupleops;
use crate::dispatch::{DispatchTable, Opcodes};
use crate::instr::dictops::Dictops;

mod arithops;
mod basicgasops;
mod cellops;
mod contops;
mod debugops;
mod randops;
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
        BasicGasOps.init(&mut cp)?;
        RandOps.init(&mut cp)?;
        Ok(cp.build())
    }

    static CP0: OnceLock<DispatchTable> = OnceLock::new();
    CP0.get_or_init(|| build().unwrap())
}

pub trait Module {
    fn init(&self, opcodes: &mut Opcodes) -> Result<()>;
}
