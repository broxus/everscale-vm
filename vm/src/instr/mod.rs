use std::sync::OnceLock;

use anyhow::Result;

use self::arithops::ArithOps;
use self::cellops::CellOps;
use self::cmpops::CmpOps;
use self::configops::ConfigOps;
use self::contops::ContOps;
use self::cryptops::CryptOps;
use self::currencyops::CurrencyOps;
use self::debugops::DebugOps;
use self::dictops::DictOps;
use self::gasops::GasOps;
use self::logicops::LogicOps;
use self::messageops::MessageOps;
use self::randops::RandOps;
use self::sizeops::SizeOps;
use self::stackops::StackOps;
use self::tupleops::TupleOps;
use crate::dispatch::{DispatchTable, Opcodes};

mod arithops;
mod cellops;
mod cmpops;
mod configops;
mod contops;
mod cryptops;
mod currencyops;
mod debugops;
mod dictops;
mod gasops;
mod logicops;
mod messageops;
mod randops;
mod sizeops;
mod stackops;
mod tupleops;

/// Codepage resolver.
pub fn codepage(n: u16) -> Option<&'static DispatchTable> {
    match n {
        0 => Some(codepage0()),
        _ => None,
    }
}

/// Default codepage.
pub fn codepage0() -> &'static DispatchTable {
    fn build() -> Result<DispatchTable> {
        let mut cp = DispatchTable::builder(0);
        ArithOps.init(&mut cp)?;
        CmpOps.init(&mut cp)?;
        LogicOps.init(&mut cp)?;
        CellOps.init(&mut cp)?;
        ContOps.init(&mut cp)?;
        StackOps.init(&mut cp)?;
        TupleOps.init(&mut cp)?;
        DebugOps.init(&mut cp)?;
        DictOps.init(&mut cp)?;
        GasOps.init(&mut cp)?;
        RandOps.init(&mut cp)?;
        ConfigOps.init(&mut cp)?;
        MessageOps.init(&mut cp)?;
        CryptOps.init(&mut cp)?;
        CurrencyOps.init(&mut cp)?;
        SizeOps.init(&mut cp)?;
        Ok(cp.build())
    }

    static CP0: OnceLock<DispatchTable> = OnceLock::new();
    CP0.get_or_init(|| build().unwrap())
}

trait Module {
    fn init(&self, opcodes: &mut Opcodes) -> Result<()>;
}
