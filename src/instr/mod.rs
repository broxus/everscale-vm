use std::sync::OnceLock;

use anyhow::Result;

use self::arithops::Arithops;
use self::basicgasops::BasicGasOps;
use self::cellops::Cellops;
use self::cmpops::CmpOps;
use self::configops::ConfigOps;
use self::contops::Contops;
use self::currencyops::CurrencyOps;
use self::debugops::Debugops;
use self::dictops::Dictops;
use self::hashops::Hashops;
use self::logicops::LogicOps;
use self::messageops::MessageOps;
use self::miscops::Miscops;
use self::randops::RandOps;
use self::stackops::Stackops;
use self::tupleops::Tupleops;
use crate::dispatch::{DispatchTable, Opcodes};

mod arithops;
mod basicgasops;
mod cellops;
mod cmpops;
mod configops;
mod contops;
mod currencyops;
mod debugops;
mod dictops;
mod hashops;
mod logicops;
mod messageops;
mod miscops;
mod randops;
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
        Arithops.init(&mut cp)?;
        CmpOps.init(&mut cp)?;
        LogicOps.init(&mut cp)?;
        Cellops.init(&mut cp)?;
        Contops.init(&mut cp)?;
        Stackops.init(&mut cp)?;
        Tupleops.init(&mut cp)?;
        Debugops.init(&mut cp)?;
        Dictops.init(&mut cp)?;
        BasicGasOps.init(&mut cp)?;
        RandOps.init(&mut cp)?;
        ConfigOps.init(&mut cp)?;
        MessageOps.init(&mut cp)?;
        Hashops.init(&mut cp)?;
        CurrencyOps.init(&mut cp)?;
        Miscops.init(&mut cp)?;
        Ok(cp.build())
    }

    static CP0: OnceLock<DispatchTable> = OnceLock::new();
    CP0.get_or_init(|| build().unwrap())
}

trait Module {
    fn init(&self, opcodes: &mut Opcodes) -> Result<()>;
}
