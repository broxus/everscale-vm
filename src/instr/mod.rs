use std::sync::OnceLock;

use crate::dispatch::DispatchTable;

pub fn codepage(n: u16) -> Option<&'static DispatchTable> {
    match n {
        0 => Some(codepage0()),
        _ => None,
    }
}

pub fn codepage0() -> &'static DispatchTable {
    static CP0: OnceLock<DispatchTable> = OnceLock::new();
    CP0.get_or_init(|| {
        // TODO: register opcodes
        DispatchTable::builder(0).build()
    })
}
