use crate::dispatch::FnDumpArgInstr;

pub fn dump_1sr(prefix: &'static str) -> Box<FnDumpArgInstr> {
    Box::new(move |_, args, f| {
        write!(f, "{prefix}s{}", args & 0xf)?;
        Ok(())
    })
}

pub fn dump_1sr_l(prefix: &'static str) -> Box<FnDumpArgInstr> {
    Box::new(move |_, args, f| {
        write!(f, "{prefix}s{}", args & 0xff)?;
        Ok(())
    })
}

pub fn dump_1c(prefix: &'static str) -> Box<FnDumpArgInstr> {
    Box::new(move |_, args, f| {
        write!(f, "{prefix}{}", args & 0xf)?;
        Ok(())
    })
}

pub fn dump_1c_suffix(prefix: &'static str, suffix: &'static str) -> Box<FnDumpArgInstr> {
    Box::new(move |_, args, f| {
        write!(f, "{prefix}{}{suffix}", args & 0xf)?;
        Ok(())
    })
}

pub fn dump_1c_and(mask: u32, prefix: &'static str) -> Box<FnDumpArgInstr> {
    Box::new(move |_, args, f| {
        write!(f, "{prefix}{}", args & mask)?;
        Ok(())
    })
}

pub fn dump_1c_l_add(add: i32, prefix: &'static str) -> Box<FnDumpArgInstr> {
    Box::new(move |_, args, f| {
        write!(f, "{prefix}{}", (args & 0xff) as i32 + add)?;
        Ok(())
    })
}

pub fn dump_2sr(prefix: &'static str) -> Box<FnDumpArgInstr> {
    Box::new(move |_, args, f| {
        write!(f, "{prefix}s{},s{}", (args >> 4) & 0xf, args & 0xf)?;
        Ok(())
    })
}

pub fn dump_2sr_adj(adj: i32, prefix: &'static str) -> Box<FnDumpArgInstr> {
    Box::new(move |_, args, f| {
        write!(
            f,
            "{prefix}s{},s{}",
            ((args as i32 >> 4) & 0xf) - ((adj >> 4) & 0xf),
            (args as i32 & 0xf) - (adj & 0xf)
        )?;
        Ok(())
    })
}

pub fn dump_2c(prefix: &'static str, sep: &'static str) -> Box<FnDumpArgInstr> {
    Box::new(move |_, args, f| {
        write!(f, "{prefix}{}{sep}{}", (args >> 4) & 0xf, args & 0xf)?;
        Ok(())
    })
}

pub fn dump_2c_add(add: u32, prefix: &'static str, sep: &'static str) -> Box<FnDumpArgInstr> {
    Box::new(move |_, args, f| {
        write!(
            f,
            "{prefix}{}{sep}{}",
            ((args >> 4) & 0xf) + ((add >> 4) & 0xf),
            (args & 0xf) + (add & 0xf)
        )?;
        Ok(())
    })
}

pub fn dump_3sr(prefix: &'static str) -> Box<FnDumpArgInstr> {
    Box::new(move |_, args, f| {
        write!(
            f,
            "{prefix}s{},s{},s{}",
            (args >> 8) & 0xf,
            (args >> 4) & 0xf,
            args & 0xf
        )?;
        Ok(())
    })
}

pub fn dump_3sr_adj(adj: i32, prefix: &'static str) -> Box<FnDumpArgInstr> {
    Box::new(move |_, args, f| {
        write!(
            f,
            "{prefix}s{},s{},s{}",
            ((args as i32 >> 8) & 0xf) - ((adj >> 8) & 0xf),
            ((args as i32 >> 4) & 0xf) - ((adj >> 4) & 0xf),
            (args as i32 & 0xf) - (adj & 0xf)
        )?;
        Ok(())
    })
}
