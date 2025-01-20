use everscale_types::models::ShardIdent;

pub const fn shift_ceil_price(value: u128) -> u128 {
    let r = value & 0xffff != 0;
    (value >> 16) + r as u128
}

pub const fn is_masterchain(workchain: i32) -> bool {
    workchain == ShardIdent::MASTERCHAIN.workchain()
}
