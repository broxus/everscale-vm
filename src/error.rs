use everscale_types::error::Error;

use crate::stack::StackValueType;

#[derive(Debug, thiserror::Error)]
pub enum VmError {
    #[error("stack underflow at depth {0}")]
    StackUnderflow(usize),
    #[error("too many arguments copied into a closure continuation: {0}")]
    TooManyArguments(usize),
    #[error("expected integer in range {min}..={max}, found {actual}")]
    IntegerOutOfRange {
        min: usize,
        max: usize,
        actual: String,
    },
    #[error("invalid opcode")]
    InvalidOpcode,
    #[error("expected type {expected:?}, found {actual:?}")]
    InvalidType {
        expected: StackValueType,
        actual: StackValueType,
    },
    #[error("out of gas")]
    OutOfGas,
}

#[derive(Debug, Clone, Copy, Eq, PartialEq, Ord, PartialOrd)]
#[repr(u8)]
pub enum VmException {
    Ok = 0,
    Alternative = 1,
    StackUnderflow = 2,
    StackOverflow = 3,
    IntOverflow = 4,
    RangeCheck = 5,
    InvalidOpcode = 6,
    TypeCheck = 7,
    CellOverflow = 8,
    CellUnderflow = 9,
    DictError = 10,
    Unknown = 11,
    Fatal = 12,
    OutOfGas = 13,
    VirtError = 14,
}

impl VmException {
    pub const fn as_exit_code(&self) -> i32 {
        !(*self as i32)
    }
}

impl std::fmt::Display for VmException {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            Self::Ok => "normal termination",
            Self::Alternative => "alternative termination",
            Self::StackUnderflow => "stack underflow",
            Self::StackOverflow => "stack overflow",
            Self::IntOverflow => "integer overflow",
            Self::RangeCheck => "integer out of range",
            Self::InvalidOpcode => "invalid opcode",
            Self::TypeCheck => "type check error",
            Self::CellOverflow => "cell overflow",
            Self::CellUnderflow => "cell underflow",
            Self::DictError => "dictionary error",
            Self::Unknown => "unknown error",
            Self::Fatal => "fatal error",
            Self::OutOfGas => "out of gas",
            Self::VirtError => "virtualization error",
        })
    }
}

impl From<anyhow::Error> for VmException {
    #[inline]
    fn from(value: anyhow::Error) -> Self {
        Self::from(&value)
    }
}

impl From<&anyhow::Error> for VmException {
    fn from(value: &anyhow::Error) -> Self {
        if let Some(e) = value.downcast_ref::<Error>() {
            match e {
                Error::CellUnderflow => Self::CellUnderflow,
                Error::CellOverflow => Self::CellOverflow,
                Error::PrunedBranchAccess => Self::VirtError,
                Error::Cancelled => Self::OutOfGas, // ?
                Error::IntOverflow => Self::IntOverflow,
                _ => Self::Fatal, // ?
            }
        } else if let Some(e) = value.downcast_ref::<VmError>() {
            match e {
                VmError::StackUnderflow(_) => Self::StackUnderflow,
                VmError::TooManyArguments(_) => Self::StackOverflow,
                VmError::IntegerOutOfRange { .. } => Self::RangeCheck,
                VmError::InvalidOpcode => Self::InvalidOpcode,
                VmError::InvalidType { .. } => Self::TypeCheck,
                VmError::OutOfGas => Self::OutOfGas,
            }
        } else {
            Self::Unknown
        }
    }
}
