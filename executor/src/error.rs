/// Execution result.
pub type TxResult<T, E = TxError> = ::core::result::Result<T, E>;

/// Execution error.
#[derive(Debug, thiserror::Error)]
pub enum TxError {
    #[error("transaction skipped")]
    Skipped,
    #[error("fatal error")]
    Fatal(#[from] anyhow::Error),
}
