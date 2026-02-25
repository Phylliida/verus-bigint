pub mod runtime_bigint_witness;

#[cfg(verus_keep_ghost)]
pub mod bigint;
pub use runtime_bigint_witness::RuntimeBigIntWitness;
pub use runtime_bigint_witness::RuntimeBigNatWitness;
