// Stub types for non-Verus builds (e.g. standalone viewer binaries).
#[cfg(not(verus_keep_ghost))]
pub struct RuntimeBigNatWitness;
#[cfg(not(verus_keep_ghost))]
pub struct RuntimeBigIntWitness;

#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

// Exact runtime big-natural witness scaffold for future scalar de-trusting work.
//
// Phase 2 intentionally starts with minimal verified constructors and representation
// predicates. Arithmetic over limb vectors is added in subsequent steps.
#[cfg(verus_keep_ghost)]
verus! {
#[verifier::ext_equal]
pub struct RuntimeBigNatWitness {
    pub limbs_le: Vec<u32>,
    pub model: Ghost<nat>,
}

#[verifier::ext_equal]
pub struct RuntimeBigIntWitness {
    pub is_negative: bool,
    pub magnitude: RuntimeBigNatWitness,
    pub model: Ghost<int>,
}
}

mod verified_impl;
mod signed_verified_impl;

#[cfg(verus_keep_ghost)]
impl core::fmt::Debug for RuntimeBigNatWitness {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str("RuntimeBigNatWitness")
    }
}

// PartialEq/Eq for RuntimeBigNatWitness are in verified_impl.rs (value-based).

#[cfg(verus_keep_ghost)]
impl core::fmt::Debug for RuntimeBigIntWitness {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str("RuntimeBigIntWitness")
    }
}

// PartialEq/Eq for RuntimeBigIntWitness are in signed_verified_impl.rs (value-based).
