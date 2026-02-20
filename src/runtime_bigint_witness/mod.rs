#[cfg(not(verus_keep_ghost))]
compile_error!(
    "verus-bigint now exposes a single verified implementation; \
     build with Verus (`cfg(verus_keep_ghost)`, e.g. `cargo verus verify`)"
);
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
pub struct RuntimeBigNatWitness {
    pub limbs_le: Vec<u32>,
    pub model: Ghost<nat>,
}

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

#[cfg(verus_keep_ghost)]
impl PartialEq for RuntimeBigNatWitness {
    fn eq(&self, other: &Self) -> bool {
        core::ptr::eq(self, other)
    }
}

#[cfg(verus_keep_ghost)]
impl Eq for RuntimeBigNatWitness {}

#[cfg(verus_keep_ghost)]
impl core::fmt::Debug for RuntimeBigIntWitness {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str("RuntimeBigIntWitness")
    }
}

#[cfg(verus_keep_ghost)]
impl PartialEq for RuntimeBigIntWitness {
    fn eq(&self, other: &Self) -> bool {
        core::ptr::eq(self, other)
    }
}

#[cfg(verus_keep_ghost)]
impl Eq for RuntimeBigIntWitness {}
