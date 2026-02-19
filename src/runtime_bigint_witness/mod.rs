#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

/// Exact runtime big-natural witness scaffold for future scalar de-trusting work.
///
/// Phase 2 intentionally starts with minimal verified constructors and representation
/// predicates. Arithmetic over limb vectors is added in subsequent steps.
#[cfg_attr(not(verus_keep_ghost), derive(Clone, Debug, Eq, PartialEq))]
#[cfg_attr(verus_keep_ghost, derive(Clone))]
pub struct RuntimeBigNatWitness {
    pub limbs_le: Vec<u32>,
    #[cfg(verus_keep_ghost)]
    pub model: Ghost<nat>,
}

mod runtime_impl;
mod verified_impl;
#[cfg(test)]
mod tests;

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
