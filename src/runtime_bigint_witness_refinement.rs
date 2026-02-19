use crate::runtime_bigint_witness::RuntimeBigNatWitness;
use vstd::prelude::*;

verus! {

/// Minimal trusted bridge allowing Verus to reason about an externally-declared
/// runtime witness type.
#[verifier::external_type_specification]
pub struct ExRuntimeBigNatWitness(RuntimeBigNatWitness);

} // verus!
