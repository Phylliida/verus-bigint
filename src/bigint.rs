use vstd::prelude::*;

pub mod algebra;

verus! {

/// Spec-level arbitrary-precision integer.
///
/// A thin wrapper around `int` that enables implementing verus-algebra
/// traits (Verus cannot implement traits on built-in types).
pub struct BigInt {
    pub value: int,
}

impl BigInt {
    /// Construct from an int value.
    pub open spec fn new(value: int) -> Self {
        BigInt { value }
    }
}

} // verus!
