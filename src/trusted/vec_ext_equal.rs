//! TRUSTED AXIOM: Vec extensional equality
//!
//! Justification: Vec's spec-level view (@) captures all semantically relevant
//! state. Capacity, pointer address, and allocator state are implementation
//! details invisible to verification. This is consistent with:
//!   - Option<V> having ext_equal in vstd (core.rs:120)
//!   - Rust's PartialEq for Vec comparing only contents
//!
//! This axiom will be removed when verus-lang/verus adds #[verifier::ext_equal]
//! to Vec's external_type_specification in vstd.

use vstd::prelude::*;

verus! {

///  Two Vecs with extensionally equal views are extensionally equal.
#[verifier::external_body]
pub broadcast proof fn axiom_vec_ext_equal<T>(v1: Vec<T>, v2: Vec<T>)
    requires
        #[trigger] v1@.len() == #[trigger] v2@.len(),
        v1@ =~= v2@,
    ensures
        v1 =~= v2,
{ }

} //  verus!
