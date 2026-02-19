# Runtime BigInt Trust Assumptions

This document tracks what remains trusted for `RuntimeBigNatWitness`.

## Internal Alignment

- The verified implementation defines and maintains alignment internally via
  `RuntimeBigNatWitness::wf_spec()` in `src/runtime_bigint_witness/verified_impl.rs`.
- The runtime representation is canonical little-endian limbs (`Vec<u32>` with no
  trailing zero limbs), and both runtime/verified constructors normalize to that form.
- The refinement bridge in `src/runtime_bigint_witness_refinement.rs` is reduced to
  a minimal `external_type_specification` marker; trusted `View` mapping is not used.

## Irreducible Trusted Assumptions

- Rust compiler/toolchain correctness for executable code generation.
- Verus checker soundness and SMT solver soundness for accepted proofs.
- Build/test configuration integrity (the intended checks are actually run in CI/local gates).
- Correctness of the `external_type_specification` boundary for
  `RuntimeBigNatWitness` in `src/runtime_bigint_witness_refinement.rs`.
