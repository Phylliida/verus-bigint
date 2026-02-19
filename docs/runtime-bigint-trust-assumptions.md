# Runtime BigInt Trust Assumptions

This document tracks what remains trusted for `RuntimeBigNatWitness`.

## Internal Alignment

- The verified implementation defines and maintains alignment internally via
  `RuntimeBigNatWitness::wf_spec()` in `src/runtime_bigint_witness/verified_impl.rs`.
- The runtime representation is canonical little-endian limbs (`Vec<u32>` with no
  trailing zero limbs), and both runtime/verified constructors normalize to that form.
- The `RuntimeBigNatWitness` proof-path datatype is declared directly in
  `src/runtime_bigint_witness/mod.rs` under `cfg(verus_keep_ghost)`, so no
  `external_type_specification` bridge is needed.

## Irreducible Trusted Assumptions

- Rust compiler/toolchain correctness for executable code generation.
- Verus checker soundness and SMT solver soundness for accepted proofs.
- Build/test configuration integrity (the intended checks are actually run in CI/local gates).
