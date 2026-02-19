# Runtime BigInt Trust Assumptions

This document tracks what remains trusted for `RuntimeBigNatWitness`.

## Internal Alignment

- The verified implementation defines and maintains alignment internally via
  `RuntimeBigNatWitness::wf_spec()` in `src/runtime_bigint_witness/verified_impl.rs`.
- The runtime representation is canonical little-endian limbs (`Vec<u32>` with no
  trailing zero limbs), and both runtime/verified constructors normalize to that form.
- In non-Verus builds, `RuntimeBigNatWitness` stores limbs in a private field
  (`src/runtime_bigint_witness/mod.rs`), so external code cannot bypass constructor
  normalization by creating struct literals with non-canonical limbs.
- The `RuntimeBigNatWitness` proof-path datatype is declared directly in
  `src/runtime_bigint_witness/mod.rs` under `cfg(verus_keep_ghost)`, so no
  `external_type_specification` bridge is needed.
- Verified numeric narrowing now uses explicit bounds reasoning; there are no
  remaining `#[verifier::truncate]` casts in non-test sources.
- The feature `target-a-strict` is enabled by default and rejects non-Verus Rust
  builds at compile time unless `runtime-compat` is explicitly enabled for local
  runtime/testing workflows, and `runtime-compat` is rejected for non-Verus
  `--release` builds.
- `scripts/check.sh` supports `--min-verified N` so CI can fail fast if Verus
  verification coverage regresses below an expected floor.
- `scripts/check.sh` includes a source gate (`check_runtime_big_nat_field_privacy`)
  that fails if non-Verus `RuntimeBigNatWitness` field visibility regresses.

## Irreducible Trusted Assumptions

- Rust compiler/toolchain correctness for executable code generation.
- Verus checker soundness and SMT solver soundness for accepted proofs.
- Build/test configuration integrity (the intended checks are actually run in CI/local gates).
