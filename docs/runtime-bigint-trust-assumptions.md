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
- Verified loops now carry explicit `decreases` measures; non-test sources no
  longer rely on `#[verifier::exec_allows_no_decreases_clause]`.
- The feature `target-a-strict` is enabled by default and rejects non-Verus Rust
  builds at compile time unless `runtime-compat` is explicitly enabled for local
  runtime/testing workflows, and `runtime-compat` is rejected for non-Verus
  `--release` builds.
- `scripts/check.sh` supports `--min-verified N` so CI can fail fast if Verus
  verification coverage regresses below an expected floor.
- In strict-smoke mode (`--target-a-strict-smoke`), `scripts/check.sh` also
  enforces verified-count parity between baseline Verus verification and
  `--features target-a-strict`, preventing feature-gated proof-coverage drift.
- `scripts/check.sh` includes a source gate (`check_runtime_big_nat_field_privacy`)
  that fails if non-Verus `RuntimeBigNatWitness` field visibility regresses.
- `scripts/check.sh` also validates that `.github/workflows/check.yml` keeps the
  same pinned Verus Rust toolchain for both `rustup toolchain install` and
  `rustup default`, and that this pin matches `scripts/check.sh`.
- `scripts/check.sh` now also validates CI workflow step wiring for end-to-end
  strict checks: `Build Verus tools` must run first in `verus/source` (with
  `./tools/get-z3.sh` + `vargo build --release`), and `Run strict checks` must
  run in `verus-bigint` with `VERUS_ROOT` pointed at the checked-out Verus tree.
- The CI workflow preflight also enforces fail-fast behavior in those critical
  steps (`set -euo pipefail`, no `continue-on-error: true`, and no `|| true`
  failure masking in step commands).

## Irreducible Trusted Assumptions

- Rust compiler/toolchain correctness for executable code generation.
- Verus checker soundness and SMT solver soundness for accepted proofs.
- Build/test configuration integrity (the intended checks are actually run in CI/local gates).
