# verus-bigint

Formally verified arbitrary-size integer witness code extracted from VerusCAD.

## Contents

- `RuntimeBigNatWitness` exported from `src/runtime_bigint_witness/mod.rs`
- Runtime execution implementation in `src/runtime_bigint_witness/runtime_impl.rs`
- Verified/spec-heavy implementation in `src/runtime_bigint_witness/verified_impl.rs`
- Runtime tests in `src/runtime_bigint_witness/tests.rs`
- Verus refinement glue in `src/runtime_bigint_witness_refinement.rs` (compiled under `cfg(verus_keep_ghost)`)

This crate currently mirrors the bigint witness implementation from VerusCAD.

## Checking

- Run all checks (runtime tests + Verus verification when local Verus tools are available):
  - `./scripts/check.sh`
- Run runtime tests only:
  - `./scripts/check.sh --runtime-only`

## Roadmaps

- Zero-trust migration TODO: `docs/zero-trust-roadmap-todo.md`
