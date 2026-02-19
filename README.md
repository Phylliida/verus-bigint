# verus-bigint

Formally verified arbitrary-size integer witness code extracted from VerusCAD.

## Contents

- `RuntimeBigNatWitness` exported from `src/runtime_bigint_witness/mod.rs`
- Runtime execution implementation in `src/runtime_bigint_witness/runtime_impl.rs`
- Verified/spec-heavy implementation in `src/runtime_bigint_witness/verified_impl.rs`
- Runtime tests in `src/runtime_bigint_witness/tests.rs`
- Verus-path witness datatype declared directly in `src/runtime_bigint_witness/mod.rs` under `cfg(verus_keep_ghost)` (no external refinement bridge file)
- Trusted-surface notes in `docs/runtime-bigint-trust-assumptions.md`

This crate currently mirrors the bigint witness implementation from VerusCAD.

## Checking

- Run all checks (runtime tests + Verus verification when local Verus tools are available):
  - `./scripts/check.sh`
- Run runtime tests only:
  - `./scripts/check.sh --runtime-only`
- Run strict checks (fail if Verus tools are unavailable, and fail on `rug` in normal deps or non-test `src/` files):
  - `./scripts/check.sh --require-verus --forbid-rug-normal-deps --forbid-trusted-escapes`
- Smoke-check strict guard (default non-Verus Rust build must fail and `target-a-strict` still verifies under Verus):
  - `./scripts/check.sh --target-a-strict-smoke --forbid-rug-normal-deps --forbid-trusted-escapes`
- Run checks in offline mode where possible:
  - `./scripts/check.sh --offline`
- Run runtime tests directly (outside `check.sh`) in local non-Verus mode:
  - `cargo test --features runtime-compat`

## Strict Feature

- Feature `target-a-strict` is enabled by default.
- In non-Verus builds it emits a compile error unless `runtime-compat` is enabled
  explicitly for local runtime/testing workflows.
- In Verus builds (`cfg(verus_keep_ghost)`), verification proceeds normally.

## Roadmaps

- Zero-trust migration TODO: `docs/zero-trust-roadmap-todo.md`
