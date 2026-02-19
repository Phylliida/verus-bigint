# verus-bigint

Formally verified arbitrary-size integer witness code extracted from VerusCAD.

## Contents

- `RuntimeBigNatWitness` exported from `src/runtime_bigint_witness/mod.rs`
- In non-Verus builds, `RuntimeBigNatWitness` runtime storage is encapsulated (private `limbs_le` field); use constructors + `limbs_le()` accessor
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
- Run strict checks (fail if Verus tools are unavailable, fail on `rug` or trusted-escape patterns in non-test `src/` files including `#[verifier::exec_allows_no_decreases_clause]`, run `rug` differential tests, and gate against verification-count regressions):
  - `./scripts/check.sh --require-verus --forbid-rug-normal-deps --forbid-trusted-escapes --rug-oracle-tests --min-verified 89`
- Smoke-check strict guards (default non-Verus Rust build must fail, non-Verus `--release --features runtime-compat` must fail, and `target-a-strict` must verify under Verus with the same verified-item count as baseline):
  - `./scripts/check.sh --target-a-strict-smoke --forbid-rug-normal-deps --forbid-trusted-escapes`
- Run the CI-equivalent strict gate locally (kept aligned with `.github/workflows/check.yml` by `check.sh`, including strict command flags and Verus toolchain pin):
  - `./scripts/check.sh --require-verus --forbid-rug-normal-deps --forbid-trusted-escapes --rug-oracle-tests --target-a-strict-smoke --min-verified 89`
  - It also preflights CI trigger coverage so strict checks remain wired to both `pull_request` and `push` on `main`, and rejects trigger filters (`paths*`, `branches-ignore`) that could silently skip enforcement.
  - It also preflights the CI `verify` job execution contract (no job-level `if:` gating and explicit `timeout-minutes`).
  - This also preflights workflow checkout + structure wiring so CI keeps the required end-to-end setup (`Checkout verus-bigint` path, `Checkout Verus` repository/path, `Build Verus tools` before strict checks, expected working directories, and `VERUS_ROOT` env wiring) and enforces fail-fast step behavior (`set -euo pipefail`, no `continue-on-error: true`, no `|| true` masking).
  - It also preflights CI workflow permission hardening (`permissions: contents: read`) and checkout credential hygiene (`persist-credentials: false` on both checkout steps).
- Run checks in offline mode where possible:
  - `./scripts/check.sh --offline`
- Run runtime tests directly (outside `check.sh`) in local non-Verus mode:
  - `cargo test --features runtime-compat`

## Strict Feature

- Feature `target-a-strict` is enabled by default.
- In non-Verus builds it emits a compile error unless `runtime-compat` is enabled
  explicitly for local runtime/testing workflows.
- In non-Verus `--release` builds, `runtime-compat` is also rejected to keep the
  non-verified backend out of production artifacts.
- In Verus builds (`cfg(verus_keep_ghost)`), verification proceeds normally.

## Roadmaps

- Zero-trust migration TODO: `docs/zero-trust-roadmap-todo.md`
