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
- Non-test source files are also kept `unsafe`-free; strict source gates fail
  if `unsafe` appears outside test code.
- The feature `target-a-strict` is enabled by default and rejects non-Verus Rust
  builds at compile time unless `runtime-compat` is explicitly enabled for local
  runtime/testing workflows, and `runtime-compat` is rejected for non-Verus
  `--release` builds.
- `scripts/check.sh` supports `--min-verified N` so CI can fail fast if Verus
  verification coverage regresses below an expected floor.
- `scripts/check.sh` also supports `--rug-oracle-tests`, and the CI-equivalent
  strict gate runs this to enforce differential testing against `rug` on each
  strict pipeline run.
- In strict-smoke mode (`--target-a-strict-smoke`), `scripts/check.sh` also
  enforces verified-count parity between baseline Verus verification and
  `--features target-a-strict`, preventing feature-gated proof-coverage drift.
- `scripts/check.sh` includes a source gate (`check_runtime_big_nat_field_privacy`)
  that fails if non-Verus `RuntimeBigNatWitness` field visibility regresses.
- `scripts/check.sh` also validates that `.github/workflows/check.yml` keeps the
  same pinned Verus Rust toolchain for both `rustup toolchain install` and
  `rustup default`, and that this pin matches `scripts/check.sh`.
- `scripts/check.sh` now also validates CI toolchain-install step wiring:
  `Install required Rust toolchain` must run before build/strict steps, be
  fail-fast, install the pinned toolchain with `--profile minimal` and required
  components (`rustfmt`, `rustc-dev`, `llvm-tools`), and set `rustup default`
  to the same toolchain pin.
- `scripts/check.sh` now also validates CI workflow checkout + step wiring for
  end-to-end strict checks: checkout steps must include `Checkout verus-bigint`
  (`path: verus-bigint`) and `Checkout Verus` (`repository: verus-lang/verus`,
  `path: verus`), both must pin `uses: actions/checkout@v4.2.2`, `Build Verus
  tools` must run first in `verus/source` (with `./tools/get-z3.sh` + `vargo
  build --release`), and `Run strict checks` must run in `verus-bigint` with
  `VERUS_ROOT` pointed at the checked-out Verus tree.
- The CI workflow also installs strict-check shell dependencies (`ripgrep`)
  before running `./scripts/check.sh`, and `scripts/check.sh` now fails early
  with an explicit error if `rg` is missing from `PATH`.
- The CI workflow preflight also enforces fail-fast behavior in those critical
  steps (`set -euo pipefail`, no step-level `if:` gating, no
  `continue-on-error: true`, and no `|| true` failure masking in step
  commands).
- `scripts/check.sh` also enforces CI workflow permission/token hardening:
  top-level `permissions` must stay least-privilege (`contents: read`, no
  `write`/`read-all`/`write-all` grants), and both checkout steps must keep
  `persist-credentials: false`.
- `scripts/check.sh` now also enforces CI trigger + job-execution wiring:
  strict checks must stay bound to both `pull_request` and `push` on `main`,
  trigger filters that can silently skip enforcement (`paths*`,
  `branches-ignore`) are rejected, and the `verify` job must remain
  unconditional (no job-level `if:` and no job-level `continue-on-error`)
  with an explicit `timeout-minutes`.
- `scripts/check.sh` also enforces pinned CI runner posture for the `verify`
  job: `runs-on` must remain `ubuntu-22.04`, with no dynamic runner
  expressions and no `self-hosted` labels.

## Irreducible Trusted Assumptions

- Rust compiler/toolchain correctness for executable code generation.
- Verus checker soundness and SMT solver soundness for accepted proofs.
- Build/test configuration integrity (the intended checks are actually run in CI/local gates).
