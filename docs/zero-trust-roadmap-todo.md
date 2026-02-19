# Zero-Trust Roadmap TODO

## Goal

- [ ] Make `verus-bigint` zero-trust for production behavior:
- [x] No production reliance on `rug::Integer`
- [x] Exported runtime operations are implemented by verified limb algorithms
- [x] Verification and runtime behavior stay aligned

## Current Trust Boundaries

- [x] Replace `rug`-backed runtime path in `src/runtime_bigint_witness/runtime_impl.rs`
- [x] Remove `cfg` split that swaps between `rug` runtime and verified code in `src/runtime_bigint_witness/mod.rs`
- [x] Remove trusted refinement bridge (`external_type_specification`) by declaring `RuntimeBigNatWitness` in Verus under `cfg(verus_keep_ghost)`

## Target Mode Decision

- [x] Choose Target A or Target B
- [x] Target A (strict): require Verus build for production and keep non-verified backend out of production artifacts (`target-a-strict` strict-by-default + `runtime-compat` local-test escape hatch + non-Verus release guard)
- [x] Target B (compat): keep Rust-only build, but runtime is limb-based; keep `rug` only as optional test oracle

## Phase 1: Representation Unification

- [x] Use canonical limb-vector representation as the runtime source of truth
- [x] Remove production `Integer` storage field
- [x] Keep canonical limb normalization invariant across constructors and ops

## Phase 2: Runtime API Alignment

- [x] Route exported operations through limb algorithms:
- [x] `zero`, `from_u32`, `from_u64`, `from_two_limbs`
- [x] `add_limbwise_small_total`, `mul_limbwise_small_total`
- [x] `cmp_limbwise_small_total`, `sub_limbwise_small_total`, `copy_small_total`
- [x] Ensure public API semantics match spec/view semantics

## Phase 3: Dependency De-Trusting

- [x] Move `rug` from `[dependencies]` to optional `[dev-dependencies]` (oracle only)
- [x] Remove/replace `value() -> &Integer` from public API
- [x] Ensure normal (non-test) builds do not pull `rug`

## Phase 4: Verification and Differential Testing

- [x] Keep/expand runtime tests for core operations and edge cases
- [x] Add differential/property tests comparing limb runtime vs `rug` oracle (when test feature is enabled)
- [x] Add regression tests for carries, borrows, zero normalization, and multi-limb boundaries

## Phase 5: CI and Check Gates

- [x] Keep `./scripts/check.sh` as the main local gate
- [x] Make CI fail if Verus verification fails
- [x] Make CI fail if `rug` appears in non-test dependency graph
- [x] Add offline-friendly check mode where practical
- [x] Harden runtime/verified API drift gate to compare normalized public method signatures (args + return types), not just method names

## Phase 6: Trusted Surface Reduction

- [x] Eliminate refinement-bridge reliance on `external_type_specification`
- [x] Prefer internal, explicit view/model alignment where possible
- [x] Remove narrowing-cast truncation annotations (`#[verifier::truncate]`) from non-test sources
- [x] Add a source-tree gate that rejects trusted proof escapes (`admit`, `assume`, and `#[verifier::external*]`) in non-test files
- [x] Document any irreducible trust assumptions

## Exit Criteria

- [x] Production path uses only limb-based verified implementation
- [x] `rug` is test-only (or fully removed)
- [x] All exported arithmetic ops are covered by Verus proofs and runtime tests
- [ ] `./scripts/check.sh` passes end-to-end in CI

## Burndown Log

### 2026-02-19

- Completed: Replaced non-Verus `RuntimeBigNatWitness` runtime storage with canonical `Vec<u32>` limbs in `src/runtime_bigint_witness/mod.rs` and removed all production `rug::Integer` usage from `src/runtime_bigint_witness/runtime_impl.rs`.
- Completed: Added limb-based runtime implementations for `add_limbwise_small_total`, `mul_limbwise_small_total`, `cmp_limbwise_small_total`, `sub_limbwise_small_total`, and wired `add`/`mul` through those limb algorithms.
- Completed: Replaced public runtime inspection API `value() -> &Integer` with `limbs_le() -> &[u32]`, and updated tests accordingly.
- Completed: Moved `rug` from `[dependencies]` to `[dev-dependencies]` in `Cargo.toml`.
- Completed: Expanded runtime tests in `src/runtime_bigint_witness/tests.rs` to include carry/borrow/multi-limb boundary and zero-canonicalization regression coverage.
- Completed: Added a gated oracle test feature `rug-oracle` in `Cargo.toml` and implemented differential/property tests in `src/runtime_bigint_witness/tests.rs` that compare `add`, `mul`, `cmp`, and `sub` against `rug::Integer` over fixed vectors and deterministic pseudorandom multi-limb inputs.
- Completed verification attempt: `./scripts/check.sh --runtime-only` passes (4/4 tests).
- Completed verification attempt: `cargo test --manifest-path Cargo.toml --features rug-oracle` passes (6/6 tests, including oracle differential tests).
- Completed dependency check: `cargo tree -e normal --manifest-path Cargo.toml` confirms no `rug` in normal dependency graph.
- Failed attempt (fixed): initial `cargo test --manifest-path Cargo.toml --features rug-oracle` run failed due to `rug` incomplete arithmetic types (`AddIncomplete` / `MulIncomplete` / `SubIncomplete`) in oracle expectations; resolved by materializing expected values as `Integer`.
- Failed/blocked attempt: `./scripts/check.sh` cannot run Verus verify path in this sandbox because `nix-shell` cannot connect to `/nix/var/nix/daemon-socket/socket` (`Operation not permitted`).
- Failed/blocked attempt: direct `cargo verus verify --manifest-path Cargo.toml -p verus-bigint -- --triggers-mode silent` fails in this environment because `rustup` is not installed in PATH (`verus: rustup not found`).
- Failed/blocked attempt: `cargo fmt --check` fails because `cargo fmt` is unavailable in this environment.
- Completed: Removed the `cfg` module switch in `src/runtime_bigint_witness/mod.rs` by making `runtime_impl`/`verified_impl` modules unconditional and moving the build split to file-level module attributes in `src/runtime_bigint_witness/runtime_impl.rs` and `src/runtime_bigint_witness/verified_impl.rs`.
- Completed: Added `docs/runtime-bigint-trust-assumptions.md` to explicitly document remaining trusted boundaries and irreducible assumptions.
- Completed verification attempt: `./scripts/check.sh` passes end-to-end in this environment (runtime tests pass and Verus reports `85 verified, 0 errors`).
- Completed verification attempt: `cargo test --manifest-path Cargo.toml` passes (4/4 tests).
- Completed dependency check: `cargo tree -e normal --manifest-path Cargo.toml` still shows no `rug` in the normal dependency graph after the module-structure refactor.
- Failed attempt (rolled back): removing `src/runtime_bigint_witness_refinement.rs` and its `lib.rs` wiring caused Verus to reject `RuntimeBigNatWitness` as an ignored external type; restored the refinement module to keep verification passing.
- Completed: Added verified-path API methods `add`, `mul`, `is_zero`, and `limbs_le` in `src/runtime_bigint_witness/verified_impl.rs`, delegating `add`/`mul` to the proven limbwise totals and proving model-level semantic alignment (`out.model@`).
- Completed verification attempt: `./scripts/check.sh` passes end-to-end after API alignment updates (runtime tests pass and Verus reports `89 verified, 0 errors`).
- Completed verification attempt: `cargo test --manifest-path Cargo.toml --features rug-oracle` passes (6/6 tests) after the verified API-alignment additions.
- Completed: Extended `scripts/check.sh` with `--require-verus`, `--forbid-rug-normal-deps`, and `--offline` flags to support strict CI gating and offline-friendly checks.
- Completed: Added `.github/workflows/check.yml` to build Verus in CI and run `./scripts/check.sh --require-verus --forbid-rug-normal-deps`.
- Completed verification attempt: `./scripts/check.sh --runtime-only --forbid-rug-normal-deps` passes (4/4 tests; dependency graph gate passes).
- Completed verification attempt: `./scripts/check.sh --require-verus --forbid-rug-normal-deps` passes (4/4 tests; Verus reports `89 verified, 0 errors`).
- Completed verification attempt: `./scripts/check.sh --runtime-only --offline --forbid-rug-normal-deps` passes (4/4 tests in offline mode; dependency graph gate passes).
- Completed verification attempt: `./scripts/check.sh --require-verus --forbid-rug-normal-deps --offline` passes (4/4 tests in offline mode; Verus reports `89 verified, 0 errors`).
- Completed verification attempt: `cargo test --manifest-path Cargo.toml --features rug-oracle` passes (6/6 tests) after the Phase 5 gate changes.
- Failed attempt (intentional guardrail test): `VERUS_ROOT=/tmp/does-not-exist ./scripts/check.sh --require-verus --forbid-rug-normal-deps` fails with missing `cargo-verus`, confirming strict-mode failure behavior.
- Failed/blocked attempt: the new GitHub Actions workflow cannot be executed inside this sandbox, so CI execution results are not directly validated here.
- Completed: Reduced trusted refinement glue in `src/runtime_bigint_witness_refinement.rs` by removing the unused trusted `View` implementation and keeping only the minimal `external_type_specification` bridge required for Verus to reason about `RuntimeBigNatWitness`.
- Completed cleanup: Removed unreferenced duplicate proof files under `src/runtime_bigint_witness/verified_sections/` to reduce dead/unverified surface area.
- Completed verification attempt: `./scripts/check.sh` passes after trust-bridge minimization and cleanup (runtime tests 4/4; Verus reports `89 verified, 0 errors`).
- Completed verification attempt: `cargo test --manifest-path Cargo.toml --features rug-oracle` passes after trust-bridge minimization and cleanup (6/6 tests).
- Completed: Added runtime/verified API drift gate to `scripts/check.sh` that compares public `RuntimeBigNatWitness` methods in `src/runtime_bigint_witness/runtime_impl.rs` and `src/runtime_bigint_witness/verified_impl.rs`, failing when the sets diverge.
- Completed verification attempt: `./scripts/check.sh --forbid-rug-normal-deps` passes after adding the API-drift gate (runtime tests 4/4, normal dependency graph excludes `rug`, Verus reports `89 verified, 0 errors`).
- Completed verification attempt: `cargo test --manifest-path Cargo.toml --features rug-oracle` still passes after the API-drift gate update (6/6 tests).
- Completed decision: Selected Target B (compat mode) for now, keeping the Rust-only limb runtime path plus Verus proof path, and enforcing alignment with proofs + oracle tests + API-drift gate.
- Failed attempt (rolled back): forcing a single runtime backend by compiling `verified_impl` in normal Rust builds failed (`#[verifier::truncate]` expression attributes and ghost-only struct field usage are not accepted by stable `cargo test` in this setup).
- Failed attempt (rolled back): making `RuntimeBigNatWitness` fields private or `pub(crate)` to harden invariant enforcement broke Verus refinement (`external_type_specification: private fields not supported for transparent datatypes`) in `src/runtime_bigint_witness_refinement.rs`.
- Completed: Hardened `scripts/check.sh` so `--forbid-rug-normal-deps` now also fails when non-test files under `src/` reference `rug` (not just dependency-graph checks), closing the production-path guardrail for limb-only runtime code.
- Completed verification attempt: `./scripts/check.sh --forbid-rug-normal-deps` passes after the source-tree `rug` guard was added (runtime tests 4/4; dependency and source-tree gates pass; Verus reports `89 verified, 0 errors`).
- Completed verification attempt: `./scripts/check.sh --require-verus --forbid-rug-normal-deps` passes after the source-tree `rug` guard was added (runtime tests 4/4; strict Verus gate passes; Verus reports `89 verified, 0 errors`).
- Completed verification attempt: `cargo test --manifest-path Cargo.toml --features rug-oracle` still passes after the strict-gate hardening (6/6 tests).
- Completed: Refactored `RuntimeBigNatWitness` declaration in `src/runtime_bigint_witness/mod.rs` so the Verus build (`cfg(verus_keep_ghost)`) declares the datatype inside `verus!`, while the Rust runtime build keeps the plain struct.
- Completed: Removed `src/runtime_bigint_witness_refinement.rs` and its `lib.rs` wiring; Verus no longer needs an `external_type_specification` bridge for `RuntimeBigNatWitness`.
- Completed verification attempt: `./scripts/check.sh --require-verus --forbid-rug-normal-deps` passes after refinement-bridge removal (runtime tests 4/4; Verus reports `89 verified, 0 errors`).
- Completed verification attempt: `cargo test --manifest-path Cargo.toml --features rug-oracle` passes after refinement-bridge removal (6/6 tests).
- Failed/blocked attempt: tried to run the GitHub Actions workflow directly from this sandbox, but both `act` and `gh` are unavailable in PATH, so CI execution still cannot be validated from this environment.
- Completed: Hardened `scripts/check.sh` API-drift gating by normalizing and comparing runtime/verified public method signatures (`name(args)->ret`) instead of only method names; Verus named returns like `(out: T)` are now normalized to `T` for comparison.
- Completed verification attempt: `./scripts/check.sh --require-verus --forbid-rug-normal-deps` passes after the signature-level API parity gate change (runtime tests 4/4; Verus reports `89 verified, 0 errors`).
- Completed verification attempt: `cargo test --manifest-path Cargo.toml --features rug-oracle` passes after the signature-level API parity gate change (6/6 tests).
- Failed attempt (fixed): the first signature extractor used `rg` replacement fields with literal `\t`, which caused false API-mismatch reports; fixed by switching to an explicit `|` delimiter during parsing and normalizing signatures before comparison.
- Completed: Added `--forbid-trusted-escapes` to `scripts/check.sh`, with a non-test `src/` source-tree gate that fails on `admit(...)`, `assume(...)`, and `#[verifier::external*]` attribute usage.
- Completed: Updated strict-check usage in `.github/workflows/check.yml` and `README.md` to include `--forbid-trusted-escapes`.
- Completed verification attempt: `./scripts/check.sh --runtime-only --forbid-rug-normal-deps --forbid-trusted-escapes` passes (4/4 runtime tests; rug and trusted-escape source-tree gates pass).
- Completed verification attempt: `./scripts/check.sh --require-verus --forbid-rug-normal-deps --forbid-trusted-escapes` passes (4/4 runtime tests; Verus reports `89 verified, 0 errors`; rug and trusted-escape source-tree gates pass).
- Completed verification attempt: `cargo test --manifest-path Cargo.toml --features rug-oracle` passes (6/6 tests) after trusted-escape gate hardening.
- Completed: Added opt-in feature `target-a-strict` in `Cargo.toml` and compile-time guard in `src/runtime_bigint_witness/mod.rs` so non-Verus builds fail fast when strict mode is requested.
- Completed: Extended `scripts/check.sh` with `--target-a-strict-smoke` to enforce Target A transition behavior: non-Verus `cargo test --features target-a-strict --no-run` must fail with the strict guard, and Verus verification with `--features target-a-strict` must pass.
- Completed: Updated `.github/workflows/check.yml` and `README.md` to run/document the new strict-mode smoke gate.
- Completed verification attempt: `./scripts/check.sh --require-verus --forbid-rug-normal-deps --forbid-trusted-escapes --target-a-strict-smoke` passes (runtime tests 4/4; baseline Verus verify `89 verified, 0 errors`; strict-mode non-Verus compile fails as expected; strict-mode Verus verify `89 verified, 0 errors`).
- Completed verification attempt: `cargo test --manifest-path Cargo.toml --features rug-oracle` passes (6/6 tests) after strict-transition guard additions.
- Failed attempt (intentional guardrail test): `./scripts/check.sh --runtime-only --target-a-strict-smoke` fails fast with argument conflict (`--runtime-only` cannot be combined with the strict-mode smoke check).
- Completed: Switched `Cargo.toml` to strict-by-default mode by enabling `target-a-strict` in default features and adding explicit `runtime-compat` for local non-Verus runtime/testing workflows; `rug-oracle` now implies `runtime-compat`.
- Completed: Updated the non-Verus strict guard in `src/runtime_bigint_witness/mod.rs` so strict builds fail unless `runtime-compat` is explicitly enabled.
- Completed: Updated `scripts/check.sh` to run runtime tests under `--features runtime-compat` while preserving strict smoke behavior (default non-Verus cargo build must fail, Verus verification must pass).
- Completed verification attempt: `./scripts/check.sh --forbid-rug-normal-deps --forbid-trusted-escapes` passes after strict-default transition (runtime tests 4/4 under `runtime-compat`; dependency and trusted-escape gates pass; Verus reports `89 verified, 0 errors`).
- Completed verification attempt: `./scripts/check.sh --require-verus --forbid-rug-normal-deps --forbid-trusted-escapes --target-a-strict-smoke` passes after strict-default transition (runtime tests 4/4 under `runtime-compat`; baseline and strict-feature Verus both report `89 verified, 0 errors`).
- Completed verification attempt: `cargo test --manifest-path Cargo.toml --features rug-oracle` passes after strict-default transition (6/6 tests).
- Failed attempt (intentional guardrail test): `cargo test --manifest-path Cargo.toml --no-run` fails in non-Verus mode with the expected strict compile guard (`feature 'target-a-strict' requires a Verus build ... enable feature 'runtime-compat' ...`).
- Completed: Removed all remaining `#[verifier::truncate]` narrowing-cast annotations from `src/runtime_bigint_witness/verified_impl.rs` by relying on explicit range reasoning before `u64 -> u32` casts.
- Completed: Added a non-Verus production guard in `src/runtime_bigint_witness/mod.rs` so `--release --features runtime-compat` now fails at compile time, keeping `runtime-compat` scoped to debug/test workflows.
- Completed: Extended `scripts/check.sh --target-a-strict-smoke` to assert the new release guard (`cargo build --release --features runtime-compat` must fail with the expected compile-error text).
- Completed: Hardened `scripts/check.sh --forbid-trusted-escapes` so non-test `src/` files are now also rejected if they reintroduce `#[verifier::truncate]`.
- Completed: Updated strict-mode documentation in `README.md` and trust-boundary notes in `docs/runtime-bigint-trust-assumptions.md` to reflect the new production guard and truncate-elimination status.
- Completed verification attempt: `./scripts/check.sh --require-verus --forbid-rug-normal-deps --forbid-trusted-escapes --target-a-strict-smoke` passes after these changes (runtime tests 4/4; baseline + strict-feature Verus `89 verified, 0 errors`; strict non-Verus and `runtime-compat` release guards both fail as expected).
- Completed verification attempt: `cargo test --manifest-path Cargo.toml --features rug-oracle` passes after these changes (6/6 tests).
- Completed: Closed the `Target A (strict)` roadmap item after re-validating that strict mode is default, non-Verus default builds are rejected, and `runtime-compat` remains debug/test-only for local workflows.
- Completed verification attempt: `./scripts/check.sh --require-verus --forbid-rug-normal-deps --forbid-trusted-escapes --target-a-strict-smoke` passes again (runtime tests 4/4; rug/trusted-escape gates pass; baseline and strict-feature Verus each report `89 verified, 0 errors`; strict non-Verus and `runtime-compat --release` guards fail as expected).
- Completed verification attempt: `cargo test --manifest-path Cargo.toml --features rug-oracle` passes after the Target A closeout pass (6/6 tests).
- Completed investigation: `cargo test --manifest-path Cargo.toml --features runtime-compat --no-run -vv` confirms Cargo builds both a normal lib target and a `--test` target, so a pure `cfg(test)` compile-gate for `runtime-compat` would currently break local test workflows.
- Completed: Added `--min-verified N` to `scripts/check.sh` so Verus runs fail fast when the reported verified-item count regresses below a configured floor.
- Completed: Updated `.github/workflows/check.yml` strict gate and `README.md` usage examples to run `./scripts/check.sh ... --min-verified 89`; documented the new guard in `docs/runtime-bigint-trust-assumptions.md`.
- Completed verification attempt: `./scripts/check.sh --require-verus --forbid-rug-normal-deps --forbid-trusted-escapes --target-a-strict-smoke --min-verified 89` passes (runtime tests 4/4; baseline and strict-feature Verus both report `89 verified, 0 errors`; verified-count gate passes on both Verus runs).
- Failed attempt (intentional guardrail test): `./scripts/check.sh --require-verus --forbid-rug-normal-deps --forbid-trusted-escapes --min-verified 90` fails with the expected regression message (`expected at least 90, got 89`), confirming the new count floor enforcement.
- Completed verification attempt: `cargo test --manifest-path Cargo.toml --features rug-oracle` passes after the verified-count gate additions (6/6 tests).
