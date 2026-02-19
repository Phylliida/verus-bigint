# Zero-Trust Roadmap TODO

## Goal

- [ ] Make `verus-bigint` zero-trust for production behavior:
- [x] No production reliance on `rug::Integer`
- [ ] Exported runtime operations are implemented by verified limb algorithms
- [ ] Verification and runtime behavior stay aligned

## Current Trust Boundaries

- [x] Replace `rug`-backed runtime path in `src/runtime_bigint_witness/runtime_impl.rs`
- [ ] Remove `cfg` split that swaps between `rug` runtime and verified code in `src/runtime_bigint_witness/mod.rs`
- [ ] Minimize trusted glue in `src/runtime_bigint_witness_refinement.rs` (`external_type_specification`)

## Target Mode Decision

- [ ] Choose Target A or Target B
- [ ] Target A (strict): require Verus build for production, remove non-verified backend
- [ ] Target B (compat): keep Rust-only build, but runtime is limb-based; keep `rug` only as optional test oracle

## Phase 1: Representation Unification

- [x] Use canonical limb-vector representation as the runtime source of truth
- [x] Remove production `Integer` storage field
- [x] Keep canonical limb normalization invariant across constructors and ops

## Phase 2: Runtime API Alignment

- [ ] Route exported operations through limb algorithms:
- [x] `zero`, `from_u32`, `from_u64`, `from_two_limbs`
- [x] `add_limbwise_small_total`, `mul_limbwise_small_total`
- [x] `cmp_limbwise_small_total`, `sub_limbwise_small_total`, `copy_small_total`
- [ ] Ensure public API semantics match spec/view semantics

## Phase 3: Dependency De-Trusting

- [x] Move `rug` from `[dependencies]` to optional `[dev-dependencies]` (oracle only)
- [x] Remove/replace `value() -> &Integer` from public API
- [x] Ensure normal (non-test) builds do not pull `rug`

## Phase 4: Verification and Differential Testing

- [x] Keep/expand runtime tests for core operations and edge cases
- [x] Add differential/property tests comparing limb runtime vs `rug` oracle (when test feature is enabled)
- [x] Add regression tests for carries, borrows, zero normalization, and multi-limb boundaries

## Phase 5: CI and Check Gates

- [ ] Keep `./scripts/check.sh` as the main local gate
- [ ] Make CI fail if Verus verification fails
- [ ] Make CI fail if `rug` appears in non-test dependency graph
- [ ] Add offline-friendly check mode where practical

## Phase 6: Trusted Surface Reduction

- [ ] Review/refactor refinement glue to reduce reliance on `external_type_specification`
- [ ] Prefer internal, explicit view/model alignment where possible
- [ ] Document any irreducible trust assumptions

## Exit Criteria

- [ ] Production path uses only limb-based verified implementation
- [ ] `rug` is test-only (or fully removed)
- [ ] All exported arithmetic ops are covered by Verus proofs and runtime tests
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
