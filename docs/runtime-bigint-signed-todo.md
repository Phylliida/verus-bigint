# Runtime BigInt Signed TODO

## Goal

- [x] Add a signed bigint witness type that is fully verified and keeps existing unsigned behavior intact.
- [x] Keep operator behavior non-consuming (borrowed operators only).

## Scope and Approach

- [x] Keep `RuntimeBigNatWitness` as the unsigned core.
- [x] Add a new signed wrapper type (for example `RuntimeBigIntWitness`) instead of changing nat internals in place.
- [x] Reuse existing verified nat algorithms wherever possible for magnitude arithmetic.

## Blocking Semantics Decisions

- [x] Choose division semantics:
- [x] Truncating division/remainder (Rust-like), or
- [x] Euclidean division/remainder (`0 <= r < |d|` for `d != 0`) considered and not selected for this implementation.
- [x] Choose total behavior for divisor zero (`a / 0`, `a % 0`) and document it.
- [x] Confirm subtraction semantics are true signed subtraction (no floor-to-zero).
- [x] Confirm canonical zero policy (`-0` forbidden).

## Phase 1: Type and Canonical Invariants

- [x] Add signed witness type declaration in `src/runtime_bigint_witness/mod.rs`.
- [x] Add representation fields (sign + magnitude).
- [x] Add ghost model as `int`.
- [x] Define canonical sign invariant (zero must be non-negative).
- [x] Define and prove signed `wf_spec`.

## Phase 2: Signed Core Spec Helpers

- [x] Add spec helpers for sign, abs, and normalization.
- [x] Add constructor helper that canonicalizes sign/magnitude.
- [x] Add bridge lemmas between nat magnitude and int model.
- [x] Add basic sign lemmas (`abs >= 0`, sign cases, zero normalization).

## Phase 3: Public API Surface

- [x] Add constructors: `zero`, `from_i32`, `from_i64`, and conversion from unsigned witness.
- [x] Add accessors/helpers: `is_zero`, `is_negative`, `abs`, `signum`.
- [x] Add compare operation over signed model.
- [x] Add unary negation API with negative-zero normalization.

## Phase 4: Arithmetic Implementation

- [x] Implement signed add via sign-case split + magnitude add/sub/compare.
- [x] Implement signed sub (directly or as add with negation).
- [x] Implement signed mul via magnitude mul + sign xor.
- [x] Implement signed div/rem with chosen semantics and zero-divisor policy.
- [x] Add optional `div_rem` convenience with coupled contracts.

## Phase 5: Proof Contracts and Lemmas

- [x] Prove `add/sub/mul/div/rem` results match signed `model@`.
- [x] Prove output canonicalization (no negative zero) for every operation.
- [x] Prove signed compare correctness (`-1/0/1` relation to model ordering).
- [x] Add algebra lemmas as appropriate:
- [x] add/mul commutativity and associativity,
- [x] distributivity,
- [x] monotonicity/cancellation with sign preconditions.
- [x] Add division/remainder recomposition and bounds lemmas for chosen semantics.

## Phase 6: Operators and Trait Specs

- [x] Add borrowed operator impls only:
- [x] `&A + &B`, `&A - &B`, `&A * &B`, `&A / &B`, `&A % &B`, and unary `-&A`.
- [x] Add matching `vstd::std_specs::ops::*SpecImpl` instances for the same operand shapes.
- [x] Keep owned operator forms intentionally unsupported.

## Phase 7: Integration and Documentation

- [x] Wire module exports so unsigned and signed witness types coexist cleanly.
- [x] Add usage examples in `README.md` for signed arithmetic and edge cases.
- [x] Document exact division/remainder and zero-divisor semantics.
- [x] Add/refresh trust-surface notes if signed-specific assumptions appear.
- [x] Add signed proof-parity matrix and signed-only lemma backlog:
      `docs/runtime-bigint-signed-proof-parity.md`.

## Phase 8: Validation and Gates

- [x] Add focused verification tests/examples for sign edge cases:
- [x] `-a + a = 0`,
- [x] `a - a = 0`,
- [x] mixed-sign arithmetic,
- [x] zero-sign normalization,
- [x] division/remainder sign edge cases.
- [x] Run strict checks and keep them green (`./scripts/check.sh ...`).
- [x] Update `--min-verified` threshold once signed proofs land.

## Nice-to-Have Follow-ons

- [x] Checked conversions to/from primitive signed/unsigned ints.
- [x] Parsing/formatting helpers if needed by downstream code.
- [x] Additional theorem wrappers mirroring unsigned operation-level proof wrappers.

## Exit Criteria

- [x] Signed type is production-usable with verified semantics.
- [x] All exported signed arithmetic is proven against signed model semantics.
- [x] No owned consuming operator overloads for signed type.
- [x] Documentation reflects semantics precisely enough to avoid ambiguity.
