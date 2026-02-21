# Runtime BigInt Signed Proof Parity Matrix

## Goal

Track which unsigned (`RuntimeBigNatWitness`) proof wrappers should be mirrored
for signed (`RuntimeBigIntWitness`), and which should stay nat-only.

This is not a 1:1 naming exercise. The target is useful signed proof surface
with correct truncating semantics.

## Already Covered In Signed

These are already proved in `src/runtime_bigint_witness/signed_verified_impl.rs`:

- Core semantics: `cmp`, `add`, `sub`, `mul`, `div`, `rem`, `div_rem` are tied
  to signed model specs.
- Canonicalization: no negative zero (`wf_spec` + constructor normalization).
- Algebra wrappers: commutativity/associativity/distributivity, monotonicity
  with sign preconditions, cancellation with positive multipliers.
- Signed edge wrappers: `-a + a = 0`, `a - a = 0`, zero-sign normalization,
  mixed-sign arithmetic, and signed div/rem sign/bounds behavior.

## Worth Re-Proving From Nat Surface

These are worth adding as signed wrappers even though core methods already prove
the underlying facts.

| Priority | Status | Nat precedent | Recommended signed lemma shape | Why it is worth adding |
|---|---|---|---|---|
| P1 | Done | `lemma_cmp_le_zero_iff_le_ops`, `lemma_cmp_lt_zero_iff_lt_ops`, `lemma_cmp_eq_zero_iff_eq_ops` | Added signed versions: `lemma_cmp_le_zero_iff_le_ops`, `lemma_cmp_lt_zero_iff_lt_ops`, `lemma_cmp_eq_zero_iff_eq_ops` | Gives API parity for compare reasoning without reopening `cmp` internals |
| P1 | Done | `lemma_model_sub_add_inverse_ge_ops` | Added `lemma_model_sub_add_inverse_ops(a,b)`: `(a-b)+b == a` (no precondition) | Stronger in signed because subtraction is exact (no floor-to-zero behavior) |
| P1 | Done | `lemma_model_add_sub_round_trip_ops` | Added signed round-trip wrapper `lemma_model_add_sub_round_trip_ops` | Common simplification theorem for arithmetic proof scripts |
| P1 | Done | `lemma_model_sub_zero_iff_le_ops` | Added signed analog `lemma_model_sub_zero_iff_eq_ops` with `a-b == 0 <==> a == b` | Nat statement is trunc-sub specific; equality form is the right signed invariant |
| P1 | Done | `lemma_model_div_rem_recompose_pos_ops` | Added `lemma_model_div_rem_recompose_nonzero_ops` for `d != 0` | Frequently needed as one reusable theorem rather than method contract unfolding |
| P1 | Done | `lemma_model_mul_div_rem_cancel_pos_ops` | Added `lemma_model_mul_div_rem_cancel_nonzero_ops` for `d != 0` | Useful cancellation fact over trunc semantics |
| P2 | Done | `lemma_model_div_monotonic_pos_ops` | Added `lemma_model_div_monotonic_pos_ops` with signed trunc semantics (`d > 0`) | Still true and useful for ordered reasoning with signed inputs |
| P2 | Done | `lemma_cmp_pos_implies_sub_pos_ops`, `lemma_cmp_eq_implies_bi_sub_zero_ops`, `lemma_cmp_neg_implies_asym_sub_ops` | Added signed versions with exact subtraction models | Useful directional reasoning after compare branches |
| P2 | Done | `lemma_model_rem_upper_bound_pos_ops` | Added one-sided signed remainder bounds: `lemma_model_rem_bounds_nonneg_dividend_pos_divisor_ops`, `lemma_model_rem_bounds_nonpos_dividend_pos_divisor_ops` | Bridges absolute bound into branch-friendly inequalities |
| P3 | Done | `lemma_model_len_window_nonzero_ops`, `lemma_model_zero_implies_len_zero_ops`, `*_len_bound_*` | Added signed shape/length wrappers: `lemma_model_len_window_nonzero_ops`, `lemma_model_zero_implies_len_zero_ops`, `lemma_abs_add_len_bound_ops`, `lemma_abs_mul_len_bound_ops`, `lemma_abs_div_len_bound_nonzero_ops`, `lemma_abs_rem_len_bound_nonzero_ops` | Optional; needed mainly for representation/cost arguments |

## Signed-Only Proofs Worth Adding

Unsigned did not need these because sign is absent.

| Priority | Status | Signed-only target | Added signed wrapper(s) |
|---|---|---|---|
| P1 | Done | `signum(a - b) == cmp(a,b)` | `lemma_signum_sub_eq_cmp_ops` |
| P1 | Done | Divisor-sign flips: `div(a,-d) == -div(a,d)`, `rem(a,-d) == rem(a,d)` (`d!=0`) | `lemma_model_div_divisor_sign_flip_ops`, `lemma_model_rem_divisor_sign_flip_ops` |
| P1 | Done | Negated-dividend laws: `div(-a,d) == -div(a,d)`, `rem(-a,d) == -rem(a,d)` (`d!=0`) | `lemma_model_div_neg_dividend_ops`, `lemma_model_rem_neg_dividend_ops` |
| P1 | Done | Unit divisor laws: `a/1=a`, `a/(-1)=-a`, `a%1=0`, `a%(-1)=0` | `lemma_model_unit_div_rem_ops` |
| P2 | Done | Explicit sign-of-result wrappers for `mul`, `div`, `rem` | `lemma_model_mul_sign_nonzero_ops`, `lemma_model_div_sign_nonzero_quotient_ops`, `lemma_model_rem_sign_nonzero_ops` |
| P2 | Done | `abs` interactions: `abs(-a)=abs(a)`, `abs(a*b)=abs(a)*abs(b)`, `abs(rem(a,d)) < abs(d)` | `lemma_abs_neg_eq_abs_ops`, `lemma_abs_mul_distribution_ops`, `lemma_abs_rem_bound_nonzero_ops` |

## Nat Lemmas That Should Not Be Ported Unchanged

These nat statements are either false under truncating signed semantics or are
the wrong abstraction for signed.

- `lemma_model_div_shift_by_multiple_pos` / `lemma_model_rem_shift_by_multiple_pos`:
  false for negative dividends under trunc division.
  Counterexample: `a=-184, d=24, k=16` gives `(a+k*d)/d = 8` but `a/d + k = 9`.
  Counterexample: `a=-45, d=47, k=9` gives `(a+k*d)%d = 2` but `a%d = -45`.
- `lemma_model_div_monotonic_in_divisor_pos` nat direction:
  `a/d2 <= a/d1` (for `d1<=d2`) fails when `a < 0`.
  Counterexample: `a=-62, d1=42, d2=199` gives `a/d2 = 0`, `a/d1 = -1`.
- Nat modular compatibility/congruence wrappers over `%`:
  these do not hold in general with truncating signed remainder.
  Counterexample (`m=-163`): `(-200 + 111) % m = -89`, while
  `((-200 % m) + (111 % m)) % m = 74`.
- `lemma_model_sub_zero_iff_le_ops` nat form:
  tied to truncating nat subtraction; signed subtraction is exact and should use
  equality characterization (`a-b == 0 <==> a==b`) instead.

## Suggested Implementation Order

1. Implement all P1 items first (highest leverage, minimal semantic risk).
2. Add P2 items as needed by downstream proofs.
3. Keep P3 representation lemmas optional unless a consumer needs size bounds.
