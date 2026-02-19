# Runtime BigInt Operation-Wrapper Proof TODO

Direct operation-level wrapper lemmas that compute required witnesses internally,
so callers can use high-level laws without precomputing intermediate results.

## Compare Wrappers

- [x] Add wrapper for `cmp <= 0 <==> a <= b`:
  - [x] `lemma_cmp_le_zero_iff_le_ops(a, b) -> cmp`

- [x] Add wrapper for `cmp < 0 <==> a < b`:
  - [x] `lemma_cmp_lt_zero_iff_lt_ops(a, b) -> cmp`

- [x] Add wrapper for `cmp == 0 <==> a == b`:
  - [x] `lemma_cmp_eq_zero_iff_eq_ops(a, b) -> cmp`

## Subtraction Wrappers

- [x] Add wrapper for subtraction zero characterization:
  - [x] `lemma_model_sub_zero_iff_le_ops(a, b) -> sub_ab`

- [x] Add wrapper for subtraction/addition inverse under `b <= a`:
  - [x] `lemma_model_sub_add_inverse_ge_ops(a, b) -> (sub_ab, add_sub_ab_b)`

## Division/Remainder Wrappers

- [x] Add wrapper for quotient monotonicity under positive divisor:
  - [x] `lemma_model_div_monotonic_pos_ops(a, b, d) -> (div_a, div_b)`

- [x] Add wrapper for remainder upper bound under positive divisor:
  - [x] `lemma_model_rem_upper_bound_pos_ops(a, d) -> rem_a`

- [x] Add wrapper for recomposition:
  - [x] `lemma_model_div_rem_recompose_pos_ops(a, d) -> (q, r)`
  - [x] prove `a == q * d + r` and `r < d` for `d > 0`
