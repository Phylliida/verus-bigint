# Runtime BigInt Length-Bound Proof TODO

Limb-length bounds useful for complexity reasoning and memory-shape invariants.

## Addition

- [x] Add operation-level wrapper for additive length bound:
  - [x] `lemma_model_add_len_bound_ops(a, b) -> add_ab`
  - [x] prove `len(add_ab) <= max(len(a), len(b)) + 1`

## Multiplication

- [x] Add operation-level wrapper for multiplicative length bound:
  - [x] `lemma_model_mul_len_bound_ops(a, b) -> mul_ab`
  - [x] prove `len(mul_ab) <= len(a) + len(b)`

## Division / Remainder

- [x] Add operation-level wrapper for quotient length bound (`d > 0`):
  - [x] `lemma_model_div_len_bound_pos_ops(a, d) -> div_a`
  - [x] prove `len(div_a) <= len(a)`

- [x] Add operation-level wrapper for remainder length bound (`d > 0`):
  - [x] `lemma_model_rem_len_bound_pos_ops(a, d) -> rem_a`
  - [x] prove `len(rem_a) <= len(d)`
