# Runtime BigInt Div/Mul/Add/Sub Follow-on TODO

Focused arithmetic identities around division, multiplication, addition,
and truncated subtraction.

## Multiplication / Division Cancellation

- [x] Add operation-level cancellation wrapper for positive divisors:
  - [x] `lemma_model_mul_div_rem_cancel_pos_ops(a, d) -> (prod, q, r)`
  - [x] prove `prod == a * d`
  - [x] prove `q == prod / d == a` for `d > 0`
  - [x] prove `r == prod % d == 0` for `d > 0`

## Floor-Division Add Bounds

- [x] Add wrapper for quotient additivity bounds (`d > 0`):
  - [x] `a / d + b / d <= (a + b) / d`
  - [x] `(a + b) / d <= a / d + b / d + 1`

## Add/Sub Round-Trip

- [x] Add wrapper for total subtraction/addition round-trip:
  - [x] `sub(a + b, b) == a`
  - [x] `sub(a + b, a) == b`
