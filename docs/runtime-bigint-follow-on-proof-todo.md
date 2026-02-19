# Runtime BigInt Follow-on Proof TODO

Additional formal properties worth proving after `runtime-bigint-next-proof-todo.md`.

## Algebraic Laws

- [x] Prove additive commutativity (model-level):
  - [x] `add(a, b) == add(b, a)`

- [x] Prove additive associativity (model-level):
  - [x] `add(add(a, b), c) == add(a, add(b, c))`

- [x] Prove multiplicative commutativity (model-level):
  - [x] `mul(a, b) == mul(b, a)`

- [x] Prove multiplicative associativity (model-level):
  - [x] `mul(mul(a, b), c) == mul(a, mul(b, c))`

## Distributivity

- [x] Prove multiplication distributes over addition (model-level):
  - [x] `mul(a, add(b, c)) == add(mul(a, b), mul(a, c))`

## Strict Order Compatibility

- [x] Prove strict monotonicity of addition:
  - [x] `a < b ==> a + c < b + c`

- [x] Prove strict monotonicity of multiplication for positive multipliers:
  - [x] `c > 0 && a < b ==> a * c < b * c`

## Cancellation Laws

- [x] Prove additive cancellation:
  - [x] `add(a, c) == add(b, c) ==> a == b`

- [x] Prove multiplicative cancellation for positive multipliers:
  - [x] `c > 0 && mul(a, c) == mul(b, c) ==> a == b`

## Div/Rem Order Coherence

- [x] Prove quotient monotonicity for positive divisors:
  - [x] `d > 0 && a <= b ==> div(a, d) <= div(b, d)`

- [x] Prove reusable remainder upper bound lemma:
  - [x] `d > 0 ==> rem(a, d) < d`
