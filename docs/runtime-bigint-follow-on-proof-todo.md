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

- [ ] Prove strict monotonicity of addition:
  - [ ] `a < b ==> a + c < b + c`

- [ ] Prove strict monotonicity of multiplication for positive multipliers:
  - [ ] `c > 0 && a < b ==> a * c < b * c`

## Cancellation Laws

- [ ] Prove additive cancellation:
  - [ ] `add(a, c) == add(b, c) ==> a == b`

- [ ] Prove multiplicative cancellation for positive multipliers:
  - [ ] `c > 0 && mul(a, c) == mul(b, c) ==> a == b`

## Div/Rem Order Coherence

- [ ] Prove quotient monotonicity for positive divisors:
  - [ ] `d > 0 && a <= b ==> div(a, d) <= div(b, d)`

- [ ] Prove reusable remainder upper bound lemma:
  - [ ] `d > 0 ==> rem(a, d) < d`
