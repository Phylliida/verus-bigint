# Runtime BigInt Advanced Proof TODO

Properties that are useful for downstream protocol work and API ergonomics.

## Compare/Order Bridge

- [x] Prove compare-order equivalence laws:
  - [x] `cmp(a, b) <= 0 <==> a <= b`
  - [x] `cmp(a, b) < 0 <==> a < b`
  - [x] `cmp(a, b) == 0 <==> a == b`

## Subtraction Characterization

- [ ] Prove strengthened subtraction/addition coherence:
  - [ ] `a >= b ==> sub(a, b) + b == a`

- [ ] Prove subtraction zero characterization:
  - [ ] `sub(a, b) == 0 <==> a <= b`

## Division Shift Laws

- [ ] Prove quotient shift law for positive divisors:
  - [ ] `d > 0 ==> div(a + k*d, d) == div(a, d) + k`

- [ ] Prove remainder shift law for positive divisors:
  - [ ] `d > 0 ==> rem(a + k*d, d) == rem(a, d)`

## Divisor Monotonicity

- [ ] Prove division monotonicity in divisor (fixed dividend):
  - [ ] `0 < d1 <= d2 ==> div(a, d2) <= div(a, d1)`

## Modular Congruence Closure

- [ ] Prove congruence closure under addition:
  - [ ] `a % m == b % m ==> (a + c) % m == (b + c) % m`

- [ ] Prove congruence closure under multiplication:
  - [ ] `a % m == b % m ==> (a * c) % m == (b * c) % m`

## API-Level Wrapper Lemmas

- [ ] Add direct operation-level wrapper lemmas so callers do not need
      precomputed result witnesses to use the core algebra/order laws.
