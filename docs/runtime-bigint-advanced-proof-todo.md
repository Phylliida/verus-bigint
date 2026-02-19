# Runtime BigInt Advanced Proof TODO

Properties that are useful for downstream protocol work and API ergonomics.

## Compare/Order Bridge

- [x] Prove compare-order equivalence laws:
  - [x] `cmp(a, b) <= 0 <==> a <= b`
  - [x] `cmp(a, b) < 0 <==> a < b`
  - [x] `cmp(a, b) == 0 <==> a == b`

## Subtraction Characterization

- [x] Prove strengthened subtraction/addition coherence:
  - [x] `a >= b ==> sub(a, b) + b == a`

- [x] Prove subtraction zero characterization:
  - [x] `sub(a, b) == 0 <==> a <= b`

## Division Shift Laws

- [x] Prove quotient shift law for positive divisors:
  - [x] `d > 0 ==> div(a + k*d, d) == div(a, d) + k`

- [x] Prove remainder shift law for positive divisors:
  - [x] `d > 0 ==> rem(a + k*d, d) == rem(a, d)`

## Divisor Monotonicity

- [x] Prove division monotonicity in divisor (fixed dividend):
  - [x] `0 < d1 <= d2 ==> div(a, d2) <= div(a, d1)`

## Modular Congruence Closure

- [x] Prove congruence closure under addition:
  - [x] `a % m == b % m ==> (a + c) % m == (b + c) % m`

- [x] Prove congruence closure under multiplication:
  - [x] `a % m == b % m ==> (a * c) % m == (b * c) % m`

## API-Level Wrapper Lemmas

- [ ] Add direct operation-level wrapper lemmas so callers do not need
      precomputed result witnesses to use the core algebra/order laws.
  - [ ] Design around Verus mode split (`proof fn` cannot invoke `exec` ops);
        likely options are exec wrappers with strong ensures or spec-level
        operator shims used by proof lemmas.
