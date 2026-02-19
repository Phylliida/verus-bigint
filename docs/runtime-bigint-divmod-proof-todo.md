# Runtime BigInt Div/Rem Proof TODO

Additional formal properties worth proving for `div`, `rem`, and `div_rem`.

## Core Semantics

- [x] Prove exact semantics for nonzero divisors:
  - [x] `rhs > 0 ==> div(self, rhs).model@ == self.model@ / rhs.model@`
  - [x] `rhs > 0 ==> rem(self, rhs).model@ == self.model@ % rhs.model@`

- [x] Prove uniqueness of quotient/remainder decomposition:
  - [x] If `self = q * rhs + r` and `0 <= r < rhs`, then `q` and `r` are unique.

- [x] Prove API coherence (model-level):
  - [x] `rhs > 0 ==> div_rem(self, rhs).0.model@ == div(self, rhs).model@`
  - [x] `rhs > 0 ==> div_rem(self, rhs).1.model@ == rem(self, rhs).model@`

## Edge Cases

- [x] Prove edge-case laws for `rhs > 0`:
  - [x] `rhs == 1 ==> div == self && rem == 0`
  - [x] `self < rhs ==> div == 0 && rem == self`
  - [x] `self == rhs ==> div == 1 && rem == 0`

- [x] Prove divisibility characterization for `rhs > 0`:
  - [x] `rem(self, rhs) == 0 <==> exists k. self == k * rhs`

## Modular Algebra (Future-facing)

- [x] Prove modular addition compatibility for `m > 0`:
  - [x] `(a + b) % m == ((a % m) + (b % m)) % m`

- [x] Prove modular multiplication compatibility for `m > 0`:
  - [x] `(a * b) % m == ((a % m) * (b % m)) % m`

## Next

- Follow-on properties now live in `docs/runtime-bigint-next-proof-todo.md`.
