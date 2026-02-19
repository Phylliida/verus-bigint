# Runtime BigInt Next Proof TODO

Follow-on properties beyond the completed div/rem checklist.

## Canonical Representation

- [x] Prove canonical coherence for compare-zero:
  - [x] `self.wf_spec() && rhs.wf_spec() && cmp_limbwise_small_total(self, rhs) == 0 ==> self.limbs_le@ == rhs.limbs_le@`

## Order Laws

- [x] Prove compare antisymmetry:
  - [x] `cmp(a, b) == -cmp(b, a)` (for all `a`, `b`)

- [x] Prove compare transitivity:
  - [x] `cmp(a, b) <= 0 && cmp(b, c) <= 0 ==> cmp(a, c) <= 0`
  - [x] `cmp(a, b) == 0 && cmp(b, c) == 0 ==> cmp(a, c) == 0`

## Arithmetic Coherence

- [x] Prove subtraction/addition inverse law:
  - [x] `rhs <= self ==> add(sub(self, rhs), rhs) == self` (model-level equality)

- [x] Prove monotonicity of addition:
  - [x] `a <= b ==> a + c <= b + c`

- [x] Prove multiplication-zero and one-sided monotonicity:
  - [x] `a * 0 == 0`, `a * 1 == a`
  - [x] `a <= b ==> a * c <= b * c`

## Next

- Further follow-on properties now live in `docs/runtime-bigint-follow-on-proof-todo.md`.
