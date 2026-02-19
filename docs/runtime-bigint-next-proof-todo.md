# Runtime BigInt Next Proof TODO

Follow-on properties beyond the completed div/rem checklist.

## Canonical Representation

- [x] Prove canonical coherence for compare-zero:
  - [x] `self.wf_spec() && rhs.wf_spec() && cmp_limbwise_small_total(self, rhs) == 0 ==> self.limbs_le@ == rhs.limbs_le@`

## Order Laws

- [x] Prove compare antisymmetry:
  - [x] `cmp(a, b) == -cmp(b, a)` (for all `a`, `b`)

- [ ] Prove compare transitivity:
  - [ ] `cmp(a, b) <= 0 && cmp(b, c) <= 0 ==> cmp(a, c) <= 0`
  - [ ] `cmp(a, b) == 0 && cmp(b, c) == 0 ==> cmp(a, c) == 0`

## Arithmetic Coherence

- [ ] Prove subtraction/addition inverse law:
  - [ ] `rhs <= self ==> add(sub(self, rhs), rhs) == self` (model-level equality)

- [ ] Prove monotonicity of addition:
  - [ ] `a <= b ==> a + c <= b + c`

- [ ] Prove multiplication-zero and one-sided monotonicity:
  - [x] `a * 0 == 0`, `a * 1 == a`
  - [ ] `a <= b ==> a * c <= b * c`
