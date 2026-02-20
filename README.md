# verus-bigint

Formally verified arbitrary-size integer witness code extracted from VerusCAD.

## Contents

- `RuntimeBigNatWitness` and `RuntimeBigIntWitness` exported from `src/runtime_bigint_witness/mod.rs`
- Verified/spec-heavy implementation in `src/runtime_bigint_witness/verified_impl.rs`
- Signed verified/spec-heavy implementation in `src/runtime_bigint_witness/signed_verified_impl.rs`
- Verus-path witness datatype declared directly in `src/runtime_bigint_witness/mod.rs` under `cfg(verus_keep_ghost)` (no external refinement bridge file)
- Non-Verus builds fail at compile time; there is no runtime fallback backend
- Trusted-surface notes in `docs/runtime-bigint-trust-assumptions.md`

This crate currently mirrors the bigint witness implementation from VerusCAD.

## Usage In A Rust Library

This crate is verified-only. A plain `cargo build`/`cargo test` in non-Verus mode
fails by design. Use it from a Verus-verified crate (`cargo verus verify`).

### 1) Add dependency

```toml
[dependencies]
verus-bigint = { path = "../verus-bigint" }
vstd = { path = "../verus/source/vstd" }
```

### 2) Unsigned witness (`RuntimeBigNatWitness`)

```rust
use vstd::prelude::*;
use verus_bigint::RuntimeBigNatWitness;

verus! {
pub fn bigint_example() -> (out: (RuntimeBigNatWitness, RuntimeBigNatWitness, RuntimeBigNatWitness, RuntimeBigNatWitness, i8, bool))
{
    let a = RuntimeBigNatWitness::from_u64(7);
    let b = RuntimeBigNatWitness::from_u64(9);
    let sum = &a + &b; // 16
    let product = &a * &b; // 63

    let numerator = RuntimeBigNatWitness::from_u64(63);
    let denominator = RuntimeBigNatWitness::from_u64(9);
    let quotient = &numerator / &denominator; // 7
    let remainder = &numerator % &denominator; // 0

    let ordering = RuntimeBigNatWitness::from_u64(7)
        .cmp_limbwise_small_total(&RuntimeBigNatWitness::from_u64(9)); // -1, 0, or 1
    let remainder_is_zero = remainder.is_zero();

    (sum, product, quotient, remainder, ordering, remainder_is_zero)
}
}
```

Notes:
- Operators are implemented only for borrowed operands (`&lhs op &rhs`).
- Owned forms like `lhs + rhs` are intentionally unsupported to prevent accidental moves.
- `-` uses the witness subtraction semantics: it floors at zero (`a - b == 0` when `a <= b`).
- `/` and `%` use existing witness semantics for divisor zero (`a / 0 == 0`, `a % 0 == 0`).

### 3) Signed witness (`RuntimeBigIntWitness`)

```rust
use vstd::prelude::*;
use verus_bigint::RuntimeBigIntWitness;

verus! {
pub fn signed_bigint_example() -> (out: (
    RuntimeBigIntWitness,
    RuntimeBigIntWitness,
    RuntimeBigIntWitness,
    RuntimeBigIntWitness,
    RuntimeBigIntWitness,
    RuntimeBigIntWitness,
    RuntimeBigIntWitness,
    i8,
    i8
))
{
    let a = RuntimeBigIntWitness::from_i64(-23);
    let b = RuntimeBigIntWitness::from_i64(5);
    let zero = RuntimeBigIntWitness::zero();

    let sum = &a + &b;      // -18
    let difference = &a - &b; // -28
    let product = &a * &b;  // -115
    let quotient = &a / &b; // -4 (truncates toward 0)
    let remainder = &a % &b; // -3 (same sign as dividend when nonzero)
    let quotient_by_zero = &a / &zero; // 0
    let remainder_by_zero = &a % &zero; // 0
    let negated = -&a; // 23

    let ordering = a.cmp(&b); // -1, 0, or 1
    let sign = remainder.signum(); // -1, 0, or 1

    (
        sum,
        difference,
        product,
        quotient,
        remainder,
        quotient_by_zero,
        negated,
        ordering,
        sign,
    )
}
}
```

Signed semantics:
- Operators are implemented only for borrowed operands (`&lhs op &rhs`, including unary `-&x`).
- `sub` is true signed subtraction (`a - a == 0`, no floor-to-zero behavior).
- `/` and `%` use truncating division/remainder (Rust-style, quotient truncates toward zero).
- `%` has the same sign as the dividend when nonzero.
- Division/remainder by zero are totalized to zero (`a / 0 == 0`, `a % 0 == 0`).
- Checked conversion helpers are available (`from_u32`, `from_u64`, `try_to_i64`, `try_to_u64`), plus lightweight sign parse/format helpers (`sign_char`, `parse_sign_char_and_u64`).

### 4) Inspect limbs

```rust
use vstd::prelude::*;
use verus_bigint::RuntimeBigNatWitness;

verus! {
pub fn limbs_example() -> (out: &[u32])
{
    let x = RuntimeBigNatWitness::from_two_limbs(5, 3);
    x.limbs_le() // little-endian limbs: [5, 3]
}
}
```

### 5) Verify

```bash
cargo verus verify
```

## Proof Coverage Map

All verification artifacts live under `src/runtime_bigint_witness/verified_impl/` (plus executable contracts in `src/runtime_bigint_witness/verified_impl.rs`).

Notation used below: `B = 2^32`, `V(xs) = limbs_value_spec(xs)`, `|xs| = xs.len()`.

### 1) Core Representation + Prefix Arithmetic

- Specs and representation model:
  `B = 4294967296` [`limb_base_spec`](src/runtime_bigint_witness/verified_impl/core_repr_prefix.rs#L3); `pow(0)=1, pow(e+1)=B*pow(e)` [`pow_base_spec`](src/runtime_bigint_witness/verified_impl/core_repr_prefix.rs#L7); `V([])=0, V([x0..])=x0 + B*V(tail)` [`limbs_value_spec`](src/runtime_bigint_witness/verified_impl/core_repr_prefix.rs#L17); `|xs|=0 or xs[|xs|-1] != 0` [`canonical_limbs_spec`](src/runtime_bigint_witness/verified_impl/core_repr_prefix.rs#L29); `model = V(limbs) /\\ canonical` [`wf_spec`](src/runtime_bigint_witness/verified_impl/core_repr_prefix.rs#L33); `idx<logical_len and idx<|limbs| ? limbs[idx] : 0` [`limb_or_zero_spec`](src/runtime_bigint_witness/verified_impl/core_repr_prefix.rs#L179); `PS(c+1)=PS(c)+limb(c)*B^c` [`prefix_sum_spec`](src/runtime_bigint_witness/verified_impl/core_repr_prefix.rs#L187); `a+b+carry` [`add_sum_spec`](src/runtime_bigint_witness/verified_impl/core_repr_prefix.rs#L199); `(a+b+carry) mod B` [`add_digit_spec`](src/runtime_bigint_witness/verified_impl/core_repr_prefix.rs#L203); `floor((a+b+carry)/B)` [`add_carry_spec`](src/runtime_bigint_witness/verified_impl/core_repr_prefix.rs#L211).
- Prefix/value/add-sub helper lemmas:
  `pow(e+1)=B*pow(e)` [`lemma_pow_base_succ`](src/runtime_bigint_witness/verified_impl/core_repr_prefix.rs#L38); `V(push(xs,d)) = V(xs) + d*B^|xs|` [`lemma_limbs_value_push`](src/runtime_bigint_witness/verified_impl/core_repr_prefix.rs#L45); `last=0 => V(xs)=V(prefix)` [`lemma_limbs_value_drop_last_zero`](src/runtime_bigint_witness/verified_impl/core_repr_prefix.rs#L91); `all suffix zeros => value unchanged after trim` [`lemma_limbs_value_trim_suffix_zeros`](src/runtime_bigint_witness/verified_impl/core_repr_prefix.rs#L132); `digit + carry_out*B = a+b+carry_in` [`lemma_add_digit_carry_decompose`](src/runtime_bigint_witness/verified_impl/core_repr_prefix.rs#L219); `prefix add invariant step` [`lemma_add_prefix_step`](src/runtime_bigint_witness/verified_impl/core_repr_prefix.rs#L255); `prefix sub invariant step` [`lemma_sub_prefix_step`](src/runtime_bigint_witness/verified_impl/core_repr_prefix.rs#L302); `idx>=logical_len => limb_or_zero=0` [`lemma_limb_or_zero_past_logical_len`](src/runtime_bigint_witness/verified_impl/core_repr_prefix.rs#L356); `PS(c+1)=PS(c)+term(c)` [`lemma_prefix_sum_step`](src/runtime_bigint_witness/verified_impl/core_repr_prefix.rs#L366); `PS(logical_len+extra)=PS(logical_len)` [`lemma_prefix_sum_constant_from_extra`](src/runtime_bigint_witness/verified_impl/core_repr_prefix.rs#L379); `count>=logical_len => PS(count)=PS(logical_len)` [`lemma_prefix_sum_constant_past_logical_len`](src/runtime_bigint_witness/verified_impl/core_repr_prefix.rs#L411); `count<=logical_len => PS(count)=V(subrange(0,count))` [`lemma_prefix_sum_matches_subrange`](src/runtime_bigint_witness/verified_impl/core_repr_prefix.rs#L427); `PS(logical_len)=V(subrange(0,logical_len))` [`lemma_prefix_sum_eq_subrange_value`](src/runtime_bigint_witness/verified_impl/core_repr_prefix.rs#L486).

### 2) Core Pow/Length/Compare Math

- Pow/length/value bounds:
  `pow(e) >= 1` [`lemma_pow_ge_one`](src/runtime_bigint_witness/verified_impl/core_pow_cmp.rs#L3); `lo<=hi => pow(lo)<=pow(hi)` [`lemma_pow_monotonic`](src/runtime_bigint_witness/verified_impl/core_pow_cmp.rs#L25); `pow(a+b)=pow(a)*pow(b)` [`lemma_pow_add`](src/runtime_bigint_witness/verified_impl/core_pow_cmp.rs#L51); `|xs|>0 => V(xs)=xs[0]+B*V(tail)` [`lemma_limbs_value_unfold_nonempty`](src/runtime_bigint_witness/verified_impl/core_pow_cmp.rs#L96); `V(a++b)=V(a)+B^|a|*V(b)` [`lemma_limbs_value_append`](src/runtime_bigint_witness/verified_impl/core_pow_cmp.rs#L123); `V(xs)<B^|xs|` [`lemma_limbs_value_lt_pow_len`](src/runtime_bigint_witness/verified_impl/core_pow_cmp.rs#L199); `|xs|>0 and last!=0 => B^(|xs|-1)<=V(xs)` [`lemma_limbs_value_ge_pow_last_nonzero`](src/runtime_bigint_witness/verified_impl/core_pow_cmp.rs#L279); `V(xs)<B^k => |xs|<=k` [`lemma_len_bound_from_value_upper_pow`](src/runtime_bigint_witness/verified_impl/core_pow_cmp.rs#L319); `|limbs|=0 => model=0; |limbs|=1 => model=limbs[0]` [`lemma_model_zero_or_single_limb`](src/runtime_bigint_witness/verified_impl/core_pow_cmp.rs#L580).
- Compare/high-limb ordering lemmas:
  `same high prefix and last_a>last_b => V(a)>V(b)` [`lemma_cmp_prefix_last_digit_gt`](src/runtime_bigint_witness/verified_impl/core_pow_cmp.rs#L344); `highest differing limb a[idx]>b[idx] => V(a)>V(b)` [`lemma_cmp_high_diff_gt`](src/runtime_bigint_witness/verified_impl/core_pow_cmp.rs#L440); `trimmed_len(a)>trimmed_len(b) => V(a)>V(b)` [`lemma_trimmed_len_gt_implies_value_gt`](src/runtime_bigint_witness/verified_impl/core_pow_cmp.rs#L505); `equal trimmed len + high-diff => V(a)>V(b)` [`lemma_trimmed_high_diff_implies_value_gt`](src/runtime_bigint_witness/verified_impl/core_pow_cmp.rs#L542).

### 3) Core Nat Division/Modulo + Congruence

- Nat-level div/rem uniqueness, shifts, and bounds:
  `x=q1*d+r1=q2*d+r2, 0<=r1,r2<d => q1=q2 and r1=r2` [`lemma_div_rem_unique_nat`](src/runtime_bigint_witness/verified_impl/core_nat_div_mod.rs#L3); `x%d=0 => exists k. x=k*d` [`lemma_mod_zero_implies_multiple_nat`](src/runtime_bigint_witness/verified_impl/core_nat_div_mod.rs#L39); `x=k*d => x%d=0` [`lemma_multiple_implies_mod_zero_nat`](src/runtime_bigint_witness/verified_impl/core_nat_div_mod.rs#L63); `(x+k*d)/d = x/d + k` [`lemma_div_rem_shift_by_multiple_nat`](src/runtime_bigint_witness/verified_impl/core_nat_div_mod.rs#L82) and `(x+k*d)%d = x%d`; `(a*d)/d=a` [`lemma_mul_div_rem_cancel_nat`](src/runtime_bigint_witness/verified_impl/core_nat_div_mod.rs#L124) and `(a*d)%d=0`; `a/d+b/d <= (a+b)/d <= a/d+b/d+1` [`lemma_div_add_bounds_nat`](src/runtime_bigint_witness/verified_impl/core_nat_div_mod.rs#L147); `0<d1<=d2 => x/d2 <= x/d1` [`lemma_div_monotonic_in_divisor_nat`](src/runtime_bigint_witness/verified_impl/core_nat_div_mod.rs#L252).
- Model-lifted div/rem/mod-congruence theorems:
  `(a+k*d)/d = a/d + k` [`lemma_model_div_shift_by_multiple_pos`](src/runtime_bigint_witness/verified_impl/core_nat_div_mod.rs#L230); `(a+k*d)%d = a%d` [`lemma_model_rem_shift_by_multiple_pos`](src/runtime_bigint_witness/verified_impl/core_nat_div_mod.rs#L241); `0<d1<=d2 => a/d2 <= a/d1` [`lemma_model_div_monotonic_in_divisor_pos`](src/runtime_bigint_witness/verified_impl/core_nat_div_mod.rs#L275); `(x+y)%m = ((x%m)+(y%m))%m` [`lemma_mod_add_compat_nat`](src/runtime_bigint_witness/verified_impl/core_nat_div_mod.rs#L287); `model-lift of add/mod compatibility` [`lemma_model_add_mod_compat`](src/runtime_bigint_witness/verified_impl/core_nat_div_mod.rs#L306); `(x*y)%m = ((x%m)*(y%m))%m` [`lemma_mod_mul_compat_nat`](src/runtime_bigint_witness/verified_impl/core_nat_div_mod.rs#L319); `model-lift of mul/mod compatibility` [`lemma_model_mul_mod_compat`](src/runtime_bigint_witness/verified_impl/core_nat_div_mod.rs#L338); `a%m=b%m => (a+c)%m=(b+c)%m` [`lemma_mod_congruence_add_nat`](src/runtime_bigint_witness/verified_impl/core_nat_div_mod.rs#L351); `model-lift add congruence` [`lemma_model_mod_congruence_add`](src/runtime_bigint_witness/verified_impl/core_nat_div_mod.rs#L366); `a%m=b%m => (a*c)%m=(b*c)%m` [`lemma_mod_congruence_mul_nat`](src/runtime_bigint_witness/verified_impl/core_nat_div_mod.rs#L380); `model-lift mul congruence` [`lemma_model_mod_congruence_mul`](src/runtime_bigint_witness/verified_impl/core_nat_div_mod.rs#L395).

### 4) Contract-Level Proof Obligations

- Compare/sub contract theorems:
  `cmp(a,b) = -cmp(b,a)` [`lemma_cmp_limbwise_small_total_antisymmetric`](src/runtime_bigint_witness/verified_impl/contracts_cmp_sub.rs#L3); `cmp(a,b)<=0 and cmp(b,c)<=0 => cmp(a,c)<=0` [`lemma_cmp_limbwise_small_total_transitive_le`](src/runtime_bigint_witness/verified_impl/contracts_cmp_sub.rs#L80); `cmp(a,b)=0 and cmp(b,c)=0 => cmp(a,c)=0` [`lemma_cmp_limbwise_small_total_transitive_eq`](src/runtime_bigint_witness/verified_impl/contracts_cmp_sub.rs#L145); `cmp<=0 <=> V(a)<=V(b)` [`lemma_cmp_le_zero_iff_le_from_total_contracts`](src/runtime_bigint_witness/verified_impl/contracts_cmp_sub.rs#L200); `cmp<0 <=> V(a)<V(b)` [`lemma_cmp_lt_zero_iff_lt_from_total_contracts`](src/runtime_bigint_witness/verified_impl/contracts_cmp_sub.rs#L244); `cmp=0 <=> V(a)=V(b)` [`lemma_cmp_eq_zero_iff_eq_from_total_contracts`](src/runtime_bigint_witness/verified_impl/contracts_cmp_sub.rs#L289); `b<=a => add(sub(a,b),b)=a` [`lemma_model_add_sub_inverse_from_total_contracts`](src/runtime_bigint_witness/verified_impl/contracts_cmp_sub.rs#L333); `b<=a => add(sub(a,b),b)=a` [`lemma_model_sub_add_inverse_ge_from_total_contracts`](src/runtime_bigint_witness/verified_impl/contracts_cmp_sub.rs#L371); `sub(a,b)=0 <=> a<=b` [`lemma_model_sub_zero_iff_le_from_total_contracts`](src/runtime_bigint_witness/verified_impl/contracts_cmp_sub.rs#L391).
- Arithmetic/algebra/div-rem contract theorems:
  `a<=b => a+c <= b+c` [`lemma_model_add_monotonic_from_total_contracts`](src/runtime_bigint_witness/verified_impl/contracts_arith.rs#L3); `a<=b => a*c <= b*c` [`lemma_model_mul_monotonic_from_total_contracts`](src/runtime_bigint_witness/verified_impl/contracts_arith.rs#L37); `a<b => a+c < b+c` [`lemma_model_add_strict_monotonic_from_total_contracts`](src/runtime_bigint_witness/verified_impl/contracts_arith.rs#L69); `0<c and a<b => a*c < b*c` [`lemma_model_mul_strict_monotonic_pos_from_total_contracts`](src/runtime_bigint_witness/verified_impl/contracts_arith.rs#L100); `a+c=b+c => a=b` [`lemma_model_add_cancellation_from_total_contracts`](src/runtime_bigint_witness/verified_impl/contracts_arith.rs#L142); `0<c and a*c=b*c => a=b` [`lemma_model_mul_cancellation_pos_from_total_contracts`](src/runtime_bigint_witness/verified_impl/contracts_arith.rs#L185); `0<d and a<=b => a/d <= b/d` [`lemma_model_div_monotonic_pos_from_total_contracts`](src/runtime_bigint_witness/verified_impl/contracts_arith.rs#L229); `0<d => a%d < d` [`lemma_model_rem_upper_bound_pos_from_total_contracts`](src/runtime_bigint_witness/verified_impl/contracts_arith.rs#L275); `a+b=b+a` [`lemma_model_add_commutative_from_total_contracts`](src/runtime_bigint_witness/verified_impl/contracts_arith.rs#L301); `(a+b)+c=a+(b+c)` [`lemma_model_add_associative_from_total_contracts`](src/runtime_bigint_witness/verified_impl/contracts_arith.rs#L323); `a*b=b*a` [`lemma_model_mul_commutative_from_total_contracts`](src/runtime_bigint_witness/verified_impl/contracts_arith.rs#L349); `(a*b)*c=a*(b*c)` [`lemma_model_mul_associative_from_total_contracts`](src/runtime_bigint_witness/verified_impl/contracts_arith.rs#L371); `a*(b+c)=a*b+a*c` [`lemma_model_mul_distributes_over_add_from_total_contracts`](src/runtime_bigint_witness/verified_impl/contracts_arith.rs#L397).

### 5) Operation-Level Proof Wrappers (Exec + Proof)

- Add wrappers:
  `returns (a+b, b+a) and proves equality` [`lemma_model_add_commutative_ops`](src/runtime_bigint_witness/verified_impl/ops_add.rs#L4); `a<=b => a+c <= b+c` [`lemma_model_add_monotonic_ops`](src/runtime_bigint_witness/verified_impl/ops_add.rs#L32); `|a+b| <= max(|a|,|b|)+1` [`lemma_model_add_len_bound_ops`](src/runtime_bigint_witness/verified_impl/ops_add.rs#L68); `sum=a+b, sum-b=a, sum-a=b` [`lemma_model_add_sub_round_trip_ops`](src/runtime_bigint_witness/verified_impl/ops_add.rs#L166).
- Mul wrappers:
  `returns (a*b, b*a) and proves equality` [`lemma_model_mul_commutative_ops`](src/runtime_bigint_witness/verified_impl/ops_mul.rs#L4); `a<=b => a*c <= b*c` [`lemma_model_mul_monotonic_ops`](src/runtime_bigint_witness/verified_impl/ops_mul.rs#L32); `|a*b| <= |a|+|b|` [`lemma_model_mul_len_bound_ops`](src/runtime_bigint_witness/verified_impl/ops_mul.rs#L68).
- Shape wrappers:
  `a>0 => B^(|a|-1) <= a < B^|a|` [`lemma_model_len_window_nonzero_ops`](src/runtime_bigint_witness/verified_impl/ops_shape.rs#L4); `a=0 => |a|=0` [`lemma_model_zero_implies_len_zero_ops`](src/runtime_bigint_witness/verified_impl/ops_shape.rs#L34).
- Compare/sub wrappers:
  `cmp<=0 <=> a<=b` [`lemma_cmp_le_zero_iff_le_ops`](src/runtime_bigint_witness/verified_impl/ops_cmp_sub.rs#L4); `cmp<0 <=> a<b` [`lemma_cmp_lt_zero_iff_lt_ops`](src/runtime_bigint_witness/verified_impl/ops_cmp_sub.rs#L39); `cmp=0 <=> a=b` [`lemma_cmp_eq_zero_iff_eq_ops`](src/runtime_bigint_witness/verified_impl/ops_cmp_sub.rs#L74); `sub(a,b)=0 <=> a<=b` [`lemma_model_sub_zero_iff_le_ops`](src/runtime_bigint_witness/verified_impl/ops_cmp_sub.rs#L109); `b<=a => add(sub(a,b),b)=a` [`lemma_model_sub_add_inverse_ge_ops`](src/runtime_bigint_witness/verified_impl/ops_cmp_sub.rs#L135); `cmp(a,b)=1 => sub(a,b)>0` [`lemma_cmp_pos_implies_sub_pos_ops`](src/runtime_bigint_witness/verified_impl/ops_cmp_sub.rs#L172); `cmp(a,b)=0 => sub(a,b)=0 and sub(b,a)=0` [`lemma_cmp_eq_implies_bi_sub_zero_ops`](src/runtime_bigint_witness/verified_impl/ops_cmp_sub.rs#L202); `cmp(a,b)=-1 => sub(a,b)=0 and sub(b,a)>0` [`lemma_cmp_neg_implies_asym_sub_ops`](src/runtime_bigint_witness/verified_impl/ops_cmp_sub.rs#L228).
- Div/rem wrappers:
  `a/d + b/d <= (a+b)/d <= a/d + b/d + 1` [`lemma_model_div_add_bounds_pos_ops`](src/runtime_bigint_witness/verified_impl/ops_div_rem.rs#L4); `a<=b and d>0 => a/d <= b/d` [`lemma_model_div_monotonic_pos_ops`](src/runtime_bigint_witness/verified_impl/ops_div_rem.rs#L43); `d>0 => |a/d| <= |a|` [`lemma_model_div_len_bound_pos_ops`](src/runtime_bigint_witness/verified_impl/ops_div_rem.rs#L78); `d>0 => a%d < d` [`lemma_model_rem_upper_bound_pos_ops`](src/runtime_bigint_witness/verified_impl/ops_div_rem.rs#L118); `d>0 => |a%d| <= |d|` [`lemma_model_rem_len_bound_pos_ops`](src/runtime_bigint_witness/verified_impl/ops_div_rem.rs#L143); `d>0 => ((a*d)/d=a) and ((a*d)%d=0)` [`lemma_model_mul_div_rem_cancel_pos_ops`](src/runtime_bigint_witness/verified_impl/ops_div_rem.rs#L174); `d>0 => a=(a/d)*d + (a%d)` [`lemma_model_div_rem_recompose_pos_ops`](src/runtime_bigint_witness/verified_impl/ops_div_rem.rs#L209) and `a%d<d`.

### 6) Executable Verified Contracted Methods

- Constructors/accessors and base ops:
  `model=0` [`zero`](src/runtime_bigint_witness/verified_impl.rs#L57); `model=x` [`from_u32`](src/runtime_bigint_witness/verified_impl.rs#L71); `model=x` [`from_u64`](src/runtime_bigint_witness/verified_impl.rs#L91); `model=lo + B*hi` [`from_two_limbs`](src/runtime_bigint_witness/verified_impl.rs#L117); `model=self+rhs` [`add`](src/runtime_bigint_witness/verified_impl.rs#L148); `model=self*rhs` [`mul`](src/runtime_bigint_witness/verified_impl.rs#L170); `rhs=0 => 0` [`div`](src/runtime_bigint_witness/verified_impl.rs#L212), `rhs>0 => model=floor(self/rhs)`; `rhs=0 => 0` [`rem`](src/runtime_bigint_witness/verified_impl.rs#L277), `rhs>0 => model=self%rhs`; `rhs>0 => self=q*rhs+r, 0<=r<rhs` [`div_rem`](src/runtime_bigint_witness/verified_impl.rs#L352); `out <=> model=0` [`is_zero`](src/runtime_bigint_witness/verified_impl.rs#L400); `out@ = limbs@` [`limbs_le`](src/runtime_bigint_witness/verified_impl.rs#L430).
- Total limbwise arithmetic/comparison/subtraction:
  `|a|<=1 and |b|<=1 => out=a+b` [`add_limbwise_small`](src/runtime_bigint_witness/verified_impl.rs#L439); `out = V(self.limbs)+V(rhs.limbs)` [`add_limbwise_small_total`](src/runtime_bigint_witness/verified_impl.rs#L523); `out = V(self.limbs)*V(rhs.limbs)` [`mul_limbwise_small_total`](src/runtime_bigint_witness/verified_impl.rs#L1035); `rhs=0 => 0; rhs>0 => floor quotient contracts` [`div_limbwise_small_total`](src/runtime_bigint_witness/verified_impl.rs#L1181); `rhs=0 => 0; rhs>0 => modulo contracts` [`rem_limbwise_small_total`](src/runtime_bigint_witness/verified_impl.rs#L1379); `rhs=0 => (0,0); rhs>0 => q/r decomposition` [`div_rem_limbwise_small_total`](src/runtime_bigint_witness/verified_impl.rs#L1415); `out in {-1,0,1} and exact order sign` [`cmp_limbwise_small_total`](src/runtime_bigint_witness/verified_impl.rs#L1525); `self<=rhs => 0 else self-rhs` [`sub_limbwise_small_total`](src/runtime_bigint_witness/verified_impl.rs#L1742); `value-preserving canonical copy` [`copy_small_total`](src/runtime_bigint_witness/verified_impl.rs#L2058).
- Internal exec helpers used in total algorithms:
  `returns n with zero suffix [n..) and n=0 or limbs[n-1]!=0` [`trimmed_len_exec`](src/runtime_bigint_witness/verified_impl.rs#L792); `canonical trim with V(out)=V(in)` [`trim_trailing_zero_limbs`](src/runtime_bigint_witness/verified_impl.rs#L818); `multiply by base: out=self*B` [`shift_base_once_total`](src/runtime_bigint_witness/verified_impl.rs#L872); `multiply by one limb: out=self*rhs_limb` [`mul_by_u32_total`](src/runtime_bigint_witness/verified_impl.rs#L966).
## Checking

- Run all checks:
  - `./scripts/check.sh`
- Run strict checks (fail if Verus tools are unavailable, fail on trusted-escape patterns in non-test `src/` files including `#[verifier::exec_allows_no_decreases_clause]` and `unsafe`, and gate against verification-count regressions):
  - `./scripts/check.sh --require-verus --forbid-trusted-escapes --min-verified 259`
- Run the CI-equivalent strict gate locally (kept aligned with `.github/workflows/check.yml` by `check.sh`, including strict command flags and Verus toolchain pin):
  - `./scripts/check.sh --require-verus --forbid-trusted-escapes --min-verified 259`
  - It also preflights CI trigger coverage so strict checks remain wired to both `pull_request` and `push` on `main`, and rejects trigger filters (`paths*`, `branches-ignore`) that could silently skip enforcement.
  - It also preflights the CI `verify` job execution contract (no job-level `if:` gating, no job-level `continue-on-error`, and explicit `timeout-minutes`).
  - It also preflights CI runner posture for `verify`: `runs-on` must stay pinned to `ubuntu-22.04`, with no dynamic runner expressions and no `self-hosted` labels.
  - It also preflights CI toolchain-install wiring so `Install required Rust toolchain` remains fail-fast, runs before build/strict steps, installs the pinned toolchain with `--profile minimal` plus required components (`rustfmt`, `rustc-dev`, `llvm-tools`), and sets `rustup default` to that same pin.
  - This also preflights workflow checkout + structure wiring so CI keeps the required end-to-end setup (`Checkout verus-bigint` path, `Checkout Verus` repository/path, both checkout steps pinned to `actions/checkout@v4.2.2`, `Build Verus tools` before strict checks, expected working directories, and `VERUS_ROOT` env wiring) and enforces fail-fast step behavior (`set -euo pipefail`, no step-level `if:` gating, no `continue-on-error: true`, no `|| true` masking).
  - It also preflights CI workflow permission hardening (`permissions: contents: read`) and checkout credential hygiene (`persist-credentials: false` on both checkout steps).
- Run checks in offline mode where possible:
  - `./scripts/check.sh --offline`

## Build Mode

- The crate now has a single implementation path: verified code under `cfg(verus_keep_ghost)`.
- Non-Verus builds fail at compile time; use Verus tooling (for example `cargo verus verify`).

## Roadmaps

- Zero-trust migration TODO: `docs/zero-trust-roadmap-todo.md`
