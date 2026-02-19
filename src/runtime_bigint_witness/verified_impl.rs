#![cfg(verus_keep_ghost)]

use super::RuntimeBigNatWitness;
use vstd::prelude::*;
use vstd::arithmetic::div_mod::{
    lemma_add_mod_noop,
    lemma_basic_div,
    lemma_div_is_ordered_by_denominator,
    lemma_fundamental_div_mod,
    lemma_fundamental_div_mod_converse,
    lemma_mul_mod_noop,
    lemma_mod_self_0,
    lemma_mod_pos_bound,
    lemma_small_mod,
};
use vstd::seq::Seq;

verus! {
impl RuntimeBigNatWitness {
    pub open spec fn limb_base_spec() -> nat {
        4_294_967_296
    }

    pub open spec fn pow_base_spec(exp: nat) -> nat
        decreases exp
    {
        if exp == 0 {
            1
        } else {
            Self::limb_base_spec() * Self::pow_base_spec((exp - 1) as nat)
        }
    }

    pub open spec fn limbs_value_spec(limbs: Seq<u32>) -> nat
        decreases limbs.len()
    {
        if limbs.len() == 0 {
            0
        } else if limbs.len() == 1 {
            limbs[0] as nat
        } else {
            limbs[0] as nat + Self::limb_base_spec() * Self::limbs_value_spec(limbs.subrange(1, limbs.len() as int))
        }
    }

    pub open spec fn canonical_limbs_spec(limbs: Seq<u32>) -> bool {
        limbs.len() == 0 || limbs[(limbs.len() - 1) as int] != 0u32
    }

    pub open spec fn wf_spec(&self) -> bool {
        &&& self.model@ == Self::limbs_value_spec(self.limbs_le@)
        &&& Self::canonical_limbs_spec(self.limbs_le@)
    }

    proof fn lemma_pow_base_succ(exp: nat)
        ensures
            Self::pow_base_spec(exp + 1) == Self::limb_base_spec() * Self::pow_base_spec(exp),
    {
    }

    /// Value update law for appending a high limb in little-endian representation.
    proof fn lemma_limbs_value_push(limbs: Seq<u32>, digit: u32)
        ensures
            Self::limbs_value_spec(limbs.push(digit))
                == Self::limbs_value_spec(limbs) + digit as nat * Self::pow_base_spec(limbs.len()),
        decreases limbs.len()
    {
        if limbs.len() == 0 {
            assert(Self::limbs_value_spec(Seq::<u32>::empty()) == 0);
            assert(Self::pow_base_spec(0) == 1);
            assert(limbs.push(digit).len() == 1);
            assert(Self::limbs_value_spec(limbs.push(digit)) == digit as nat);
            assert(
                Self::limbs_value_spec(limbs.push(digit))
                    == Self::limbs_value_spec(limbs) + digit as nat * Self::pow_base_spec(limbs.len())
            );
        } else {
            let tail = limbs.subrange(1, limbs.len() as int);
            Self::lemma_limbs_value_push(tail, digit);
            assert(tail.len() + 1 == limbs.len());
            assert(limbs.push(digit).subrange(1, limbs.push(digit).len() as int) == tail.push(digit));
            assert(Self::limbs_value_spec(limbs.push(digit)) == limbs[0] as nat + Self::limb_base_spec() * Self::limbs_value_spec(tail.push(digit)));
            assert(Self::limbs_value_spec(limbs) == limbs[0] as nat + Self::limb_base_spec() * Self::limbs_value_spec(tail));
            assert(Self::limbs_value_spec(tail.push(digit)) == Self::limbs_value_spec(tail) + digit as nat * Self::pow_base_spec(tail.len()));
            assert(
                Self::limbs_value_spec(limbs.push(digit))
                    == Self::limbs_value_spec(limbs)
                        + Self::limb_base_spec() * (digit as nat * Self::pow_base_spec(tail.len()))
            );
            Self::lemma_pow_base_succ(tail.len() as nat);
            assert(Self::pow_base_spec(limbs.len()) == Self::limb_base_spec() * Self::pow_base_spec(tail.len() as nat));
            assert(
                Self::limb_base_spec() * (digit as nat * Self::pow_base_spec(tail.len()))
                    == digit as nat * (Self::limb_base_spec() * Self::pow_base_spec(tail.len()))
            ) by (nonlinear_arith)
            ;
            assert(
                digit as nat * (Self::limb_base_spec() * Self::pow_base_spec(tail.len()))
                    == digit as nat * Self::pow_base_spec(limbs.len())
            );
            assert(
                Self::limbs_value_spec(limbs.push(digit))
                    == Self::limbs_value_spec(limbs) + digit as nat * Self::pow_base_spec(limbs.len())
            );
        }
    }

    proof fn lemma_limbs_value_drop_last_zero(limbs: Seq<u32>)
        requires
            limbs.len() > 0,
            limbs[(limbs.len() - 1) as int] == 0u32,
        ensures
            Self::limbs_value_spec(limbs)
                == Self::limbs_value_spec(limbs.subrange(0, limbs.len() as int - 1)),
    {
        let prefix = limbs.subrange(0, limbs.len() as int - 1);
        assert(prefix.len() + 1 == limbs.len());
        assert(prefix.push(0u32).len() == limbs.len());
        assert forall|i: int| 0 <= i < limbs.len() implies #[trigger] prefix.push(0u32)[i] == limbs[i] by {
            if i < prefix.len() {
                assert(prefix.push(0u32)[i] == prefix[i]);
                assert(prefix[i] == limbs[i]);
            } else {
                assert(i == prefix.len());
                assert(i == limbs.len() - 1);
                assert(prefix.push(0u32)[i] == 0u32);
                assert(limbs[(limbs.len() - 1) as int] == 0u32);
                assert(limbs[i] == 0u32);
            }
        };
        assert(prefix.push(0u32) == limbs);
        Self::lemma_limbs_value_push(prefix, 0u32);
        assert(Self::pow_base_spec(prefix.len()) >= 0);
        assert(0u32 as nat * Self::pow_base_spec(prefix.len()) == 0);
        assert(
            Self::limbs_value_spec(prefix.push(0u32))
                == Self::limbs_value_spec(prefix) + 0
        );
        assert(
            Self::limbs_value_spec(prefix.push(0u32))
                == Self::limbs_value_spec(prefix)
        );
        assert(
            Self::limbs_value_spec(limbs)
                == Self::limbs_value_spec(limbs.subrange(0, limbs.len() as int - 1))
        );
    }

    proof fn lemma_limbs_value_trim_suffix_zeros(limbs: Seq<u32>, n: nat)
        requires
            n <= limbs.len(),
            forall|i: int| n <= i < limbs.len() ==> limbs[i] == 0u32,
        ensures
            Self::limbs_value_spec(limbs)
                == Self::limbs_value_spec(limbs.subrange(0, n as int)),
        decreases limbs.len() - n
    {
        if limbs.len() == n {
            assert(limbs.subrange(0, n as int) == limbs);
        } else {
            assert(limbs.len() > 0);
            assert(n < limbs.len());
            let last = limbs.len() - 1;
            assert(n <= last);
            assert(limbs[last as int] == 0u32);
            let prefix = limbs.subrange(0, limbs.len() as int - 1);
            Self::lemma_limbs_value_drop_last_zero(limbs);
            assert(
                Self::limbs_value_spec(limbs)
                    == Self::limbs_value_spec(prefix)
            );
            assert forall|i: int| n <= i < prefix.len() implies prefix[i] == 0u32 by {
                assert(i < prefix.len());
                assert(prefix.len() == limbs.len() - 1);
                assert(i < limbs.len());
                assert(limbs[i] == 0u32);
                assert(prefix[i] == limbs[i]);
            };
            Self::lemma_limbs_value_trim_suffix_zeros(prefix, n);
            assert(prefix.subrange(0, n as int) == limbs.subrange(0, n as int));
            assert(
                Self::limbs_value_spec(prefix)
                    == Self::limbs_value_spec(prefix.subrange(0, n as int))
            );
            assert(
                Self::limbs_value_spec(prefix.subrange(0, n as int))
                    == Self::limbs_value_spec(limbs.subrange(0, n as int))
            );
            assert(
                Self::limbs_value_spec(limbs)
                    == Self::limbs_value_spec(limbs.subrange(0, n as int))
            );
        }
    }

    pub open spec fn limb_or_zero_spec(limbs: Seq<u32>, logical_len: nat, idx: nat) -> nat {
        if idx < logical_len && idx < limbs.len() {
            limbs[idx as int] as nat
        } else {
            0
        }
    }

    pub open spec fn prefix_sum_spec(limbs: Seq<u32>, logical_len: nat, count: nat) -> nat
        decreases count
    {
        if count == 0 {
            0
        } else {
            let prev = (count - 1) as nat;
            Self::prefix_sum_spec(limbs, logical_len, prev)
                + Self::limb_or_zero_spec(limbs, logical_len, prev) * Self::pow_base_spec(prev)
        }
    }

    pub open spec fn add_sum_spec(a: nat, b: nat, carry_in: nat) -> nat {
        a + b + carry_in
    }

    pub open spec fn add_digit_spec(a: nat, b: nat, carry_in: nat) -> nat {
        if Self::add_sum_spec(a, b, carry_in) >= Self::limb_base_spec() {
            (Self::add_sum_spec(a, b, carry_in) - Self::limb_base_spec()) as nat
        } else {
            Self::add_sum_spec(a, b, carry_in)
        }
    }

    pub open spec fn add_carry_spec(a: nat, b: nat, carry_in: nat) -> nat {
        if Self::add_sum_spec(a, b, carry_in) >= Self::limb_base_spec() {
            1
        } else {
            0
        }
    }

    proof fn lemma_add_digit_carry_decompose(a: nat, b: nat, carry_in: nat)
        requires
            a < Self::limb_base_spec(),
            b < Self::limb_base_spec(),
            carry_in <= 1,
        ensures
            Self::add_carry_spec(a, b, carry_in) <= 1,
            Self::add_digit_spec(a, b, carry_in)
                + Self::add_carry_spec(a, b, carry_in) * Self::limb_base_spec()
                == Self::add_sum_spec(a, b, carry_in),
    {
        let sum = Self::add_sum_spec(a, b, carry_in);
        let base = Self::limb_base_spec();
        if sum >= base {
            assert(Self::add_digit_spec(a, b, carry_in) == (sum - base) as nat);
            assert(Self::add_carry_spec(a, b, carry_in) == 1);
            assert(Self::add_carry_spec(a, b, carry_in) <= 1);
            assert((sum - base) as nat + base == sum);
            assert(
                Self::add_digit_spec(a, b, carry_in)
                    + Self::add_carry_spec(a, b, carry_in) * base
                    == sum
            );
        } else {
            assert(Self::add_digit_spec(a, b, carry_in) == sum);
            assert(Self::add_carry_spec(a, b, carry_in) == 0);
            assert(Self::add_carry_spec(a, b, carry_in) <= 1);
            assert(
                Self::add_digit_spec(a, b, carry_in)
                    + Self::add_carry_spec(a, b, carry_in) * base
                    == sum
            );
        }
        assert(sum == Self::add_sum_spec(a, b, carry_in));
    }

    proof fn lemma_add_prefix_step(
        psr: nat,
        psa: nat,
        psb: nat,
        digit: nat,
        a: nat,
        b: nat,
        carry_in: nat,
        carry_out: nat,
        pow_i: nat,
        pow_next: nat,
    )
        requires
            psr + carry_in * pow_i == psa + psb,
            digit + carry_out * Self::limb_base_spec() == a + b + carry_in,
            pow_next == Self::limb_base_spec() * pow_i,
        ensures
            psr + digit * pow_i + carry_out * pow_next
                == psa + psb + a * pow_i + b * pow_i,
    {
        assert(carry_out * pow_next == carry_out * (Self::limb_base_spec() * pow_i));
        assert(carry_out * (Self::limb_base_spec() * pow_i) == carry_out * Self::limb_base_spec() * pow_i)
            by (nonlinear_arith);
        assert(
            digit * pow_i + carry_out * pow_next
                == digit * pow_i + carry_out * Self::limb_base_spec() * pow_i
        );
        assert(
            digit * pow_i + carry_out * Self::limb_base_spec() * pow_i
                == (digit + carry_out * Self::limb_base_spec()) * pow_i
        ) by (nonlinear_arith);
        assert((digit + carry_out * Self::limb_base_spec()) * pow_i == (a + b + carry_in) * pow_i);
        assert((a + b + carry_in) * pow_i == a * pow_i + b * pow_i + carry_in * pow_i)
            by (nonlinear_arith);
        assert(
            psr + digit * pow_i + carry_out * pow_next
                == psr + a * pow_i + b * pow_i + carry_in * pow_i
        );
        assert(
            psr + a * pow_i + b * pow_i + carry_in * pow_i
                == (psr + carry_in * pow_i) + a * pow_i + b * pow_i
        ) by (nonlinear_arith);
        assert((psr + carry_in * pow_i) + a * pow_i + b * pow_i == (psa + psb) + a * pow_i + b * pow_i);
        assert((psa + psb) + a * pow_i + b * pow_i == psa + psb + a * pow_i + b * pow_i)
            by (nonlinear_arith);
    }

    proof fn lemma_sub_prefix_step(
        psr: nat,
        psa: nat,
        psb: nat,
        digit: nat,
        a: nat,
        b: nat,
        borrow_in: nat,
        borrow_out: nat,
        pow_i: nat,
        pow_next: nat,
    )
        requires
            psr + psb == psa + borrow_in * pow_i,
            digit + b + borrow_in == a + borrow_out * Self::limb_base_spec(),
            pow_next == Self::limb_base_spec() * pow_i,
        ensures
            (psr + digit * pow_i) + (psb + b * pow_i)
                == (psa + a * pow_i) + borrow_out * pow_next,
    {
        assert((digit + b + borrow_in) * pow_i == (a + borrow_out * Self::limb_base_spec()) * pow_i);
        assert((digit + b + borrow_in) * pow_i == digit * pow_i + b * pow_i + borrow_in * pow_i)
            by (nonlinear_arith);
        assert((a + borrow_out * Self::limb_base_spec()) * pow_i == a * pow_i + borrow_out * Self::limb_base_spec() * pow_i)
            by (nonlinear_arith);
        assert(borrow_out * pow_next == borrow_out * (Self::limb_base_spec() * pow_i));
        assert(borrow_out * (Self::limb_base_spec() * pow_i) == borrow_out * Self::limb_base_spec() * pow_i)
            by (nonlinear_arith);
        assert(
            digit * pow_i + b * pow_i + borrow_in * pow_i
                == a * pow_i + borrow_out * pow_next
        );
        assert(
            (psr + digit * pow_i) + (psb + b * pow_i)
                == psr + psb + digit * pow_i + b * pow_i
        ) by (nonlinear_arith);
        assert(
            psr + psb + digit * pow_i + b * pow_i
                == psa + borrow_in * pow_i + digit * pow_i + b * pow_i
        );
        assert(
            psa + borrow_in * pow_i + digit * pow_i + b * pow_i
                == psa + (a * pow_i + borrow_out * pow_next)
        );
        assert(
            psa + (a * pow_i + borrow_out * pow_next)
                == (psa + a * pow_i) + borrow_out * pow_next
        ) by (nonlinear_arith);
        assert(
            (psr + digit * pow_i) + (psb + b * pow_i)
                == (psa + a * pow_i) + borrow_out * pow_next
        );
    }

    proof fn lemma_limb_or_zero_past_logical_len(limbs: Seq<u32>, logical_len: nat, idx: nat)
        requires
            logical_len <= idx,
        ensures
            Self::limb_or_zero_spec(limbs, logical_len, idx) == 0,
    {
        assert(!(idx < logical_len));
        assert(Self::limb_or_zero_spec(limbs, logical_len, idx) == 0);
    }

    proof fn lemma_prefix_sum_step(limbs: Seq<u32>, logical_len: nat, count: nat)
        ensures
            Self::prefix_sum_spec(limbs, logical_len, count + 1)
                == Self::prefix_sum_spec(limbs, logical_len, count)
                    + Self::limb_or_zero_spec(limbs, logical_len, count) * Self::pow_base_spec(count),
    {
        assert(
            Self::prefix_sum_spec(limbs, logical_len, count + 1)
                == Self::prefix_sum_spec(limbs, logical_len, count)
                    + Self::limb_or_zero_spec(limbs, logical_len, count) * Self::pow_base_spec(count)
        );
    }

    proof fn lemma_prefix_sum_constant_from_extra(limbs: Seq<u32>, logical_len: nat, extra: nat)
        ensures
            Self::prefix_sum_spec(limbs, logical_len, logical_len + extra)
                == Self::prefix_sum_spec(limbs, logical_len, logical_len),
        decreases extra
    {
        if extra == 0 {
            assert(logical_len + extra == logical_len);
        } else {
            let prev = (extra - 1) as nat;
            Self::lemma_prefix_sum_constant_from_extra(limbs, logical_len, prev);
            assert(extra == prev + 1);
            assert((logical_len + prev) + 1 == logical_len + extra);
            Self::lemma_prefix_sum_step(limbs, logical_len, logical_len + prev);
            Self::lemma_limb_or_zero_past_logical_len(limbs, logical_len, logical_len + prev);
            assert(
                Self::prefix_sum_spec(limbs, logical_len, logical_len + extra)
                    == Self::prefix_sum_spec(limbs, logical_len, logical_len + prev)
                        + Self::limb_or_zero_spec(limbs, logical_len, logical_len + prev)
                            * Self::pow_base_spec(logical_len + prev)
            );
            assert(
                Self::prefix_sum_spec(limbs, logical_len, logical_len + extra)
                    == Self::prefix_sum_spec(limbs, logical_len, logical_len + prev)
            );
            assert(
                Self::prefix_sum_spec(limbs, logical_len, logical_len + prev)
                    == Self::prefix_sum_spec(limbs, logical_len, logical_len)
            );
        }
    }

    proof fn lemma_prefix_sum_constant_past_logical_len(limbs: Seq<u32>, logical_len: nat, count: nat)
        requires
            logical_len <= count,
        ensures
            Self::prefix_sum_spec(limbs, logical_len, count)
                == Self::prefix_sum_spec(limbs, logical_len, logical_len),
    {
        let extra = (count - logical_len) as nat;
        assert(logical_len + extra == count);
        Self::lemma_prefix_sum_constant_from_extra(limbs, logical_len, extra);
        assert(
            Self::prefix_sum_spec(limbs, logical_len, count)
                == Self::prefix_sum_spec(limbs, logical_len, logical_len + extra)
        );
    }

    proof fn lemma_prefix_sum_matches_subrange(limbs: Seq<u32>, logical_len: nat, count: nat)
        requires
            count <= logical_len,
            count <= limbs.len(),
        ensures
            Self::prefix_sum_spec(limbs, logical_len, count)
                == Self::limbs_value_spec(limbs.subrange(0, count as int)),
        decreases count
    {
        if count == 0 {
            assert(limbs.subrange(0, 0) == Seq::<u32>::empty());
            assert(Self::prefix_sum_spec(limbs, logical_len, count) == 0);
            assert(Self::limbs_value_spec(limbs.subrange(0, count as int)) == 0);
        } else {
            let prev = (count - 1) as nat;
            Self::lemma_prefix_sum_matches_subrange(limbs, logical_len, prev);

            assert(prev < count);
            assert(prev < logical_len);
            assert(prev < limbs.len());
            assert(Self::limb_or_zero_spec(limbs, logical_len, prev) == limbs[prev as int] as nat);
            assert(
                Self::prefix_sum_spec(limbs, logical_len, count)
                    == Self::prefix_sum_spec(limbs, logical_len, prev)
                        + Self::limb_or_zero_spec(limbs, logical_len, prev) * Self::pow_base_spec(prev)
            );
            assert(
                Self::prefix_sum_spec(limbs, logical_len, count)
                    == Self::limbs_value_spec(limbs.subrange(0, prev as int))
                        + limbs[prev as int] as nat * Self::pow_base_spec(prev)
            );

            let prefix = limbs.subrange(0, prev as int);
            assert(prefix.push(limbs[prev as int]).len() == count);
            assert forall|i: int| 0 <= i < count implies #[trigger] prefix.push(limbs[prev as int])[i] == limbs.subrange(0, count as int)[i] by {
                if i < prev {
                    assert(prefix.push(limbs[prev as int])[i] == prefix[i]);
                    assert(prefix[i] == limbs[i]);
                    assert(limbs.subrange(0, count as int)[i] == limbs[i]);
                } else {
                    assert(i == prev);
                    assert(prefix.push(limbs[prev as int])[i] == limbs[prev as int]);
                    assert(limbs.subrange(0, count as int)[i] == limbs[prev as int]);
                }
            };
            assert(prefix.push(limbs[prev as int]) == limbs.subrange(0, count as int));
            Self::lemma_limbs_value_push(prefix, limbs[prev as int]);
            assert(
                Self::limbs_value_spec(limbs.subrange(0, count as int))
                    == Self::limbs_value_spec(prefix)
                        + limbs[prev as int] as nat * Self::pow_base_spec(prev)
            );
            assert(
                Self::prefix_sum_spec(limbs, logical_len, count)
                    == Self::limbs_value_spec(limbs.subrange(0, count as int))
            );
        }
    }

    proof fn lemma_prefix_sum_eq_subrange_value(limbs: Seq<u32>, logical_len: nat)
        requires
            logical_len <= limbs.len(),
        ensures
            Self::prefix_sum_spec(limbs, logical_len, logical_len)
                == Self::limbs_value_spec(limbs.subrange(0, logical_len as int)),
    {
        Self::lemma_prefix_sum_matches_subrange(limbs, logical_len, logical_len);
    }

    proof fn lemma_pow_ge_one(exp: nat)
        ensures
            Self::pow_base_spec(exp) >= 1,
        decreases exp
    {
        if exp == 0 {
            assert(Self::pow_base_spec(exp) == 1);
        } else {
            let prev = (exp - 1) as nat;
            Self::lemma_pow_ge_one(prev);
            Self::lemma_pow_base_succ(prev);
            assert(Self::limb_base_spec() == 4_294_967_296);
            assert(Self::limb_base_spec() >= 1);
            assert(Self::pow_base_spec(prev) >= 1);
            assert(Self::pow_base_spec(exp) == Self::limb_base_spec() * Self::pow_base_spec(prev));
            assert(Self::pow_base_spec(prev) <= Self::limb_base_spec() * Self::pow_base_spec(prev))
                by (nonlinear_arith);
            assert(Self::pow_base_spec(prev) <= Self::pow_base_spec(exp));
            assert(Self::pow_base_spec(exp) >= 1);
        }
    }

    proof fn lemma_pow_monotonic(lo: nat, hi: nat)
        requires
            lo <= hi,
        ensures
            Self::pow_base_spec(lo) <= Self::pow_base_spec(hi),
        decreases hi - lo
    {
        if lo == hi {
            assert(Self::pow_base_spec(lo) <= Self::pow_base_spec(hi));
        } else {
            assert(lo < hi);
            let prev = (hi - 1) as nat;
            assert(lo <= prev);
            Self::lemma_pow_monotonic(lo, prev);
            Self::lemma_pow_ge_one(prev);
            Self::lemma_pow_base_succ(prev);
            assert(Self::limb_base_spec() == 4_294_967_296);
            assert(Self::limb_base_spec() >= 1);
            assert(Self::pow_base_spec(prev) <= Self::limb_base_spec() * Self::pow_base_spec(prev))
                by (nonlinear_arith);
            assert(Self::pow_base_spec(hi) == Self::limb_base_spec() * Self::pow_base_spec(prev));
            assert(Self::pow_base_spec(prev) <= Self::pow_base_spec(hi));
            assert(Self::pow_base_spec(lo) <= Self::pow_base_spec(hi));
        }
    }

    proof fn lemma_pow_add(lhs: nat, rhs: nat)
        ensures
            Self::pow_base_spec(lhs + rhs) == Self::pow_base_spec(lhs) * Self::pow_base_spec(rhs),
        decreases rhs
    {
        if rhs == 0 {
            assert(lhs + rhs == lhs);
            assert(Self::pow_base_spec(0) == 1);
            assert(Self::pow_base_spec(lhs + rhs) == Self::pow_base_spec(lhs));
            assert(Self::pow_base_spec(lhs) * Self::pow_base_spec(rhs) == Self::pow_base_spec(lhs));
        } else {
            let prev = (rhs - 1) as nat;
            Self::lemma_pow_add(lhs, prev);
            assert(lhs + rhs == lhs + prev + 1);
            Self::lemma_pow_base_succ(lhs + prev);
            Self::lemma_pow_base_succ(prev);
            assert(
                Self::pow_base_spec(lhs + rhs)
                    == Self::limb_base_spec() * Self::pow_base_spec(lhs + prev)
            );
            assert(
                Self::pow_base_spec(lhs + prev)
                    == Self::pow_base_spec(lhs) * Self::pow_base_spec(prev)
            );
            assert(
                Self::pow_base_spec(lhs + rhs)
                    == Self::limb_base_spec()
                        * (Self::pow_base_spec(lhs) * Self::pow_base_spec(prev))
            );
            assert(
                Self::limb_base_spec() * (Self::pow_base_spec(lhs) * Self::pow_base_spec(prev))
                    == Self::pow_base_spec(lhs)
                        * (Self::limb_base_spec() * Self::pow_base_spec(prev))
            ) by (nonlinear_arith);
            assert(
                Self::pow_base_spec(rhs)
                    == Self::limb_base_spec() * Self::pow_base_spec(prev)
            );
            assert(
                Self::pow_base_spec(lhs + rhs)
                    == Self::pow_base_spec(lhs) * Self::pow_base_spec(rhs)
            );
        }
    }

    proof fn lemma_limbs_value_unfold_nonempty(limbs: Seq<u32>)
        requires
            limbs.len() > 0,
        ensures
            Self::limbs_value_spec(limbs)
                == limbs[0] as nat
                    + Self::limb_base_spec() * Self::limbs_value_spec(limbs.subrange(1, limbs.len() as int)),
    {
        if limbs.len() == 1 {
            assert(Self::limbs_value_spec(limbs) == limbs[0] as nat);
            assert(limbs.subrange(1, limbs.len() as int) == Seq::<u32>::empty());
            assert(Self::limbs_value_spec(Seq::<u32>::empty()) == 0);
            assert(
                limbs[0] as nat
                    + Self::limb_base_spec() * Self::limbs_value_spec(limbs.subrange(1, limbs.len() as int))
                    == limbs[0] as nat
            );
        } else {
            assert(
                Self::limbs_value_spec(limbs)
                    == limbs[0] as nat
                        + Self::limb_base_spec()
                            * Self::limbs_value_spec(limbs.subrange(1, limbs.len() as int))
            );
        }
    }

    proof fn lemma_limbs_value_append(left: Seq<u32>, right: Seq<u32>)
        ensures
            Self::limbs_value_spec(left + right)
                == Self::limbs_value_spec(left)
                    + Self::pow_base_spec(left.len()) * Self::limbs_value_spec(right),
        decreases left.len()
    {
        if left.len() == 0 {
            assert(left + right == right);
            assert(Self::limbs_value_spec(left) == 0);
            assert(Self::pow_base_spec(left.len()) == 1);
            assert(
                Self::limbs_value_spec(left + right)
                    == Self::limbs_value_spec(left)
                        + Self::pow_base_spec(left.len()) * Self::limbs_value_spec(right)
            );
        } else {
            let tail = left.subrange(1, left.len() as int);
            let whole = left + right;
            let pow_tail = Self::pow_base_spec(tail.len());
            let right_val = Self::limbs_value_spec(right);
            Self::lemma_limbs_value_append(tail, right);
            Self::lemma_limbs_value_unfold_nonempty(left);
            Self::lemma_limbs_value_unfold_nonempty(whole);
            assert(whole.subrange(1, whole.len() as int) == tail + right);
            assert(
                Self::limbs_value_spec(whole)
                    == left[0] as nat
                        + Self::limb_base_spec() * Self::limbs_value_spec(tail + right)
            );
            assert(
                Self::limbs_value_spec(tail + right)
                    == Self::limbs_value_spec(tail)
                        + pow_tail * right_val
            );
            let right_shifted = pow_tail * right_val;
            assert(
                Self::limbs_value_spec(whole)
                    == left[0] as nat
                        + Self::limb_base_spec()
                            * (Self::limbs_value_spec(tail) + right_shifted)
            );
            assert(
                Self::limb_base_spec() * (Self::limbs_value_spec(tail) + right_shifted)
                    == Self::limb_base_spec() * Self::limbs_value_spec(tail)
                        + Self::limb_base_spec() * right_shifted
            ) by (nonlinear_arith);
            assert(
                Self::limb_base_spec() * right_shifted
                    == (Self::limb_base_spec() * pow_tail) * right_val
            ) by {
                assert(
                    Self::limb_base_spec() * right_shifted
                        == Self::limb_base_spec() * (pow_tail * right_val)
                );
                assert(
                    Self::limb_base_spec() * (pow_tail * right_val)
                        == (Self::limb_base_spec() * pow_tail) * right_val
                ) by (nonlinear_arith);
            };
            assert(
                Self::limbs_value_spec(whole)
                    == (left[0] as nat + Self::limb_base_spec() * Self::limbs_value_spec(tail))
                        + (Self::limb_base_spec() * pow_tail) * right_val
            );
            Self::lemma_pow_base_succ(tail.len() as nat);
            assert(Self::pow_base_spec(left.len()) == Self::limb_base_spec() * pow_tail);
            assert(Self::limbs_value_spec(left) == left[0] as nat + Self::limb_base_spec() * Self::limbs_value_spec(tail));
            assert(
                Self::limbs_value_spec(whole)
                    == Self::limbs_value_spec(left)
                        + Self::pow_base_spec(left.len()) * Self::limbs_value_spec(right)
            );
        }
    }

    proof fn lemma_limbs_value_lt_pow_len(limbs: Seq<u32>)
        ensures
            Self::limbs_value_spec(limbs) < Self::pow_base_spec(limbs.len()),
        decreases limbs.len()
    {
        if limbs.len() == 0 {
            assert(Self::limbs_value_spec(limbs) == 0);
            assert(Self::pow_base_spec(0) == 1);
        } else {
            let n = (limbs.len() - 1) as nat;
            let prefix = limbs.subrange(0, n as int);
            let last = limbs[n as int];
            let last_nat = last as nat;
            let pow_n = Self::pow_base_spec(n);
            Self::lemma_limbs_value_lt_pow_len(prefix);
            Self::lemma_limbs_value_push(prefix, last);
            assert(prefix.push(last).len() == limbs.len());
            assert forall|i: int| 0 <= i < limbs.len() implies #[trigger] prefix.push(last)[i] == limbs[i] by {
                if i < prefix.len() {
                    assert(prefix.push(last)[i] == prefix[i]);
                    assert(prefix[i] == limbs[i]);
                } else {
                    assert(i == prefix.len());
                    assert(i == n as int);
                    assert(prefix.push(last)[i] == last);
                    assert(last == limbs[i]);
                }
            };
            assert(prefix.push(last) == limbs);
            assert(Self::limbs_value_spec(limbs) == Self::limbs_value_spec(prefix) + last_nat * pow_n);
            assert(Self::limb_base_spec() == 4_294_967_296);
            assert(last_nat <= 4_294_967_295);
            assert(last_nat + 1 <= Self::limb_base_spec());
            assert(Self::limbs_value_spec(prefix) < pow_n);
            let shifted = last_nat * pow_n;
            assert(
                Self::limbs_value_spec(prefix) + shifted
                    < pow_n + shifted
            );
            assert(
                pow_n + shifted
                    == shifted + pow_n
            ) by (nonlinear_arith);
            assert(
                (last_nat + 1) * pow_n
                    == last_nat * pow_n + 1 * pow_n
            ) by (nonlinear_arith);
            assert(1 * pow_n == pow_n);
            assert(last_nat * pow_n == shifted);
            assert(
                (last_nat + 1) * pow_n
                    == shifted + pow_n
            );
            assert(
                pow_n + shifted
                    == (last_nat + 1) * pow_n
            );
            Self::lemma_pow_ge_one(n);
            let headroom = Self::limb_base_spec() - (last_nat + 1);
            assert(0 <= headroom);
            assert(Self::limb_base_spec() == (last_nat + 1) + headroom);
            assert(
                Self::limb_base_spec() * pow_n
                    == ((last_nat + 1) + headroom) * pow_n
            );
            assert(
                ((last_nat + 1) + headroom) * pow_n
                    == (last_nat + 1) * pow_n + headroom * pow_n
            ) by (nonlinear_arith);
            assert(0 <= headroom * pow_n);
            assert(
                (last_nat + 1) * pow_n
                    <= Self::limb_base_spec() * pow_n
            );
            Self::lemma_pow_base_succ(n);
            assert(Self::pow_base_spec(limbs.len()) == Self::limb_base_spec() * pow_n);
            assert(Self::limbs_value_spec(limbs) < Self::pow_base_spec(limbs.len()));
        }
    }

    proof fn lemma_limbs_value_ge_pow_last_nonzero(limbs: Seq<u32>)
        requires
            limbs.len() > 0,
            limbs[(limbs.len() - 1) as int] != 0u32,
        ensures
            Self::pow_base_spec((limbs.len() - 1) as nat) <= Self::limbs_value_spec(limbs),
    {
        let n = (limbs.len() - 1) as nat;
        let prefix = limbs.subrange(0, n as int);
        let last = limbs[n as int];
        Self::lemma_limbs_value_push(prefix, last);
        assert(prefix.push(last).len() == limbs.len());
        assert forall|i: int| 0 <= i < limbs.len() implies #[trigger] prefix.push(last)[i] == limbs[i] by {
            if i < prefix.len() {
                assert(prefix.push(last)[i] == prefix[i]);
                assert(prefix[i] == limbs[i]);
            } else {
                assert(i == prefix.len());
                assert(i == n as int);
                assert(prefix.push(last)[i] == last);
                assert(last == limbs[i]);
            }
        };
        assert(prefix.push(last) == limbs);
        assert(Self::limbs_value_spec(limbs) == Self::limbs_value_spec(prefix) + last as nat * Self::pow_base_spec(n));
        assert(last != 0u32);
        assert(1 <= last as nat);
        Self::lemma_pow_ge_one(n);
        assert(
            last as nat * Self::pow_base_spec(n)
                == Self::pow_base_spec(n) + (last as nat - 1) * Self::pow_base_spec(n)
        ) by (nonlinear_arith);
        assert(0 <= (last as nat - 1) * Self::pow_base_spec(n));
        assert(Self::pow_base_spec(n) <= last as nat * Self::pow_base_spec(n));
        assert(Self::limbs_value_spec(prefix) >= 0);
        assert(last as nat * Self::pow_base_spec(n) <= Self::limbs_value_spec(prefix) + last as nat * Self::pow_base_spec(n));
        assert(Self::pow_base_spec(n) <= Self::limbs_value_spec(prefix) + last as nat * Self::pow_base_spec(n));
        assert(Self::pow_base_spec(n) <= Self::limbs_value_spec(limbs));
    }

    proof fn lemma_len_bound_from_value_upper_pow(limbs: Seq<u32>, upper_exp: nat)
        requires
            Self::canonical_limbs_spec(limbs),
            Self::limbs_value_spec(limbs) < Self::pow_base_spec(upper_exp),
        ensures
            limbs.len() <= upper_exp,
    {
        if limbs.len() > upper_exp {
            assert(limbs.len() > 0);
            assert(Self::canonical_limbs_spec(limbs));
            assert(limbs[(limbs.len() - 1) as int] != 0u32);
            let n = (limbs.len() - 1) as nat;
            assert(upper_exp + 1 <= limbs.len());
            assert(upper_exp + 1 <= n + 1);
            assert(upper_exp <= n);
            Self::lemma_pow_monotonic(upper_exp, n);
            Self::lemma_limbs_value_ge_pow_last_nonzero(limbs);
            assert(Self::pow_base_spec(upper_exp) <= Self::pow_base_spec(n));
            assert(Self::pow_base_spec(n) <= Self::limbs_value_spec(limbs));
            assert(Self::pow_base_spec(upper_exp) <= Self::limbs_value_spec(limbs));
            assert(Self::limbs_value_spec(limbs) < Self::pow_base_spec(upper_exp));
            assert(false);
        }
    }

    proof fn lemma_cmp_prefix_last_digit_gt(a: Seq<u32>, b: Seq<u32>)
        requires
            a.len() == b.len(),
            a.len() > 0,
            a[(a.len() - 1) as int] > b[(b.len() - 1) as int],
        ensures
            Self::limbs_value_spec(a) > Self::limbs_value_spec(b),
    {
        let n = (a.len() - 1) as nat;
        let a_prefix = a.subrange(0, n as int);
        let b_prefix = b.subrange(0, n as int);
        let a_last = a[n as int];
        let b_last = b[n as int];
        let a_last_nat = a_last as nat;
        let b_last_nat = b_last as nat;
        let pow_n = Self::pow_base_spec(n);

        Self::lemma_limbs_value_push(a_prefix, a_last);
        Self::lemma_limbs_value_push(b_prefix, b_last);
        assert(a_prefix.push(a_last).len() == a.len());
        assert(b_prefix.push(b_last).len() == b.len());
        assert forall|i: int| 0 <= i < a.len() implies #[trigger] a_prefix.push(a_last)[i] == a[i] by {
            if i < a_prefix.len() {
                assert(a_prefix.push(a_last)[i] == a_prefix[i]);
                assert(a_prefix[i] == a[i]);
            } else {
                assert(i == a_prefix.len());
                assert(i == n as int);
                assert(a_prefix.push(a_last)[i] == a_last);
                assert(a_last == a[i]);
            }
        };
        assert forall|i: int| 0 <= i < b.len() implies #[trigger] b_prefix.push(b_last)[i] == b[i] by {
            if i < b_prefix.len() {
                assert(b_prefix.push(b_last)[i] == b_prefix[i]);
                assert(b_prefix[i] == b[i]);
            } else {
                assert(i == b_prefix.len());
                assert(i == n as int);
                assert(b_prefix.push(b_last)[i] == b_last);
                assert(b_last == b[i]);
            }
        };
        assert(a_prefix.push(a_last) == a);
        assert(b_prefix.push(b_last) == b);
        assert(Self::limbs_value_spec(a) == Self::limbs_value_spec(a_prefix) + a_last_nat * pow_n);
        assert(Self::limbs_value_spec(b) == Self::limbs_value_spec(b_prefix) + b_last_nat * pow_n);
        Self::lemma_limbs_value_lt_pow_len(b_prefix);
        assert(Self::limbs_value_spec(b_prefix) < pow_n);
        let b_shifted = b_last_nat * pow_n;
        assert(
            Self::limbs_value_spec(b_prefix) + b_shifted
                < pow_n + b_shifted
        );
        assert(
            pow_n + b_shifted
                == b_shifted + pow_n
        ) by (nonlinear_arith);
        assert(
            (b_last_nat + 1) * pow_n
                == b_last_nat * pow_n + 1 * pow_n
        ) by (nonlinear_arith);
        assert(1 * pow_n == pow_n);
        assert(b_last_nat * pow_n == b_shifted);
        assert(
            (b_last_nat + 1) * pow_n
                == b_shifted + pow_n
        );
        assert(
            pow_n + b_shifted
                == (b_last_nat + 1) * pow_n
        );
        assert(a_last_nat > b_last_nat);
        assert(b_last_nat + 1 <= a_last_nat);
        assert(
            a_last_nat * pow_n
                == (b_last_nat + 1) * pow_n
                    + (a_last_nat - (b_last_nat + 1)) * pow_n
        ) by (nonlinear_arith);
        assert(0 <= (a_last_nat - (b_last_nat + 1)) * pow_n);
        assert(
            (b_last_nat + 1) * pow_n
                <= a_last_nat * pow_n
        );
        assert(
            Self::limbs_value_spec(b)
                < a_last_nat * pow_n
        );
        assert(Self::limbs_value_spec(a_prefix) >= 0);
        assert(
            a_last_nat * pow_n
                <= Self::limbs_value_spec(a_prefix) + a_last_nat * pow_n
        );
        assert(Self::limbs_value_spec(a) > Self::limbs_value_spec(b));
    }

    proof fn lemma_cmp_high_diff_gt(a: Seq<u32>, b: Seq<u32>, idx: nat)
        requires
            a.len() == b.len(),
            idx < a.len(),
            a[idx as int] > b[idx as int],
            forall|j: int| idx < j < a.len() ==> a[j] == b[j],
        ensures
            Self::limbs_value_spec(a) > Self::limbs_value_spec(b),
    {
        let split = idx + 1;
        let a_prefix = a.subrange(0, split as int);
        let b_prefix = b.subrange(0, split as int);
        let a_suffix = a.subrange(split as int, a.len() as int);
        let b_suffix = b.subrange(split as int, b.len() as int);

        assert(a == a_prefix + a_suffix);
        assert(b == b_prefix + b_suffix);
        assert(a_prefix.len() == split);
        assert(b_prefix.len() == split);
        assert(a_prefix[(a_prefix.len() - 1) as int] == a[idx as int]);
        assert(b_prefix[(b_prefix.len() - 1) as int] == b[idx as int]);
        assert(a_prefix[(a_prefix.len() - 1) as int] > b_prefix[(b_prefix.len() - 1) as int]);
        assert forall|j: int| 0 <= j < a_suffix.len() implies #[trigger] a_suffix[j] == b_suffix[j] by {
            assert(a_suffix[j] == a[(split + j) as int]);
            assert(b_suffix[j] == b[(split + j) as int]);
            assert(idx < split + j);
            assert(split + j < a.len());
            assert(a[(split + j) as int] == b[(split + j) as int]);
        };
        assert(a_suffix == b_suffix);

        Self::lemma_cmp_prefix_last_digit_gt(a_prefix, b_prefix);
        Self::lemma_limbs_value_append(a_prefix, a_suffix);
        Self::lemma_limbs_value_append(b_prefix, b_suffix);
        assert(
            Self::limbs_value_spec(a)
                == Self::limbs_value_spec(a_prefix)
                    + Self::pow_base_spec(a_prefix.len()) * Self::limbs_value_spec(a_suffix)
        );
        assert(
            Self::limbs_value_spec(b)
                == Self::limbs_value_spec(b_prefix)
                    + Self::pow_base_spec(b_prefix.len()) * Self::limbs_value_spec(b_suffix)
        );
        assert(
            Self::limbs_value_spec(b)
                == Self::limbs_value_spec(b_prefix)
                    + Self::pow_base_spec(b_prefix.len()) * Self::limbs_value_spec(a_suffix)
        );
        let suffix_shift = Self::pow_base_spec(a_prefix.len()) * Self::limbs_value_spec(a_suffix);
        assert(
            Self::limbs_value_spec(a)
                == Self::limbs_value_spec(a_prefix) + suffix_shift
        );
        assert(
            Self::limbs_value_spec(b)
                == Self::limbs_value_spec(b_prefix) + suffix_shift
        );
        assert(
            Self::limbs_value_spec(a_prefix) + suffix_shift
                > Self::limbs_value_spec(b_prefix) + suffix_shift
        );
        assert(Self::limbs_value_spec(a) > Self::limbs_value_spec(b));
    }

    proof fn lemma_trimmed_len_gt_implies_value_gt(a: Seq<u32>, alen: nat, b: Seq<u32>, blen: nat)
        requires
            alen <= a.len(),
            blen <= b.len(),
            forall|i: int| alen <= i < a.len() ==> a[i] == 0u32,
            forall|i: int| blen <= i < b.len() ==> b[i] == 0u32,
            blen < alen,
            alen > 0,
            a[(alen - 1) as int] != 0u32,
        ensures
            Self::limbs_value_spec(a) > Self::limbs_value_spec(b),
    {
        let a_trim = a.subrange(0, alen as int);
        let b_trim = b.subrange(0, blen as int);
        Self::lemma_limbs_value_trim_suffix_zeros(a, alen);
        Self::lemma_limbs_value_trim_suffix_zeros(b, blen);
        assert(Self::limbs_value_spec(a) == Self::limbs_value_spec(a_trim));
        assert(Self::limbs_value_spec(b) == Self::limbs_value_spec(b_trim));

        Self::lemma_limbs_value_lt_pow_len(b_trim);
        assert(Self::limbs_value_spec(b_trim) < Self::pow_base_spec(blen));
        assert(blen + 1 <= alen);
        assert((alen - 1) + 1 == alen);
        assert(blen <= (alen - 1) as nat);
        Self::lemma_pow_monotonic(blen, (alen - 1) as nat);
        assert(Self::pow_base_spec(blen) <= Self::pow_base_spec((alen - 1) as nat));
        assert(Self::limbs_value_spec(b_trim) < Self::pow_base_spec((alen - 1) as nat));

        assert(a_trim.len() == alen);
        assert(a_trim[(a_trim.len() - 1) as int] == a[(alen - 1) as int]);
        assert(a_trim[(a_trim.len() - 1) as int] != 0u32);
        Self::lemma_limbs_value_ge_pow_last_nonzero(a_trim);
        assert(Self::pow_base_spec((alen - 1) as nat) <= Self::limbs_value_spec(a_trim));
        assert(Self::limbs_value_spec(b_trim) < Self::limbs_value_spec(a_trim));
        assert(Self::limbs_value_spec(a) > Self::limbs_value_spec(b));
    }

    proof fn lemma_trimmed_high_diff_implies_value_gt(a: Seq<u32>, alen: nat, b: Seq<u32>, blen: nat, idx: nat)
        requires
            alen == blen,
            alen <= a.len(),
            blen <= b.len(),
            forall|i: int| alen <= i < a.len() ==> a[i] == 0u32,
            forall|i: int| blen <= i < b.len() ==> b[i] == 0u32,
            idx < alen,
            a[idx as int] > b[idx as int],
            forall|j: int| idx < j < alen ==> a[j] == b[j],
        ensures
            Self::limbs_value_spec(a) > Self::limbs_value_spec(b),
    {
        let a_trim = a.subrange(0, alen as int);
        let b_trim = b.subrange(0, blen as int);
        assert(a_trim.len() == alen);
        assert(b_trim.len() == blen);
        assert(a_trim.len() == b_trim.len());
        assert(a_trim[idx as int] == a[idx as int]);
        assert(b_trim[idx as int] == b[idx as int]);
        assert(a_trim[idx as int] > b_trim[idx as int]);
        assert forall|j: int| idx < j < a_trim.len() implies #[trigger] a_trim[j] == b_trim[j] by {
            assert(j < a_trim.len());
            assert(a_trim.len() == alen);
            assert(j < alen);
            assert(j < blen);
            assert(a_trim[j] == a[j]);
            assert(b_trim[j] == b[j]);
        };

        Self::lemma_cmp_high_diff_gt(a_trim, b_trim, idx);
        Self::lemma_limbs_value_trim_suffix_zeros(a, alen);
        Self::lemma_limbs_value_trim_suffix_zeros(b, blen);
        assert(Self::limbs_value_spec(a) == Self::limbs_value_spec(a_trim));
        assert(Self::limbs_value_spec(b) == Self::limbs_value_spec(b_trim));
        assert(Self::limbs_value_spec(a) > Self::limbs_value_spec(b));
    }

    proof fn lemma_model_zero_or_single_limb(&self)
        requires
            self.wf_spec(),
            self.limbs_le@.len() <= 1,
        ensures
            self.limbs_le@.len() == 0 ==> self.model@ == 0,
            self.limbs_le@.len() == 1 ==> self.model@ == self.limbs_le@[0] as nat,
    {
        if self.limbs_le@.len() == 0 {
            assert(self.model@ == Self::limbs_value_spec(self.limbs_le@));
            assert(Self::limbs_value_spec(self.limbs_le@) == 0);
        } else {
            assert(self.limbs_le@.len() == 1);
            assert(self.model@ == Self::limbs_value_spec(self.limbs_le@));
            assert(Self::limbs_value_spec(self.limbs_le@) == self.limbs_le@[0] as nat);
        }
    }

    proof fn lemma_div_rem_unique_nat(x: nat, d: nat, q1: nat, r1: nat, q2: nat, r2: nat)
        requires
            d > 0,
            x == q1 * d + r1,
            r1 < d,
            x == q2 * d + r2,
            r2 < d,
        ensures
            q1 == q2,
            r1 == r2,
    {
        let xi = x as int;
        let di = d as int;
        let q1i = q1 as int;
        let r1i = r1 as int;
        let q2i = q2 as int;
        let r2i = r2 as int;

        assert(di != 0);
        assert(0 <= r1i < di);
        assert(0 <= r2i < di);
        assert(xi == q1i * di + r1i);
        assert(xi == q2i * di + r2i);

        lemma_fundamental_div_mod_converse(xi, di, q1i, r1i);
        lemma_fundamental_div_mod_converse(xi, di, q2i, r2i);
        assert(q1i == xi / di);
        assert(q2i == xi / di);
        assert(q1i == q2i);
        assert(r1i == xi % di);
        assert(r2i == xi % di);
        assert(r1i == r2i);
        assert(q1 == q2);
        assert(r1 == r2);
    }

    proof fn lemma_mod_zero_implies_multiple_nat(x: nat, d: nat) -> (k: nat)
        requires
            d > 0,
            x % d == 0,
        ensures
            x == k * d,
    {
        let xi = x as int;
        let di = d as int;
        lemma_fundamental_div_mod(xi, di);
        assert((x % d) as int == xi % di);
        assert(xi % di == 0);
        assert(xi == di * (xi / di) + xi % di);
        assert(xi == di * (xi / di));
        assert((x / d) as int == xi / di);
        assert(xi == di * ((x / d) as int));
        assert(di * ((x / d) as int) == ((x / d) as int) * di) by (nonlinear_arith);
        assert(xi == ((x / d) as int) * di);
        assert(x == (x / d) * d);
        let k = x / d;
        assert(x == k * d);
        k
    }

    proof fn lemma_multiple_implies_mod_zero_nat(x: nat, d: nat, k: nat)
        requires
            d > 0,
            x == k * d,
        ensures
            x % d == 0,
    {
        let xi = x as int;
        let di = d as int;
        let ki = k as int;
        assert(di != 0);
        assert(0 <= 0 < di);
        assert(xi == ki * di + 0);
        lemma_fundamental_div_mod_converse(xi, di, ki, 0);
        assert(xi % di == 0);
        assert((x % d) as int == xi % di);
        assert(x % d == 0);
    }

    proof fn lemma_div_rem_shift_by_multiple_nat(x: nat, d: nat, k: nat)
        requires
            d > 0,
        ensures
            (x + k * d) / d == x / d + k,
            (x + k * d) % d == x % d,
    {
        let xi = x as int;
        let di = d as int;
        let ki = k as int;
        let x_shift = x + k * d;
        let x_shift_i = x_shift as int;

        lemma_fundamental_div_mod(xi, di);
        let qi = xi / di;
        let ri = xi % di;
        assert((x / d) as int == qi);
        assert((x % d) as int == ri);
        assert(0 <= ri < di);

        assert(x_shift_i == xi + ki * di);
        assert(xi == di * (xi / di) + xi % di);
        assert(di * qi + ri == di * (xi / di) + xi % di);
        assert(di * qi == qi * di) by (nonlinear_arith);
        assert(xi == qi * di + ri);
        assert(x_shift_i == (qi * di + ri) + ki * di);
        assert((qi * di + ri) + ki * di == (qi + ki) * di + ri) by (nonlinear_arith);
        assert(x_shift_i == (qi + ki) * di + ri);
        lemma_fundamental_div_mod_converse(x_shift_i, di, qi + ki, ri);
        assert(x_shift_i / di == qi + ki);
        assert(x_shift_i % di == ri);

        assert((x_shift / d) as int == x_shift_i / di);
        assert((x_shift % d) as int == x_shift_i % di);
        assert((x / d + k) as int == (x / d) as int + k as int);
        assert((x / d + k) as int == qi + ki);
        assert((x_shift / d) as int == (x / d + k) as int);
        assert((x_shift % d) as int == (x % d) as int);
        assert(x_shift / d == x / d + k);
        assert(x_shift % d == x % d);
    }

    pub proof fn lemma_model_div_shift_by_multiple_pos(a: &Self, d: &Self, k: nat)
        requires
            a.wf_spec(),
            d.wf_spec(),
            d.model@ > 0,
        ensures
            (a.model@ + k * d.model@) / d.model@ == a.model@ / d.model@ + k,
    {
        Self::lemma_div_rem_shift_by_multiple_nat(a.model@, d.model@, k);
    }

    pub proof fn lemma_model_rem_shift_by_multiple_pos(a: &Self, d: &Self, k: nat)
        requires
            a.wf_spec(),
            d.wf_spec(),
            d.model@ > 0,
        ensures
            (a.model@ + k * d.model@) % d.model@ == a.model@ % d.model@,
    {
        Self::lemma_div_rem_shift_by_multiple_nat(a.model@, d.model@, k);
    }

    proof fn lemma_div_monotonic_in_divisor_nat(x: nat, d1: nat, d2: nat)
        requires
            d1 > 0,
            d1 <= d2,
        ensures
            x / d2 <= x / d1,
    {
        let xi = x as int;
        let d1i = d1 as int;
        let d2i = d2 as int;

        assert(0 <= xi);
        assert(0 < d1i);
        assert(d1i <= d2i);
        assert(1 <= d1i <= d2i);
        lemma_div_is_ordered_by_denominator(xi, d1i, d2i);
        assert(xi / d1i >= xi / d2i);
        assert((x / d1) as int == xi / d1i);
        assert((x / d2) as int == xi / d2i);
        assert((x / d1) as int >= (x / d2) as int);
        assert(x / d2 <= x / d1);
    }

    pub proof fn lemma_model_div_monotonic_in_divisor_pos(a: &Self, d1: &Self, d2: &Self)
        requires
            a.wf_spec(),
            d1.wf_spec(),
            d2.wf_spec(),
            0 < d1.model@ <= d2.model@,
        ensures
            a.model@ / d2.model@ <= a.model@ / d1.model@,
    {
        Self::lemma_div_monotonic_in_divisor_nat(a.model@, d1.model@, d2.model@);
    }

    proof fn lemma_mod_add_compat_nat(x: nat, y: nat, m: nat)
        requires
            m > 0,
        ensures
            (x + y) % m == ((x % m) + (y % m)) % m,
    {
        let xi = x as int;
        let yi = y as int;
        let mi = m as int;
        lemma_add_mod_noop(xi, yi, mi);
        assert((x % m) as int == xi % mi);
        assert((y % m) as int == yi % mi);
        assert(((x + y) % m) as int == (xi + yi) % mi);
        assert((((x % m) + (y % m)) % m) as int == ((xi % mi) + (yi % mi)) % mi);
        assert(((xi % mi) + (yi % mi)) % mi == (xi + yi) % mi);
        assert((((x % m) + (y % m)) % m) as int == ((x + y) % m) as int);
        assert((x + y) % m == ((x % m) + (y % m)) % m);
    }

    pub proof fn lemma_model_add_mod_compat(a: &Self, b: &Self, m: &Self)
        requires
            a.wf_spec(),
            b.wf_spec(),
            m.wf_spec(),
            m.model@ > 0,
        ensures
            (a.model@ + b.model@) % m.model@
                == ((a.model@ % m.model@) + (b.model@ % m.model@)) % m.model@,
    {
        Self::lemma_mod_add_compat_nat(a.model@, b.model@, m.model@);
    }

    proof fn lemma_mod_mul_compat_nat(x: nat, y: nat, m: nat)
        requires
            m > 0,
        ensures
            (x * y) % m == ((x % m) * (y % m)) % m,
    {
        let xi = x as int;
        let yi = y as int;
        let mi = m as int;
        lemma_mul_mod_noop(xi, yi, mi);
        assert((x % m) as int == xi % mi);
        assert((y % m) as int == yi % mi);
        assert(((x * y) % m) as int == (xi * yi) % mi);
        assert((((x % m) * (y % m)) % m) as int == (((xi % mi) * (yi % mi)) % mi));
        assert((((xi % mi) * (yi % mi)) % mi) == (xi * yi) % mi);
        assert((((x % m) * (y % m)) % m) as int == ((x * y) % m) as int);
        assert((x * y) % m == ((x % m) * (y % m)) % m);
    }

    pub proof fn lemma_model_mul_mod_compat(a: &Self, b: &Self, m: &Self)
        requires
            a.wf_spec(),
            b.wf_spec(),
            m.wf_spec(),
            m.model@ > 0,
        ensures
            (a.model@ * b.model@) % m.model@
                == ((a.model@ % m.model@) * (b.model@ % m.model@)) % m.model@,
    {
        Self::lemma_mod_mul_compat_nat(a.model@, b.model@, m.model@);
    }

    proof fn lemma_mod_congruence_add_nat(a: nat, b: nat, c: nat, m: nat)
        requires
            m > 0,
            a % m == b % m,
        ensures
            (a + c) % m == (b + c) % m,
    {
        Self::lemma_mod_add_compat_nat(a, c, m);
        Self::lemma_mod_add_compat_nat(b, c, m);
        assert((a + c) % m == ((a % m) + (c % m)) % m);
        assert((b + c) % m == ((b % m) + (c % m)) % m);
        assert(((a % m) + (c % m)) % m == ((b % m) + (c % m)) % m);
        assert((a + c) % m == (b + c) % m);
    }

    pub proof fn lemma_model_mod_congruence_add(a: &Self, b: &Self, c: &Self, m: &Self)
        requires
            a.wf_spec(),
            b.wf_spec(),
            c.wf_spec(),
            m.wf_spec(),
            m.model@ > 0,
            a.model@ % m.model@ == b.model@ % m.model@,
        ensures
            (a.model@ + c.model@) % m.model@ == (b.model@ + c.model@) % m.model@,
    {
        Self::lemma_mod_congruence_add_nat(a.model@, b.model@, c.model@, m.model@);
    }

    proof fn lemma_mod_congruence_mul_nat(a: nat, b: nat, c: nat, m: nat)
        requires
            m > 0,
            a % m == b % m,
        ensures
            (a * c) % m == (b * c) % m,
    {
        Self::lemma_mod_mul_compat_nat(a, c, m);
        Self::lemma_mod_mul_compat_nat(b, c, m);
        assert((a * c) % m == ((a % m) * (c % m)) % m);
        assert((b * c) % m == ((b % m) * (c % m)) % m);
        assert(((a % m) * (c % m)) % m == ((b % m) * (c % m)) % m);
        assert((a * c) % m == (b * c) % m);
    }

    pub proof fn lemma_model_mod_congruence_mul(a: &Self, b: &Self, c: &Self, m: &Self)
        requires
            a.wf_spec(),
            b.wf_spec(),
            c.wf_spec(),
            m.wf_spec(),
            m.model@ > 0,
            a.model@ % m.model@ == b.model@ % m.model@,
        ensures
            (a.model@ * c.model@) % m.model@ == (b.model@ * c.model@) % m.model@,
    {
        Self::lemma_mod_congruence_mul_nat(a.model@, b.model@, c.model@, m.model@);
    }

    fn from_parts(limbs_le: Vec<u32>, Ghost(model): Ghost<nat>) -> (out: Self)
        requires
            model == Self::limbs_value_spec(limbs_le@),
            Self::canonical_limbs_spec(limbs_le@),
        ensures
            out.limbs_le@ == limbs_le@,
            out.model@ == model,
            out.wf_spec(),
    {
        let out = RuntimeBigNatWitness { limbs_le, model: Ghost(model) };
        proof {
            assert(out.limbs_le@ == limbs_le@);
            assert(out.model@ == model);
            assert(out.wf_spec());
        }
        out
    }

    pub fn zero() -> (out: Self)
        ensures
            out.model@ == 0,
            out.wf_spec(),
    {
        let limbs_le: Vec<u32> = Vec::new();
        let out = Self::from_parts(limbs_le, Ghost(0));
        proof {
            assert(Self::limbs_value_spec(Seq::<u32>::empty()) == 0);
            assert(Self::canonical_limbs_spec(Seq::<u32>::empty()));
        }
        out
    }

    pub fn from_u32(x: u32) -> (out: Self)
        ensures
            out.model@ == x as nat,
            out.wf_spec(),
    {
        if x == 0 {
            Self::zero()
        } else {
            let mut limbs_le: Vec<u32> = Vec::new();
            limbs_le.push(x);
            proof {
                assert(limbs_le@.len() == 1);
                assert(limbs_le@[0] == x);
                assert(Self::limbs_value_spec(limbs_le@) == x as nat);
                assert(Self::canonical_limbs_spec(limbs_le@));
            }
            Self::from_parts(limbs_le, Ghost(x as nat))
        }
    }

    pub fn from_u64(x: u64) -> (out: Self)
        ensures
            out.model@ == x as nat,
            out.wf_spec(),
    {
        let base_u64 = 4_294_967_296u64;
        let lo_u64 = x % base_u64;
        let hi_u64 = x / base_u64;
        let lo = lo_u64 as u32;
        let hi = hi_u64 as u32;
        let out = Self::from_two_limbs(lo, hi);
        proof {
            assert(x == hi_u64 * base_u64 + lo_u64);
            assert(lo_u64 < base_u64);
            assert(hi_u64 <= 4_294_967_295u64);
            assert(lo as u64 == lo_u64);
            assert(hi as u64 == hi_u64);
            assert(out.model@ == lo as nat + Self::limb_base_spec() * hi as nat);
            assert(Self::limb_base_spec() == 4_294_967_296);
            assert(x == hi as u64 * 4_294_967_296u64 + lo as u64);
            assert(x as nat == hi as nat * 4_294_967_296nat + lo as nat);
            assert(out.model@ == x as nat);
        }
        out
    }

    pub fn from_two_limbs(lo: u32, hi: u32) -> (out: Self)
        ensures
            out.model@ == lo as nat + Self::limb_base_spec() * hi as nat,
            out.wf_spec(),
    {
        if hi == 0 {
            let out = Self::from_u32(lo);
            proof {
                assert(Self::limb_base_spec() * hi as nat == 0);
                assert(out.model@ == lo as nat);
                assert(out.model@ == lo as nat + Self::limb_base_spec() * hi as nat);
            }
            out
        } else {
            let mut limbs_le: Vec<u32> = Vec::new();
            limbs_le.push(lo);
            limbs_le.push(hi);
            proof {
                assert(limbs_le@.len() == 2);
                assert(limbs_le@[0] == lo);
                assert(limbs_le@[1] == hi);
                assert(limbs_le@.subrange(1, limbs_le@.len() as int).len() == 1);
                assert(limbs_le@.subrange(1, limbs_le@.len() as int)[0] == hi);
                assert(Self::limbs_value_spec(limbs_le@.subrange(1, limbs_le@.len() as int)) == hi as nat);
                assert(Self::limbs_value_spec(limbs_le@) == lo as nat + Self::limb_base_spec() * hi as nat);
                assert(Self::canonical_limbs_spec(limbs_le@));
            }
            Self::from_parts(limbs_le, Ghost(lo as nat + Self::limb_base_spec() * hi as nat))
        }
    }

    pub fn add(&self, rhs: &Self) -> (out: Self)
        requires
            self.wf_spec(),
            rhs.wf_spec(),
        ensures
            out.wf_spec(),
            out.model@ == self.model@ + rhs.model@,
    {
        let out = self.add_limbwise_small_total(rhs);
        proof {
            assert(self.model@ == Self::limbs_value_spec(self.limbs_le@));
            assert(rhs.model@ == Self::limbs_value_spec(rhs.limbs_le@));
            assert(
                out.model@
                    == Self::limbs_value_spec(self.limbs_le@)
                        + Self::limbs_value_spec(rhs.limbs_le@)
            );
            assert(out.model@ == self.model@ + rhs.model@);
        }
        out
    }

    pub fn mul(&self, rhs: &Self) -> (out: Self)
        requires
            self.wf_spec(),
            rhs.wf_spec(),
        ensures
            out.wf_spec(),
            out.model@ == self.model@ * rhs.model@,
            rhs.model@ == 0 ==> out.model@ == 0,
            rhs.model@ == 1 ==> out.model@ == self.model@,
            self.model@ == 0 ==> out.model@ == 0,
            self.model@ == 1 ==> out.model@ == rhs.model@,
    {
        let out = self.mul_limbwise_small_total(rhs);
        proof {
            assert(self.model@ == Self::limbs_value_spec(self.limbs_le@));
            assert(rhs.model@ == Self::limbs_value_spec(rhs.limbs_le@));
            assert(
                out.model@
                    == Self::limbs_value_spec(self.limbs_le@)
                        * Self::limbs_value_spec(rhs.limbs_le@)
            );
            assert(out.model@ == self.model@ * rhs.model@);
            if rhs.model@ == 0 {
                assert(out.model@ == self.model@ * 0);
                assert(out.model@ == 0);
            }
            if rhs.model@ == 1 {
                assert(out.model@ == self.model@ * 1);
                assert(out.model@ == self.model@);
            }
            if self.model@ == 0 {
                assert(out.model@ == 0 * rhs.model@);
                assert(out.model@ == 0);
            }
            if self.model@ == 1 {
                assert(out.model@ == 1 * rhs.model@);
                assert(out.model@ == rhs.model@);
            }
        }
        out
    }

    pub fn div(&self, rhs: &Self) -> (out: Self)
        requires
            self.wf_spec(),
            rhs.wf_spec(),
        ensures
            out.wf_spec(),
            rhs.model@ == 0 ==> out.model@ == 0,
            rhs.model@ > 0 ==> out.model@ * rhs.model@ <= self.model@,
            rhs.model@ > 0 ==> self.model@ < (out.model@ + 1) * rhs.model@,
            rhs.model@ > 0 ==> out.model@ == self.model@ / rhs.model@,
            rhs.model@ > 0 && rhs.model@ == 1 ==> out.model@ == self.model@,
            rhs.model@ > 0 && self.model@ < rhs.model@ ==> out.model@ == 0,
            rhs.model@ > 0 && self.model@ == rhs.model@ ==> out.model@ == 1,
    {
        let out = self.div_limbwise_small_total(rhs);
        proof {
            assert(self.model@ == Self::limbs_value_spec(self.limbs_le@));
            assert(rhs.model@ == Self::limbs_value_spec(rhs.limbs_le@));
            if rhs.model@ == 0 {
                assert(Self::limbs_value_spec(rhs.limbs_le@) == 0);
                assert(out.model@ == 0);
            }
            if rhs.model@ > 0 {
                assert(Self::limbs_value_spec(rhs.limbs_le@) > 0);
                assert(
                    out.model@ * Self::limbs_value_spec(rhs.limbs_le@)
                        <= Self::limbs_value_spec(self.limbs_le@)
                );
                assert(
                    Self::limbs_value_spec(self.limbs_le@)
                        < (out.model@ + 1) * Self::limbs_value_spec(rhs.limbs_le@)
                );
                assert(
                    out.model@
                        == Self::limbs_value_spec(self.limbs_le@)
                            / Self::limbs_value_spec(rhs.limbs_le@)
                );
                assert(out.model@ * rhs.model@ <= self.model@);
                assert(self.model@ < (out.model@ + 1) * rhs.model@);
                assert(out.model@ == self.model@ / rhs.model@);

                if rhs.model@ == 1 {
                    assert(self.model@ / rhs.model@ == self.model@);
                    assert(out.model@ == self.model@);
                }
                if self.model@ < rhs.model@ {
                    let xi = self.model@ as int;
                    let di = rhs.model@ as int;
                    assert(0 <= xi < di);
                    lemma_basic_div(xi, di);
                    assert(xi / di == 0);
                    assert((self.model@ / rhs.model@) as int == xi / di);
                    assert(self.model@ / rhs.model@ == 0);
                    assert(out.model@ == 0);
                }
                if self.model@ == rhs.model@ {
                    assert(self.model@ / rhs.model@ == rhs.model@ / rhs.model@);
                    assert(rhs.model@ / rhs.model@ == 1);
                    assert(out.model@ == 1);
                }
            }
        }
        out
    }

    pub fn rem(&self, rhs: &Self) -> (out: Self)
        requires
            self.wf_spec(),
            rhs.wf_spec(),
        ensures
            out.wf_spec(),
            rhs.model@ == 0 ==> out.model@ == 0,
            rhs.model@ > 0 ==> out.model@ < rhs.model@,
            rhs.model@ > 0 ==> out.model@ == self.model@ % rhs.model@,
            rhs.model@ > 0
                ==> (out.model@ == 0 <==> exists|k: nat| #[trigger] (k * rhs.model@) == self.model@),
            rhs.model@ > 0 && rhs.model@ == 1 ==> out.model@ == 0,
            rhs.model@ > 0 && self.model@ < rhs.model@ ==> out.model@ == self.model@,
            rhs.model@ > 0 && self.model@ == rhs.model@ ==> out.model@ == 0,
    {
        let out = self.rem_limbwise_small_total(rhs);
        proof {
            assert(self.model@ == Self::limbs_value_spec(self.limbs_le@));
            assert(rhs.model@ == Self::limbs_value_spec(rhs.limbs_le@));
            if rhs.model@ == 0 {
                assert(Self::limbs_value_spec(rhs.limbs_le@) == 0);
                assert(out.model@ == 0);
            }
            if rhs.model@ > 0 {
                assert(Self::limbs_value_spec(rhs.limbs_le@) > 0);
                assert(out.model@ < Self::limbs_value_spec(rhs.limbs_le@));
                assert(
                    out.model@
                        == Self::limbs_value_spec(self.limbs_le@)
                            % Self::limbs_value_spec(rhs.limbs_le@)
                );
                assert(out.model@ < rhs.model@);
                assert(out.model@ == self.model@ % rhs.model@);

                if out.model@ == 0 {
                    assert(self.model@ % rhs.model@ == 0);
                    let k = Self::lemma_mod_zero_implies_multiple_nat(self.model@, rhs.model@);
                    assert(self.model@ == k * rhs.model@);
                    assert(exists|kw: nat| #[trigger] (kw * rhs.model@) == self.model@) by {
                        let kw = k;
                        assert(kw * rhs.model@ == self.model@);
                    };
                }
                if exists|kw: nat| #[trigger] (kw * rhs.model@) == self.model@ {
                    let k = choose|kw: nat| #[trigger] (kw * rhs.model@) == self.model@;
                    assert(k * rhs.model@ == self.model@);
                    assert(self.model@ == k * rhs.model@);
                    Self::lemma_multiple_implies_mod_zero_nat(self.model@, rhs.model@, k);
                    assert(self.model@ % rhs.model@ == 0);
                    assert(out.model@ == 0);
                }

                if rhs.model@ == 1 {
                    assert(out.model@ < 1);
                    assert(out.model@ == 0);
                }
                if self.model@ < rhs.model@ {
                    lemma_small_mod(self.model@, rhs.model@);
                    assert(self.model@ % rhs.model@ == self.model@);
                    assert(out.model@ == self.model@);
                }
                if self.model@ == rhs.model@ {
                    let di = rhs.model@ as int;
                    lemma_mod_self_0(di);
                    assert(di % di == 0);
                    assert((rhs.model@ % rhs.model@) as int == di % di);
                    assert(rhs.model@ % rhs.model@ == 0);
                    assert(self.model@ % rhs.model@ == 0);
                    assert(out.model@ == 0);
                }
            }
        }
        out
    }

    pub fn div_rem(&self, rhs: &Self) -> (out: (Self, Self))
        requires
            self.wf_spec(),
            rhs.wf_spec(),
        ensures
            out.0.wf_spec(),
            out.1.wf_spec(),
            rhs.model@ == 0 ==> out.0.model@ == 0 && out.1.model@ == 0,
            rhs.model@ > 0 ==> self.model@ == out.0.model@ * rhs.model@ + out.1.model@,
            rhs.model@ > 0 ==> out.1.model@ < rhs.model@,
            rhs.model@ > 0 ==> out.0.model@ == self.model@ / rhs.model@,
            rhs.model@ > 0 ==> out.1.model@ == self.model@ % rhs.model@,
    {
        let out = self.div_rem_limbwise_small_total(rhs);
        proof {
            assert(self.model@ == Self::limbs_value_spec(self.limbs_le@));
            assert(rhs.model@ == Self::limbs_value_spec(rhs.limbs_le@));
            if rhs.model@ == 0 {
                assert(Self::limbs_value_spec(rhs.limbs_le@) == 0);
                assert(out.0.model@ == 0);
                assert(out.1.model@ == 0);
            }
            if rhs.model@ > 0 {
                assert(Self::limbs_value_spec(rhs.limbs_le@) > 0);
                assert(
                    Self::limbs_value_spec(self.limbs_le@)
                        == out.0.model@ * Self::limbs_value_spec(rhs.limbs_le@) + out.1.model@
                );
                assert(out.1.model@ < Self::limbs_value_spec(rhs.limbs_le@));
                assert(
                    out.0.model@
                        == Self::limbs_value_spec(self.limbs_le@)
                            / Self::limbs_value_spec(rhs.limbs_le@)
                );
                assert(
                    out.1.model@
                        == Self::limbs_value_spec(self.limbs_le@)
                            % Self::limbs_value_spec(rhs.limbs_le@)
                );
                assert(self.model@ == out.0.model@ * rhs.model@ + out.1.model@);
                assert(out.1.model@ < rhs.model@);
                assert(out.0.model@ == self.model@ / rhs.model@);
                assert(out.1.model@ == self.model@ % rhs.model@);
            }
        }
        out
    }

    pub fn is_zero(&self) -> (out: bool)
        requires
            self.wf_spec(),
        ensures
            out == (self.model@ == 0),
    {
        let out = self.limbs_le.len() == 0;
        proof {
            if out {
                assert(self.limbs_le@.len() == 0);
                assert(self.model@ == Self::limbs_value_spec(self.limbs_le@));
                assert(Self::limbs_value_spec(self.limbs_le@) == 0);
                assert(self.model@ == 0);
            } else {
                assert(self.limbs_le@.len() > 0);
                assert(Self::canonical_limbs_spec(self.limbs_le@));
                let last = (self.limbs_le@.len() - 1) as nat;
                assert(self.limbs_le@[last as int] != 0u32);
                Self::lemma_limbs_value_ge_pow_last_nonzero(self.limbs_le@);
                Self::lemma_pow_ge_one(last);
                assert(Self::pow_base_spec(last) <= Self::limbs_value_spec(self.limbs_le@));
                assert(Self::pow_base_spec(last) >= 1);
                assert(Self::limbs_value_spec(self.limbs_le@) >= 1);
                assert(self.model@ == Self::limbs_value_spec(self.limbs_le@));
                assert(self.model@ != 0);
            }
        }
        out
    }

    pub fn limbs_le(&self) -> (out: &[u32])
        ensures
            out@ == self.limbs_le@,
    {
        &self.limbs_le
    }

    /// First constructive limb-wise addition milestone:
    /// supports operands represented by at most one limb each.
    pub fn add_limbwise_small(&self, rhs: &Self) -> (out: Self)
        requires
            self.wf_spec(),
            rhs.wf_spec(),
            self.limbs_le@.len() <= 1,
            rhs.limbs_le@.len() <= 1,
        ensures
            out.wf_spec(),
            out.model@ == self.model@ + rhs.model@,
    {
        let a0 = if self.limbs_le.len() == 0 { 0u32 } else { self.limbs_le[0] };
        let b0 = if rhs.limbs_le.len() == 0 { 0u32 } else { rhs.limbs_le[0] };

        let sum = a0 as u64 + b0 as u64;
        let base_u64 = 4_294_967_296u64;
        let (lo, hi) = if sum < base_u64 {
            (sum as u32, 0u32)
        } else {
            ((sum - base_u64) as u32, 1u32)
        };

        let out = Self::from_two_limbs(lo, hi);
        proof {
            self.lemma_model_zero_or_single_limb();
            rhs.lemma_model_zero_or_single_limb();

            if self.limbs_le@.len() == 0 {
                assert(a0 == 0u32);
                assert(self.model@ == 0);
                assert(self.model@ == a0 as nat);
            } else {
                assert(self.limbs_le@.len() == 1);
                assert(a0 == self.limbs_le@[0]);
                assert(self.model@ == self.limbs_le@[0] as nat);
                assert(self.model@ == a0 as nat);
            }

            if rhs.limbs_le@.len() == 0 {
                assert(b0 == 0u32);
                assert(rhs.model@ == 0);
                assert(rhs.model@ == b0 as nat);
            } else {
                assert(rhs.limbs_le@.len() == 1);
                assert(b0 == rhs.limbs_le@[0]);
                assert(rhs.model@ == rhs.limbs_le@[0] as nat);
                assert(rhs.model@ == b0 as nat);
            }

            assert(a0 as nat + rhs.model@ == a0 as nat + b0 as nat);
            assert(self.model@ + rhs.model@ == a0 as nat + b0 as nat);

            if sum < base_u64 {
                assert(hi == 0u32);
                assert(lo as u64 == sum);
                assert(lo as nat == sum as nat);
                assert(sum as nat == a0 as nat + b0 as nat);
                assert(out.model@ == lo as nat + Self::limb_base_spec() * hi as nat);
                assert(Self::limb_base_spec() * hi as nat == 0);
                assert(out.model@ == lo as nat);
                assert(out.model@ == sum as nat);
                assert(out.model@ == self.model@ + rhs.model@);
            } else {
                assert(hi == 1u32);
                assert(base_u64 <= sum);
                assert(sum < 2 * base_u64);
                assert((sum - base_u64) < base_u64);
                assert(lo as u64 == sum - base_u64);
                assert(lo as nat == (sum - base_u64) as nat);
                assert(sum as nat == a0 as nat + b0 as nat);
                assert(out.model@ == lo as nat + Self::limb_base_spec() * hi as nat);
                assert(Self::limb_base_spec() * hi as nat == Self::limb_base_spec());
                assert(out.model@ == (sum - base_u64) as nat + Self::limb_base_spec());
                assert(base_u64 as nat == Self::limb_base_spec());
                assert(out.model@ == sum as nat);
                assert(out.model@ == self.model@ + rhs.model@);
            }
        }
        out
    }

    /// Total limb-wise addition helper used by scalar witness plumbing.
    ///
    /// Computes carry-propagating multi-limb addition over little-endian limbs,
    /// then canonicalizes the output by trimming trailing zero limbs.
    pub fn add_limbwise_small_total(&self, rhs: &Self) -> (out: Self)
        ensures
            out.wf_spec(),
            out.model@ == Self::limbs_value_spec(self.limbs_le@) + Self::limbs_value_spec(rhs.limbs_le@),
    {
        let alen = Self::trimmed_len_exec(&self.limbs_le);
        let blen = Self::trimmed_len_exec(&rhs.limbs_le);
        assert(alen <= self.limbs_le.len());
        assert(blen <= rhs.limbs_le.len());
        let ghost alen_nat = alen as nat;
        let ghost blen_nat = blen as nat;
        proof {
            assert(alen_nat == alen as nat);
            assert(blen_nat == blen as nat);
        }
        let n = if alen > blen { alen } else { blen };
        let mut out_limbs: Vec<u32> = Vec::new();
        let mut i: usize = 0;
        let mut carry: u64 = 0u64;
        while i < n
            invariant
                i <= n,
                alen <= self.limbs_le.len(),
                blen <= rhs.limbs_le.len(),
                out_limbs@.len() == i,
                carry == 0u64 || carry == 1u64,
                Self::limbs_value_spec(out_limbs@) + carry as nat * Self::pow_base_spec(i as nat)
                    == Self::prefix_sum_spec(self.limbs_le@, alen as nat, i as nat)
                        + Self::prefix_sum_spec(rhs.limbs_le@, blen as nat, i as nat),
            decreases n - i,
        {
            let i_old = i;
            let carry_in = carry;
            let ghost i_nat = i_old as nat;
            let a = if i < alen {
                assert(i < self.limbs_le.len());
                self.limbs_le[i] as u64
            } else {
                0u64
            };
            let b = if i < blen {
                assert(i < rhs.limbs_le.len());
                rhs.limbs_le[i] as u64
            } else {
                0u64
            };
            let sum = a + b + carry_in;
            let (digit, next_carry) = if sum >= 4_294_967_296u64 {
                assert(sum == a + b + carry_in);
                assert(a <= 4_294_967_295u64);
                assert(b <= 4_294_967_295u64);
                assert(carry_in <= 1u64);
                assert(sum <= 8_589_934_591u64);
                assert(sum >= 4_294_967_296u64);
                assert(sum - 4_294_967_296u64 <= 4_294_967_295u64);
                let d = (sum - 4_294_967_296u64) as u32;
                (d, 1u64)
            } else {
                assert(sum == a + b + carry_in);
                assert(a <= 4_294_967_295u64);
                assert(b <= 4_294_967_295u64);
                assert(carry_in <= 1u64);
                assert(sum <= 8_589_934_591u64);
                assert(!(sum >= 4_294_967_296u64));
                assert(sum < 4_294_967_296u64);
                assert(sum <= 4_294_967_295u64);
                let d = sum as u32;
                (d, 0u64)
            };
            proof {
                let a_nat = a as nat;
                let b_nat = b as nat;
                let carry_nat = carry_in as nat;
                let digit_nat = digit as nat;
                let next_carry_nat = next_carry as nat;
                assert(i_nat == i_old as nat);
                if i_old < alen {
                    assert(i_old < self.limbs_le.len());
                    assert((i_old as int) < (alen as int));
                    assert(i_nat < alen as nat);
                    assert(i_nat < self.limbs_le@.len());
                    assert(a == self.limbs_le[i_old as int] as u64);
                    assert(a_nat == self.limbs_le@[i_old as int] as nat);
                    assert(a_nat < Self::limb_base_spec());
                    assert(
                        Self::limb_or_zero_spec(self.limbs_le@, alen as nat, i_nat)
                            == self.limbs_le@[i_old as int] as nat
                    );
                    assert(Self::limb_or_zero_spec(self.limbs_le@, alen as nat, i_nat) == a_nat);
                } else {
                    assert(a == 0u64);
                    assert(a_nat == 0);
                    assert(a_nat < Self::limb_base_spec());
                    assert((alen as int) <= (i_old as int));
                    assert(alen as nat <= i_nat);
                    Self::lemma_limb_or_zero_past_logical_len(self.limbs_le@, alen as nat, i_nat);
                    assert(Self::limb_or_zero_spec(self.limbs_le@, alen as nat, i_nat) == a_nat);
                }
                if i_old < blen {
                    assert(i_old < rhs.limbs_le.len());
                    assert((i_old as int) < (blen as int));
                    assert(i_nat < blen as nat);
                    assert(i_nat < rhs.limbs_le@.len());
                    assert(b == rhs.limbs_le[i_old as int] as u64);
                    assert(b_nat == rhs.limbs_le@[i_old as int] as nat);
                    assert(b_nat < Self::limb_base_spec());
                    assert(
                        Self::limb_or_zero_spec(rhs.limbs_le@, blen as nat, i_nat)
                            == rhs.limbs_le@[i_old as int] as nat
                    );
                    assert(Self::limb_or_zero_spec(rhs.limbs_le@, blen as nat, i_nat) == b_nat);
                } else {
                    assert(b == 0u64);
                    assert(b_nat == 0);
                    assert(b_nat < Self::limb_base_spec());
                    assert((blen as int) <= (i_old as int));
                    assert(blen as nat <= i_nat);
                    Self::lemma_limb_or_zero_past_logical_len(rhs.limbs_le@, blen as nat, i_nat);
                    assert(Self::limb_or_zero_spec(rhs.limbs_le@, blen as nat, i_nat) == b_nat);
                }
                assert(carry_in == 0u64 || carry_in == 1u64);
                assert(carry_nat <= 1);
                Self::lemma_add_digit_carry_decompose(a_nat, b_nat, carry_nat);

                assert(sum == a + b + carry_in);
                assert(sum as nat == a_nat + b_nat + carry_nat);
                if sum >= 4_294_967_296u64 {
                    assert(next_carry == 1u64);
                    assert(next_carry_nat == 1);
                    assert(digit as u64 == sum - 4_294_967_296u64);
                    assert(digit_nat == (sum - 4_294_967_296u64) as nat);
                    assert(Self::limb_base_spec() == 4_294_967_296);
                    assert((sum - 4_294_967_296u64) as nat + Self::limb_base_spec() == sum as nat);
                    assert(digit_nat + next_carry_nat * Self::limb_base_spec() == sum as nat);
                } else {
                    assert(next_carry == 0u64);
                    assert(next_carry_nat == 0);
                    assert(digit as u64 == sum);
                    assert(digit_nat == sum as nat);
                    assert(digit_nat + next_carry_nat * Self::limb_base_spec() == sum as nat);
                }
                assert(digit_nat + next_carry_nat * Self::limb_base_spec() == a_nat + b_nat + carry_nat);

                Self::lemma_prefix_sum_step(self.limbs_le@, alen as nat, i_nat);
                Self::lemma_prefix_sum_step(rhs.limbs_le@, blen as nat, i_nat);
                Self::lemma_pow_base_succ(i_nat);
                Self::lemma_add_prefix_step(
                    Self::limbs_value_spec(out_limbs@),
                    Self::prefix_sum_spec(self.limbs_le@, alen as nat, i_nat),
                    Self::prefix_sum_spec(rhs.limbs_le@, blen as nat, i_nat),
                    digit_nat,
                    a_nat,
                    b_nat,
                    carry_nat,
                    next_carry_nat,
                    Self::pow_base_spec(i_nat),
                    Self::pow_base_spec(i_nat + 1),
                );
                Self::lemma_limbs_value_push(out_limbs@, digit);
                assert(out_limbs@.push(digit).len() == i_nat + 1);
                assert(
                    Self::prefix_sum_spec(self.limbs_le@, alen as nat, i_nat + 1)
                        == Self::prefix_sum_spec(self.limbs_le@, alen as nat, i_nat)
                            + Self::limb_or_zero_spec(self.limbs_le@, alen as nat, i_nat)
                                * Self::pow_base_spec(i_nat)
                );
                assert(
                    Self::prefix_sum_spec(rhs.limbs_le@, blen as nat, i_nat + 1)
                        == Self::prefix_sum_spec(rhs.limbs_le@, blen as nat, i_nat)
                            + Self::limb_or_zero_spec(rhs.limbs_le@, blen as nat, i_nat)
                                * Self::pow_base_spec(i_nat)
                );
                assert(
                    Self::prefix_sum_spec(self.limbs_le@, alen as nat, i_nat + 1)
                        == Self::prefix_sum_spec(self.limbs_le@, alen as nat, i_nat)
                            + a_nat * Self::pow_base_spec(i_nat)
                );
                assert(
                    Self::prefix_sum_spec(rhs.limbs_le@, blen as nat, i_nat + 1)
                        == Self::prefix_sum_spec(rhs.limbs_le@, blen as nat, i_nat)
                            + b_nat * Self::pow_base_spec(i_nat)
                );
                assert(
                    Self::limbs_value_spec(out_limbs@.push(digit))
                        + next_carry_nat * Self::pow_base_spec(i_nat + 1)
                        == Self::prefix_sum_spec(self.limbs_le@, alen as nat, i_nat + 1)
                            + Self::prefix_sum_spec(rhs.limbs_le@, blen as nat, i_nat + 1)
                );
            }
            carry = next_carry;
            out_limbs.push(digit);
            i = i + 1;
        }
        assert(i == n);
        assert(out_limbs@.len() == n);
        let ghost n_nat = n as nat;
        let ghost pre_push = out_limbs@;
        proof {
            assert(
                Self::limbs_value_spec(pre_push) + carry as nat * Self::pow_base_spec(n_nat)
                    == Self::prefix_sum_spec(self.limbs_le@, alen_nat, n_nat)
                        + Self::prefix_sum_spec(rhs.limbs_le@, blen_nat, n_nat)
            );
            if alen_nat <= n_nat {
                Self::lemma_prefix_sum_constant_past_logical_len(self.limbs_le@, alen_nat, n_nat);
            }
            if blen_nat <= n_nat {
                Self::lemma_prefix_sum_constant_past_logical_len(rhs.limbs_le@, blen_nat, n_nat);
            }
            Self::lemma_prefix_sum_eq_subrange_value(self.limbs_le@, alen_nat);
            Self::lemma_prefix_sum_eq_subrange_value(rhs.limbs_le@, blen_nat);
            assert(forall|j: int| alen_nat <= j < self.limbs_le@.len() ==> self.limbs_le@[j] == 0u32);
            assert(forall|j: int| blen_nat <= j < rhs.limbs_le@.len() ==> rhs.limbs_le@[j] == 0u32);
            Self::lemma_limbs_value_trim_suffix_zeros(self.limbs_le@, alen_nat);
            Self::lemma_limbs_value_trim_suffix_zeros(rhs.limbs_le@, blen_nat);
            assert(
                Self::prefix_sum_spec(self.limbs_le@, alen_nat, n_nat)
                    == Self::limbs_value_spec(self.limbs_le@)
            );
            assert(
                Self::prefix_sum_spec(rhs.limbs_le@, blen_nat, n_nat)
                    == Self::limbs_value_spec(rhs.limbs_le@)
            );
        }
        if carry != 0u64 {
            out_limbs.push(1u32);
        }
        proof {
            if carry == 0u64 {
                assert(out_limbs@ == pre_push);
                assert(carry as nat == 0);
                assert(
                    Self::limbs_value_spec(out_limbs@)
                        == Self::limbs_value_spec(self.limbs_le@)
                            + Self::limbs_value_spec(rhs.limbs_le@)
                );
            } else {
                assert(carry == 1u64);
                assert(carry as nat == 1);
                Self::lemma_limbs_value_push(pre_push, 1u32);
                assert(out_limbs@ == pre_push.push(1u32));
                assert(
                    Self::limbs_value_spec(out_limbs@)
                        == Self::limbs_value_spec(pre_push) + Self::pow_base_spec(n_nat)
                );
                assert(
                    Self::limbs_value_spec(out_limbs@)
                        == Self::limbs_value_spec(self.limbs_le@)
                            + Self::limbs_value_spec(rhs.limbs_le@)
                );
            }
        }
        let out_limbs = Self::trim_trailing_zero_limbs(out_limbs);
        proof {
            assert(
                Self::limbs_value_spec(out_limbs@)
                    == Self::limbs_value_spec(self.limbs_le@)
                        + Self::limbs_value_spec(rhs.limbs_le@)
            );
        }
        let ghost model = Self::limbs_value_spec(out_limbs@);
        let out = Self::from_parts(out_limbs, Ghost(model));
        proof {
            assert(out.model@ == Self::limbs_value_spec(out.limbs_le@));
            assert(out.model@ == Self::limbs_value_spec(self.limbs_le@) + Self::limbs_value_spec(rhs.limbs_le@));
        }
        out
    }

    fn trimmed_len_exec(limbs: &Vec<u32>) -> (out: usize)
        ensures
            out <= limbs.len(),
            forall|i: int| out <= i < limbs.len() ==> limbs@[i] == 0u32,
            out > 0 ==> limbs@[(out - 1) as int] != 0u32,
    {
        let mut n = limbs.len();
        while n > 0 && limbs[n - 1] == 0u32
            invariant
                n <= limbs.len(),
                forall|i: int| n <= i < limbs.len() ==> limbs@[i] == 0u32,
            decreases n,
        {
            assert(n > 0);
            assert(limbs[(n - 1) as int] == 0u32);
            n = n - 1;
        }
        assert(n <= limbs.len());
        if n > 0 {
            assert(!(n > 0 && limbs[n - 1] == 0u32));
            assert(limbs[n - 1] != 0u32);
            assert(limbs@[(n - 1) as int] != 0u32);
        }
        n
    }

    fn trim_trailing_zero_limbs(limbs: Vec<u32>) -> (out: Vec<u32>)
        ensures
            Self::canonical_limbs_spec(out@),
            Self::limbs_value_spec(out@) == Self::limbs_value_spec(limbs@),
    {
        let n = Self::trimmed_len_exec(&limbs);
        assert(n <= limbs.len());
        let mut out: Vec<u32> = Vec::new();
        let mut i: usize = 0;
        while i < n
            invariant
                i <= n,
                n <= limbs.len(),
                out@ == limbs@.subrange(0, i as int),
            decreases n - i,
        {
            assert(i < limbs.len());
            out.push(limbs[i]);
            i = i + 1;
        }
        proof {
            assert(out@ == limbs@.subrange(0, n as int));
            if n == 0 {
                assert(out@.len() == 0);
                assert(Self::canonical_limbs_spec(out@));
            } else {
                assert(0 < n);
                assert(out@.len() == n);
                assert(limbs@[(n - 1) as int] != 0u32);
                assert(out@[(out@.len() - 1) as int] == limbs@[(n - 1) as int]);
                assert(out@[(out@.len() - 1) as int] != 0u32);
                assert(Self::canonical_limbs_spec(out@));
            }
        }
        proof {
            let ng: nat = n as nat;
            assert(ng <= limbs@.len());
            assert(forall|i: int| ng <= i < limbs@.len() ==> limbs@[i] == 0u32);
            Self::lemma_limbs_value_trim_suffix_zeros(limbs@, ng);
            assert(
                Self::limbs_value_spec(limbs@)
                    == Self::limbs_value_spec(limbs@.subrange(0, n as int))
            );
            assert(out@ == limbs@.subrange(0, n as int));
            assert(
                Self::limbs_value_spec(out@)
                    == Self::limbs_value_spec(limbs@.subrange(0, n as int))
            );
            assert(Self::limbs_value_spec(out@) == Self::limbs_value_spec(limbs@));
        }
        out
    }

    /// Multiplies by one base limb (`2^32`) by prepending a zero low limb.
    fn shift_base_once_total(&self) -> (out: Self)
        ensures
            out.wf_spec(),
            out.model@ == Self::limbs_value_spec(self.limbs_le@) * Self::limb_base_spec(),
    {
        let n = Self::trimmed_len_exec(&self.limbs_le);
        assert(n <= self.limbs_le.len());
        if n == 0 {
            let out = Self::zero();
            proof {
                let ng: nat = n as nat;
                assert(ng == 0);
                assert(ng <= self.limbs_le@.len());
                assert(forall|j: int| ng <= j < self.limbs_le@.len() ==> self.limbs_le@[j] == 0u32);
                Self::lemma_limbs_value_trim_suffix_zeros(self.limbs_le@, ng);
                assert(self.limbs_le@.subrange(0, n as int) == Seq::<u32>::empty());
                assert(Self::limbs_value_spec(Seq::<u32>::empty()) == 0);
                assert(Self::limbs_value_spec(self.limbs_le@) == 0);
                assert(out.model@ == 0);
                assert(out.model@ == Self::limbs_value_spec(self.limbs_le@) * Self::limb_base_spec());
            }
            out
        } else {
            let mut out_limbs: Vec<u32> = Vec::new();
            out_limbs.push(0u32);
            let mut i: usize = 0;
            while i < n
                invariant
                    i <= n,
                    n <= self.limbs_le.len(),
                    out_limbs@ == Seq::<u32>::empty().push(0u32) + self.limbs_le@.subrange(0, i as int),
                decreases n - i,
            {
                assert(i < self.limbs_le.len());
                out_limbs.push(self.limbs_le[i]);
                i = i + 1;
            }
            proof {
                assert(i == n);
                let ghost zero_prefix = Seq::<u32>::empty().push(0u32);
                let ghost trimmed = self.limbs_le@.subrange(0, n as int);
                assert(out_limbs@ == zero_prefix + trimmed);
                assert(zero_prefix.len() == 1);
                assert(Self::limbs_value_spec(zero_prefix) == 0);
                Self::lemma_limbs_value_append(zero_prefix, trimmed);
                assert(
                    Self::limbs_value_spec(out_limbs@)
                        == Self::limbs_value_spec(zero_prefix)
                            + Self::pow_base_spec(zero_prefix.len()) * Self::limbs_value_spec(trimmed)
                );
                assert(Self::pow_base_spec(zero_prefix.len()) == Self::pow_base_spec(1));
                Self::lemma_pow_base_succ(0);
                assert(Self::pow_base_spec(0) == 1);
                assert(Self::pow_base_spec(1) == Self::limb_base_spec() * Self::pow_base_spec(0));
                assert(Self::pow_base_spec(1) == Self::limb_base_spec());
                assert(
                    Self::limbs_value_spec(out_limbs@)
                        == Self::limb_base_spec() * Self::limbs_value_spec(trimmed)
                );
                let ng: nat = n as nat;
                assert(ng <= self.limbs_le@.len());
                assert(forall|j: int| ng <= j < self.limbs_le@.len() ==> self.limbs_le@[j] == 0u32);
                Self::lemma_limbs_value_trim_suffix_zeros(self.limbs_le@, ng);
                assert(Self::limbs_value_spec(self.limbs_le@) == Self::limbs_value_spec(trimmed));
                assert(
                    Self::limbs_value_spec(out_limbs@)
                        == Self::limb_base_spec() * Self::limbs_value_spec(self.limbs_le@)
                );
                let ghost self_val = Self::limbs_value_spec(self.limbs_le@);
                assert(
                    Self::limb_base_spec() * self_val
                        == self_val * Self::limb_base_spec()
                ) by (nonlinear_arith);

                assert(out_limbs@.len() == n + 1);
                assert(self.limbs_le@[(n - 1) as int] != 0u32);
                assert(out_limbs@[(out_limbs@.len() - 1) as int] == self.limbs_le@[(n - 1) as int]);
                assert(out_limbs@[(out_limbs@.len() - 1) as int] != 0u32);
                assert(Self::canonical_limbs_spec(out_limbs@));
            }
            let ghost model = Self::limbs_value_spec(out_limbs@);
            let out = Self::from_parts(out_limbs, Ghost(model));
            proof {
                assert(out.model@ == Self::limbs_value_spec(out.limbs_le@));
                let ghost self_val = Self::limbs_value_spec(self.limbs_le@);
                assert(Self::limb_base_spec() * self_val == self_val * Self::limb_base_spec()) by (nonlinear_arith);
                assert(out.model@ == Self::limb_base_spec() * self_val);
                assert(out.model@ == Self::limbs_value_spec(self.limbs_le@) * Self::limb_base_spec());
            }
            out
        }
    }

    /// Multiplies by one `u32` limb via repeated semantic addition.
    fn mul_by_u32_total(&self, rhs_limb: u32) -> (out: Self)
        ensures
            out.wf_spec(),
            out.model@ == Self::limbs_value_spec(self.limbs_le@) * rhs_limb as nat,
    {
        let mut acc = Self::zero();
        let mut remaining = rhs_limb;
        while remaining > 0
            invariant
                acc.wf_spec(),
                acc.model@ + Self::limbs_value_spec(self.limbs_le@) * (remaining as nat)
                    == Self::limbs_value_spec(self.limbs_le@) * rhs_limb as nat,
            decreases remaining,
        {
            let prev_remaining = remaining;
            let next = acc.add_limbwise_small_total(self);
            remaining = prev_remaining - 1;
            proof {
                let ghost self_val = Self::limbs_value_spec(self.limbs_le@);
                assert(prev_remaining > 0);
                assert(prev_remaining as nat == remaining as nat + 1);
                assert(Self::limbs_value_spec(acc.limbs_le@) == acc.model@);
                assert(Self::limbs_value_spec(next.limbs_le@) == next.model@);
                assert(next.model@ == Self::limbs_value_spec(acc.limbs_le@) + Self::limbs_value_spec(self.limbs_le@));
                assert(next.model@ == acc.model@ + self_val);
                assert(
                    self_val * (prev_remaining as nat)
                        == self_val * ((remaining as nat) + 1)
                );
                assert(
                    self_val * ((remaining as nat) + 1)
                        == self_val * (remaining as nat) + self_val
                ) by (nonlinear_arith);
                assert(
                    next.model@ + self_val * (remaining as nat)
                        == (acc.model@ + self_val) + self_val * (remaining as nat)
                );
                assert(
                    (acc.model@ + self_val) + self_val * (remaining as nat)
                        == acc.model@ + (self_val * (remaining as nat) + self_val)
                ) by (nonlinear_arith);
                assert(
                    acc.model@ + (self_val * (remaining as nat) + self_val)
                        == acc.model@ + self_val * (prev_remaining as nat)
                );
                assert(
                    acc.model@ + self_val * (prev_remaining as nat)
                        == self_val * rhs_limb as nat
                );
                assert(next.model@ + self_val * (remaining as nat) == self_val * rhs_limb as nat);
            }
            acc = next;
        }
        proof {
            let ghost self_val = Self::limbs_value_spec(self.limbs_le@);
            assert(!(remaining > 0));
            assert(remaining == 0);
            assert(remaining as nat == 0);
            assert(acc.model@ + self_val * (remaining as nat) == self_val * rhs_limb as nat);
            assert(acc.model@ == self_val * rhs_limb as nat);
        }
        acc
    }
    /// Total limb-wise multiplication helper used by scalar witness plumbing.
    ///
    /// Computes exact multiplication in little-endian limb space by combining:
    /// - per-limb scalar multiplication (`mul_by_u32_total`)
    /// - base shifting (`shift_base_once_total`)
    /// - semantic accumulation (`add_limbwise_small_total`)
    pub fn mul_limbwise_small_total(&self, rhs: &Self) -> (out: Self)
        ensures
            out.wf_spec(),
            out.model@ == Self::limbs_value_spec(self.limbs_le@) * Self::limbs_value_spec(rhs.limbs_le@),
    {
        let blen = Self::trimmed_len_exec(&rhs.limbs_le);
        assert(blen <= rhs.limbs_le.len());
        let mut acc = Self::zero();
        let mut shifted = self.copy_small_total();
        let mut i: usize = 0;
        proof {
            assert(acc.model@ == 0);
            assert(Self::prefix_sum_spec(rhs.limbs_le@, blen as nat, 0) == 0);
            assert(Self::pow_base_spec(0) == 1);
            assert(
                Self::limbs_value_spec(self.limbs_le@)
                    * Self::prefix_sum_spec(rhs.limbs_le@, blen as nat, 0)
                    == 0
            ) by (nonlinear_arith);
            assert(
                acc.model@
                    == Self::limbs_value_spec(self.limbs_le@)
                        * Self::prefix_sum_spec(rhs.limbs_le@, blen as nat, 0)
            );
            assert(shifted.model@ == Self::limbs_value_spec(self.limbs_le@));
            assert(
                shifted.model@
                    == Self::limbs_value_spec(self.limbs_le@) * Self::pow_base_spec(0)
            );
        }
        while i < blen
            invariant
                i <= blen,
                blen <= rhs.limbs_le.len(),
                acc.wf_spec(),
                shifted.wf_spec(),
                acc.model@ == Self::limbs_value_spec(self.limbs_le@)
                    * Self::prefix_sum_spec(rhs.limbs_le@, blen as nat, i as nat),
                shifted.model@ == Self::limbs_value_spec(self.limbs_le@) * Self::pow_base_spec(i as nat),
            decreases blen - i,
        {
            assert(i < rhs.limbs_le.len());
            let limb = rhs.limbs_le[i];
            let term = shifted.mul_by_u32_total(limb);
            let next_acc = acc.add_limbwise_small_total(&term);
            let next_shifted = shifted.shift_base_once_total();
            proof {
                let i_nat = i as nat;
                let blen_nat = blen as nat;
                let ghost self_val = Self::limbs_value_spec(self.limbs_le@);
                let ghost prefix_i = Self::prefix_sum_spec(rhs.limbs_le@, blen_nat, i_nat);
                let ghost prefix_next = Self::prefix_sum_spec(rhs.limbs_le@, blen_nat, i_nat + 1);
                assert(i_nat < blen_nat);
                assert(i_nat < rhs.limbs_le@.len());
                assert(Self::limb_or_zero_spec(rhs.limbs_le@, blen_nat, i_nat) == rhs.limbs_le@[i as int] as nat);
                assert(Self::limb_or_zero_spec(rhs.limbs_le@, blen_nat, i_nat) == limb as nat);
                Self::lemma_prefix_sum_step(rhs.limbs_le@, blen_nat, i_nat);
                assert(
                    prefix_next
                        == prefix_i + limb as nat * Self::pow_base_spec(i_nat)
                );

                assert(Self::limbs_value_spec(shifted.limbs_le@) == shifted.model@);
                assert(term.model@ == Self::limbs_value_spec(shifted.limbs_le@) * limb as nat);
                assert(term.model@ == shifted.model@ * limb as nat);
                assert(shifted.model@ == self_val * Self::pow_base_spec(i_nat));
                let ghost pow_i = Self::pow_base_spec(i_nat);
                let ghost limb_nat = limb as nat;
                assert(term.model@ == (self_val * pow_i) * limb_nat);

                assert(Self::limbs_value_spec(acc.limbs_le@) == acc.model@);
                assert(Self::limbs_value_spec(term.limbs_le@) == term.model@);
                assert(
                    next_acc.model@
                        == Self::limbs_value_spec(acc.limbs_le@) + Self::limbs_value_spec(term.limbs_le@)
                );
                assert(next_acc.model@ == acc.model@ + term.model@);
                assert(acc.model@ == self_val * prefix_i);
                assert(
                    next_acc.model@
                        == self_val * prefix_i
                            + (self_val * pow_i) * limb_nat
                );
                assert((self_val * pow_i) * limb_nat == self_val * (pow_i * limb_nat))
                    by (nonlinear_arith);
                assert(pow_i * limb_nat == limb_nat * pow_i) by (nonlinear_arith);
                assert(self_val * (pow_i * limb_nat) == self_val * (limb_nat * pow_i))
                    by (nonlinear_arith);
                assert(
                    next_acc.model@
                        == self_val * prefix_i + self_val * (limb_nat * pow_i)
                );
                assert(
                    self_val * prefix_i + self_val * (limb_nat * pow_i)
                        == self_val * (prefix_i + limb_nat * pow_i)
                ) by (nonlinear_arith);
                assert(next_acc.model@ == self_val * (prefix_i + limb_nat * pow_i));
                assert(next_acc.model@ == self_val * prefix_next);

                assert(Self::limbs_value_spec(next_shifted.limbs_le@) == next_shifted.model@);
                assert(next_shifted.model@ == Self::limbs_value_spec(shifted.limbs_le@) * Self::limb_base_spec());
                assert(next_shifted.model@ == shifted.model@ * Self::limb_base_spec());
                Self::lemma_pow_base_succ(i_nat);
                let ghost pow_next = Self::pow_base_spec(i_nat + 1);
                assert(pow_next == Self::limb_base_spec() * pow_i);
                let ghost base = Self::limb_base_spec();
                assert(next_shifted.model@ == (self_val * pow_i) * base);
                assert((self_val * pow_i) * base == self_val * (pow_i * base))
                    by (nonlinear_arith);
                assert(pow_i * base == base * pow_i) by (nonlinear_arith);
                assert(self_val * (pow_i * base) == self_val * (base * pow_i))
                    by (nonlinear_arith);
                assert(next_shifted.model@ == self_val * (base * pow_i));
                assert(next_shifted.model@ == self_val * pow_next);
            }
            acc = next_acc;
            shifted = next_shifted;
            i = i + 1;
        }
        proof {
            let blen_nat = blen as nat;
            assert(i == blen);
            assert(
                acc.model@
                    == Self::limbs_value_spec(self.limbs_le@)
                        * Self::prefix_sum_spec(rhs.limbs_le@, blen_nat, blen_nat)
            );
            Self::lemma_prefix_sum_eq_subrange_value(rhs.limbs_le@, blen_nat);
            assert(forall|j: int| blen_nat <= j < rhs.limbs_le@.len() ==> rhs.limbs_le@[j] == 0u32);
            Self::lemma_limbs_value_trim_suffix_zeros(rhs.limbs_le@, blen_nat);
            assert(
                Self::prefix_sum_spec(rhs.limbs_le@, blen_nat, blen_nat)
                    == Self::limbs_value_spec(rhs.limbs_le@)
            );
            assert(
                acc.model@
                    == Self::limbs_value_spec(self.limbs_le@) * Self::limbs_value_spec(rhs.limbs_le@)
            );
        }
        acc
    }

    /// Total small-limb division helper used by scalar witness plumbing.
    ///
    /// Computes the floor quotient of `self / rhs` using monotone
    /// multiplication-by-addition accumulation. Returns `0` when `rhs == 0`.
    pub fn div_limbwise_small_total(&self, rhs: &Self) -> (out: Self)
        requires
            self.wf_spec(),
            rhs.wf_spec(),
        ensures
            out.wf_spec(),
            Self::limbs_value_spec(rhs.limbs_le@) == 0 ==> out.model@ == 0,
            Self::limbs_value_spec(rhs.limbs_le@) > 0
                ==> out.model@ * Self::limbs_value_spec(rhs.limbs_le@)
                    <= Self::limbs_value_spec(self.limbs_le@),
            Self::limbs_value_spec(rhs.limbs_le@) > 0
                ==> Self::limbs_value_spec(self.limbs_le@)
                    < (out.model@ + 1) * Self::limbs_value_spec(rhs.limbs_le@),
            Self::limbs_value_spec(rhs.limbs_le@) > 0
                ==> out.model@
                    == Self::limbs_value_spec(self.limbs_le@)
                        / Self::limbs_value_spec(rhs.limbs_le@),
    {
        let ghost self_val = Self::limbs_value_spec(self.limbs_le@);
        let ghost rhs_val = Self::limbs_value_spec(rhs.limbs_le@);
        if rhs.is_zero() {
            let out = Self::zero();
            proof {
                assert(rhs.model@ == rhs_val);
                assert(rhs.model@ == 0);
                assert(rhs_val == 0);
                assert(out.model@ == 0);
            }
            out
        } else {
            let one = Self::from_u32(1);
            let mut q = Self::zero();
            let mut accum = Self::zero();
            let mut next_accum = accum.add_limbwise_small_total(rhs);
            let mut cmp = next_accum.cmp_limbwise_small_total(self);
            proof {
                assert(rhs.model@ == rhs_val);
                assert(rhs.model@ != 0);
                assert(rhs_val > 0);
                assert(self.model@ == self_val);
                assert(q.model@ == 0);
                assert(accum.model@ == 0);
                assert(one.model@ == 1);
                assert(accum.model@ == q.model@ * rhs_val);
                assert(next_accum.model@ == accum.model@ + rhs_val);
                assert(cmp == -1 || cmp == 0 || cmp == 1);
                assert(accum.model@ <= self_val);
                assert(q.model@ <= self_val);
                if cmp == -1 {
                    assert(Self::limbs_value_spec(next_accum.limbs_le@) < Self::limbs_value_spec(self.limbs_le@));
                    assert(next_accum.model@ < self_val);
                    assert(next_accum.model@ <= self_val);
                }
                if cmp == 0 {
                    assert(Self::limbs_value_spec(next_accum.limbs_le@) == Self::limbs_value_spec(self.limbs_le@));
                    assert(next_accum.model@ == self_val);
                    assert(next_accum.model@ <= self_val);
                }
                if cmp == 1 {
                    assert(Self::limbs_value_spec(next_accum.limbs_le@) > Self::limbs_value_spec(self.limbs_le@));
                    assert(self_val < next_accum.model@);
                }
            }

            while cmp <= 0
                invariant
                    q.wf_spec(),
                    accum.wf_spec(),
                    next_accum.wf_spec(),
                    self.wf_spec(),
                    rhs.wf_spec(),
                    one.wf_spec(),
                    one.model@ == 1,
                    rhs_val == rhs.model@,
                    rhs_val > 0,
                    self_val == self.model@,
                    cmp == -1 || cmp == 0 || cmp == 1,
                    cmp <= 0 ==> next_accum.model@ <= self_val,
                    cmp == 1 ==> self_val < next_accum.model@,
                    accum.model@ == q.model@ * rhs_val,
                    next_accum.model@ == accum.model@ + rhs_val,
                    accum.model@ <= self_val,
                    q.model@ <= self_val,
                decreases self_val - q.model@,
            {
                let new_q = q.add_limbwise_small_total(&one);
                let new_accum = next_accum;
                let new_next_accum = new_accum.add_limbwise_small_total(rhs);
                proof {
                    assert(cmp != 1);
                    assert(next_accum.model@ <= self_val);
                    assert(Self::limbs_value_spec(q.limbs_le@) == q.model@);
                    assert(Self::limbs_value_spec(one.limbs_le@) == one.model@);
                    assert(new_q.model@ == q.model@ + one.model@);
                    assert(new_q.model@ == q.model@ + 1);
                    assert(new_accum.model@ == next_accum.model@);
                    assert(new_accum.model@ == accum.model@ + rhs_val);
                    assert(accum.model@ == q.model@ * rhs_val);
                    assert(new_accum.model@ == q.model@ * rhs_val + rhs_val);
                    assert(q.model@ * rhs_val + rhs_val == (q.model@ + 1) * rhs_val)
                        by (nonlinear_arith);
                    assert(new_accum.model@ == (q.model@ + 1) * rhs_val);
                    assert(new_accum.model@ == new_q.model@ * rhs_val);
                    assert(new_accum.model@ <= self_val);
                    assert(rhs_val >= 1);
                    if rhs_val == 1 {
                        assert((q.model@ + 1) * rhs_val == q.model@ + 1);
                    } else {
                        assert(rhs_val > 1);
                        assert(rhs_val == 1 + (rhs_val - 1));
                        assert(
                            (q.model@ + 1) * rhs_val
                                == (q.model@ + 1) * 1 + (q.model@ + 1) * (rhs_val - 1)
                        ) by (nonlinear_arith);
                        assert((q.model@ + 1) * (rhs_val - 1) >= 0);
                        assert((q.model@ + 1) * rhs_val >= q.model@ + 1);
                    }
                    assert((q.model@ + 1) * rhs_val >= q.model@ + 1);
                    assert(q.model@ + 1 <= self_val);
                    assert(new_q.model@ <= self_val);
                    assert(self_val - new_q.model@ < self_val - q.model@);
                    assert(new_next_accum.model@ == new_accum.model@ + rhs_val);
                }
                q = new_q;
                accum = new_accum;
                next_accum = new_next_accum;
                cmp = next_accum.cmp_limbwise_small_total(self);
                proof {
                    assert(cmp == -1 || cmp == 0 || cmp == 1);
                    if cmp == -1 {
                        assert(Self::limbs_value_spec(next_accum.limbs_le@) < Self::limbs_value_spec(self.limbs_le@));
                        assert(next_accum.model@ < self_val);
                        assert(next_accum.model@ <= self_val);
                    }
                    if cmp == 0 {
                        assert(Self::limbs_value_spec(next_accum.limbs_le@) == Self::limbs_value_spec(self.limbs_le@));
                        assert(next_accum.model@ == self_val);
                        assert(next_accum.model@ <= self_val);
                    }
                    if cmp == 1 {
                        assert(Self::limbs_value_spec(next_accum.limbs_le@) > Self::limbs_value_spec(self.limbs_le@));
                        assert(self_val < next_accum.model@);
                    }
                }
            }
            proof {
                assert(!(cmp <= 0));
                assert(cmp == -1 || cmp == 0 || cmp == 1);
                assert(cmp == 1);
                assert(self_val < next_accum.model@);
                assert(accum.model@ == q.model@ * rhs_val);
                assert(next_accum.model@ == accum.model@ + rhs_val);
                assert(q.model@ * rhs_val <= self_val);
                assert(next_accum.model@ == q.model@ * rhs_val + rhs_val);
                assert(q.model@ * rhs_val + rhs_val == (q.model@ + 1) * rhs_val)
                    by (nonlinear_arith);
                assert(next_accum.model@ == (q.model@ + 1) * rhs_val);
                assert(self_val < (q.model@ + 1) * rhs_val);

                assert(q.model@ * rhs_val <= self_val);
                let r = (self_val - q.model@ * rhs_val) as nat;
                assert(r == self_val - q.model@ * rhs_val);
                assert(q.model@ * rhs_val + r == self_val);
                assert(self_val == q.model@ * rhs_val + r);
                assert(q.model@ * rhs_val + r < q.model@ * rhs_val + rhs_val);
                assert(r < rhs_val);

                let xi = self_val as int;
                let di = rhs_val as int;
                lemma_fundamental_div_mod(xi, di);
                lemma_mod_pos_bound(xi, di);
                assert((self_val / rhs_val) as int == xi / di);
                assert((self_val % rhs_val) as int == xi % di);
                let xi = self_val as int;
                let di = rhs_val as int;
                lemma_fundamental_div_mod(xi, di);
                lemma_mod_pos_bound(xi, di);
                assert((self_val / rhs_val) as int == xi / di);
                assert((self_val % rhs_val) as int == xi % di);
                assert(self_val == (self_val / rhs_val) * rhs_val + self_val % rhs_val);
                assert(self_val % rhs_val < rhs_val);
                Self::lemma_div_rem_unique_nat(
                    self_val,
                    rhs_val,
                    q.model@,
                    r,
                    self_val / rhs_val,
                    self_val % rhs_val,
                );
                assert(q.model@ == self_val / rhs_val);
            }
            q
        }
    }

    /// Total small-limb remainder helper used by scalar witness plumbing.
    ///
    /// Computes `self % rhs` with total semantics, returning `0` when `rhs == 0`.
    pub fn rem_limbwise_small_total(&self, rhs: &Self) -> (out: Self)
        requires
            self.wf_spec(),
            rhs.wf_spec(),
        ensures
            out.wf_spec(),
            Self::limbs_value_spec(rhs.limbs_le@) == 0 ==> out.model@ == 0,
            Self::limbs_value_spec(rhs.limbs_le@) > 0 ==> out.model@ < Self::limbs_value_spec(rhs.limbs_le@),
            Self::limbs_value_spec(rhs.limbs_le@) > 0
                ==> out.model@
                    == Self::limbs_value_spec(self.limbs_le@)
                        % Self::limbs_value_spec(rhs.limbs_le@),
    {
        let pair = self.div_rem_limbwise_small_total(rhs);
        let out = pair.1;
        proof {
            let ghost rhs_val = Self::limbs_value_spec(rhs.limbs_le@);
            assert(out.wf_spec());
            if rhs_val == 0 {
                assert(pair.1.model@ == 0);
                assert(out.model@ == 0);
            }
            if rhs_val > 0 {
                assert(pair.1.model@ < rhs_val);
                assert(out.model@ < rhs_val);
                assert(pair.1.model@ == Self::limbs_value_spec(self.limbs_le@) % rhs_val);
                assert(out.model@ == Self::limbs_value_spec(self.limbs_le@) % rhs_val);
            }
        }
        out
    }

    /// Total small-limb quotient/remainder helper used by scalar witness plumbing.
    ///
    /// Returns `(q, r)` where `q = floor(self / rhs)` and `r = self % rhs`.
    /// Uses total semantics `(0, 0)` when `rhs == 0`.
    pub fn div_rem_limbwise_small_total(&self, rhs: &Self) -> (out: (Self, Self))
        requires
            self.wf_spec(),
            rhs.wf_spec(),
        ensures
            out.0.wf_spec(),
            out.1.wf_spec(),
            Self::limbs_value_spec(rhs.limbs_le@) == 0 ==> out.0.model@ == 0 && out.1.model@ == 0,
            Self::limbs_value_spec(rhs.limbs_le@) > 0
                ==> Self::limbs_value_spec(self.limbs_le@)
                    == out.0.model@ * Self::limbs_value_spec(rhs.limbs_le@) + out.1.model@,
            Self::limbs_value_spec(rhs.limbs_le@) > 0
                ==> out.1.model@ < Self::limbs_value_spec(rhs.limbs_le@),
            Self::limbs_value_spec(rhs.limbs_le@) > 0
                ==> out.0.model@
                    == Self::limbs_value_spec(self.limbs_le@)
                        / Self::limbs_value_spec(rhs.limbs_le@),
            Self::limbs_value_spec(rhs.limbs_le@) > 0
                ==> out.1.model@
                    == Self::limbs_value_spec(self.limbs_le@)
                        % Self::limbs_value_spec(rhs.limbs_le@),
    {
        let ghost self_val = Self::limbs_value_spec(self.limbs_le@);
        let ghost rhs_val = Self::limbs_value_spec(rhs.limbs_le@);
        if rhs.is_zero() {
            let q = Self::zero();
            let r = Self::zero();
            proof {
                assert(rhs.model@ == rhs_val);
                assert(rhs.model@ == 0);
                assert(rhs_val == 0);
                assert(q.model@ == 0);
                assert(r.model@ == 0);
            }
            (q, r)
        } else {
            let q = self.div_limbwise_small_total(rhs);
            let prod = q.mul_limbwise_small_total(rhs);
            let r = self.sub_limbwise_small_total(&prod);
            proof {
                assert(rhs.model@ == rhs_val);
                assert(rhs.model@ > 0);
                assert(rhs_val > 0);
                assert(self.model@ == self_val);
                assert(q.model@ * rhs_val <= self_val);
                assert(self_val < (q.model@ + 1) * rhs_val);
                assert(prod.model@ == q.model@ * rhs_val);
                assert(prod.model@ <= self_val);

                assert(Self::limbs_value_spec(self.limbs_le@) == self_val);
                assert(Self::limbs_value_spec(prod.limbs_le@) == prod.model@);

                if self_val <= prod.model@ {
                    assert(self_val == prod.model@);
                    assert(Self::limbs_value_spec(self.limbs_le@) <= Self::limbs_value_spec(prod.limbs_le@));
                    assert(r.model@ == 0);
                    assert(self_val == q.model@ * rhs_val);
                    assert(self_val == q.model@ * rhs_val + r.model@);
                    assert(r.model@ < rhs_val);
                } else {
                    assert(prod.model@ < self_val);
                    assert(Self::limbs_value_spec(prod.limbs_le@) < Self::limbs_value_spec(self.limbs_le@));
                    assert(
                        r.model@
                            == Self::limbs_value_spec(self.limbs_le@)
                                - Self::limbs_value_spec(prod.limbs_le@)
                    );
                    assert(r.model@ == self_val - prod.model@);
                    assert((self_val - prod.model@) + prod.model@ == self_val);
                    assert(r.model@ + prod.model@ == self_val);
                    assert(r.model@ + q.model@ * rhs_val == self_val);
                    assert(self_val == q.model@ * rhs_val + r.model@);
                    assert((q.model@ + 1) * rhs_val == q.model@ * rhs_val + rhs_val)
                        by (nonlinear_arith);
                    assert(self_val < q.model@ * rhs_val + rhs_val);
                    assert(q.model@ * rhs_val + r.model@ < q.model@ * rhs_val + rhs_val);
                    assert(r.model@ < rhs_val);
                }

                if self_val <= prod.model@ {
                    assert(self_val == q.model@ * rhs_val + r.model@);
                } else {
                    assert(self_val == q.model@ * rhs_val + r.model@);
                }

                let xi = self_val as int;
                let di = rhs_val as int;
                let qi = q.model@ as int;
                let ri = r.model@ as int;
                assert(di != 0);
                assert(0 <= ri < di);
                assert(xi == qi * di + ri);
                lemma_fundamental_div_mod_converse(xi, di, qi, ri);
                assert(qi == xi / di);
                assert(ri == xi % di);
                assert((self_val / rhs_val) as int == xi / di);
                assert((self_val % rhs_val) as int == xi % di);
                assert(q.model@ as int == (self_val / rhs_val) as int);
                assert(r.model@ as int == (self_val % rhs_val) as int);
                assert(q.model@ == self_val / rhs_val);
                assert(r.model@ == self_val % rhs_val);
            }
            (q, r)
        }
    }

    /// Total small-limb compare helper used by scalar witness plumbing.
    ///
    /// Returns the exact sign of `(self - rhs)` as `-1/0/1` using full
    /// multi-limb comparison with trailing-zero normalization.
    pub fn cmp_limbwise_small_total(&self, rhs: &Self) -> (out: i8)
        ensures
            out == -1 || out == 0 || out == 1,
            out == -1 ==> Self::limbs_value_spec(self.limbs_le@) < Self::limbs_value_spec(rhs.limbs_le@),
            out == 0 ==> Self::limbs_value_spec(self.limbs_le@) == Self::limbs_value_spec(rhs.limbs_le@),
            out == 1 ==> Self::limbs_value_spec(self.limbs_le@) > Self::limbs_value_spec(rhs.limbs_le@),
            self.limbs_le@ == rhs.limbs_le@ ==> out == 0,
            self.wf_spec() && rhs.wf_spec() && out == 0 ==> self.limbs_le@ == rhs.limbs_le@,
    {
        let alen = Self::trimmed_len_exec(&self.limbs_le);
        let blen = Self::trimmed_len_exec(&rhs.limbs_le);
        if alen > blen {
            proof {
                let alen_nat = alen as nat;
                let blen_nat = blen as nat;
                assert(alen_nat <= self.limbs_le@.len());
                assert(blen_nat <= rhs.limbs_le@.len());
                assert(forall|j: int| alen_nat <= j < self.limbs_le@.len() ==> self.limbs_le@[j] == 0u32);
                assert(forall|j: int| blen_nat <= j < rhs.limbs_le@.len() ==> rhs.limbs_le@[j] == 0u32);
                assert(alen_nat > blen_nat);
                assert(alen_nat > 0);
                assert(self.limbs_le@[(alen - 1) as int] != 0u32);
                Self::lemma_trimmed_len_gt_implies_value_gt(
                    self.limbs_le@,
                    alen_nat,
                    rhs.limbs_le@,
                    blen_nat,
                );
            }
            1i8
        } else if alen < blen {
            proof {
                let alen_nat = alen as nat;
                let blen_nat = blen as nat;
                assert(alen_nat <= self.limbs_le@.len());
                assert(blen_nat <= rhs.limbs_le@.len());
                assert(forall|j: int| alen_nat <= j < self.limbs_le@.len() ==> self.limbs_le@[j] == 0u32);
                assert(forall|j: int| blen_nat <= j < rhs.limbs_le@.len() ==> rhs.limbs_le@[j] == 0u32);
                assert(blen_nat > alen_nat);
                assert(blen_nat > 0);
                assert(rhs.limbs_le@[(blen - 1) as int] != 0u32);
                Self::lemma_trimmed_len_gt_implies_value_gt(
                    rhs.limbs_le@,
                    blen_nat,
                    self.limbs_le@,
                    alen_nat,
                );
                assert(Self::limbs_value_spec(rhs.limbs_le@) > Self::limbs_value_spec(self.limbs_le@));
                assert(Self::limbs_value_spec(self.limbs_le@) < Self::limbs_value_spec(rhs.limbs_le@));
            }
            -1i8
        } else {
            assert(alen == blen);
            assert(alen <= self.limbs_le.len());
            assert(blen <= rhs.limbs_le.len());
            let mut i = alen;
            while i > 0
                invariant
                    i <= alen,
                    alen == blen,
                    alen <= self.limbs_le.len(),
                    blen <= rhs.limbs_le.len(),
                    forall|j: int| alen <= j < self.limbs_le@.len() ==> self.limbs_le@[j] == 0u32,
                    forall|j: int| blen <= j < rhs.limbs_le@.len() ==> rhs.limbs_le@[j] == 0u32,
                    forall|j: int| i <= j < alen ==> self.limbs_le@[j] == rhs.limbs_le@[j],
                decreases i,
            {
                let idx = i - 1;
                assert(idx < self.limbs_le.len());
                assert(idx < rhs.limbs_le.len());
                let a = self.limbs_le[idx];
                let b = rhs.limbs_le[idx];
                if a > b {
                    proof {
                        let alen_nat = alen as nat;
                        let blen_nat = blen as nat;
                        let idx_nat = idx as nat;
                        assert(alen_nat == blen_nat);
                        assert(alen_nat <= self.limbs_le@.len());
                        assert(blen_nat <= rhs.limbs_le@.len());
                        assert(forall|j: int| alen_nat <= j < self.limbs_le@.len() ==> self.limbs_le@[j] == 0u32);
                        assert(forall|j: int| blen_nat <= j < rhs.limbs_le@.len() ==> rhs.limbs_le@[j] == 0u32);
                        assert(idx_nat < alen_nat);
                        assert(self.limbs_le@[idx as int] > rhs.limbs_le@[idx as int]);
                        assert(i == idx + 1);
                        assert forall|j: int| idx_nat < j < alen_nat
                            implies self.limbs_le@[j] == rhs.limbs_le@[j] by {
                            assert(idx as int + 1 <= j);
                            assert(i as int == idx as int + 1);
                            assert(i <= j);
                            assert(j < alen);
                            assert(self.limbs_le@[j] == rhs.limbs_le@[j]);
                        };
                        Self::lemma_trimmed_high_diff_implies_value_gt(
                            self.limbs_le@,
                            alen_nat,
                            rhs.limbs_le@,
                            blen_nat,
                            idx_nat,
                        );
                    }
                    return 1i8;
                } else if a < b {
                    proof {
                        let alen_nat = alen as nat;
                        let blen_nat = blen as nat;
                        let idx_nat = idx as nat;
                        assert(alen_nat == blen_nat);
                        assert(alen_nat <= self.limbs_le@.len());
                        assert(blen_nat <= rhs.limbs_le@.len());
                        assert(forall|j: int| alen_nat <= j < self.limbs_le@.len() ==> self.limbs_le@[j] == 0u32);
                        assert(forall|j: int| blen_nat <= j < rhs.limbs_le@.len() ==> rhs.limbs_le@[j] == 0u32);
                        assert(idx_nat < alen_nat);
                        assert(rhs.limbs_le@[idx as int] > self.limbs_le@[idx as int]);
                        assert(i == idx + 1);
                        assert forall|j: int| idx_nat < j < alen_nat
                            implies rhs.limbs_le@[j] == self.limbs_le@[j] by {
                            assert(idx as int + 1 <= j);
                            assert(i as int == idx as int + 1);
                            assert(i <= j);
                            assert(j < alen);
                            assert(self.limbs_le@[j] == rhs.limbs_le@[j]);
                        };
                        Self::lemma_trimmed_high_diff_implies_value_gt(
                            rhs.limbs_le@,
                            blen_nat,
                            self.limbs_le@,
                            alen_nat,
                            idx_nat,
                        );
                        assert(Self::limbs_value_spec(rhs.limbs_le@) > Self::limbs_value_spec(self.limbs_le@));
                        assert(Self::limbs_value_spec(self.limbs_le@) < Self::limbs_value_spec(rhs.limbs_le@));
                    }
                    return -1i8;
                }
                assert(a == b);
                assert(self.limbs_le@[idx as int] == rhs.limbs_le@[idx as int]);
                i = i - 1;
            }
            proof {
                let alen_nat = alen as nat;
                let blen_nat = blen as nat;
                assert(i == 0);
                assert(alen == blen);
                assert(forall|j: int| 0 <= j < alen ==> self.limbs_le@[j] == rhs.limbs_le@[j]);
                assert forall|j: int| (0 <= j && j < alen) implies
                    #[trigger] self.limbs_le@.subrange(0, alen as int)[j]
                        == rhs.limbs_le@.subrange(0, blen as int)[j] by {
                    if 0 <= j && j < alen {
                        assert(self.limbs_le@.subrange(0, alen as int)[j] == self.limbs_le@[j]);
                        assert(rhs.limbs_le@.subrange(0, blen as int)[j] == rhs.limbs_le@[j]);
                    }
                };
                assert(self.limbs_le@.subrange(0, alen as int) == rhs.limbs_le@.subrange(0, blen as int));
                assert(alen_nat <= self.limbs_le@.len());
                assert(blen_nat <= rhs.limbs_le@.len());
                assert(forall|j: int| alen_nat <= j < self.limbs_le@.len() ==> self.limbs_le@[j] == 0u32);
                assert(forall|j: int| blen_nat <= j < rhs.limbs_le@.len() ==> rhs.limbs_le@[j] == 0u32);
                Self::lemma_limbs_value_trim_suffix_zeros(self.limbs_le@, alen_nat);
                Self::lemma_limbs_value_trim_suffix_zeros(rhs.limbs_le@, blen_nat);
                assert(
                    Self::limbs_value_spec(self.limbs_le@)
                        == Self::limbs_value_spec(self.limbs_le@.subrange(0, alen as int))
                );
                assert(
                    Self::limbs_value_spec(rhs.limbs_le@)
                        == Self::limbs_value_spec(rhs.limbs_le@.subrange(0, blen as int))
                );
                assert(
                    Self::limbs_value_spec(self.limbs_le@.subrange(0, alen as int))
                        == Self::limbs_value_spec(rhs.limbs_le@.subrange(0, blen as int))
                );
                assert(
                    Self::limbs_value_spec(self.limbs_le@)
                        == Self::limbs_value_spec(rhs.limbs_le@)
                );
                assert(self.wf_spec() && rhs.wf_spec() ==> self.limbs_le@ == rhs.limbs_le@) by {
                    if self.wf_spec() && rhs.wf_spec() {
                        assert(Self::canonical_limbs_spec(self.limbs_le@));
                        assert(Self::canonical_limbs_spec(rhs.limbs_le@));

                        if alen_nat < self.limbs_le@.len() {
                            assert(self.limbs_le@.len() > 0);
                            let last = self.limbs_le@.len() - 1;
                            assert(alen_nat <= last);
                            assert(last < self.limbs_le@.len());
                            assert(self.limbs_le@[last as int] == 0u32);
                            assert(self.limbs_le@[last as int] != 0u32);
                        }
                        assert(alen_nat == self.limbs_le@.len());

                        if blen_nat < rhs.limbs_le@.len() {
                            assert(rhs.limbs_le@.len() > 0);
                            let last = rhs.limbs_le@.len() - 1;
                            assert(blen_nat <= last);
                            assert(last < rhs.limbs_le@.len());
                            assert(rhs.limbs_le@[last as int] == 0u32);
                            assert(rhs.limbs_le@[last as int] != 0u32);
                        }
                        assert(blen_nat == rhs.limbs_le@.len());
                        assert(self.limbs_le@.len() == rhs.limbs_le@.len());
                        assert(self.limbs_le@.subrange(0, alen as int) == self.limbs_le@);
                        assert(rhs.limbs_le@.subrange(0, blen as int) == rhs.limbs_le@);
                        assert(self.limbs_le@ == rhs.limbs_le@);
                    }
                };
            }
            0i8
        }
    }

    pub proof fn lemma_cmp_limbwise_small_total_antisymmetric(
        a: &Self,
        b: &Self,
        ab: i8,
        ba: i8,
    )
        requires
            ab == -1 || ab == 0 || ab == 1,
            ba == -1 || ba == 0 || ba == 1,
            ab == -1 ==> Self::limbs_value_spec(a.limbs_le@) < Self::limbs_value_spec(b.limbs_le@),
            ab == 0 ==> Self::limbs_value_spec(a.limbs_le@) == Self::limbs_value_spec(b.limbs_le@),
            ab == 1 ==> Self::limbs_value_spec(a.limbs_le@) > Self::limbs_value_spec(b.limbs_le@),
            ba == -1 ==> Self::limbs_value_spec(b.limbs_le@) < Self::limbs_value_spec(a.limbs_le@),
            ba == 0 ==> Self::limbs_value_spec(b.limbs_le@) == Self::limbs_value_spec(a.limbs_le@),
            ba == 1 ==> Self::limbs_value_spec(b.limbs_le@) > Self::limbs_value_spec(a.limbs_le@),
        ensures
            (ab as int) == -((ba) as int),
    {
        let a_val = Self::limbs_value_spec(a.limbs_le@);
        let b_val = Self::limbs_value_spec(b.limbs_le@);

        if ab == -1 {
            assert(a_val < b_val);
            assert(!(b_val < a_val));
            assert(a_val != b_val);
            assert(ba != -1) by {
                if ba == -1 {
                    assert(b_val < a_val);
                    assert(!(b_val < a_val));
                }
            };
            assert(ba != 0) by {
                if ba == 0 {
                    assert(b_val == a_val);
                    assert(a_val != b_val);
                }
            };
            assert(ba == 1);
            assert((ab as int) == -((ba) as int));
        } else if ab == 0 {
            assert(a_val == b_val);
            assert(ba != -1) by {
                if ba == -1 {
                    assert(b_val < a_val);
                    assert(!(b_val < a_val));
                }
            };
            assert(ba != 1) by {
                if ba == 1 {
                    assert(b_val > a_val);
                    assert(!(b_val > a_val));
                }
            };
            assert(ba == 0);
            assert((ab as int) == -((ba) as int));
        } else {
            assert(ab == 1);
            assert(a_val > b_val);
            assert(!(b_val > a_val));
            assert(a_val != b_val);
            assert(ba != 1) by {
                if ba == 1 {
                    assert(b_val > a_val);
                    assert(!(b_val > a_val));
                }
            };
            assert(ba != 0) by {
                if ba == 0 {
                    assert(b_val == a_val);
                    assert(a_val != b_val);
                }
            };
            assert(ba == -1);
            assert((ab as int) == -((ba) as int));
        }
    }

    pub proof fn lemma_cmp_limbwise_small_total_transitive_le(
        a: &Self,
        b: &Self,
        c: &Self,
        ab: i8,
        bc: i8,
        ac: i8,
    )
        requires
            ab == -1 || ab == 0 || ab == 1,
            bc == -1 || bc == 0 || bc == 1,
            ac == -1 || ac == 0 || ac == 1,
            ab == -1 ==> Self::limbs_value_spec(a.limbs_le@) < Self::limbs_value_spec(b.limbs_le@),
            ab == 0 ==> Self::limbs_value_spec(a.limbs_le@) == Self::limbs_value_spec(b.limbs_le@),
            ab == 1 ==> Self::limbs_value_spec(a.limbs_le@) > Self::limbs_value_spec(b.limbs_le@),
            bc == -1 ==> Self::limbs_value_spec(b.limbs_le@) < Self::limbs_value_spec(c.limbs_le@),
            bc == 0 ==> Self::limbs_value_spec(b.limbs_le@) == Self::limbs_value_spec(c.limbs_le@),
            bc == 1 ==> Self::limbs_value_spec(b.limbs_le@) > Self::limbs_value_spec(c.limbs_le@),
            ac == -1 ==> Self::limbs_value_spec(a.limbs_le@) < Self::limbs_value_spec(c.limbs_le@),
            ac == 0 ==> Self::limbs_value_spec(a.limbs_le@) == Self::limbs_value_spec(c.limbs_le@),
            ac == 1 ==> Self::limbs_value_spec(a.limbs_le@) > Self::limbs_value_spec(c.limbs_le@),
            ab <= 0i8,
            bc <= 0i8,
        ensures
            ac <= 0i8,
    {
        let a_val = Self::limbs_value_spec(a.limbs_le@);
        let b_val = Self::limbs_value_spec(b.limbs_le@);
        let c_val = Self::limbs_value_spec(c.limbs_le@);

        if ab == -1 {
            assert(a_val < b_val);
            assert(a_val <= b_val);
        } else {
            assert(ab == 0);
            assert(a_val == b_val);
            assert(a_val <= b_val);
        }

        if bc == -1 {
            assert(b_val < c_val);
            assert(b_val <= c_val);
        } else {
            assert(bc == 0);
            assert(b_val == c_val);
            assert(b_val <= c_val);
        }

        assert(a_val <= c_val);
        assert(ac != 1) by {
            if ac == 1 {
                assert(a_val > c_val);
                assert(!(a_val > c_val));
            }
        };

        if ac == -1 {
        } else if ac == 0 {
        } else {
            assert(ac == 1);
            assert(false);
        }
        assert(ac <= 0i8);
    }

    pub proof fn lemma_cmp_limbwise_small_total_transitive_eq(
        a: &Self,
        b: &Self,
        c: &Self,
        ab: i8,
        bc: i8,
        ac: i8,
    )
        requires
            ab == -1 || ab == 0 || ab == 1,
            bc == -1 || bc == 0 || bc == 1,
            ac == -1 || ac == 0 || ac == 1,
            ab == -1 ==> Self::limbs_value_spec(a.limbs_le@) < Self::limbs_value_spec(b.limbs_le@),
            ab == 0 ==> Self::limbs_value_spec(a.limbs_le@) == Self::limbs_value_spec(b.limbs_le@),
            ab == 1 ==> Self::limbs_value_spec(a.limbs_le@) > Self::limbs_value_spec(b.limbs_le@),
            bc == -1 ==> Self::limbs_value_spec(b.limbs_le@) < Self::limbs_value_spec(c.limbs_le@),
            bc == 0 ==> Self::limbs_value_spec(b.limbs_le@) == Self::limbs_value_spec(c.limbs_le@),
            bc == 1 ==> Self::limbs_value_spec(b.limbs_le@) > Self::limbs_value_spec(c.limbs_le@),
            ac == -1 ==> Self::limbs_value_spec(a.limbs_le@) < Self::limbs_value_spec(c.limbs_le@),
            ac == 0 ==> Self::limbs_value_spec(a.limbs_le@) == Self::limbs_value_spec(c.limbs_le@),
            ac == 1 ==> Self::limbs_value_spec(a.limbs_le@) > Self::limbs_value_spec(c.limbs_le@),
            ab == 0i8,
            bc == 0i8,
        ensures
            ac == 0i8,
    {
        let a_val = Self::limbs_value_spec(a.limbs_le@);
        let b_val = Self::limbs_value_spec(b.limbs_le@);
        let c_val = Self::limbs_value_spec(c.limbs_le@);

        assert(a_val == b_val);
        assert(b_val == c_val);
        assert(a_val == c_val);
        assert(ac != -1) by {
            if ac == -1 {
                assert(a_val < c_val);
                assert(!(a_val < c_val));
            }
        };
        assert(ac != 1) by {
            if ac == 1 {
                assert(a_val > c_val);
                assert(!(a_val > c_val));
            }
        };

        if ac == -1 {
            assert(false);
        } else if ac == 1 {
            assert(false);
        } else {
            assert(ac == 0);
        }
    }

    pub proof fn lemma_cmp_le_zero_iff_le_from_total_contracts(
        a: &Self,
        b: &Self,
        ab: i8,
    )
        requires
            ab == -1 || ab == 0 || ab == 1,
            ab == -1 ==> Self::limbs_value_spec(a.limbs_le@) < Self::limbs_value_spec(b.limbs_le@),
            ab == 0 ==> Self::limbs_value_spec(a.limbs_le@) == Self::limbs_value_spec(b.limbs_le@),
            ab == 1 ==> Self::limbs_value_spec(a.limbs_le@) > Self::limbs_value_spec(b.limbs_le@),
        ensures
            (ab <= 0i8) <==> (Self::limbs_value_spec(a.limbs_le@) <= Self::limbs_value_spec(b.limbs_le@)),
    {
        let a_val = Self::limbs_value_spec(a.limbs_le@);
        let b_val = Self::limbs_value_spec(b.limbs_le@);

        if ab <= 0i8 {
            if ab == -1 {
                assert(a_val < b_val);
                assert(a_val <= b_val);
            } else {
                assert(ab == 0);
                assert(a_val == b_val);
                assert(a_val <= b_val);
            }
        }

        if a_val <= b_val {
            assert(ab != 1) by {
                if ab == 1 {
                    assert(a_val > b_val);
                    assert(!(a_val > b_val));
                }
            };
            if ab == -1 {
            } else if ab == 0 {
            } else {
                assert(ab == 1);
                assert(false);
            }
            assert(ab <= 0i8);
        }
    }

    pub proof fn lemma_cmp_lt_zero_iff_lt_from_total_contracts(
        a: &Self,
        b: &Self,
        ab: i8,
    )
        requires
            ab == -1 || ab == 0 || ab == 1,
            ab == -1 ==> Self::limbs_value_spec(a.limbs_le@) < Self::limbs_value_spec(b.limbs_le@),
            ab == 0 ==> Self::limbs_value_spec(a.limbs_le@) == Self::limbs_value_spec(b.limbs_le@),
            ab == 1 ==> Self::limbs_value_spec(a.limbs_le@) > Self::limbs_value_spec(b.limbs_le@),
        ensures
            (ab < 0i8) <==> (Self::limbs_value_spec(a.limbs_le@) < Self::limbs_value_spec(b.limbs_le@)),
    {
        let a_val = Self::limbs_value_spec(a.limbs_le@);
        let b_val = Self::limbs_value_spec(b.limbs_le@);

        if ab < 0i8 {
            assert(ab == -1);
            assert(a_val < b_val);
        }

        if a_val < b_val {
            assert(ab != 0) by {
                if ab == 0 {
                    assert(a_val == b_val);
                    assert(!(a_val == b_val));
                }
            };
            assert(ab != 1) by {
                if ab == 1 {
                    assert(a_val > b_val);
                    assert(!(a_val > b_val));
                }
            };
            if ab == -1 {
            } else if ab == 0 {
                assert(false);
            } else {
                assert(ab == 1);
                assert(false);
            }
            assert(ab < 0i8);
        }
    }

    pub proof fn lemma_cmp_eq_zero_iff_eq_from_total_contracts(
        a: &Self,
        b: &Self,
        ab: i8,
    )
        requires
            ab == -1 || ab == 0 || ab == 1,
            ab == -1 ==> Self::limbs_value_spec(a.limbs_le@) < Self::limbs_value_spec(b.limbs_le@),
            ab == 0 ==> Self::limbs_value_spec(a.limbs_le@) == Self::limbs_value_spec(b.limbs_le@),
            ab == 1 ==> Self::limbs_value_spec(a.limbs_le@) > Self::limbs_value_spec(b.limbs_le@),
        ensures
            (ab == 0i8) <==> (Self::limbs_value_spec(a.limbs_le@) == Self::limbs_value_spec(b.limbs_le@)),
    {
        let a_val = Self::limbs_value_spec(a.limbs_le@);
        let b_val = Self::limbs_value_spec(b.limbs_le@);

        if ab == 0i8 {
            assert(a_val == b_val);
        }

        if a_val == b_val {
            assert(ab != -1) by {
                if ab == -1 {
                    assert(a_val < b_val);
                    assert(!(a_val < b_val));
                }
            };
            assert(ab != 1) by {
                if ab == 1 {
                    assert(a_val > b_val);
                    assert(!(a_val > b_val));
                }
            };
            if ab == 0 {
            } else if ab == -1 {
                assert(false);
            } else {
                assert(ab == 1);
                assert(false);
            }
            assert(ab == 0i8);
        }
    }

    pub proof fn lemma_model_add_sub_inverse_from_total_contracts(
        self_in: &Self,
        rhs: &Self,
        sub_out: &Self,
        add_out: &Self,
    )
        requires
            Self::limbs_value_spec(rhs.limbs_le@) <= Self::limbs_value_spec(self_in.limbs_le@),
            Self::limbs_value_spec(self_in.limbs_le@) <= Self::limbs_value_spec(rhs.limbs_le@)
                ==> sub_out.model@ == 0,
            Self::limbs_value_spec(rhs.limbs_le@) < Self::limbs_value_spec(self_in.limbs_le@)
                ==> sub_out.model@
                    == Self::limbs_value_spec(self_in.limbs_le@) - Self::limbs_value_spec(rhs.limbs_le@),
            add_out.model@ == sub_out.model@ + Self::limbs_value_spec(rhs.limbs_le@),
        ensures
            add_out.model@ == Self::limbs_value_spec(self_in.limbs_le@),
    {
        let self_val = Self::limbs_value_spec(self_in.limbs_le@);
        let rhs_val = Self::limbs_value_spec(rhs.limbs_le@);

        if rhs_val == self_val {
            assert(self_val <= rhs_val);
            assert(sub_out.model@ == 0);
            assert(add_out.model@ == sub_out.model@ + rhs_val);
            assert(add_out.model@ == 0 + rhs_val);
            assert(add_out.model@ == rhs_val);
            assert(add_out.model@ == self_val);
        } else {
            assert(rhs_val != self_val);
            assert(rhs_val < self_val);
            assert(sub_out.model@ == self_val - rhs_val);
            assert(add_out.model@ == sub_out.model@ + rhs_val);
            assert(add_out.model@ == (self_val - rhs_val) + rhs_val);
            assert((self_val - rhs_val) + rhs_val == self_val);
            assert(add_out.model@ == self_val);
        }
    }

    pub proof fn lemma_model_sub_add_inverse_ge_from_total_contracts(
        a: &Self,
        b: &Self,
        sub_ab: &Self,
        add_sub_ab_b: &Self,
    )
        requires
            Self::limbs_value_spec(b.limbs_le@) <= Self::limbs_value_spec(a.limbs_le@),
            Self::limbs_value_spec(a.limbs_le@) <= Self::limbs_value_spec(b.limbs_le@)
                ==> sub_ab.model@ == 0,
            Self::limbs_value_spec(b.limbs_le@) < Self::limbs_value_spec(a.limbs_le@)
                ==> sub_ab.model@
                    == Self::limbs_value_spec(a.limbs_le@) - Self::limbs_value_spec(b.limbs_le@),
            add_sub_ab_b.model@ == sub_ab.model@ + Self::limbs_value_spec(b.limbs_le@),
        ensures
            add_sub_ab_b.model@ == Self::limbs_value_spec(a.limbs_le@),
    {
        Self::lemma_model_add_sub_inverse_from_total_contracts(a, b, sub_ab, add_sub_ab_b);
    }

    pub proof fn lemma_model_sub_zero_iff_le_from_total_contracts(
        a: &Self,
        b: &Self,
        sub_ab: &Self,
    )
        requires
            Self::limbs_value_spec(a.limbs_le@) <= Self::limbs_value_spec(b.limbs_le@)
                ==> sub_ab.model@ == 0,
            Self::limbs_value_spec(b.limbs_le@) < Self::limbs_value_spec(a.limbs_le@)
                ==> sub_ab.model@
                    == Self::limbs_value_spec(a.limbs_le@) - Self::limbs_value_spec(b.limbs_le@),
        ensures
            (sub_ab.model@ == 0) <==> (Self::limbs_value_spec(a.limbs_le@) <= Self::limbs_value_spec(b.limbs_le@)),
    {
        let a_val = Self::limbs_value_spec(a.limbs_le@);
        let b_val = Self::limbs_value_spec(b.limbs_le@);

        if a_val <= b_val {
            assert(sub_ab.model@ == 0);
        }

        if sub_ab.model@ == 0 {
            if b_val < a_val {
                let d = a_val - b_val;
                assert(sub_ab.model@ == a_val - b_val);
                assert(a_val == b_val + d);
                assert(b_val + 1 <= a_val);
                assert(b_val + 1 <= b_val + d);
                assert(1 <= d);
                assert(0 < d);
                assert(0 < sub_ab.model@);
                assert(sub_ab.model@ == 0);
                assert(false);
            }
            assert(!(b_val < a_val));
            assert(a_val <= b_val);
        }
    }

    pub proof fn lemma_model_add_monotonic_from_total_contracts(
        a: &Self,
        b: &Self,
        c: &Self,
        add_ac: &Self,
        add_bc: &Self,
    )
        requires
            Self::limbs_value_spec(a.limbs_le@) <= Self::limbs_value_spec(b.limbs_le@),
            add_ac.model@
                == Self::limbs_value_spec(a.limbs_le@) + Self::limbs_value_spec(c.limbs_le@),
            add_bc.model@
                == Self::limbs_value_spec(b.limbs_le@) + Self::limbs_value_spec(c.limbs_le@),
        ensures
            add_ac.model@ <= add_bc.model@,
    {
        let a_val = Self::limbs_value_spec(a.limbs_le@);
        let b_val = Self::limbs_value_spec(b.limbs_le@);
        let c_val = Self::limbs_value_spec(c.limbs_le@);

        let ai = a_val as int;
        let bi = b_val as int;
        let ci = c_val as int;
        assert(ai <= bi);
        assert(ai + ci <= bi + ci);
        assert((a_val + c_val) as int == ai + ci);
        assert((b_val + c_val) as int == bi + ci);
        assert((a_val + c_val) as int <= (b_val + c_val) as int);
        assert(a_val + c_val <= b_val + c_val);
        assert(add_ac.model@ == a_val + c_val);
        assert(add_bc.model@ == b_val + c_val);
        assert(add_ac.model@ <= add_bc.model@);
    }

    pub proof fn lemma_model_mul_monotonic_from_total_contracts(
        a: &Self,
        b: &Self,
        c: &Self,
        mul_ac: &Self,
        mul_bc: &Self,
    )
        requires
            Self::limbs_value_spec(a.limbs_le@) <= Self::limbs_value_spec(b.limbs_le@),
            mul_ac.model@
                == Self::limbs_value_spec(a.limbs_le@) * Self::limbs_value_spec(c.limbs_le@),
            mul_bc.model@
                == Self::limbs_value_spec(b.limbs_le@) * Self::limbs_value_spec(c.limbs_le@),
        ensures
            mul_ac.model@ <= mul_bc.model@,
    {
        let a_val = Self::limbs_value_spec(a.limbs_le@);
        let b_val = Self::limbs_value_spec(b.limbs_le@);
        let c_val = Self::limbs_value_spec(c.limbs_le@);

        let d = b_val - a_val;
        assert(b_val == a_val + d);
        assert(b_val * c_val == (a_val + d) * c_val);
        assert((a_val + d) * c_val == a_val * c_val + d * c_val) by (nonlinear_arith);
        assert(0 <= d * c_val);
        assert(a_val * c_val <= a_val * c_val + d * c_val);
        assert(a_val * c_val <= b_val * c_val);
        assert(mul_ac.model@ == a_val * c_val);
        assert(mul_bc.model@ == b_val * c_val);
        assert(mul_ac.model@ <= mul_bc.model@);
    }

    pub proof fn lemma_model_add_strict_monotonic_from_total_contracts(
        a: &Self,
        b: &Self,
        c: &Self,
        add_ac: &Self,
        add_bc: &Self,
    )
        requires
            Self::limbs_value_spec(a.limbs_le@) < Self::limbs_value_spec(b.limbs_le@),
            add_ac.model@
                == Self::limbs_value_spec(a.limbs_le@) + Self::limbs_value_spec(c.limbs_le@),
            add_bc.model@
                == Self::limbs_value_spec(b.limbs_le@) + Self::limbs_value_spec(c.limbs_le@),
        ensures
            add_ac.model@ < add_bc.model@,
    {
        let a_val = Self::limbs_value_spec(a.limbs_le@);
        let b_val = Self::limbs_value_spec(b.limbs_le@);
        let c_val = Self::limbs_value_spec(c.limbs_le@);

        let d = b_val - a_val;
        assert(0 < d);
        assert(b_val == a_val + d);
        assert(b_val + c_val == a_val + c_val + d);
        assert(a_val + c_val < a_val + c_val + d);
        assert(a_val + c_val < b_val + c_val);
        assert(add_ac.model@ == a_val + c_val);
        assert(add_bc.model@ == b_val + c_val);
        assert(add_ac.model@ < add_bc.model@);
    }

    pub proof fn lemma_model_mul_strict_monotonic_pos_from_total_contracts(
        a: &Self,
        b: &Self,
        c: &Self,
        mul_ac: &Self,
        mul_bc: &Self,
    )
        requires
            Self::limbs_value_spec(c.limbs_le@) > 0,
            Self::limbs_value_spec(a.limbs_le@) < Self::limbs_value_spec(b.limbs_le@),
            mul_ac.model@
                == Self::limbs_value_spec(a.limbs_le@) * Self::limbs_value_spec(c.limbs_le@),
            mul_bc.model@
                == Self::limbs_value_spec(b.limbs_le@) * Self::limbs_value_spec(c.limbs_le@),
        ensures
            mul_ac.model@ < mul_bc.model@,
    {
        let a_val = Self::limbs_value_spec(a.limbs_le@);
        let b_val = Self::limbs_value_spec(b.limbs_le@);
        let c_val = Self::limbs_value_spec(c.limbs_le@);

        let d = b_val - a_val;
        assert(0 < d);
        assert(b_val == a_val + d);
        assert(b_val * c_val == (a_val + d) * c_val);
        assert((a_val + d) * c_val == a_val * c_val + d * c_val) by (nonlinear_arith);
        assert(1 <= d);
        assert(d == 1 + (d - 1));
        assert(d * c_val == (1 + (d - 1)) * c_val);
        assert((1 + (d - 1)) * c_val == c_val + (d - 1) * c_val) by (nonlinear_arith);
        assert(0 <= (d - 1) * c_val);
        assert(c_val <= c_val + (d - 1) * c_val);
        assert(c_val <= d * c_val);
        assert(0 < c_val);
        assert(0 < d * c_val);
        assert(a_val * c_val < a_val * c_val + d * c_val);
        assert(a_val * c_val < b_val * c_val);
        assert(mul_ac.model@ == a_val * c_val);
        assert(mul_bc.model@ == b_val * c_val);
        assert(mul_ac.model@ < mul_bc.model@);
    }

    pub proof fn lemma_model_add_cancellation_from_total_contracts(
        a: &Self,
        b: &Self,
        c: &Self,
        add_ac: &Self,
        add_bc: &Self,
    )
        requires
            add_ac.model@
                == Self::limbs_value_spec(a.limbs_le@) + Self::limbs_value_spec(c.limbs_le@),
            add_bc.model@
                == Self::limbs_value_spec(b.limbs_le@) + Self::limbs_value_spec(c.limbs_le@),
            add_ac.model@ == add_bc.model@,
        ensures
            Self::limbs_value_spec(a.limbs_le@) == Self::limbs_value_spec(b.limbs_le@),
    {
        let a_val = Self::limbs_value_spec(a.limbs_le@);
        let b_val = Self::limbs_value_spec(b.limbs_le@);

        if a_val < b_val {
            Self::lemma_model_add_strict_monotonic_from_total_contracts(a, b, c, add_ac, add_bc);
            assert(add_ac.model@ < add_bc.model@);
            assert(add_ac.model@ == add_bc.model@);
            assert(false);
        }

        if b_val < a_val {
            Self::lemma_model_add_strict_monotonic_from_total_contracts(b, a, c, add_bc, add_ac);
            assert(add_bc.model@ < add_ac.model@);
            assert(add_ac.model@ == add_bc.model@);
            assert(false);
        }

        assert(!(a_val < b_val));
        assert(!(b_val < a_val));
        let ai = a_val as int;
        let bi = b_val as int;
        assert(!(ai < bi));
        assert(!(bi < ai));
        assert(ai == bi);
        assert(a_val == b_val);
    }

    pub proof fn lemma_model_mul_cancellation_pos_from_total_contracts(
        a: &Self,
        b: &Self,
        c: &Self,
        mul_ac: &Self,
        mul_bc: &Self,
    )
        requires
            Self::limbs_value_spec(c.limbs_le@) > 0,
            mul_ac.model@
                == Self::limbs_value_spec(a.limbs_le@) * Self::limbs_value_spec(c.limbs_le@),
            mul_bc.model@
                == Self::limbs_value_spec(b.limbs_le@) * Self::limbs_value_spec(c.limbs_le@),
            mul_ac.model@ == mul_bc.model@,
        ensures
            Self::limbs_value_spec(a.limbs_le@) == Self::limbs_value_spec(b.limbs_le@),
    {
        let a_val = Self::limbs_value_spec(a.limbs_le@);
        let b_val = Self::limbs_value_spec(b.limbs_le@);

        if a_val < b_val {
            Self::lemma_model_mul_strict_monotonic_pos_from_total_contracts(a, b, c, mul_ac, mul_bc);
            assert(mul_ac.model@ < mul_bc.model@);
            assert(mul_ac.model@ == mul_bc.model@);
            assert(false);
        }

        if b_val < a_val {
            Self::lemma_model_mul_strict_monotonic_pos_from_total_contracts(b, a, c, mul_bc, mul_ac);
            assert(mul_bc.model@ < mul_ac.model@);
            assert(mul_ac.model@ == mul_bc.model@);
            assert(false);
        }

        assert(!(a_val < b_val));
        assert(!(b_val < a_val));
        let ai = a_val as int;
        let bi = b_val as int;
        assert(!(ai < bi));
        assert(!(bi < ai));
        assert(ai == bi);
        assert(a_val == b_val);
    }

    pub proof fn lemma_model_div_monotonic_pos_from_total_contracts(
        a: &Self,
        b: &Self,
        d: &Self,
        div_a: &Self,
        div_b: &Self,
    )
        requires
            Self::limbs_value_spec(d.limbs_le@) > 0,
            Self::limbs_value_spec(a.limbs_le@) <= Self::limbs_value_spec(b.limbs_le@),
            div_a.model@ * Self::limbs_value_spec(d.limbs_le@) <= Self::limbs_value_spec(a.limbs_le@),
            Self::limbs_value_spec(b.limbs_le@) < (div_b.model@ + 1) * Self::limbs_value_spec(d.limbs_le@),
        ensures
            div_a.model@ <= div_b.model@,
    {
        let a_val = Self::limbs_value_spec(a.limbs_le@);
        let b_val = Self::limbs_value_spec(b.limbs_le@);
        let d_val = Self::limbs_value_spec(d.limbs_le@);
        let qa = div_a.model@;
        let qb = div_b.model@;

        if qb < qa {
            assert(qb + 1 <= qa);
            assert(d_val > 0);
            let t = qa - (qb + 1);
            assert(qa == qb + 1 + t);
            assert(qa * d_val == (qb + 1 + t) * d_val);
            assert((qb + 1 + t) * d_val == (qb + 1) * d_val + t * d_val) by (nonlinear_arith);
            assert(0 <= t * d_val);
            assert((qb + 1) * d_val <= (qb + 1) * d_val + t * d_val);
            assert((qb + 1) * d_val <= qa * d_val);
            assert(qa * d_val <= a_val);
            assert(a_val <= b_val);
            assert((qb + 1) * d_val <= b_val);
            assert(b_val < (qb + 1) * d_val);
            assert(false);
        }

        assert(!(qb < qa));
        let qai = qa as int;
        let qbi = qb as int;
        assert(!(qbi < qai));
        assert(qai <= qbi);
        assert(qa <= qb);
    }

    pub proof fn lemma_model_rem_upper_bound_pos_from_total_contracts(
        a: &Self,
        d: &Self,
        rem_a: &Self,
    )
        requires
            Self::limbs_value_spec(d.limbs_le@) > 0,
            rem_a.model@ == Self::limbs_value_spec(a.limbs_le@) % Self::limbs_value_spec(d.limbs_le@),
        ensures
            rem_a.model@ < Self::limbs_value_spec(d.limbs_le@),
    {
        let a_val = Self::limbs_value_spec(a.limbs_le@);
        let d_val = Self::limbs_value_spec(d.limbs_le@);
        let ai = a_val as int;
        let di = d_val as int;

        assert(di > 0);
        lemma_mod_pos_bound(ai, di);
        assert((a_val % d_val) as int == ai % di);
        assert(((a_val % d_val) as int) < di);
        assert(((a_val % d_val) as int) < d_val as int);
        assert(a_val % d_val < d_val);
        assert(rem_a.model@ == a_val % d_val);
        assert(rem_a.model@ < d_val);
    }

    pub proof fn lemma_model_add_commutative_from_total_contracts(
        a: &Self,
        b: &Self,
        add_ab: &Self,
        add_ba: &Self,
    )
        requires
            add_ab.model@
                == Self::limbs_value_spec(a.limbs_le@) + Self::limbs_value_spec(b.limbs_le@),
            add_ba.model@
                == Self::limbs_value_spec(b.limbs_le@) + Self::limbs_value_spec(a.limbs_le@),
        ensures
            add_ab.model@ == add_ba.model@,
    {
        let a_val = Self::limbs_value_spec(a.limbs_le@);
        let b_val = Self::limbs_value_spec(b.limbs_le@);
        assert(add_ab.model@ == a_val + b_val);
        assert(add_ba.model@ == b_val + a_val);
        assert(a_val + b_val == b_val + a_val);
        assert(add_ab.model@ == add_ba.model@);
    }

    pub proof fn lemma_model_add_associative_from_total_contracts(
        a: &Self,
        b: &Self,
        c: &Self,
        add_ab_c: &Self,
        add_a_bc: &Self,
    )
        requires
            add_ab_c.model@
                == (Self::limbs_value_spec(a.limbs_le@) + Self::limbs_value_spec(b.limbs_le@))
                    + Self::limbs_value_spec(c.limbs_le@),
            add_a_bc.model@
                == Self::limbs_value_spec(a.limbs_le@)
                    + (Self::limbs_value_spec(b.limbs_le@) + Self::limbs_value_spec(c.limbs_le@)),
        ensures
            add_ab_c.model@ == add_a_bc.model@,
    {
        let a_val = Self::limbs_value_spec(a.limbs_le@);
        let b_val = Self::limbs_value_spec(b.limbs_le@);
        let c_val = Self::limbs_value_spec(c.limbs_le@);
        assert(add_ab_c.model@ == (a_val + b_val) + c_val);
        assert(add_a_bc.model@ == a_val + (b_val + c_val));
        assert((a_val + b_val) + c_val == a_val + (b_val + c_val));
        assert(add_ab_c.model@ == add_a_bc.model@);
    }

    pub proof fn lemma_model_mul_commutative_from_total_contracts(
        a: &Self,
        b: &Self,
        mul_ab: &Self,
        mul_ba: &Self,
    )
        requires
            mul_ab.model@
                == Self::limbs_value_spec(a.limbs_le@) * Self::limbs_value_spec(b.limbs_le@),
            mul_ba.model@
                == Self::limbs_value_spec(b.limbs_le@) * Self::limbs_value_spec(a.limbs_le@),
        ensures
            mul_ab.model@ == mul_ba.model@,
    {
        let a_val = Self::limbs_value_spec(a.limbs_le@);
        let b_val = Self::limbs_value_spec(b.limbs_le@);
        assert(mul_ab.model@ == a_val * b_val);
        assert(mul_ba.model@ == b_val * a_val);
        assert(a_val * b_val == b_val * a_val) by (nonlinear_arith);
        assert(mul_ab.model@ == mul_ba.model@);
    }

    pub proof fn lemma_model_mul_associative_from_total_contracts(
        a: &Self,
        b: &Self,
        c: &Self,
        mul_ab_c: &Self,
        mul_a_bc: &Self,
    )
        requires
            mul_ab_c.model@
                == (Self::limbs_value_spec(a.limbs_le@) * Self::limbs_value_spec(b.limbs_le@))
                    * Self::limbs_value_spec(c.limbs_le@),
            mul_a_bc.model@
                == Self::limbs_value_spec(a.limbs_le@)
                    * (Self::limbs_value_spec(b.limbs_le@) * Self::limbs_value_spec(c.limbs_le@)),
        ensures
            mul_ab_c.model@ == mul_a_bc.model@,
    {
        let a_val = Self::limbs_value_spec(a.limbs_le@);
        let b_val = Self::limbs_value_spec(b.limbs_le@);
        let c_val = Self::limbs_value_spec(c.limbs_le@);
        assert(mul_ab_c.model@ == (a_val * b_val) * c_val);
        assert(mul_a_bc.model@ == a_val * (b_val * c_val));
        assert((a_val * b_val) * c_val == a_val * (b_val * c_val)) by (nonlinear_arith);
        assert(mul_ab_c.model@ == mul_a_bc.model@);
    }

    pub proof fn lemma_model_mul_distributes_over_add_from_total_contracts(
        a: &Self,
        b: &Self,
        c: &Self,
        mul_a_b_plus_c: &Self,
        add_mul_ab_mul_ac: &Self,
    )
        requires
            mul_a_b_plus_c.model@
                == Self::limbs_value_spec(a.limbs_le@)
                    * (Self::limbs_value_spec(b.limbs_le@) + Self::limbs_value_spec(c.limbs_le@)),
            add_mul_ab_mul_ac.model@
                == Self::limbs_value_spec(a.limbs_le@) * Self::limbs_value_spec(b.limbs_le@)
                    + Self::limbs_value_spec(a.limbs_le@) * Self::limbs_value_spec(c.limbs_le@),
        ensures
            mul_a_b_plus_c.model@ == add_mul_ab_mul_ac.model@,
    {
        let a_val = Self::limbs_value_spec(a.limbs_le@);
        let b_val = Self::limbs_value_spec(b.limbs_le@);
        let c_val = Self::limbs_value_spec(c.limbs_le@);
        assert(mul_a_b_plus_c.model@ == a_val * (b_val + c_val));
        assert(add_mul_ab_mul_ac.model@ == a_val * b_val + a_val * c_val);
        assert(a_val * (b_val + c_val) == a_val * b_val + a_val * c_val) by (nonlinear_arith);
        assert(mul_a_b_plus_c.model@ == add_mul_ab_mul_ac.model@);
    }

    /// Operation-level wrapper: computes both sums and proves additive commutativity.
    pub fn lemma_model_add_commutative_ops(a: &Self, b: &Self) -> (out: (Self, Self))
        requires
            a.wf_spec(),
            b.wf_spec(),
        ensures
            out.0.wf_spec(),
            out.1.wf_spec(),
            out.0.model@ == a.model@ + b.model@,
            out.1.model@ == b.model@ + a.model@,
            out.0.model@ == out.1.model@,
    {
        let add_ab = a.add_limbwise_small_total(b);
        let add_ba = b.add_limbwise_small_total(a);
        proof {
            assert(a.model@ == Self::limbs_value_spec(a.limbs_le@));
            assert(b.model@ == Self::limbs_value_spec(b.limbs_le@));
            assert(add_ab.model@ == a.model@ + b.model@);
            assert(add_ba.model@ == b.model@ + a.model@);
            assert(add_ab.model@
                == Self::limbs_value_spec(a.limbs_le@) + Self::limbs_value_spec(b.limbs_le@));
            assert(add_ba.model@
                == Self::limbs_value_spec(b.limbs_le@) + Self::limbs_value_spec(a.limbs_le@));
            Self::lemma_model_add_commutative_from_total_contracts(a, b, &add_ab, &add_ba);
        }
        (add_ab, add_ba)
    }

    /// Operation-level wrapper: computes both sums and proves additive monotonicity.
    pub fn lemma_model_add_monotonic_ops(a: &Self, b: &Self, c: &Self) -> (out: (Self, Self))
        requires
            a.wf_spec(),
            b.wf_spec(),
            c.wf_spec(),
            a.model@ <= b.model@,
        ensures
            out.0.wf_spec(),
            out.1.wf_spec(),
            out.0.model@ == a.model@ + c.model@,
            out.1.model@ == b.model@ + c.model@,
            out.0.model@ <= out.1.model@,
    {
        let add_ac = a.add_limbwise_small_total(c);
        let add_bc = b.add_limbwise_small_total(c);
        proof {
            assert(a.model@ == Self::limbs_value_spec(a.limbs_le@));
            assert(b.model@ == Self::limbs_value_spec(b.limbs_le@));
            assert(c.model@ == Self::limbs_value_spec(c.limbs_le@));
            assert(a.model@ <= b.model@);
            assert(
                Self::limbs_value_spec(a.limbs_le@)
                    <= Self::limbs_value_spec(b.limbs_le@)
            );
            assert(add_ac.model@ == a.model@ + c.model@);
            assert(add_bc.model@ == b.model@ + c.model@);
            assert(add_ac.model@
                == Self::limbs_value_spec(a.limbs_le@) + Self::limbs_value_spec(c.limbs_le@));
            assert(add_bc.model@
                == Self::limbs_value_spec(b.limbs_le@) + Self::limbs_value_spec(c.limbs_le@));
            Self::lemma_model_add_monotonic_from_total_contracts(a, b, c, &add_ac, &add_bc);
        }
        (add_ac, add_bc)
    }

    /// Operation-level wrapper: computes sum and proves canonical length upper bounds.
    pub fn lemma_model_add_len_bound_ops(a: &Self, b: &Self) -> (out: Self)
        requires
            a.wf_spec(),
            b.wf_spec(),
        ensures
            out.wf_spec(),
            out.model@ == a.model@ + b.model@,
            a.limbs_le@.len() >= b.limbs_le@.len() ==> out.limbs_le@.len() <= a.limbs_le@.len() + 1,
            b.limbs_le@.len() >= a.limbs_le@.len() ==> out.limbs_le@.len() <= b.limbs_le@.len() + 1,
    {
        let out_sum = a.add_limbwise_small_total(b);
        proof {
            let alen = a.limbs_le@.len();
            let blen = b.limbs_le@.len();
            assert(a.model@ == Self::limbs_value_spec(a.limbs_le@));
            assert(b.model@ == Self::limbs_value_spec(b.limbs_le@));
            assert(out_sum.model@ == a.model@ + b.model@);
            assert(out_sum.wf_spec());
            assert(Self::canonical_limbs_spec(out_sum.limbs_le@));
            Self::lemma_limbs_value_lt_pow_len(a.limbs_le@);
            Self::lemma_limbs_value_lt_pow_len(b.limbs_le@);
            assert(a.model@ < Self::pow_base_spec(alen));
            assert(b.model@ < Self::pow_base_spec(blen));

            if alen >= blen {
                Self::lemma_pow_monotonic(blen, alen);
                assert(Self::pow_base_spec(blen) <= Self::pow_base_spec(alen));
                assert(b.model@ < Self::pow_base_spec(alen));
                let p = Self::pow_base_spec(alen);
                let ai = a.model@ as int;
                let bi = b.model@ as int;
                let pi = p as int;
                assert(ai < pi);
                assert(bi < pi);
                assert(ai + bi < pi + pi);
                assert((a.model@ + b.model@) as int == ai + bi);
                assert((p + p) as int == pi + pi);
                let sum_i = (a.model@ + b.model@) as int;
                let two_p_i = (p + p) as int;
                assert(sum_i < two_p_i);
                assert(a.model@ + b.model@ < p + p);
                assert(
                    Self::pow_base_spec(alen) + Self::pow_base_spec(alen)
                        == 2 * Self::pow_base_spec(alen)
                ) by (nonlinear_arith);
                Self::lemma_pow_base_succ(alen);
                assert(Self::limb_base_spec() == 4_294_967_296);
                assert(2 <= Self::limb_base_spec());
                assert(
                    2 * Self::pow_base_spec(alen)
                        <= Self::limb_base_spec() * Self::pow_base_spec(alen)
                ) by (nonlinear_arith);
                assert(Self::pow_base_spec(alen + 1) == Self::limb_base_spec() * Self::pow_base_spec(alen));
                assert(a.model@ + b.model@ < Self::pow_base_spec(alen + 1));
                assert(out_sum.model@ < Self::pow_base_spec(alen + 1));
                Self::lemma_len_bound_from_value_upper_pow(out_sum.limbs_le@, alen + 1);
                assert(out_sum.limbs_le@.len() <= alen + 1);
            }

            if blen >= alen {
                Self::lemma_pow_monotonic(alen, blen);
                assert(Self::pow_base_spec(alen) <= Self::pow_base_spec(blen));
                assert(a.model@ < Self::pow_base_spec(blen));
                let p = Self::pow_base_spec(blen);
                let ai = a.model@ as int;
                let bi = b.model@ as int;
                let pi = p as int;
                assert(ai < pi);
                assert(bi < pi);
                assert(ai + bi < pi + pi);
                assert((a.model@ + b.model@) as int == ai + bi);
                assert((p + p) as int == pi + pi);
                let sum_i = (a.model@ + b.model@) as int;
                let two_p_i = (p + p) as int;
                assert(sum_i < two_p_i);
                assert(a.model@ + b.model@ < p + p);
                assert(
                    Self::pow_base_spec(blen) + Self::pow_base_spec(blen)
                        == 2 * Self::pow_base_spec(blen)
                ) by (nonlinear_arith);
                Self::lemma_pow_base_succ(blen);
                assert(Self::limb_base_spec() == 4_294_967_296);
                assert(2 <= Self::limb_base_spec());
                assert(
                    2 * Self::pow_base_spec(blen)
                        <= Self::limb_base_spec() * Self::pow_base_spec(blen)
                ) by (nonlinear_arith);
                assert(Self::pow_base_spec(blen + 1) == Self::limb_base_spec() * Self::pow_base_spec(blen));
                assert(a.model@ + b.model@ < Self::pow_base_spec(blen + 1));
                assert(out_sum.model@ < Self::pow_base_spec(blen + 1));
                Self::lemma_len_bound_from_value_upper_pow(out_sum.limbs_le@, blen + 1);
                assert(out_sum.limbs_le@.len() <= blen + 1);
            }
        }
        out_sum
    }

    /// Operation-level wrapper: computes both products and proves multiplicative commutativity.
    pub fn lemma_model_mul_commutative_ops(a: &Self, b: &Self) -> (out: (Self, Self))
        requires
            a.wf_spec(),
            b.wf_spec(),
        ensures
            out.0.wf_spec(),
            out.1.wf_spec(),
            out.0.model@ == a.model@ * b.model@,
            out.1.model@ == b.model@ * a.model@,
            out.0.model@ == out.1.model@,
    {
        let mul_ab = a.mul_limbwise_small_total(b);
        let mul_ba = b.mul_limbwise_small_total(a);
        proof {
            assert(a.model@ == Self::limbs_value_spec(a.limbs_le@));
            assert(b.model@ == Self::limbs_value_spec(b.limbs_le@));
            assert(mul_ab.model@ == a.model@ * b.model@);
            assert(mul_ba.model@ == b.model@ * a.model@);
            assert(mul_ab.model@
                == Self::limbs_value_spec(a.limbs_le@) * Self::limbs_value_spec(b.limbs_le@));
            assert(mul_ba.model@
                == Self::limbs_value_spec(b.limbs_le@) * Self::limbs_value_spec(a.limbs_le@));
            Self::lemma_model_mul_commutative_from_total_contracts(a, b, &mul_ab, &mul_ba);
        }
        (mul_ab, mul_ba)
    }

    /// Operation-level wrapper: computes both products and proves multiplicative monotonicity.
    pub fn lemma_model_mul_monotonic_ops(a: &Self, b: &Self, c: &Self) -> (out: (Self, Self))
        requires
            a.wf_spec(),
            b.wf_spec(),
            c.wf_spec(),
            a.model@ <= b.model@,
        ensures
            out.0.wf_spec(),
            out.1.wf_spec(),
            out.0.model@ == a.model@ * c.model@,
            out.1.model@ == b.model@ * c.model@,
            out.0.model@ <= out.1.model@,
    {
        let mul_ac = a.mul_limbwise_small_total(c);
        let mul_bc = b.mul_limbwise_small_total(c);
        proof {
            assert(a.model@ == Self::limbs_value_spec(a.limbs_le@));
            assert(b.model@ == Self::limbs_value_spec(b.limbs_le@));
            assert(c.model@ == Self::limbs_value_spec(c.limbs_le@));
            assert(a.model@ <= b.model@);
            assert(
                Self::limbs_value_spec(a.limbs_le@)
                    <= Self::limbs_value_spec(b.limbs_le@)
            );
            assert(mul_ac.model@ == a.model@ * c.model@);
            assert(mul_bc.model@ == b.model@ * c.model@);
            assert(mul_ac.model@
                == Self::limbs_value_spec(a.limbs_le@) * Self::limbs_value_spec(c.limbs_le@));
            assert(mul_bc.model@
                == Self::limbs_value_spec(b.limbs_le@) * Self::limbs_value_spec(c.limbs_le@));
            Self::lemma_model_mul_monotonic_from_total_contracts(a, b, c, &mul_ac, &mul_bc);
        }
        (mul_ac, mul_bc)
    }

    /// Operation-level wrapper: computes product and proves canonical length upper bound.
    pub fn lemma_model_mul_len_bound_ops(a: &Self, b: &Self) -> (out: Self)
        requires
            a.wf_spec(),
            b.wf_spec(),
        ensures
            out.wf_spec(),
            out.model@ == a.model@ * b.model@,
            out.limbs_le@.len() <= a.limbs_le@.len() + b.limbs_le@.len(),
    {
        let out_mul = a.mul_limbwise_small_total(b);
        proof {
            let alen = a.limbs_le@.len();
            let blen = b.limbs_le@.len();
            let pa = Self::pow_base_spec(alen);
            let pb = Self::pow_base_spec(blen);

            assert(a.model@ == Self::limbs_value_spec(a.limbs_le@));
            assert(b.model@ == Self::limbs_value_spec(b.limbs_le@));
            assert(out_mul.model@ == a.model@ * b.model@);
            assert(out_mul.wf_spec());
            assert(Self::canonical_limbs_spec(out_mul.limbs_le@));

            Self::lemma_limbs_value_lt_pow_len(a.limbs_le@);
            Self::lemma_limbs_value_lt_pow_len(b.limbs_le@);
            assert(a.model@ < pa);
            assert(b.model@ < pb);
            Self::lemma_pow_ge_one(alen);
            Self::lemma_pow_ge_one(blen);
            assert(1 <= pa);
            assert(1 <= pb);
            assert(a.model@ <= pa - 1);
            assert(b.model@ <= pb - 1);
            assert(0 <= pa - 1);
            assert(0 <= pb - 1);
            let d1 = (pa - 1) - a.model@;
            assert(pa - 1 == a.model@ + d1);
            assert((a.model@ + d1) * b.model@ == a.model@ * b.model@ + d1 * b.model@)
                by (nonlinear_arith);
            assert((pa - 1) * b.model@ == (a.model@ + d1) * b.model@);
            assert((pa - 1) * b.model@ == a.model@ * b.model@ + d1 * b.model@);
            assert(0 <= d1 * b.model@);
            assert(a.model@ * b.model@ <= (pa - 1) * b.model@);
            let d2 = (pb - 1) - b.model@;
            assert(pb - 1 == b.model@ + d2);
            assert((pa - 1) * (b.model@ + d2) == (pa - 1) * b.model@ + (pa - 1) * d2)
                by (nonlinear_arith);
            assert((pa - 1) * (pb - 1) == (pa - 1) * (b.model@ + d2));
            assert((pa - 1) * (pb - 1) == (pa - 1) * b.model@ + (pa - 1) * d2);
            assert(0 <= (pa - 1) * d2);
            assert((pa - 1) * b.model@ <= (pa - 1) * (pb - 1));
            assert(out_mul.model@ <= (pa - 1) * (pb - 1));
            assert(pa == (pa - 1) + 1);
            assert(pb == (pb - 1) + 1);
            assert(
                pa * pb
                    == (pa - 1) * (pb - 1) + (pa - 1) + (pb - 1) + 1
            ) by (nonlinear_arith);
            assert(0 <= (pa - 1) + (pb - 1) + 1);
            assert((pa - 1) * (pb - 1) < pa * pb);
            assert(out_mul.model@ < pa * pb);

            Self::lemma_pow_add(alen, blen);
            assert(Self::pow_base_spec(alen + blen) == pa * pb);
            assert(out_mul.model@ < Self::pow_base_spec(alen + blen));
            Self::lemma_len_bound_from_value_upper_pow(out_mul.limbs_le@, alen + blen);
            assert(out_mul.limbs_le@.len() <= alen + blen);
        }
        out_mul
    }

    /// Operation-level wrapper: proves tight nonzero limb-length/value window.
    pub fn lemma_model_len_window_nonzero_ops(a: &Self)
        requires
            a.wf_spec(),
            a.model@ > 0,
        ensures
            a.limbs_le@.len() > 0,
            Self::pow_base_spec((a.limbs_le@.len() - 1) as nat) <= a.model@,
            a.model@ < Self::pow_base_spec(a.limbs_le@.len()),
    {
        proof {
            assert(a.model@ == Self::limbs_value_spec(a.limbs_le@));
            if a.limbs_le@.len() == 0 {
                assert(Self::limbs_value_spec(a.limbs_le@) == 0);
                assert(a.model@ == 0);
                assert(a.model@ > 0);
                assert(false);
            }
            assert(a.limbs_le@.len() > 0);
            assert(Self::canonical_limbs_spec(a.limbs_le@));
            assert(a.limbs_le@[(a.limbs_le@.len() - 1) as int] != 0u32);
            Self::lemma_limbs_value_ge_pow_last_nonzero(a.limbs_le@);
            Self::lemma_limbs_value_lt_pow_len(a.limbs_le@);
            assert(Self::pow_base_spec((a.limbs_le@.len() - 1) as nat) <= Self::limbs_value_spec(a.limbs_le@));
            assert(Self::limbs_value_spec(a.limbs_le@) < Self::pow_base_spec(a.limbs_le@.len()));
            assert(Self::pow_base_spec((a.limbs_le@.len() - 1) as nat) <= a.model@);
            assert(a.model@ < Self::pow_base_spec(a.limbs_le@.len()));
        }
    }

    /// Operation-level wrapper: zero value implies empty canonical limb vector.
    pub fn lemma_model_zero_implies_len_zero_ops(a: &Self)
        requires
            a.wf_spec(),
            a.model@ == 0,
        ensures
            a.limbs_le@.len() == 0,
    {
        proof {
            assert(a.model@ == Self::limbs_value_spec(a.limbs_le@));
            if a.limbs_le@.len() > 0 {
                assert(Self::canonical_limbs_spec(a.limbs_le@));
                assert(a.limbs_le@[(a.limbs_le@.len() - 1) as int] != 0u32);
                Self::lemma_limbs_value_ge_pow_last_nonzero(a.limbs_le@);
                assert(Self::pow_base_spec((a.limbs_le@.len() - 1) as nat) <= a.model@);
                Self::lemma_pow_ge_one((a.limbs_le@.len() - 1) as nat);
                assert(1 <= Self::pow_base_spec((a.limbs_le@.len() - 1) as nat));
                assert(1 <= a.model@);
                assert(a.model@ == 0);
                assert(false);
            }
            assert(a.limbs_le@.len() == 0);
        }
    }

    /// Operation-level wrapper: computes compare output and proves `cmp <= 0 <==> a <= b`.
    pub fn lemma_cmp_le_zero_iff_le_ops(a: &Self, b: &Self) -> (out: i8)
        requires
            a.wf_spec(),
            b.wf_spec(),
        ensures
            out == -1 || out == 0 || out == 1,
            out == -1 ==> a.model@ < b.model@,
            out == 0 ==> a.model@ == b.model@,
            out == 1 ==> a.model@ > b.model@,
            (out <= 0i8) <==> (a.model@ <= b.model@),
    {
        let out_cmp = a.cmp_limbwise_small_total(b);
        proof {
            assert(a.model@ == Self::limbs_value_spec(a.limbs_le@));
            assert(b.model@ == Self::limbs_value_spec(b.limbs_le@));
            if out_cmp == -1 {
                assert(Self::limbs_value_spec(a.limbs_le@) < Self::limbs_value_spec(b.limbs_le@));
                assert(a.model@ < b.model@);
            }
            if out_cmp == 0 {
                assert(Self::limbs_value_spec(a.limbs_le@) == Self::limbs_value_spec(b.limbs_le@));
                assert(a.model@ == b.model@);
            }
            if out_cmp == 1 {
                assert(Self::limbs_value_spec(a.limbs_le@) > Self::limbs_value_spec(b.limbs_le@));
                assert(a.model@ > b.model@);
            }
            Self::lemma_cmp_le_zero_iff_le_from_total_contracts(a, b, out_cmp);
            assert((out_cmp <= 0i8) <==> (Self::limbs_value_spec(a.limbs_le@) <= Self::limbs_value_spec(b.limbs_le@)));
            assert((out_cmp <= 0i8) <==> (a.model@ <= b.model@));
        }
        out_cmp
    }

    /// Operation-level wrapper: computes compare output and proves `cmp < 0 <==> a < b`.
    pub fn lemma_cmp_lt_zero_iff_lt_ops(a: &Self, b: &Self) -> (out: i8)
        requires
            a.wf_spec(),
            b.wf_spec(),
        ensures
            out == -1 || out == 0 || out == 1,
            out == -1 ==> a.model@ < b.model@,
            out == 0 ==> a.model@ == b.model@,
            out == 1 ==> a.model@ > b.model@,
            (out < 0i8) <==> (a.model@ < b.model@),
    {
        let out_cmp = a.cmp_limbwise_small_total(b);
        proof {
            assert(a.model@ == Self::limbs_value_spec(a.limbs_le@));
            assert(b.model@ == Self::limbs_value_spec(b.limbs_le@));
            if out_cmp == -1 {
                assert(Self::limbs_value_spec(a.limbs_le@) < Self::limbs_value_spec(b.limbs_le@));
                assert(a.model@ < b.model@);
            }
            if out_cmp == 0 {
                assert(Self::limbs_value_spec(a.limbs_le@) == Self::limbs_value_spec(b.limbs_le@));
                assert(a.model@ == b.model@);
            }
            if out_cmp == 1 {
                assert(Self::limbs_value_spec(a.limbs_le@) > Self::limbs_value_spec(b.limbs_le@));
                assert(a.model@ > b.model@);
            }
            Self::lemma_cmp_lt_zero_iff_lt_from_total_contracts(a, b, out_cmp);
            assert((out_cmp < 0i8) <==> (Self::limbs_value_spec(a.limbs_le@) < Self::limbs_value_spec(b.limbs_le@)));
            assert((out_cmp < 0i8) <==> (a.model@ < b.model@));
        }
        out_cmp
    }

    /// Operation-level wrapper: computes compare output and proves `cmp == 0 <==> a == b`.
    pub fn lemma_cmp_eq_zero_iff_eq_ops(a: &Self, b: &Self) -> (out: i8)
        requires
            a.wf_spec(),
            b.wf_spec(),
        ensures
            out == -1 || out == 0 || out == 1,
            out == -1 ==> a.model@ < b.model@,
            out == 0 ==> a.model@ == b.model@,
            out == 1 ==> a.model@ > b.model@,
            (out == 0i8) <==> (a.model@ == b.model@),
    {
        let out_cmp = a.cmp_limbwise_small_total(b);
        proof {
            assert(a.model@ == Self::limbs_value_spec(a.limbs_le@));
            assert(b.model@ == Self::limbs_value_spec(b.limbs_le@));
            if out_cmp == -1 {
                assert(Self::limbs_value_spec(a.limbs_le@) < Self::limbs_value_spec(b.limbs_le@));
                assert(a.model@ < b.model@);
            }
            if out_cmp == 0 {
                assert(Self::limbs_value_spec(a.limbs_le@) == Self::limbs_value_spec(b.limbs_le@));
                assert(a.model@ == b.model@);
            }
            if out_cmp == 1 {
                assert(Self::limbs_value_spec(a.limbs_le@) > Self::limbs_value_spec(b.limbs_le@));
                assert(a.model@ > b.model@);
            }
            Self::lemma_cmp_eq_zero_iff_eq_from_total_contracts(a, b, out_cmp);
            assert((out_cmp == 0i8) <==> (Self::limbs_value_spec(a.limbs_le@) == Self::limbs_value_spec(b.limbs_le@)));
            assert((out_cmp == 0i8) <==> (a.model@ == b.model@));
        }
        out_cmp
    }

    /// Operation-level wrapper: computes subtraction and proves zero-iff-order characterization.
    pub fn lemma_model_sub_zero_iff_le_ops(a: &Self, b: &Self) -> (out: Self)
        requires
            a.wf_spec(),
            b.wf_spec(),
        ensures
            out.wf_spec(),
            (out.model@ == 0) <==> (a.model@ <= b.model@),
    {
        let sub_ab = a.sub_limbwise_small_total(b);
        proof {
            assert(a.model@ == Self::limbs_value_spec(a.limbs_le@));
            assert(b.model@ == Self::limbs_value_spec(b.limbs_le@));
            if Self::limbs_value_spec(a.limbs_le@) <= Self::limbs_value_spec(b.limbs_le@) {
                assert(sub_ab.model@ == 0);
            }
            if Self::limbs_value_spec(b.limbs_le@) < Self::limbs_value_spec(a.limbs_le@) {
                assert(sub_ab.model@ == Self::limbs_value_spec(a.limbs_le@) - Self::limbs_value_spec(b.limbs_le@));
            }
            Self::lemma_model_sub_zero_iff_le_from_total_contracts(a, b, &sub_ab);
            assert((sub_ab.model@ == 0) <==> (Self::limbs_value_spec(a.limbs_le@) <= Self::limbs_value_spec(b.limbs_le@)));
            assert((sub_ab.model@ == 0) <==> (a.model@ <= b.model@));
        }
        sub_ab
    }

    /// Operation-level wrapper: computes `sub(a, b)` and `add(sub(a, b), b)` under `b <= a`.
    pub fn lemma_model_sub_add_inverse_ge_ops(a: &Self, b: &Self) -> (out: (Self, Self))
        requires
            a.wf_spec(),
            b.wf_spec(),
            b.model@ <= a.model@,
        ensures
            out.0.wf_spec(),
            out.1.wf_spec(),
            out.0.model@ == a.model@ - b.model@,
            out.1.model@ == out.0.model@ + b.model@,
            out.1.model@ == a.model@,
    {
        let sub_ab = a.sub_limbwise_small_total(b);
        let add_sub_ab_b = sub_ab.add_limbwise_small_total(b);
        proof {
            assert(a.model@ == Self::limbs_value_spec(a.limbs_le@));
            assert(b.model@ == Self::limbs_value_spec(b.limbs_le@));
            assert(b.model@ <= a.model@);
            assert(Self::limbs_value_spec(b.limbs_le@) <= Self::limbs_value_spec(a.limbs_le@));

            if Self::limbs_value_spec(a.limbs_le@) <= Self::limbs_value_spec(b.limbs_le@) {
                assert(sub_ab.model@ == 0);
            }
            if Self::limbs_value_spec(b.limbs_le@) < Self::limbs_value_spec(a.limbs_le@) {
                assert(sub_ab.model@ == Self::limbs_value_spec(a.limbs_le@) - Self::limbs_value_spec(b.limbs_le@));
            }
            assert(add_sub_ab_b.model@ == sub_ab.model@ + Self::limbs_value_spec(b.limbs_le@));
            Self::lemma_model_sub_add_inverse_ge_from_total_contracts(a, b, &sub_ab, &add_sub_ab_b);

            assert(sub_ab.model@ == a.model@ - b.model@);
            assert(add_sub_ab_b.model@ == sub_ab.model@ + b.model@);
            assert(add_sub_ab_b.model@ == a.model@);
        }
        (sub_ab, add_sub_ab_b)
    }

    /// Operation-level wrapper: computes compare and subtraction; positive compare implies positive subtraction.
    pub fn lemma_cmp_pos_implies_sub_pos_ops(a: &Self, b: &Self) -> (out: (i8, Self))
        requires
            a.wf_spec(),
            b.wf_spec(),
        ensures
            out.0 == -1 || out.0 == 0 || out.0 == 1,
            out.1.wf_spec(),
            (out.1.model@ == 0) <==> (a.model@ <= b.model@),
            out.0 == 1 ==> out.1.model@ > 0,
    {
        let cmp = Self::lemma_cmp_eq_zero_iff_eq_ops(a, b);
        let sub_ab = Self::lemma_model_sub_zero_iff_le_ops(a, b);
        proof {
            if cmp == 1 {
                assert(a.model@ > b.model@);
                assert(!(a.model@ <= b.model@));
                assert(sub_ab.model@ != 0) by {
                    if sub_ab.model@ == 0 {
                        assert(a.model@ <= b.model@);
                        assert(false);
                    }
                };
                assert(sub_ab.model@ > 0);
            }
        }
        (cmp, sub_ab)
    }

    /// Operation-level wrapper: computes compare and both directional subtractions;
    /// equality compare implies both truncated subtractions are zero.
    pub fn lemma_cmp_eq_implies_bi_sub_zero_ops(a: &Self, b: &Self) -> (out: (i8, Self, Self))
        requires
            a.wf_spec(),
            b.wf_spec(),
        ensures
            out.0 == -1 || out.0 == 0 || out.0 == 1,
            out.1.wf_spec(),
            out.2.wf_spec(),
            out.0 == 0 ==> out.1.model@ == 0 && out.2.model@ == 0,
    {
        let cmp = Self::lemma_cmp_eq_zero_iff_eq_ops(a, b);
        let sub_ab = Self::lemma_model_sub_zero_iff_le_ops(a, b);
        let sub_ba = Self::lemma_model_sub_zero_iff_le_ops(b, a);
        proof {
            if cmp == 0 {
                assert(a.model@ == b.model@);
                assert(a.model@ <= b.model@);
                assert(b.model@ <= a.model@);
                assert(sub_ab.model@ == 0);
                assert(sub_ba.model@ == 0);
            }
        }
        (cmp, sub_ab, sub_ba)
    }

    /// Operation-level wrapper: negative compare implies one-sided zero/positive trunc-sub split.
    pub fn lemma_cmp_neg_implies_asym_sub_ops(a: &Self, b: &Self) -> (out: (i8, Self, Self))
        requires
            a.wf_spec(),
            b.wf_spec(),
        ensures
            out.0 == -1 || out.0 == 0 || out.0 == 1,
            out.1.wf_spec(),
            out.2.wf_spec(),
            out.0 == -1 ==> out.1.model@ == 0 && out.2.model@ > 0,
    {
        let cmp = Self::lemma_cmp_eq_zero_iff_eq_ops(a, b);
        let sub_ab = Self::lemma_model_sub_zero_iff_le_ops(a, b);
        let sub_ba = Self::lemma_model_sub_zero_iff_le_ops(b, a);
        proof {
            if cmp == -1 {
                assert(a.model@ < b.model@);
                assert(a.model@ <= b.model@);
                assert(!(b.model@ <= a.model@));
                assert(sub_ab.model@ == 0);
                assert(sub_ba.model@ != 0) by {
                    if sub_ba.model@ == 0 {
                        assert(b.model@ <= a.model@);
                        assert(false);
                    }
                };
                assert(sub_ba.model@ > 0);
            }
        }
        (cmp, sub_ab, sub_ba)
    }

    /// Operation-level wrapper: computes both quotients and proves quotient monotonicity.
    pub fn lemma_model_div_monotonic_pos_ops(a: &Self, b: &Self, d: &Self) -> (out: (Self, Self))
        requires
            a.wf_spec(),
            b.wf_spec(),
            d.wf_spec(),
            a.model@ <= b.model@,
            d.model@ > 0,
        ensures
            out.0.wf_spec(),
            out.1.wf_spec(),
            out.0.model@ == a.model@ / d.model@,
            out.1.model@ == b.model@ / d.model@,
            out.0.model@ <= out.1.model@,
    {
        let div_a = a.div_limbwise_small_total(d);
        let div_b = b.div_limbwise_small_total(d);
        proof {
            assert(a.model@ == Self::limbs_value_spec(a.limbs_le@));
            assert(b.model@ == Self::limbs_value_spec(b.limbs_le@));
            assert(d.model@ == Self::limbs_value_spec(d.limbs_le@));
            assert(a.model@ <= b.model@);
            assert(d.model@ > 0);
            assert(Self::limbs_value_spec(a.limbs_le@) <= Self::limbs_value_spec(b.limbs_le@));
            assert(Self::limbs_value_spec(d.limbs_le@) > 0);
            assert(div_a.model@ * Self::limbs_value_spec(d.limbs_le@) <= Self::limbs_value_spec(a.limbs_le@));
            assert(Self::limbs_value_spec(b.limbs_le@) < (div_b.model@ + 1) * Self::limbs_value_spec(d.limbs_le@));
            Self::lemma_model_div_monotonic_pos_from_total_contracts(a, b, d, &div_a, &div_b);
            assert(div_a.model@ == a.model@ / d.model@);
            assert(div_b.model@ == b.model@ / d.model@);
            assert(div_a.model@ <= div_b.model@);
        }
        (div_a, div_b)
    }

    /// Operation-level wrapper: computes quotient and proves quotient limb-length bound.
    pub fn lemma_model_div_len_bound_pos_ops(a: &Self, d: &Self) -> (out: Self)
        requires
            a.wf_spec(),
            d.wf_spec(),
            d.model@ > 0,
        ensures
            out.wf_spec(),
            out.model@ == a.model@ / d.model@,
            out.limbs_le@.len() <= a.limbs_le@.len(),
    {
        let div_a = a.div_limbwise_small_total(d);
        proof {
            let alen = a.limbs_le@.len();
            assert(a.model@ == Self::limbs_value_spec(a.limbs_le@));
            assert(d.model@ == Self::limbs_value_spec(d.limbs_le@));
            assert(d.model@ > 0);
            assert(1 <= d.model@);
            assert(div_a.wf_spec());
            assert(Self::canonical_limbs_spec(div_a.limbs_le@));
            assert(div_a.model@ * d.model@ <= a.model@);
            assert(d.model@ == 1 + (d.model@ - 1));
            assert(
                div_a.model@ * d.model@
                    == div_a.model@ + div_a.model@ * (d.model@ - 1)
            ) by (nonlinear_arith);
            assert(0 <= div_a.model@ * (d.model@ - 1));
            assert(div_a.model@ <= div_a.model@ + div_a.model@ * (d.model@ - 1));
            assert(div_a.model@ <= div_a.model@ * d.model@);
            assert(div_a.model@ <= a.model@);
            Self::lemma_limbs_value_lt_pow_len(a.limbs_le@);
            assert(a.model@ < Self::pow_base_spec(alen));
            assert(div_a.model@ < Self::pow_base_spec(alen));
            Self::lemma_len_bound_from_value_upper_pow(div_a.limbs_le@, alen);
            assert(div_a.limbs_le@.len() <= alen);
            assert(div_a.model@ == a.model@ / d.model@);
        }
        div_a
    }

    /// Operation-level wrapper: computes remainder and proves positive-divisor upper bound.
    pub fn lemma_model_rem_upper_bound_pos_ops(a: &Self, d: &Self) -> (out: Self)
        requires
            a.wf_spec(),
            d.wf_spec(),
            d.model@ > 0,
        ensures
            out.wf_spec(),
            out.model@ == a.model@ % d.model@,
            out.model@ < d.model@,
    {
        let rem_a = a.rem_limbwise_small_total(d);
        proof {
            assert(a.model@ == Self::limbs_value_spec(a.limbs_le@));
            assert(d.model@ == Self::limbs_value_spec(d.limbs_le@));
            assert(d.model@ > 0);
            assert(Self::limbs_value_spec(d.limbs_le@) > 0);
            assert(rem_a.model@ == Self::limbs_value_spec(a.limbs_le@) % Self::limbs_value_spec(d.limbs_le@));
            Self::lemma_model_rem_upper_bound_pos_from_total_contracts(a, d, &rem_a);
            assert(rem_a.model@ == a.model@ % d.model@);
            assert(rem_a.model@ < d.model@);
        }
        rem_a
    }

    /// Operation-level wrapper: computes remainder and proves remainder limb-length bound.
    pub fn lemma_model_rem_len_bound_pos_ops(a: &Self, d: &Self) -> (out: Self)
        requires
            a.wf_spec(),
            d.wf_spec(),
            d.model@ > 0,
        ensures
            out.wf_spec(),
            out.model@ == a.model@ % d.model@,
            out.limbs_le@.len() <= d.limbs_le@.len(),
    {
        let rem_a = a.rem_limbwise_small_total(d);
        proof {
            let dlen = d.limbs_le@.len();
            assert(a.model@ == Self::limbs_value_spec(a.limbs_le@));
            assert(d.model@ == Self::limbs_value_spec(d.limbs_le@));
            assert(d.model@ > 0);
            assert(rem_a.wf_spec());
            assert(Self::canonical_limbs_spec(rem_a.limbs_le@));
            assert(rem_a.model@ == a.model@ % d.model@);
            assert(rem_a.model@ < d.model@);
            Self::lemma_limbs_value_lt_pow_len(d.limbs_le@);
            assert(d.model@ < Self::pow_base_spec(dlen));
            assert(rem_a.model@ < Self::pow_base_spec(dlen));
            Self::lemma_len_bound_from_value_upper_pow(rem_a.limbs_le@, dlen);
            assert(rem_a.limbs_le@.len() <= dlen);
        }
        rem_a
    }

    /// Operation-level wrapper: computes `(q, r)` and proves recomposition for `d > 0`.
    pub fn lemma_model_div_rem_recompose_pos_ops(a: &Self, d: &Self) -> (out: (Self, Self))
        requires
            a.wf_spec(),
            d.wf_spec(),
            d.model@ > 0,
        ensures
            out.0.wf_spec(),
            out.1.wf_spec(),
            out.0.model@ == a.model@ / d.model@,
            out.1.model@ == a.model@ % d.model@,
            a.model@ == out.0.model@ * d.model@ + out.1.model@,
            out.1.model@ < d.model@,
    {
        let pair = a.div_rem_limbwise_small_total(d);
        proof {
            assert(a.model@ == Self::limbs_value_spec(a.limbs_le@));
            assert(d.model@ == Self::limbs_value_spec(d.limbs_le@));
            assert(d.model@ > 0);
            assert(Self::limbs_value_spec(d.limbs_le@) > 0);
            assert(
                Self::limbs_value_spec(a.limbs_le@)
                    == pair.0.model@ * Self::limbs_value_spec(d.limbs_le@) + pair.1.model@
            );
            assert(pair.0.model@ == Self::limbs_value_spec(a.limbs_le@) / Self::limbs_value_spec(d.limbs_le@));
            assert(pair.1.model@ == Self::limbs_value_spec(a.limbs_le@) % Self::limbs_value_spec(d.limbs_le@));
            assert(pair.1.model@ < Self::limbs_value_spec(d.limbs_le@));
            assert(a.model@ == pair.0.model@ * d.model@ + pair.1.model@);
            assert(pair.0.model@ == a.model@ / d.model@);
            assert(pair.1.model@ == a.model@ % d.model@);
            assert(pair.1.model@ < d.model@);
        }
        pair
    }

    /// Total small-limb subtraction helper used by scalar witness plumbing.
    ///
    /// Computes the exact nonnegative difference when `self >= rhs` using full
    /// multi-limb borrow propagation (with trailing-zero normalization).
    /// Returns `0` when `self < rhs`.
    pub fn sub_limbwise_small_total(&self, rhs: &Self) -> (out: Self)
        ensures
            out.wf_spec(),
            Self::limbs_value_spec(self.limbs_le@) <= Self::limbs_value_spec(rhs.limbs_le@) ==> out.model@ == 0,
            Self::limbs_value_spec(rhs.limbs_le@) < Self::limbs_value_spec(self.limbs_le@)
                ==> out.model@ == Self::limbs_value_spec(self.limbs_le@) - Self::limbs_value_spec(rhs.limbs_le@),
    {
        let cmp = self.cmp_limbwise_small_total(rhs);
        if cmp == -1i8 {
            let out = Self::zero();
            proof {
                assert(Self::limbs_value_spec(self.limbs_le@) < Self::limbs_value_spec(rhs.limbs_le@));
                assert(Self::limbs_value_spec(self.limbs_le@) <= Self::limbs_value_spec(rhs.limbs_le@));
                assert(out.model@ == 0);
            }
            out
        } else if cmp == 0i8 {
            let out = Self::zero();
            proof {
                assert(Self::limbs_value_spec(self.limbs_le@) == Self::limbs_value_spec(rhs.limbs_le@));
                assert(Self::limbs_value_spec(self.limbs_le@) <= Self::limbs_value_spec(rhs.limbs_le@));
                assert(out.model@ == 0);
            }
            out
        } else {
            proof {
                assert(cmp == -1 || cmp == 0 || cmp == 1);
                assert(cmp != -1i8);
                assert(cmp != 0i8);
                assert(cmp == 1i8);
                assert(Self::limbs_value_spec(self.limbs_le@) > Self::limbs_value_spec(rhs.limbs_le@));
                assert(!(Self::limbs_value_spec(self.limbs_le@) <= Self::limbs_value_spec(rhs.limbs_le@)));
            }
            let alen = Self::trimmed_len_exec(&self.limbs_le);
            let blen = Self::trimmed_len_exec(&rhs.limbs_le);
            assert(alen <= self.limbs_le.len());
            assert(blen <= rhs.limbs_le.len());
            proof {
                if blen > alen {
                    let alen_nat = alen as nat;
                    let blen_nat = blen as nat;
                    assert(alen_nat <= self.limbs_le@.len());
                    assert(blen_nat <= rhs.limbs_le@.len());
                    assert(forall|j: int| alen_nat <= j < self.limbs_le@.len() ==> self.limbs_le@[j] == 0u32);
                    assert(forall|j: int| blen_nat <= j < rhs.limbs_le@.len() ==> rhs.limbs_le@[j] == 0u32);
                    assert(blen_nat > alen_nat);
                    assert(blen_nat > 0);
                    assert(rhs.limbs_le@[(blen - 1) as int] != 0u32);
                    Self::lemma_trimmed_len_gt_implies_value_gt(
                        rhs.limbs_le@,
                        blen_nat,
                        self.limbs_le@,
                        alen_nat,
                    );
                    assert(Self::limbs_value_spec(rhs.limbs_le@) > Self::limbs_value_spec(self.limbs_le@));
                    assert(Self::limbs_value_spec(self.limbs_le@) > Self::limbs_value_spec(rhs.limbs_le@));
                }
                assert(blen <= alen);
            }
            let mut out_limbs: Vec<u32> = Vec::new();
            let mut i: usize = 0;
            let mut borrow: u64 = 0u64;

            while i < alen
                invariant
                    i <= alen,
                    alen <= self.limbs_le.len(),
                    blen <= rhs.limbs_le.len(),
                    out_limbs@.len() == i,
                    borrow == 0u64 || borrow == 1u64,
                    Self::limbs_value_spec(out_limbs@)
                        + Self::prefix_sum_spec(rhs.limbs_le@, blen as nat, i as nat)
                        == Self::prefix_sum_spec(self.limbs_le@, alen as nat, i as nat)
                            + borrow as nat * Self::pow_base_spec(i as nat),
                decreases alen - i,
            {
                assert(i < self.limbs_le.len());
                let a = self.limbs_le[i] as u64;
                let b = if i < blen {
                    assert(i < rhs.limbs_le.len());
                    rhs.limbs_le[i] as u64
                } else {
                    0u64
                };
                let borrow_in = borrow;
                assert(a <= 4_294_967_295u64);
                assert(b <= 4_294_967_295u64);
                assert(borrow_in <= 1u64);
                let need = b + borrow_in;
                let digit64: u64;
                let next_borrow: u64;
                if a >= need {
                    next_borrow = 0u64;
                    digit64 = a - need;
                } else {
                    let a_plus_base = 4_294_967_296u64.wrapping_add(a);
                    next_borrow = 1u64;
                    digit64 = a_plus_base.wrapping_sub(need);
                }
                let digit = digit64 as u32;
                proof {
                    let i_nat = i as nat;
                    let alen_nat = alen as nat;
                    let blen_nat = blen as nat;
                    let a_nat = a as nat;
                    let b_nat = b as nat;
                    let borrow_nat = borrow_in as nat;
                    let next_borrow_nat = next_borrow as nat;
                    let digit_nat = digit as nat;

                    assert(a <= 4_294_967_295u64);
                    assert(a < 4_294_967_296u64);
                    assert(b <= 4_294_967_295u64);
                    assert(b < 4_294_967_296u64);
                    assert(a_nat < Self::limb_base_spec());
                    assert(b_nat < Self::limb_base_spec());
                    assert(Self::limb_base_spec() == 4_294_967_296);
                    assert(borrow_in == 0u64 || borrow_in == 1u64);
                    assert(borrow_nat <= 1);
                    assert(next_borrow == 0u64 || next_borrow == 1u64);
                    assert(next_borrow_nat <= 1);
                    assert(need == b + borrow_in);
                    assert(need as nat == b_nat + borrow_nat);

                    if a >= need {
                        assert(next_borrow == 0u64);
                        assert(next_borrow_nat == 0);
                        assert(digit64 == a - need);
                        assert(digit64 < 4_294_967_296u64);
                        assert(digit as u64 == digit64);
                        assert(digit_nat == digit64 as nat);
                        assert(digit_nat + b_nat + borrow_nat == a_nat);
                        assert(digit_nat + b_nat + borrow_nat == a_nat + next_borrow_nat * Self::limb_base_spec());
                    } else {
                        assert(next_borrow == 1u64);
                        assert(next_borrow_nat == 1);
                        assert(a < need);
                        assert(borrow_in <= 1u64);
                        assert(b + borrow_in <= 4_294_967_295u64 + 1u64);
                        assert(need <= 4_294_967_295u64 + 1u64);
                        assert(need <= 4_294_967_296u64);
                        assert(digit64 == 4_294_967_296u64.wrapping_add(a).wrapping_sub(need));
                        assert(4_294_967_296u64 + a <= 8_589_934_591u64);
                        assert(4_294_967_296u64.wrapping_add(a) == 4_294_967_296u64 + a);
                        assert(need <= 4_294_967_296u64 + a);
                        assert(4_294_967_296u64.wrapping_add(a).wrapping_sub(need) == 4_294_967_296u64 + a - need);
                        assert(digit64 == 4_294_967_296u64 + a - need);
                        assert(digit64 < 4_294_967_296u64);
                        assert(digit as u64 == digit64);
                        assert(digit_nat == digit64 as nat);
                        assert(
                            digit_nat
                                == a_nat + 4_294_967_296nat - (b_nat + borrow_nat)
                        );
                        assert(digit_nat + b_nat + borrow_nat == a_nat + 4_294_967_296nat);
                        assert(digit_nat + b_nat + borrow_nat == a_nat + next_borrow_nat * Self::limb_base_spec());
                    }

                    assert(i_nat < alen_nat);
                    assert(Self::limb_or_zero_spec(self.limbs_le@, alen_nat, i_nat) == a_nat);
                    if i < blen {
                        assert(i_nat < blen_nat);
                        assert(Self::limb_or_zero_spec(rhs.limbs_le@, blen_nat, i_nat) == b_nat);
                    } else {
                        assert(blen_nat <= i_nat);
                        Self::lemma_limb_or_zero_past_logical_len(rhs.limbs_le@, blen_nat, i_nat);
                        assert(Self::limb_or_zero_spec(rhs.limbs_le@, blen_nat, i_nat) == 0);
                        assert(b_nat == 0);
                    }

                    Self::lemma_prefix_sum_step(self.limbs_le@, alen_nat, i_nat);
                    Self::lemma_prefix_sum_step(rhs.limbs_le@, blen_nat, i_nat);
                    assert(
                        Self::prefix_sum_spec(self.limbs_le@, alen_nat, i_nat + 1)
                            == Self::prefix_sum_spec(self.limbs_le@, alen_nat, i_nat)
                                + a_nat * Self::pow_base_spec(i_nat)
                    );
                    assert(
                        Self::prefix_sum_spec(rhs.limbs_le@, blen_nat, i_nat + 1)
                            == Self::prefix_sum_spec(rhs.limbs_le@, blen_nat, i_nat)
                                + b_nat * Self::pow_base_spec(i_nat)
                    );

                    Self::lemma_pow_base_succ(i_nat);
                    Self::lemma_sub_prefix_step(
                        Self::limbs_value_spec(out_limbs@),
                        Self::prefix_sum_spec(self.limbs_le@, alen_nat, i_nat),
                        Self::prefix_sum_spec(rhs.limbs_le@, blen_nat, i_nat),
                        digit_nat,
                        a_nat,
                        b_nat,
                        borrow_nat,
                        next_borrow_nat,
                        Self::pow_base_spec(i_nat),
                        Self::pow_base_spec(i_nat + 1),
                    );
                    Self::lemma_limbs_value_push(out_limbs@, digit);
                    assert(
                        Self::limbs_value_spec(out_limbs@.push(digit))
                            + Self::prefix_sum_spec(rhs.limbs_le@, blen_nat, i_nat + 1)
                            == Self::prefix_sum_spec(self.limbs_le@, alen_nat, i_nat + 1)
                                + next_borrow_nat * Self::pow_base_spec(i_nat + 1)
                    );
                }
                borrow = next_borrow;
                out_limbs.push(digit);
                i = i + 1;
            }
            assert(i == alen);
            assert(out_limbs@.len() == alen);
            let ghost alen_nat = alen as nat;
            let ghost blen_nat = blen as nat;
            let ghost pre_trim = out_limbs@;
            proof {
                assert(
                    Self::limbs_value_spec(pre_trim)
                        + Self::prefix_sum_spec(rhs.limbs_le@, blen_nat, alen_nat)
                        == Self::prefix_sum_spec(self.limbs_le@, alen_nat, alen_nat)
                            + borrow as nat * Self::pow_base_spec(alen_nat)
                );

                assert(blen_nat <= alen_nat);
                Self::lemma_prefix_sum_constant_past_logical_len(rhs.limbs_le@, blen_nat, alen_nat);
                Self::lemma_prefix_sum_eq_subrange_value(rhs.limbs_le@, blen_nat);
                assert(forall|j: int| blen_nat <= j < rhs.limbs_le@.len() ==> rhs.limbs_le@[j] == 0u32);
                Self::lemma_limbs_value_trim_suffix_zeros(rhs.limbs_le@, blen_nat);
                assert(
                    Self::prefix_sum_spec(rhs.limbs_le@, blen_nat, alen_nat)
                        == Self::limbs_value_spec(rhs.limbs_le@)
                );

                Self::lemma_prefix_sum_eq_subrange_value(self.limbs_le@, alen_nat);
                assert(forall|j: int| alen_nat <= j < self.limbs_le@.len() ==> self.limbs_le@[j] == 0u32);
                Self::lemma_limbs_value_trim_suffix_zeros(self.limbs_le@, alen_nat);
                assert(
                    Self::prefix_sum_spec(self.limbs_le@, alen_nat, alen_nat)
                        == Self::limbs_value_spec(self.limbs_le@)
                );
                assert(
                    Self::limbs_value_spec(pre_trim)
                        + Self::limbs_value_spec(rhs.limbs_le@)
                        == Self::limbs_value_spec(self.limbs_le@)
                            + borrow as nat * Self::pow_base_spec(alen_nat)
                );

                let self_trim = self.limbs_le@.subrange(0, alen as int);
                assert(self_trim.len() == alen_nat);
                Self::lemma_limbs_value_lt_pow_len(self_trim);
                assert(Self::limbs_value_spec(self_trim) < Self::pow_base_spec(alen_nat));
                assert(Self::limbs_value_spec(self.limbs_le@) == Self::limbs_value_spec(self_trim));
                assert(Self::limbs_value_spec(self.limbs_le@) < Self::pow_base_spec(alen_nat));

                Self::lemma_limbs_value_lt_pow_len(pre_trim);
                assert(Self::limbs_value_spec(pre_trim) < Self::pow_base_spec(alen_nat));
                assert(borrow == 0u64 || borrow == 1u64);
                assert(Self::limbs_value_spec(self.limbs_le@) > Self::limbs_value_spec(rhs.limbs_le@));
                if borrow == 1u64 {
                    let pre_val = Self::limbs_value_spec(pre_trim);
                    let rhs_val = Self::limbs_value_spec(rhs.limbs_le@);
                    let self_val = Self::limbs_value_spec(self.limbs_le@);
                    let pow_n = Self::pow_base_spec(alen_nat);
                    assert(borrow as nat == 1);
                    assert(
                        pre_val + rhs_val
                            == self_val + pow_n
                    );
                    assert(pre_val < pow_n);
                    assert(pre_val <= pow_n);
                    assert(pre_val + rhs_val <= pow_n + rhs_val);
                    assert(self_val + pow_n <= pow_n + rhs_val);
                    let d = self_val - rhs_val;
                    assert(self_val == rhs_val + d);
                    assert(rhs_val + 1 <= self_val);
                    assert(1 <= d);
                    assert(rhs_val + 1 <= rhs_val + d);
                    assert(rhs_val + 1 + pow_n <= rhs_val + d + pow_n);
                    assert(rhs_val + d + pow_n == self_val + pow_n);
                    assert(rhs_val + 1 + pow_n <= self_val + pow_n);
                    assert(rhs_val + 1 + pow_n <= pow_n + rhs_val);
                    assert(false);
                }
                assert(borrow != 1u64);
                assert(borrow == 0u64);
                assert(
                    Self::limbs_value_spec(pre_trim) + Self::limbs_value_spec(rhs.limbs_le@)
                        == Self::limbs_value_spec(self.limbs_le@)
                );
                assert(
                    Self::limbs_value_spec(pre_trim)
                        == Self::limbs_value_spec(self.limbs_le@) - Self::limbs_value_spec(rhs.limbs_le@)
                );
            }

            let out_limbs = Self::trim_trailing_zero_limbs(out_limbs);
            proof {
                assert(Self::limbs_value_spec(out_limbs@) == Self::limbs_value_spec(pre_trim));
                assert(
                    Self::limbs_value_spec(out_limbs@)
                        == Self::limbs_value_spec(self.limbs_le@) - Self::limbs_value_spec(rhs.limbs_le@)
                );
            }
            let ghost model = Self::limbs_value_spec(out_limbs@);
            let out = Self::from_parts(out_limbs, Ghost(model));
            proof {
                assert(
                    out.model@
                        == Self::limbs_value_spec(self.limbs_le@) - Self::limbs_value_spec(rhs.limbs_le@)
                );
            }
            out
        }
    }

    /// Total witness copy helper for scalar witness plumbing.
    ///
    /// Preserves all limbs exactly (after trailing-zero normalization).
    pub fn copy_small_total(&self) -> (out: Self)
        ensures
            out.wf_spec(),
            out.model@ == Self::limbs_value_spec(self.limbs_le@),
    {
        let n = Self::trimmed_len_exec(&self.limbs_le);
        assert(n <= self.limbs_le.len());
        let mut out_limbs: Vec<u32> = Vec::new();
        let mut i: usize = 0;
        while i < n
            invariant
                i <= n,
                n <= self.limbs_le.len(),
                out_limbs@ == self.limbs_le@.subrange(0, i as int),
            decreases n - i,
        {
            assert(i < self.limbs_le.len());
            out_limbs.push(self.limbs_le[i]);
            i = i + 1;
        }
        proof {
            assert(out_limbs@ == self.limbs_le@.subrange(0, n as int));
        }
        proof {
            if n == 0 {
                assert(out_limbs@.len() == 0);
                assert(Self::canonical_limbs_spec(out_limbs@));
            } else {
                assert(0 < n);
                assert(out_limbs@.len() == n);
                assert(self.limbs_le@[(n - 1) as int] != 0u32);
                assert(out_limbs@[(out_limbs@.len() - 1) as int] == self.limbs_le@[(n - 1) as int]);
                assert(out_limbs@[(out_limbs@.len() - 1) as int] != 0u32);
                assert(Self::canonical_limbs_spec(out_limbs@));
            }
        }
        proof {
            let ng: nat = n as nat;
            assert(ng <= self.limbs_le@.len());
            assert(forall|i: int| ng <= i < self.limbs_le@.len() ==> self.limbs_le@[i] == 0u32);
            Self::lemma_limbs_value_trim_suffix_zeros(self.limbs_le@, ng);
            assert(
                Self::limbs_value_spec(self.limbs_le@)
                    == Self::limbs_value_spec(self.limbs_le@.subrange(0, n as int))
            );
            assert(out_limbs@ == self.limbs_le@.subrange(0, n as int));
            assert(
                Self::limbs_value_spec(self.limbs_le@)
                    == Self::limbs_value_spec(out_limbs@)
            );
        }
        let ghost model = Self::limbs_value_spec(out_limbs@);
        let out = Self::from_parts(out_limbs, Ghost(model));
        proof {
            assert(out.model@ == Self::limbs_value_spec(out.limbs_le@));
            assert(out.limbs_le@ == self.limbs_le@.subrange(0, n as int));
            assert(
                Self::limbs_value_spec(self.limbs_le@)
                    == Self::limbs_value_spec(out.limbs_le@)
            );
            assert(out.model@ == Self::limbs_value_spec(self.limbs_le@));
        }
        out
    }
}
}
