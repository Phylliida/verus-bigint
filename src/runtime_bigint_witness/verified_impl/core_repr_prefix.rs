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

    pub proof fn lemma_pow_base_succ(exp: nat)
        ensures
            Self::pow_base_spec(exp + 1) == Self::limb_base_spec() * Self::pow_base_spec(exp),
    {
    }

    /// Value update law for appending a high limb in little-endian representation.
    pub proof fn lemma_limbs_value_push(limbs: Seq<u32>, digit: u32)
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

    pub proof fn lemma_limbs_value_drop_last_zero(limbs: Seq<u32>)
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

    pub proof fn lemma_limbs_value_trim_suffix_zeros(limbs: Seq<u32>, n: nat)
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

    pub proof fn lemma_add_digit_carry_decompose(a: nat, b: nat, carry_in: nat)
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

    pub proof fn lemma_add_prefix_step(
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

    pub proof fn lemma_sub_prefix_step(
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

    pub proof fn lemma_limb_or_zero_past_logical_len(limbs: Seq<u32>, logical_len: nat, idx: nat)
        requires
            logical_len <= idx,
        ensures
            Self::limb_or_zero_spec(limbs, logical_len, idx) == 0,
    {
        assert(!(idx < logical_len));
        assert(Self::limb_or_zero_spec(limbs, logical_len, idx) == 0);
    }

    pub proof fn lemma_prefix_sum_step(limbs: Seq<u32>, logical_len: nat, count: nat)
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

    pub proof fn lemma_prefix_sum_constant_from_extra(limbs: Seq<u32>, logical_len: nat, extra: nat)
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

    pub proof fn lemma_prefix_sum_constant_past_logical_len(limbs: Seq<u32>, logical_len: nat, count: nat)
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

    pub proof fn lemma_prefix_sum_matches_subrange(limbs: Seq<u32>, logical_len: nat, count: nat)
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

    pub proof fn lemma_prefix_sum_eq_subrange_value(limbs: Seq<u32>, logical_len: nat)
        requires
            logical_len <= limbs.len(),
        ensures
            Self::prefix_sum_spec(limbs, logical_len, logical_len)
                == Self::limbs_value_spec(limbs.subrange(0, logical_len as int)),
    {
        Self::lemma_prefix_sum_matches_subrange(limbs, logical_len, logical_len);
    }

}
}
