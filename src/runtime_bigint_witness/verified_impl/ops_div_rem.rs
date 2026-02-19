verus! {
impl RuntimeBigNatWitness {
    /// Operation-level wrapper: computes quotients and proves floor-division add bounds.
    pub fn lemma_model_div_add_bounds_pos_ops(a: &Self, b: &Self, d: &Self) -> (out: (Self, Self, Self))
        requires
            a.wf_spec(),
            b.wf_spec(),
            d.wf_spec(),
            d.model@ > 0,
        ensures
            out.0.wf_spec(),
            out.1.wf_spec(),
            out.2.wf_spec(),
            out.0.model@ == a.model@ / d.model@,
            out.1.model@ == b.model@ / d.model@,
            out.2.model@ == (a.model@ + b.model@) / d.model@,
            out.0.model@ + out.1.model@ <= out.2.model@,
            out.2.model@ <= out.0.model@ + out.1.model@ + 1,
    {
        let sum = a.add_limbwise_small_total(b);
        let q_a = a.div_limbwise_small_total(d);
        let q_b = b.div_limbwise_small_total(d);
        let q_sum = sum.div_limbwise_small_total(d);
        proof {
            assert(a.model@ == Self::limbs_value_spec(a.limbs_le@));
            assert(b.model@ == Self::limbs_value_spec(b.limbs_le@));
            assert(d.model@ == Self::limbs_value_spec(d.limbs_le@));
            assert(sum.model@ == a.model@ + b.model@);
            assert(q_a.model@ == a.model@ / d.model@);
            assert(q_b.model@ == b.model@ / d.model@);
            assert(q_sum.model@ == sum.model@ / d.model@);
            assert(q_sum.model@ == (a.model@ + b.model@) / d.model@);
            Self::lemma_div_add_bounds_nat(a.model@, b.model@, d.model@);
            assert(a.model@ / d.model@ + b.model@ / d.model@ <= (a.model@ + b.model@) / d.model@);
            assert((a.model@ + b.model@) / d.model@ <= a.model@ / d.model@ + b.model@ / d.model@ + 1);
            assert(q_a.model@ + q_b.model@ <= q_sum.model@);
            assert(q_sum.model@ <= q_a.model@ + q_b.model@ + 1);
        }
        (q_a, q_b, q_sum)
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

    /// Operation-level wrapper: computes product/quotient/remainder and proves
    /// exact cancellation for positive divisors.
    pub fn lemma_model_mul_div_rem_cancel_pos_ops(a: &Self, d: &Self) -> (out: (Self, Self, Self))
        requires
            a.wf_spec(),
            d.wf_spec(),
            d.model@ > 0,
        ensures
            out.0.wf_spec(),
            out.1.wf_spec(),
            out.2.wf_spec(),
            out.0.model@ == a.model@ * d.model@,
            out.1.model@ == out.0.model@ / d.model@,
            out.2.model@ == out.0.model@ % d.model@,
            out.1.model@ == a.model@,
            out.2.model@ == 0,
    {
        let prod = a.mul_limbwise_small_total(d);
        let q = prod.div_limbwise_small_total(d);
        let r = prod.rem_limbwise_small_total(d);
        proof {
            assert(a.model@ == Self::limbs_value_spec(a.limbs_le@));
            assert(d.model@ == Self::limbs_value_spec(d.limbs_le@));
            assert(d.model@ > 0);
            assert(prod.model@ == a.model@ * d.model@);
            assert(q.model@ == prod.model@ / d.model@);
            assert(r.model@ == prod.model@ % d.model@);
            Self::lemma_mul_div_rem_cancel_nat(a.model@, d.model@);
            assert((a.model@ * d.model@) / d.model@ == a.model@);
            assert((a.model@ * d.model@) % d.model@ == 0);
            assert(q.model@ == a.model@);
            assert(r.model@ == 0);
        }
        (prod, q, r)
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

}
}
