verus! {
impl RuntimeBigNatWitness {
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

    /// Operation-level wrapper: computes `sum = a + b` and proves both subtraction round-trips.
    pub fn lemma_model_add_sub_round_trip_ops(a: &Self, b: &Self) -> (out: (Self, Self, Self))
        requires
            a.wf_spec(),
            b.wf_spec(),
        ensures
            out.0.wf_spec(),
            out.1.wf_spec(),
            out.2.wf_spec(),
            out.0.model@ == a.model@ + b.model@,
            out.1.model@ == a.model@,
            out.2.model@ == b.model@,
    {
        let sum = a.add_limbwise_small_total(b);
        let (sub_sum_b, _) = Self::lemma_model_sub_add_inverse_ge_ops(&sum, b);
        let (sub_sum_a, _) = Self::lemma_model_sub_add_inverse_ge_ops(&sum, a);
        proof {
            assert(a.model@ == Self::limbs_value_spec(a.limbs_le@));
            assert(b.model@ == Self::limbs_value_spec(b.limbs_le@));
            assert(sum.model@ == a.model@ + b.model@);
            assert(b.model@ <= a.model@ + b.model@);
            assert(a.model@ <= a.model@ + b.model@);
            assert(b.model@ <= sum.model@);
            assert(a.model@ <= sum.model@);
            assert(sub_sum_b.model@ == sum.model@ - b.model@);
            assert(sub_sum_a.model@ == sum.model@ - a.model@);
            assert(sub_sum_b.model@ == (a.model@ + b.model@) - b.model@);
            assert(sub_sum_a.model@ == (a.model@ + b.model@) - a.model@);
            assert((a.model@ + b.model@) - b.model@ == a.model@);
            assert((a.model@ + b.model@) - a.model@ == b.model@);
            assert(sub_sum_b.model@ == a.model@);
            assert(sub_sum_a.model@ == b.model@);
        }
        (sum, sub_sum_b, sub_sum_a)
    }

}
}
