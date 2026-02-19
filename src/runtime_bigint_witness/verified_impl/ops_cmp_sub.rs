verus! {
impl RuntimeBigNatWitness {
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

}
}
