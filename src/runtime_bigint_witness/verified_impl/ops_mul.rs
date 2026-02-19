verus! {
impl RuntimeBigNatWitness {
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

}
}
