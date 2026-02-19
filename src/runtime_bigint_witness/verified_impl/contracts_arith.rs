verus! {
impl RuntimeBigNatWitness {
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
}
}
