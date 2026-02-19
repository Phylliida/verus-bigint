verus! {
impl RuntimeBigNatWitness {
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
}
}
