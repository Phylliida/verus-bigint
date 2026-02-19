verus! {
impl RuntimeBigNatWitness {
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

}
}
