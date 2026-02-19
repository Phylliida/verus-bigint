    /// Total limb-wise multiplication helper used by scalar witness plumbing.
    ///
    /// Computes exact multiplication in little-endian limb space by combining:
    /// - per-limb scalar multiplication (`mul_by_u32_total`)
    /// - base shifting (`shift_base_once_total`)
    /// - semantic accumulation (`add_limbwise_small_total`)
    #[verifier::exec_allows_no_decreases_clause]
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

    /// Total small-limb compare helper used by scalar witness plumbing.
    ///
    /// Returns the exact sign of `(self - rhs)` as `-1/0/1` using full
    /// multi-limb comparison with trailing-zero normalization.
    #[verifier::exec_allows_no_decreases_clause]
    pub fn cmp_limbwise_small_total(&self, rhs: &Self) -> (out: i8)
        ensures
            out == -1 || out == 0 || out == 1,
            out == -1 ==> Self::limbs_value_spec(self.limbs_le@) < Self::limbs_value_spec(rhs.limbs_le@),
            out == 0 ==> Self::limbs_value_spec(self.limbs_le@) == Self::limbs_value_spec(rhs.limbs_le@),
            out == 1 ==> Self::limbs_value_spec(self.limbs_le@) > Self::limbs_value_spec(rhs.limbs_le@),
            self.limbs_le@ == rhs.limbs_le@ ==> out == 0,
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
            }
            0i8
        }
    }
