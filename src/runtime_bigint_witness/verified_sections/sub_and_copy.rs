    /// Total small-limb subtraction helper used by scalar witness plumbing.
    ///
    /// Computes the exact nonnegative difference when `self >= rhs` using full
    /// multi-limb borrow propagation (with trailing-zero normalization).
    /// Returns `0` when `self < rhs`.
    #[verifier::exec_allows_no_decreases_clause]
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
                #[verifier::truncate]
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
    #[verifier::exec_allows_no_decreases_clause]
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
