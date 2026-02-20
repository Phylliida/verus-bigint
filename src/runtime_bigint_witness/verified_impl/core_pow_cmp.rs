verus! {
impl RuntimeBigNatWitness {
    pub proof fn lemma_pow_ge_one(exp: nat)
        ensures
            Self::pow_base_spec(exp) >= 1,
        decreases exp
    {
        if exp == 0 {
            assert(Self::pow_base_spec(exp) == 1);
        } else {
            let prev = (exp - 1) as nat;
            Self::lemma_pow_ge_one(prev);
            Self::lemma_pow_base_succ(prev);
            assert(Self::limb_base_spec() == 4_294_967_296);
            assert(Self::limb_base_spec() >= 1);
            assert(Self::pow_base_spec(prev) >= 1);
            assert(Self::pow_base_spec(exp) == Self::limb_base_spec() * Self::pow_base_spec(prev));
            assert(Self::pow_base_spec(prev) <= Self::limb_base_spec() * Self::pow_base_spec(prev))
                by (nonlinear_arith);
            assert(Self::pow_base_spec(prev) <= Self::pow_base_spec(exp));
            assert(Self::pow_base_spec(exp) >= 1);
        }
    }

    pub proof fn lemma_pow_monotonic(lo: nat, hi: nat)
        requires
            lo <= hi,
        ensures
            Self::pow_base_spec(lo) <= Self::pow_base_spec(hi),
        decreases hi - lo
    {
        if lo == hi {
            assert(Self::pow_base_spec(lo) <= Self::pow_base_spec(hi));
        } else {
            assert(lo < hi);
            let prev = (hi - 1) as nat;
            assert(lo <= prev);
            Self::lemma_pow_monotonic(lo, prev);
            Self::lemma_pow_ge_one(prev);
            Self::lemma_pow_base_succ(prev);
            assert(Self::limb_base_spec() == 4_294_967_296);
            assert(Self::limb_base_spec() >= 1);
            assert(Self::pow_base_spec(prev) <= Self::limb_base_spec() * Self::pow_base_spec(prev))
                by (nonlinear_arith);
            assert(Self::pow_base_spec(hi) == Self::limb_base_spec() * Self::pow_base_spec(prev));
            assert(Self::pow_base_spec(prev) <= Self::pow_base_spec(hi));
            assert(Self::pow_base_spec(lo) <= Self::pow_base_spec(hi));
        }
    }

    pub proof fn lemma_pow_add(lhs: nat, rhs: nat)
        ensures
            Self::pow_base_spec(lhs + rhs) == Self::pow_base_spec(lhs) * Self::pow_base_spec(rhs),
        decreases rhs
    {
        if rhs == 0 {
            assert(lhs + rhs == lhs);
            assert(Self::pow_base_spec(0) == 1);
            assert(Self::pow_base_spec(lhs + rhs) == Self::pow_base_spec(lhs));
            assert(Self::pow_base_spec(lhs) * Self::pow_base_spec(rhs) == Self::pow_base_spec(lhs));
        } else {
            let prev = (rhs - 1) as nat;
            Self::lemma_pow_add(lhs, prev);
            assert(lhs + rhs == lhs + prev + 1);
            Self::lemma_pow_base_succ(lhs + prev);
            Self::lemma_pow_base_succ(prev);
            assert(
                Self::pow_base_spec(lhs + rhs)
                    == Self::limb_base_spec() * Self::pow_base_spec(lhs + prev)
            );
            assert(
                Self::pow_base_spec(lhs + prev)
                    == Self::pow_base_spec(lhs) * Self::pow_base_spec(prev)
            );
            assert(
                Self::pow_base_spec(lhs + rhs)
                    == Self::limb_base_spec()
                        * (Self::pow_base_spec(lhs) * Self::pow_base_spec(prev))
            );
            assert(
                Self::limb_base_spec() * (Self::pow_base_spec(lhs) * Self::pow_base_spec(prev))
                    == Self::pow_base_spec(lhs)
                        * (Self::limb_base_spec() * Self::pow_base_spec(prev))
            ) by (nonlinear_arith);
            assert(
                Self::pow_base_spec(rhs)
                    == Self::limb_base_spec() * Self::pow_base_spec(prev)
            );
            assert(
                Self::pow_base_spec(lhs + rhs)
                    == Self::pow_base_spec(lhs) * Self::pow_base_spec(rhs)
            );
        }
    }

    pub proof fn lemma_limbs_value_unfold_nonempty(limbs: Seq<u32>)
        requires
            limbs.len() > 0,
        ensures
            Self::limbs_value_spec(limbs)
                == limbs[0] as nat
                    + Self::limb_base_spec() * Self::limbs_value_spec(limbs.subrange(1, limbs.len() as int)),
    {
        if limbs.len() == 1 {
            assert(Self::limbs_value_spec(limbs) == limbs[0] as nat);
            assert(limbs.subrange(1, limbs.len() as int) == Seq::<u32>::empty());
            assert(Self::limbs_value_spec(Seq::<u32>::empty()) == 0);
            assert(
                limbs[0] as nat
                    + Self::limb_base_spec() * Self::limbs_value_spec(limbs.subrange(1, limbs.len() as int))
                    == limbs[0] as nat
            );
        } else {
            assert(
                Self::limbs_value_spec(limbs)
                    == limbs[0] as nat
                        + Self::limb_base_spec()
                            * Self::limbs_value_spec(limbs.subrange(1, limbs.len() as int))
            );
        }
    }

    pub proof fn lemma_limbs_value_append(left: Seq<u32>, right: Seq<u32>)
        ensures
            Self::limbs_value_spec(left + right)
                == Self::limbs_value_spec(left)
                    + Self::pow_base_spec(left.len()) * Self::limbs_value_spec(right),
        decreases left.len()
    {
        if left.len() == 0 {
            assert(left + right == right);
            assert(Self::limbs_value_spec(left) == 0);
            assert(Self::pow_base_spec(left.len()) == 1);
            assert(
                Self::limbs_value_spec(left + right)
                    == Self::limbs_value_spec(left)
                        + Self::pow_base_spec(left.len()) * Self::limbs_value_spec(right)
            );
        } else {
            let tail = left.subrange(1, left.len() as int);
            let whole = left + right;
            let pow_tail = Self::pow_base_spec(tail.len());
            let right_val = Self::limbs_value_spec(right);
            Self::lemma_limbs_value_append(tail, right);
            Self::lemma_limbs_value_unfold_nonempty(left);
            Self::lemma_limbs_value_unfold_nonempty(whole);
            assert(whole.subrange(1, whole.len() as int) == tail + right);
            assert(
                Self::limbs_value_spec(whole)
                    == left[0] as nat
                        + Self::limb_base_spec() * Self::limbs_value_spec(tail + right)
            );
            assert(
                Self::limbs_value_spec(tail + right)
                    == Self::limbs_value_spec(tail)
                        + pow_tail * right_val
            );
            let right_shifted = pow_tail * right_val;
            assert(
                Self::limbs_value_spec(whole)
                    == left[0] as nat
                        + Self::limb_base_spec()
                            * (Self::limbs_value_spec(tail) + right_shifted)
            );
            assert(
                Self::limb_base_spec() * (Self::limbs_value_spec(tail) + right_shifted)
                    == Self::limb_base_spec() * Self::limbs_value_spec(tail)
                        + Self::limb_base_spec() * right_shifted
            ) by (nonlinear_arith);
            assert(
                Self::limb_base_spec() * right_shifted
                    == (Self::limb_base_spec() * pow_tail) * right_val
            ) by {
                assert(
                    Self::limb_base_spec() * right_shifted
                        == Self::limb_base_spec() * (pow_tail * right_val)
                );
                assert(
                    Self::limb_base_spec() * (pow_tail * right_val)
                        == (Self::limb_base_spec() * pow_tail) * right_val
                ) by (nonlinear_arith);
            };
            assert(
                Self::limbs_value_spec(whole)
                    == (left[0] as nat + Self::limb_base_spec() * Self::limbs_value_spec(tail))
                        + (Self::limb_base_spec() * pow_tail) * right_val
            );
            Self::lemma_pow_base_succ(tail.len() as nat);
            assert(Self::pow_base_spec(left.len()) == Self::limb_base_spec() * pow_tail);
            assert(Self::limbs_value_spec(left) == left[0] as nat + Self::limb_base_spec() * Self::limbs_value_spec(tail));
            assert(
                Self::limbs_value_spec(whole)
                    == Self::limbs_value_spec(left)
                        + Self::pow_base_spec(left.len()) * Self::limbs_value_spec(right)
            );
        }
    }

    pub proof fn lemma_limbs_value_lt_pow_len(limbs: Seq<u32>)
        ensures
            Self::limbs_value_spec(limbs) < Self::pow_base_spec(limbs.len()),
        decreases limbs.len()
    {
        if limbs.len() == 0 {
            assert(Self::limbs_value_spec(limbs) == 0);
            assert(Self::pow_base_spec(0) == 1);
        } else {
            let n = (limbs.len() - 1) as nat;
            let prefix = limbs.subrange(0, n as int);
            let last = limbs[n as int];
            let last_nat = last as nat;
            let pow_n = Self::pow_base_spec(n);
            Self::lemma_limbs_value_lt_pow_len(prefix);
            Self::lemma_limbs_value_push(prefix, last);
            assert(prefix.push(last).len() == limbs.len());
            assert forall|i: int| 0 <= i < limbs.len() implies #[trigger] prefix.push(last)[i] == limbs[i] by {
                if i < prefix.len() {
                    assert(prefix.push(last)[i] == prefix[i]);
                    assert(prefix[i] == limbs[i]);
                } else {
                    assert(i == prefix.len());
                    assert(i == n as int);
                    assert(prefix.push(last)[i] == last);
                    assert(last == limbs[i]);
                }
            };
            assert(prefix.push(last) == limbs);
            assert(Self::limbs_value_spec(limbs) == Self::limbs_value_spec(prefix) + last_nat * pow_n);
            assert(Self::limb_base_spec() == 4_294_967_296);
            assert(last_nat <= 4_294_967_295);
            assert(last_nat + 1 <= Self::limb_base_spec());
            assert(Self::limbs_value_spec(prefix) < pow_n);
            let shifted = last_nat * pow_n;
            assert(
                Self::limbs_value_spec(prefix) + shifted
                    < pow_n + shifted
            );
            assert(
                pow_n + shifted
                    == shifted + pow_n
            ) by (nonlinear_arith);
            assert(
                (last_nat + 1) * pow_n
                    == last_nat * pow_n + 1 * pow_n
            ) by (nonlinear_arith);
            assert(1 * pow_n == pow_n);
            assert(last_nat * pow_n == shifted);
            assert(
                (last_nat + 1) * pow_n
                    == shifted + pow_n
            );
            assert(
                pow_n + shifted
                    == (last_nat + 1) * pow_n
            );
            Self::lemma_pow_ge_one(n);
            let headroom = Self::limb_base_spec() - (last_nat + 1);
            assert(0 <= headroom);
            assert(Self::limb_base_spec() == (last_nat + 1) + headroom);
            assert(
                Self::limb_base_spec() * pow_n
                    == ((last_nat + 1) + headroom) * pow_n
            );
            assert(
                ((last_nat + 1) + headroom) * pow_n
                    == (last_nat + 1) * pow_n + headroom * pow_n
            ) by (nonlinear_arith);
            assert(0 <= headroom * pow_n);
            assert(
                (last_nat + 1) * pow_n
                    <= Self::limb_base_spec() * pow_n
            );
            Self::lemma_pow_base_succ(n);
            assert(Self::pow_base_spec(limbs.len()) == Self::limb_base_spec() * pow_n);
            assert(Self::limbs_value_spec(limbs) < Self::pow_base_spec(limbs.len()));
        }
    }

    pub proof fn lemma_limbs_value_ge_pow_last_nonzero(limbs: Seq<u32>)
        requires
            limbs.len() > 0,
            limbs[(limbs.len() - 1) as int] != 0u32,
        ensures
            Self::pow_base_spec((limbs.len() - 1) as nat) <= Self::limbs_value_spec(limbs),
    {
        let n = (limbs.len() - 1) as nat;
        let prefix = limbs.subrange(0, n as int);
        let last = limbs[n as int];
        Self::lemma_limbs_value_push(prefix, last);
        assert(prefix.push(last).len() == limbs.len());
        assert forall|i: int| 0 <= i < limbs.len() implies #[trigger] prefix.push(last)[i] == limbs[i] by {
            if i < prefix.len() {
                assert(prefix.push(last)[i] == prefix[i]);
                assert(prefix[i] == limbs[i]);
            } else {
                assert(i == prefix.len());
                assert(i == n as int);
                assert(prefix.push(last)[i] == last);
                assert(last == limbs[i]);
            }
        };
        assert(prefix.push(last) == limbs);
        assert(Self::limbs_value_spec(limbs) == Self::limbs_value_spec(prefix) + last as nat * Self::pow_base_spec(n));
        assert(last != 0u32);
        assert(1 <= last as nat);
        Self::lemma_pow_ge_one(n);
        assert(
            last as nat * Self::pow_base_spec(n)
                == Self::pow_base_spec(n) + (last as nat - 1) * Self::pow_base_spec(n)
        ) by (nonlinear_arith);
        assert(0 <= (last as nat - 1) * Self::pow_base_spec(n));
        assert(Self::pow_base_spec(n) <= last as nat * Self::pow_base_spec(n));
        assert(Self::limbs_value_spec(prefix) >= 0);
        assert(last as nat * Self::pow_base_spec(n) <= Self::limbs_value_spec(prefix) + last as nat * Self::pow_base_spec(n));
        assert(Self::pow_base_spec(n) <= Self::limbs_value_spec(prefix) + last as nat * Self::pow_base_spec(n));
        assert(Self::pow_base_spec(n) <= Self::limbs_value_spec(limbs));
    }

    pub proof fn lemma_len_bound_from_value_upper_pow(limbs: Seq<u32>, upper_exp: nat)
        requires
            Self::canonical_limbs_spec(limbs),
            Self::limbs_value_spec(limbs) < Self::pow_base_spec(upper_exp),
        ensures
            limbs.len() <= upper_exp,
    {
        if limbs.len() > upper_exp {
            assert(limbs.len() > 0);
            assert(Self::canonical_limbs_spec(limbs));
            assert(limbs[(limbs.len() - 1) as int] != 0u32);
            let n = (limbs.len() - 1) as nat;
            assert(upper_exp + 1 <= limbs.len());
            assert(upper_exp + 1 <= n + 1);
            assert(upper_exp <= n);
            Self::lemma_pow_monotonic(upper_exp, n);
            Self::lemma_limbs_value_ge_pow_last_nonzero(limbs);
            assert(Self::pow_base_spec(upper_exp) <= Self::pow_base_spec(n));
            assert(Self::pow_base_spec(n) <= Self::limbs_value_spec(limbs));
            assert(Self::pow_base_spec(upper_exp) <= Self::limbs_value_spec(limbs));
            assert(Self::limbs_value_spec(limbs) < Self::pow_base_spec(upper_exp));
            assert(false);
        }
    }

    pub proof fn lemma_cmp_prefix_last_digit_gt(a: Seq<u32>, b: Seq<u32>)
        requires
            a.len() == b.len(),
            a.len() > 0,
            a[(a.len() - 1) as int] > b[(b.len() - 1) as int],
        ensures
            Self::limbs_value_spec(a) > Self::limbs_value_spec(b),
    {
        let n = (a.len() - 1) as nat;
        let a_prefix = a.subrange(0, n as int);
        let b_prefix = b.subrange(0, n as int);
        let a_last = a[n as int];
        let b_last = b[n as int];
        let a_last_nat = a_last as nat;
        let b_last_nat = b_last as nat;
        let pow_n = Self::pow_base_spec(n);

        Self::lemma_limbs_value_push(a_prefix, a_last);
        Self::lemma_limbs_value_push(b_prefix, b_last);
        assert(a_prefix.push(a_last).len() == a.len());
        assert(b_prefix.push(b_last).len() == b.len());
        assert forall|i: int| 0 <= i < a.len() implies #[trigger] a_prefix.push(a_last)[i] == a[i] by {
            if i < a_prefix.len() {
                assert(a_prefix.push(a_last)[i] == a_prefix[i]);
                assert(a_prefix[i] == a[i]);
            } else {
                assert(i == a_prefix.len());
                assert(i == n as int);
                assert(a_prefix.push(a_last)[i] == a_last);
                assert(a_last == a[i]);
            }
        };
        assert forall|i: int| 0 <= i < b.len() implies #[trigger] b_prefix.push(b_last)[i] == b[i] by {
            if i < b_prefix.len() {
                assert(b_prefix.push(b_last)[i] == b_prefix[i]);
                assert(b_prefix[i] == b[i]);
            } else {
                assert(i == b_prefix.len());
                assert(i == n as int);
                assert(b_prefix.push(b_last)[i] == b_last);
                assert(b_last == b[i]);
            }
        };
        assert(a_prefix.push(a_last) == a);
        assert(b_prefix.push(b_last) == b);
        assert(Self::limbs_value_spec(a) == Self::limbs_value_spec(a_prefix) + a_last_nat * pow_n);
        assert(Self::limbs_value_spec(b) == Self::limbs_value_spec(b_prefix) + b_last_nat * pow_n);
        Self::lemma_limbs_value_lt_pow_len(b_prefix);
        assert(Self::limbs_value_spec(b_prefix) < pow_n);
        let b_shifted = b_last_nat * pow_n;
        assert(
            Self::limbs_value_spec(b_prefix) + b_shifted
                < pow_n + b_shifted
        );
        assert(
            pow_n + b_shifted
                == b_shifted + pow_n
        ) by (nonlinear_arith);
        assert(
            (b_last_nat + 1) * pow_n
                == b_last_nat * pow_n + 1 * pow_n
        ) by (nonlinear_arith);
        assert(1 * pow_n == pow_n);
        assert(b_last_nat * pow_n == b_shifted);
        assert(
            (b_last_nat + 1) * pow_n
                == b_shifted + pow_n
        );
        assert(
            pow_n + b_shifted
                == (b_last_nat + 1) * pow_n
        );
        assert(a_last_nat > b_last_nat);
        assert(b_last_nat + 1 <= a_last_nat);
        assert(
            a_last_nat * pow_n
                == (b_last_nat + 1) * pow_n
                    + (a_last_nat - (b_last_nat + 1)) * pow_n
        ) by (nonlinear_arith);
        assert(0 <= (a_last_nat - (b_last_nat + 1)) * pow_n);
        assert(
            (b_last_nat + 1) * pow_n
                <= a_last_nat * pow_n
        );
        assert(
            Self::limbs_value_spec(b)
                < a_last_nat * pow_n
        );
        assert(Self::limbs_value_spec(a_prefix) >= 0);
        assert(
            a_last_nat * pow_n
                <= Self::limbs_value_spec(a_prefix) + a_last_nat * pow_n
        );
        assert(Self::limbs_value_spec(a) > Self::limbs_value_spec(b));
    }

    pub proof fn lemma_cmp_high_diff_gt(a: Seq<u32>, b: Seq<u32>, idx: nat)
        requires
            a.len() == b.len(),
            idx < a.len(),
            a[idx as int] > b[idx as int],
            forall|j: int| idx < j < a.len() ==> a[j] == b[j],
        ensures
            Self::limbs_value_spec(a) > Self::limbs_value_spec(b),
    {
        let split = idx + 1;
        let a_prefix = a.subrange(0, split as int);
        let b_prefix = b.subrange(0, split as int);
        let a_suffix = a.subrange(split as int, a.len() as int);
        let b_suffix = b.subrange(split as int, b.len() as int);

        assert(a == a_prefix + a_suffix);
        assert(b == b_prefix + b_suffix);
        assert(a_prefix.len() == split);
        assert(b_prefix.len() == split);
        assert(a_prefix[(a_prefix.len() - 1) as int] == a[idx as int]);
        assert(b_prefix[(b_prefix.len() - 1) as int] == b[idx as int]);
        assert(a_prefix[(a_prefix.len() - 1) as int] > b_prefix[(b_prefix.len() - 1) as int]);
        assert forall|j: int| 0 <= j < a_suffix.len() implies #[trigger] a_suffix[j] == b_suffix[j] by {
            assert(a_suffix[j] == a[(split + j) as int]);
            assert(b_suffix[j] == b[(split + j) as int]);
            assert(idx < split + j);
            assert(split + j < a.len());
            assert(a[(split + j) as int] == b[(split + j) as int]);
        };
        assert(a_suffix == b_suffix);

        Self::lemma_cmp_prefix_last_digit_gt(a_prefix, b_prefix);
        Self::lemma_limbs_value_append(a_prefix, a_suffix);
        Self::lemma_limbs_value_append(b_prefix, b_suffix);
        assert(
            Self::limbs_value_spec(a)
                == Self::limbs_value_spec(a_prefix)
                    + Self::pow_base_spec(a_prefix.len()) * Self::limbs_value_spec(a_suffix)
        );
        assert(
            Self::limbs_value_spec(b)
                == Self::limbs_value_spec(b_prefix)
                    + Self::pow_base_spec(b_prefix.len()) * Self::limbs_value_spec(b_suffix)
        );
        assert(
            Self::limbs_value_spec(b)
                == Self::limbs_value_spec(b_prefix)
                    + Self::pow_base_spec(b_prefix.len()) * Self::limbs_value_spec(a_suffix)
        );
        let suffix_shift = Self::pow_base_spec(a_prefix.len()) * Self::limbs_value_spec(a_suffix);
        assert(
            Self::limbs_value_spec(a)
                == Self::limbs_value_spec(a_prefix) + suffix_shift
        );
        assert(
            Self::limbs_value_spec(b)
                == Self::limbs_value_spec(b_prefix) + suffix_shift
        );
        assert(
            Self::limbs_value_spec(a_prefix) + suffix_shift
                > Self::limbs_value_spec(b_prefix) + suffix_shift
        );
        assert(Self::limbs_value_spec(a) > Self::limbs_value_spec(b));
    }

    pub proof fn lemma_trimmed_len_gt_implies_value_gt(a: Seq<u32>, alen: nat, b: Seq<u32>, blen: nat)
        requires
            alen <= a.len(),
            blen <= b.len(),
            forall|i: int| alen <= i < a.len() ==> a[i] == 0u32,
            forall|i: int| blen <= i < b.len() ==> b[i] == 0u32,
            blen < alen,
            alen > 0,
            a[(alen - 1) as int] != 0u32,
        ensures
            Self::limbs_value_spec(a) > Self::limbs_value_spec(b),
    {
        let a_trim = a.subrange(0, alen as int);
        let b_trim = b.subrange(0, blen as int);
        Self::lemma_limbs_value_trim_suffix_zeros(a, alen);
        Self::lemma_limbs_value_trim_suffix_zeros(b, blen);
        assert(Self::limbs_value_spec(a) == Self::limbs_value_spec(a_trim));
        assert(Self::limbs_value_spec(b) == Self::limbs_value_spec(b_trim));

        Self::lemma_limbs_value_lt_pow_len(b_trim);
        assert(Self::limbs_value_spec(b_trim) < Self::pow_base_spec(blen));
        assert(blen + 1 <= alen);
        assert((alen - 1) + 1 == alen);
        assert(blen <= (alen - 1) as nat);
        Self::lemma_pow_monotonic(blen, (alen - 1) as nat);
        assert(Self::pow_base_spec(blen) <= Self::pow_base_spec((alen - 1) as nat));
        assert(Self::limbs_value_spec(b_trim) < Self::pow_base_spec((alen - 1) as nat));

        assert(a_trim.len() == alen);
        assert(a_trim[(a_trim.len() - 1) as int] == a[(alen - 1) as int]);
        assert(a_trim[(a_trim.len() - 1) as int] != 0u32);
        Self::lemma_limbs_value_ge_pow_last_nonzero(a_trim);
        assert(Self::pow_base_spec((alen - 1) as nat) <= Self::limbs_value_spec(a_trim));
        assert(Self::limbs_value_spec(b_trim) < Self::limbs_value_spec(a_trim));
        assert(Self::limbs_value_spec(a) > Self::limbs_value_spec(b));
    }

    pub proof fn lemma_trimmed_high_diff_implies_value_gt(a: Seq<u32>, alen: nat, b: Seq<u32>, blen: nat, idx: nat)
        requires
            alen == blen,
            alen <= a.len(),
            blen <= b.len(),
            forall|i: int| alen <= i < a.len() ==> a[i] == 0u32,
            forall|i: int| blen <= i < b.len() ==> b[i] == 0u32,
            idx < alen,
            a[idx as int] > b[idx as int],
            forall|j: int| idx < j < alen ==> a[j] == b[j],
        ensures
            Self::limbs_value_spec(a) > Self::limbs_value_spec(b),
    {
        let a_trim = a.subrange(0, alen as int);
        let b_trim = b.subrange(0, blen as int);
        assert(a_trim.len() == alen);
        assert(b_trim.len() == blen);
        assert(a_trim.len() == b_trim.len());
        assert(a_trim[idx as int] == a[idx as int]);
        assert(b_trim[idx as int] == b[idx as int]);
        assert(a_trim[idx as int] > b_trim[idx as int]);
        assert forall|j: int| idx < j < a_trim.len() implies #[trigger] a_trim[j] == b_trim[j] by {
            assert(j < a_trim.len());
            assert(a_trim.len() == alen);
            assert(j < alen);
            assert(j < blen);
            assert(a_trim[j] == a[j]);
            assert(b_trim[j] == b[j]);
        };

        Self::lemma_cmp_high_diff_gt(a_trim, b_trim, idx);
        Self::lemma_limbs_value_trim_suffix_zeros(a, alen);
        Self::lemma_limbs_value_trim_suffix_zeros(b, blen);
        assert(Self::limbs_value_spec(a) == Self::limbs_value_spec(a_trim));
        assert(Self::limbs_value_spec(b) == Self::limbs_value_spec(b_trim));
        assert(Self::limbs_value_spec(a) > Self::limbs_value_spec(b));
    }

    pub proof fn lemma_model_zero_or_single_limb(&self)
        requires
            self.wf_spec(),
            self.limbs_le@.len() <= 1,
        ensures
            self.limbs_le@.len() == 0 ==> self.model@ == 0,
            self.limbs_le@.len() == 1 ==> self.model@ == self.limbs_le@[0] as nat,
    {
        if self.limbs_le@.len() == 0 {
            assert(self.model@ == Self::limbs_value_spec(self.limbs_le@));
            assert(Self::limbs_value_spec(self.limbs_le@) == 0);
        } else {
            assert(self.limbs_le@.len() == 1);
            assert(self.model@ == Self::limbs_value_spec(self.limbs_le@));
            assert(Self::limbs_value_spec(self.limbs_le@) == self.limbs_le@[0] as nat);
        }
    }
}
}
