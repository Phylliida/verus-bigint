verus! {
impl RuntimeBigNatWitness {
    /// For non-empty canonical limbs, the value mod base equals the first limb.
    pub proof fn lemma_limbs_value_mod_base(xs: Seq<u32>)
        requires
            xs.len() > 0,
        ensures
            Self::limbs_value_spec(xs) % Self::limb_base_spec()
                == xs[0] as nat,
        decreases xs.len()
    {
        if xs.len() == 1 {
            let base = Self::limb_base_spec();
            let x0 = xs[0] as nat;
            assert(Self::limbs_value_spec(xs) == x0);
            assert(x0 < base);
            lemma_small_mod(x0, base);
            assert(Self::limbs_value_spec(xs) % base == x0);
        } else {
            let tail = xs.subrange(1, xs.len() as int);
            let x0 = xs[0] as nat;
            let b = Self::limb_base_spec();
            assert(Self::limbs_value_spec(xs) == x0 + b * Self::limbs_value_spec(tail));
            // xs[0] < limb_base, and value = xs[0] + base * tail_value
            // So value % base = xs[0]
            assert(x0 < b);
            let tv = Self::limbs_value_spec(tail);
            assert(Self::limbs_value_spec(xs) == x0 + b * tv);
            // x0 + b * tv: since x0 < b, (x0 + b*tv) % b == x0
            lemma_fundamental_div_mod_converse(
                (x0 + b * tv) as int,
                b as int,
                tv as int,
                x0 as int,
            );
            assert(x0 + b * tv == tv * b + x0) by (nonlinear_arith);
            assert((x0 + b * tv) as int == (tv as int) * (b as int) + (x0 as int)) by (nonlinear_arith);
            lemma_fundamental_div_mod((x0 + b * tv) as int, b as int);
            assert(((x0 + b * tv) as int) % (b as int) == x0 as int);
            assert(Self::limbs_value_spec(xs) % Self::limb_base_spec() == xs[0] as nat);
        }
    }

    /// For non-empty limbs, the value divided by base equals the tail value.
    pub proof fn lemma_limbs_value_div_base(xs: Seq<u32>)
        requires
            xs.len() > 0,
        ensures
            Self::limbs_value_spec(xs) / Self::limb_base_spec()
                == Self::limbs_value_spec(xs.subrange(1, xs.len() as int)),
        decreases xs.len()
    {
        let tail = xs.subrange(1, xs.len() as int);
        if xs.len() == 1 {
            let x0 = xs[0] as nat;
            let base = Self::limb_base_spec();
            assert(Self::limbs_value_spec(xs) == x0);
            assert(x0 < base);
            assert(tail.len() == 0);
            assert(Self::limbs_value_spec(tail) == 0);
            let xi = xs[0] as int;
            let bi = base as int;
            assert(0 <= xi && xi < bi);
            lemma_basic_div(xi, bi);
            assert(xi / bi == 0);
            assert(Self::limbs_value_spec(xs) / Self::limb_base_spec() == 0);
            assert(Self::limbs_value_spec(xs) / Self::limb_base_spec() == Self::limbs_value_spec(tail));
        } else {
            let x0 = xs[0] as nat;
            let b = Self::limb_base_spec();
            let tv = Self::limbs_value_spec(tail);
            assert(Self::limbs_value_spec(xs) == x0 + b * tv);
            assert(x0 < b);
            // (x0 + b * tv) / b == tv
            lemma_fundamental_div_mod_converse(
                (x0 + b * tv) as int,
                b as int,
                tv as int,
                x0 as int,
            );
            assert(x0 + b * tv == tv * b + x0) by (nonlinear_arith);
            assert((x0 + b * tv) as int == (tv as int) * (b as int) + (x0 as int)) by (nonlinear_arith);
            lemma_fundamental_div_mod((x0 + b * tv) as int, b as int);
            assert(((x0 + b * tv) as int) / (b as int) == tv as int);
            assert(Self::limbs_value_spec(xs) / Self::limb_base_spec() == Self::limbs_value_spec(tail));
        }
    }

    /// If two canonical sequences have the same value, they are equal.
    pub proof fn lemma_canonical_limbs_unique(xs: Seq<u32>, ys: Seq<u32>)
        requires
            Self::canonical_limbs_spec(xs),
            Self::canonical_limbs_spec(ys),
            Self::limbs_value_spec(xs) == Self::limbs_value_spec(ys),
        ensures
            xs == ys,
        decreases xs.len() + ys.len()
    {
        if xs.len() == 0 && ys.len() == 0 {
            assert(xs == ys);
        } else if xs.len() == 0 && ys.len() > 0 {
            // xs value is 0, ys must also be 0 but ys is canonical with len > 0
            assert(Self::limbs_value_spec(xs) == 0);
            assert(Self::limbs_value_spec(ys) == 0);
            // canonical and non-empty means last limb != 0
            assert(ys[(ys.len() - 1) as int] != 0u32);
            // But value is 0, so all limbs must be 0 — contradiction
            Self::lemma_limbs_value_ge_pow_last_nonzero(ys);
            Self::lemma_pow_ge_one((ys.len() - 1) as nat);
            assert(Self::limbs_value_spec(ys) >= 1);
            assert(false);
        } else if xs.len() > 0 && ys.len() == 0 {
            assert(Self::limbs_value_spec(ys) == 0);
            assert(Self::limbs_value_spec(xs) == 0);
            assert(xs[(xs.len() - 1) as int] != 0u32);
            Self::lemma_limbs_value_ge_pow_last_nonzero(xs);
            Self::lemma_pow_ge_one((xs.len() - 1) as nat);
            assert(Self::limbs_value_spec(xs) >= 1);
            assert(false);
        } else {
            // Both non-empty
            assert(xs.len() > 0);
            assert(ys.len() > 0);

            // First limbs must be equal (via mod base)
            Self::lemma_limbs_value_mod_base(xs);
            Self::lemma_limbs_value_mod_base(ys);
            assert(Self::limbs_value_spec(xs) % Self::limb_base_spec() == xs[0] as nat);
            assert(Self::limbs_value_spec(ys) % Self::limb_base_spec() == ys[0] as nat);
            assert(xs[0] as nat == ys[0] as nat);
            assert(xs[0] == ys[0]);

            // Tail values must be equal (via div base)
            Self::lemma_limbs_value_div_base(xs);
            Self::lemma_limbs_value_div_base(ys);
            let xs_tail = xs.subrange(1, xs.len() as int);
            let ys_tail = ys.subrange(1, ys.len() as int);
            assert(Self::limbs_value_spec(xs_tail) == Self::limbs_value_spec(ys_tail));

            // Tails are canonical
            if xs_tail.len() > 0 {
                assert(xs_tail[(xs_tail.len() - 1) as int] == xs[(xs.len() - 1) as int]);
                assert(Self::canonical_limbs_spec(xs_tail));
            } else {
                assert(Self::canonical_limbs_spec(xs_tail));
            }
            if ys_tail.len() > 0 {
                assert(ys_tail[(ys_tail.len() - 1) as int] == ys[(ys.len() - 1) as int]);
                assert(Self::canonical_limbs_spec(ys_tail));
            } else {
                assert(Self::canonical_limbs_spec(ys_tail));
            }

            // Recurse
            Self::lemma_canonical_limbs_unique(xs_tail, ys_tail);
            assert(xs_tail == ys_tail);

            // Now reconstruct: xs[0] == ys[0] and xs[1..] == ys[1..]
            assert(xs.len() == ys.len()) by {
                assert(xs_tail.len() == ys_tail.len());
                assert(xs.len() - 1 == ys.len() - 1);
            };
            assert forall|i: int| 0 <= i < xs.len() implies xs[i] == ys[i] by {
                if i == 0 {
                    assert(xs[0] == ys[0]);
                } else {
                    assert(1 <= i < xs.len());
                    assert(xs_tail[i - 1] == ys_tail[i - 1]);
                    assert(xs[i] == xs_tail[i - 1]);
                    assert(ys[i] == ys_tail[i - 1]);
                }
            };
            assert(xs =~= ys);
        }
    }

    /// If two well-formed BigNat witnesses have the same model, their limb sequences are equal.
    pub proof fn lemma_wf_same_model_same_limbs(a: RuntimeBigNatWitness, b: RuntimeBigNatWitness)
        requires
            a.wf_spec(),
            b.wf_spec(),
            a.model@ == b.model@,
        ensures
            a.limbs_le@ == b.limbs_le@,
    {
        assert(a.model@ == Self::limbs_value_spec(a.limbs_le@));
        assert(b.model@ == Self::limbs_value_spec(b.limbs_le@));
        assert(Self::limbs_value_spec(a.limbs_le@) == Self::limbs_value_spec(b.limbs_le@));
        assert(Self::canonical_limbs_spec(a.limbs_le@));
        assert(Self::canonical_limbs_spec(b.limbs_le@));
        Self::lemma_canonical_limbs_unique(a.limbs_le@, b.limbs_le@);
    }
}
}
