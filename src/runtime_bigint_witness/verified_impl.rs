#![cfg(verus_keep_ghost)]

use super::RuntimeBigNatWitness;
use vstd::prelude::*;
use vstd::arithmetic::div_mod::{
    lemma_add_mod_noop,
    lemma_basic_div,
    lemma_div_is_ordered,
    lemma_div_is_ordered_by_denominator,
    lemma_fundamental_div_mod,
    lemma_fundamental_div_mod_converse,
    lemma_multiply_divide_lt,
    lemma_mul_mod_noop,
    lemma_mod_self_0,
    lemma_mod_pos_bound,
    lemma_small_mod,
};
use vstd::seq::Seq;

// Core representation/arithmetic proof helpers are split by theme for readability.
include!("verified_impl/core_repr_prefix.rs");
include!("verified_impl/core_pow_cmp.rs");
include!("verified_impl/core_nat_div_mod.rs");

// Operation-level proof wrappers are split by operation for readability.
include!("verified_impl/ops_add.rs");
include!("verified_impl/ops_mul.rs");
include!("verified_impl/ops_shape.rs");
include!("verified_impl/ops_cmp_sub.rs");
include!("verified_impl/ops_div_rem.rs");

// Contract-level proof obligations are split from exec implementations.
include!("verified_impl/contracts_cmp_sub.rs");
include!("verified_impl/contracts_arith.rs");

verus! {
impl RuntimeBigNatWitness {

    fn from_parts(limbs_le: Vec<u32>, Ghost(model): Ghost<nat>) -> (out: Self)
        requires
            model == Self::limbs_value_spec(limbs_le@),
            Self::canonical_limbs_spec(limbs_le@),
        ensures
            out.limbs_le@ == limbs_le@,
            out.model@ == model,
            out.wf_spec(),
    {
        let out = RuntimeBigNatWitness { limbs_le, model: Ghost(model) };
        proof {
            assert(out.limbs_le@ == limbs_le@);
            assert(out.model@ == model);
            assert(out.wf_spec());
        }
        out
    }

    pub fn zero() -> (out: Self)
        ensures
            out.model@ == 0,
            out.wf_spec(),
    {
        let limbs_le: Vec<u32> = Vec::new();
        let out = Self::from_parts(limbs_le, Ghost(0));
        proof {
            assert(Self::limbs_value_spec(Seq::<u32>::empty()) == 0);
            assert(Self::canonical_limbs_spec(Seq::<u32>::empty()));
        }
        out
    }

    pub fn from_u32(x: u32) -> (out: Self)
        ensures
            out.model@ == x as nat,
            out.wf_spec(),
    {
        if x == 0 {
            Self::zero()
        } else {
            let mut limbs_le: Vec<u32> = Vec::new();
            limbs_le.push(x);
            proof {
                assert(limbs_le@.len() == 1);
                assert(limbs_le@[0] == x);
                assert(Self::limbs_value_spec(limbs_le@) == x as nat);
                assert(Self::canonical_limbs_spec(limbs_le@));
            }
            Self::from_parts(limbs_le, Ghost(x as nat))
        }
    }

    pub fn from_u64(x: u64) -> (out: Self)
        ensures
            out.model@ == x as nat,
            out.wf_spec(),
    {
        let base_u64 = 4_294_967_296u64;
        let lo_u64 = x % base_u64;
        let hi_u64 = x / base_u64;
        let lo = lo_u64 as u32;
        let hi = hi_u64 as u32;
        let out = Self::from_two_limbs(lo, hi);
        proof {
            assert(x == hi_u64 * base_u64 + lo_u64);
            assert(lo_u64 < base_u64);
            assert(hi_u64 <= 4_294_967_295u64);
            assert(lo as u64 == lo_u64);
            assert(hi as u64 == hi_u64);
            assert(out.model@ == lo as nat + Self::limb_base_spec() * hi as nat);
            assert(Self::limb_base_spec() == 4_294_967_296);
            assert(x == hi as u64 * 4_294_967_296u64 + lo as u64);
            assert(x as nat == hi as nat * 4_294_967_296nat + lo as nat);
            assert(out.model@ == x as nat);
        }
        out
    }

    pub fn from_two_limbs(lo: u32, hi: u32) -> (out: Self)
        ensures
            out.model@ == lo as nat + Self::limb_base_spec() * hi as nat,
            out.wf_spec(),
    {
        if hi == 0 {
            let out = Self::from_u32(lo);
            proof {
                assert(Self::limb_base_spec() * hi as nat == 0);
                assert(out.model@ == lo as nat);
                assert(out.model@ == lo as nat + Self::limb_base_spec() * hi as nat);
            }
            out
        } else {
            let mut limbs_le: Vec<u32> = Vec::new();
            limbs_le.push(lo);
            limbs_le.push(hi);
            proof {
                assert(limbs_le@.len() == 2);
                assert(limbs_le@[0] == lo);
                assert(limbs_le@[1] == hi);
                assert(limbs_le@.subrange(1, limbs_le@.len() as int).len() == 1);
                assert(limbs_le@.subrange(1, limbs_le@.len() as int)[0] == hi);
                assert(Self::limbs_value_spec(limbs_le@.subrange(1, limbs_le@.len() as int)) == hi as nat);
                assert(Self::limbs_value_spec(limbs_le@) == lo as nat + Self::limb_base_spec() * hi as nat);
                assert(Self::canonical_limbs_spec(limbs_le@));
            }
            Self::from_parts(limbs_le, Ghost(lo as nat + Self::limb_base_spec() * hi as nat))
        }
    }

    pub fn add(&self, rhs: &Self) -> (out: Self)
        requires
            self.wf_spec(),
            rhs.wf_spec(),
        ensures
            out.wf_spec(),
            out.model@ == self.model@ + rhs.model@,
    {
        let out = self.add_limbwise_small_total(rhs);
        proof {
            assert(self.model@ == Self::limbs_value_spec(self.limbs_le@));
            assert(rhs.model@ == Self::limbs_value_spec(rhs.limbs_le@));
            assert(
                out.model@
                    == Self::limbs_value_spec(self.limbs_le@)
                        + Self::limbs_value_spec(rhs.limbs_le@)
            );
            assert(out.model@ == self.model@ + rhs.model@);
        }
        out
    }

    pub fn mul(&self, rhs: &Self) -> (out: Self)
        requires
            self.wf_spec(),
            rhs.wf_spec(),
        ensures
            out.wf_spec(),
            out.model@ == self.model@ * rhs.model@,
            rhs.model@ == 0 ==> out.model@ == 0,
            rhs.model@ == 1 ==> out.model@ == self.model@,
            self.model@ == 0 ==> out.model@ == 0,
            self.model@ == 1 ==> out.model@ == rhs.model@,
    {
        let out = self.mul_limbwise_small_total(rhs);
        proof {
            assert(self.model@ == Self::limbs_value_spec(self.limbs_le@));
            assert(rhs.model@ == Self::limbs_value_spec(rhs.limbs_le@));
            assert(
                out.model@
                    == Self::limbs_value_spec(self.limbs_le@)
                        * Self::limbs_value_spec(rhs.limbs_le@)
            );
            assert(out.model@ == self.model@ * rhs.model@);
            if rhs.model@ == 0 {
                assert(out.model@ == self.model@ * 0);
                assert(out.model@ == 0);
            }
            if rhs.model@ == 1 {
                assert(out.model@ == self.model@ * 1);
                assert(out.model@ == self.model@);
            }
            if self.model@ == 0 {
                assert(out.model@ == 0 * rhs.model@);
                assert(out.model@ == 0);
            }
            if self.model@ == 1 {
                assert(out.model@ == 1 * rhs.model@);
                assert(out.model@ == rhs.model@);
            }
        }
        out
    }

    pub fn div(&self, rhs: &Self) -> (out: Self)
        requires
            self.wf_spec(),
            rhs.wf_spec(),
        ensures
            out.wf_spec(),
            rhs.model@ == 0 ==> out.model@ == 0,
            rhs.model@ > 0 ==> out.model@ * rhs.model@ <= self.model@,
            rhs.model@ > 0 ==> self.model@ < (out.model@ + 1) * rhs.model@,
            rhs.model@ > 0 ==> out.model@ == self.model@ / rhs.model@,
            rhs.model@ > 0 && rhs.model@ == 1 ==> out.model@ == self.model@,
            rhs.model@ > 0 && self.model@ < rhs.model@ ==> out.model@ == 0,
            rhs.model@ > 0 && self.model@ == rhs.model@ ==> out.model@ == 1,
    {
        let out = self.div_limbwise_small_total(rhs);
        proof {
            assert(self.model@ == Self::limbs_value_spec(self.limbs_le@));
            assert(rhs.model@ == Self::limbs_value_spec(rhs.limbs_le@));
            if rhs.model@ == 0 {
                assert(Self::limbs_value_spec(rhs.limbs_le@) == 0);
                assert(out.model@ == 0);
            }
            if rhs.model@ > 0 {
                assert(Self::limbs_value_spec(rhs.limbs_le@) > 0);
                assert(
                    out.model@ * Self::limbs_value_spec(rhs.limbs_le@)
                        <= Self::limbs_value_spec(self.limbs_le@)
                );
                assert(
                    Self::limbs_value_spec(self.limbs_le@)
                        < (out.model@ + 1) * Self::limbs_value_spec(rhs.limbs_le@)
                );
                assert(
                    out.model@
                        == Self::limbs_value_spec(self.limbs_le@)
                            / Self::limbs_value_spec(rhs.limbs_le@)
                );
                assert(out.model@ * rhs.model@ <= self.model@);
                assert(self.model@ < (out.model@ + 1) * rhs.model@);
                assert(out.model@ == self.model@ / rhs.model@);

                if rhs.model@ == 1 {
                    assert(self.model@ / rhs.model@ == self.model@);
                    assert(out.model@ == self.model@);
                }
                if self.model@ < rhs.model@ {
                    let xi = self.model@ as int;
                    let di = rhs.model@ as int;
                    assert(0 <= xi < di);
                    lemma_basic_div(xi, di);
                    assert(xi / di == 0);
                    assert((self.model@ / rhs.model@) as int == xi / di);
                    assert(self.model@ / rhs.model@ == 0);
                    assert(out.model@ == 0);
                }
                if self.model@ == rhs.model@ {
                    assert(self.model@ / rhs.model@ == rhs.model@ / rhs.model@);
                    assert(rhs.model@ / rhs.model@ == 1);
                    assert(out.model@ == 1);
                }
            }
        }
        out
    }

    pub fn rem(&self, rhs: &Self) -> (out: Self)
        requires
            self.wf_spec(),
            rhs.wf_spec(),
        ensures
            out.wf_spec(),
            rhs.model@ == 0 ==> out.model@ == 0,
            rhs.model@ > 0 ==> out.model@ < rhs.model@,
            rhs.model@ > 0 ==> out.model@ == self.model@ % rhs.model@,
            rhs.model@ > 0
                ==> (out.model@ == 0 <==> exists|k: nat| #[trigger] (k * rhs.model@) == self.model@),
            rhs.model@ > 0 && rhs.model@ == 1 ==> out.model@ == 0,
            rhs.model@ > 0 && self.model@ < rhs.model@ ==> out.model@ == self.model@,
            rhs.model@ > 0 && self.model@ == rhs.model@ ==> out.model@ == 0,
    {
        let out = self.rem_limbwise_small_total(rhs);
        proof {
            assert(self.model@ == Self::limbs_value_spec(self.limbs_le@));
            assert(rhs.model@ == Self::limbs_value_spec(rhs.limbs_le@));
            if rhs.model@ == 0 {
                assert(Self::limbs_value_spec(rhs.limbs_le@) == 0);
                assert(out.model@ == 0);
            }
            if rhs.model@ > 0 {
                assert(Self::limbs_value_spec(rhs.limbs_le@) > 0);
                assert(out.model@ < Self::limbs_value_spec(rhs.limbs_le@));
                assert(
                    out.model@
                        == Self::limbs_value_spec(self.limbs_le@)
                            % Self::limbs_value_spec(rhs.limbs_le@)
                );
                assert(out.model@ < rhs.model@);
                assert(out.model@ == self.model@ % rhs.model@);

                if out.model@ == 0 {
                    assert(self.model@ % rhs.model@ == 0);
                    let k = Self::lemma_mod_zero_implies_multiple_nat(self.model@, rhs.model@);
                    assert(self.model@ == k * rhs.model@);
                    assert(exists|kw: nat| #[trigger] (kw * rhs.model@) == self.model@) by {
                        let kw = k;
                        assert(kw * rhs.model@ == self.model@);
                    };
                }
                if exists|kw: nat| #[trigger] (kw * rhs.model@) == self.model@ {
                    let k = choose|kw: nat| #[trigger] (kw * rhs.model@) == self.model@;
                    assert(k * rhs.model@ == self.model@);
                    assert(self.model@ == k * rhs.model@);
                    Self::lemma_multiple_implies_mod_zero_nat(self.model@, rhs.model@, k);
                    assert(self.model@ % rhs.model@ == 0);
                    assert(out.model@ == 0);
                }

                if rhs.model@ == 1 {
                    assert(out.model@ < 1);
                    assert(out.model@ == 0);
                }
                if self.model@ < rhs.model@ {
                    lemma_small_mod(self.model@, rhs.model@);
                    assert(self.model@ % rhs.model@ == self.model@);
                    assert(out.model@ == self.model@);
                }
                if self.model@ == rhs.model@ {
                    let di = rhs.model@ as int;
                    lemma_mod_self_0(di);
                    assert(di % di == 0);
                    assert((rhs.model@ % rhs.model@) as int == di % di);
                    assert(rhs.model@ % rhs.model@ == 0);
                    assert(self.model@ % rhs.model@ == 0);
                    assert(out.model@ == 0);
                }
            }
        }
        out
    }

    pub fn div_rem(&self, rhs: &Self) -> (out: (Self, Self))
        requires
            self.wf_spec(),
            rhs.wf_spec(),
        ensures
            out.0.wf_spec(),
            out.1.wf_spec(),
            rhs.model@ == 0 ==> out.0.model@ == 0 && out.1.model@ == 0,
            rhs.model@ > 0 ==> self.model@ == out.0.model@ * rhs.model@ + out.1.model@,
            rhs.model@ > 0 ==> out.1.model@ < rhs.model@,
            rhs.model@ > 0 ==> out.0.model@ == self.model@ / rhs.model@,
            rhs.model@ > 0 ==> out.1.model@ == self.model@ % rhs.model@,
    {
        let out = self.div_rem_limbwise_small_total(rhs);
        proof {
            assert(self.model@ == Self::limbs_value_spec(self.limbs_le@));
            assert(rhs.model@ == Self::limbs_value_spec(rhs.limbs_le@));
            if rhs.model@ == 0 {
                assert(Self::limbs_value_spec(rhs.limbs_le@) == 0);
                assert(out.0.model@ == 0);
                assert(out.1.model@ == 0);
            }
            if rhs.model@ > 0 {
                assert(Self::limbs_value_spec(rhs.limbs_le@) > 0);
                assert(
                    Self::limbs_value_spec(self.limbs_le@)
                        == out.0.model@ * Self::limbs_value_spec(rhs.limbs_le@) + out.1.model@
                );
                assert(out.1.model@ < Self::limbs_value_spec(rhs.limbs_le@));
                assert(
                    out.0.model@
                        == Self::limbs_value_spec(self.limbs_le@)
                            / Self::limbs_value_spec(rhs.limbs_le@)
                );
                assert(
                    out.1.model@
                        == Self::limbs_value_spec(self.limbs_le@)
                            % Self::limbs_value_spec(rhs.limbs_le@)
                );
                assert(self.model@ == out.0.model@ * rhs.model@ + out.1.model@);
                assert(out.1.model@ < rhs.model@);
                assert(out.0.model@ == self.model@ / rhs.model@);
                assert(out.1.model@ == self.model@ % rhs.model@);
            }
        }
        out
    }

    pub fn is_zero(&self) -> (out: bool)
        requires
            self.wf_spec(),
        ensures
            out == (self.model@ == 0),
    {
        let out = self.limbs_le.len() == 0;
        proof {
            if out {
                assert(self.limbs_le@.len() == 0);
                assert(self.model@ == Self::limbs_value_spec(self.limbs_le@));
                assert(Self::limbs_value_spec(self.limbs_le@) == 0);
                assert(self.model@ == 0);
            } else {
                assert(self.limbs_le@.len() > 0);
                assert(Self::canonical_limbs_spec(self.limbs_le@));
                let last = (self.limbs_le@.len() - 1) as nat;
                assert(self.limbs_le@[last as int] != 0u32);
                Self::lemma_limbs_value_ge_pow_last_nonzero(self.limbs_le@);
                Self::lemma_pow_ge_one(last);
                assert(Self::pow_base_spec(last) <= Self::limbs_value_spec(self.limbs_le@));
                assert(Self::pow_base_spec(last) >= 1);
                assert(Self::limbs_value_spec(self.limbs_le@) >= 1);
                assert(self.model@ == Self::limbs_value_spec(self.limbs_le@));
                assert(self.model@ != 0);
            }
        }
        out
    }

    pub fn limbs_le(&self) -> (out: &[u32])
        ensures
            out@ == self.limbs_le@,
    {
        &self.limbs_le
    }

    /// First constructive limb-wise addition milestone:
    /// supports operands represented by at most one limb each.
    pub fn add_limbwise_small(&self, rhs: &Self) -> (out: Self)
        requires
            self.wf_spec(),
            rhs.wf_spec(),
            self.limbs_le@.len() <= 1,
            rhs.limbs_le@.len() <= 1,
        ensures
            out.wf_spec(),
            out.model@ == self.model@ + rhs.model@,
    {
        let a0 = if self.limbs_le.len() == 0 { 0u32 } else { self.limbs_le[0] };
        let b0 = if rhs.limbs_le.len() == 0 { 0u32 } else { rhs.limbs_le[0] };

        let sum = a0 as u64 + b0 as u64;
        let base_u64 = 4_294_967_296u64;
        let (lo, hi) = if sum < base_u64 {
            (sum as u32, 0u32)
        } else {
            ((sum - base_u64) as u32, 1u32)
        };

        let out = Self::from_two_limbs(lo, hi);
        proof {
            self.lemma_model_zero_or_single_limb();
            rhs.lemma_model_zero_or_single_limb();

            if self.limbs_le@.len() == 0 {
                assert(a0 == 0u32);
                assert(self.model@ == 0);
                assert(self.model@ == a0 as nat);
            } else {
                assert(self.limbs_le@.len() == 1);
                assert(a0 == self.limbs_le@[0]);
                assert(self.model@ == self.limbs_le@[0] as nat);
                assert(self.model@ == a0 as nat);
            }

            if rhs.limbs_le@.len() == 0 {
                assert(b0 == 0u32);
                assert(rhs.model@ == 0);
                assert(rhs.model@ == b0 as nat);
            } else {
                assert(rhs.limbs_le@.len() == 1);
                assert(b0 == rhs.limbs_le@[0]);
                assert(rhs.model@ == rhs.limbs_le@[0] as nat);
                assert(rhs.model@ == b0 as nat);
            }

            assert(a0 as nat + rhs.model@ == a0 as nat + b0 as nat);
            assert(self.model@ + rhs.model@ == a0 as nat + b0 as nat);

            if sum < base_u64 {
                assert(hi == 0u32);
                assert(lo as u64 == sum);
                assert(lo as nat == sum as nat);
                assert(sum as nat == a0 as nat + b0 as nat);
                assert(out.model@ == lo as nat + Self::limb_base_spec() * hi as nat);
                assert(Self::limb_base_spec() * hi as nat == 0);
                assert(out.model@ == lo as nat);
                assert(out.model@ == sum as nat);
                assert(out.model@ == self.model@ + rhs.model@);
            } else {
                assert(hi == 1u32);
                assert(base_u64 <= sum);
                assert(sum < 2 * base_u64);
                assert((sum - base_u64) < base_u64);
                assert(lo as u64 == sum - base_u64);
                assert(lo as nat == (sum - base_u64) as nat);
                assert(sum as nat == a0 as nat + b0 as nat);
                assert(out.model@ == lo as nat + Self::limb_base_spec() * hi as nat);
                assert(Self::limb_base_spec() * hi as nat == Self::limb_base_spec());
                assert(out.model@ == (sum - base_u64) as nat + Self::limb_base_spec());
                assert(base_u64 as nat == Self::limb_base_spec());
                assert(out.model@ == sum as nat);
                assert(out.model@ == self.model@ + rhs.model@);
            }
        }
        out
    }

    /// Total limb-wise addition helper used by scalar witness plumbing.
    ///
    /// Computes carry-propagating multi-limb addition over little-endian limbs,
    /// then canonicalizes the output by trimming trailing zero limbs.
    pub fn add_limbwise_small_total(&self, rhs: &Self) -> (out: Self)
        ensures
            out.wf_spec(),
            out.model@ == Self::limbs_value_spec(self.limbs_le@) + Self::limbs_value_spec(rhs.limbs_le@),
    {
        let alen = Self::trimmed_len_exec(&self.limbs_le);
        let blen = Self::trimmed_len_exec(&rhs.limbs_le);
        assert(alen <= self.limbs_le.len());
        assert(blen <= rhs.limbs_le.len());
        let ghost alen_nat = alen as nat;
        let ghost blen_nat = blen as nat;
        proof {
            assert(alen_nat == alen as nat);
            assert(blen_nat == blen as nat);
        }
        let n = if alen > blen { alen } else { blen };
        let mut out_limbs: Vec<u32> = Vec::new();
        let mut i: usize = 0;
        let mut carry: u64 = 0u64;
        while i < n
            invariant
                i <= n,
                alen <= self.limbs_le.len(),
                blen <= rhs.limbs_le.len(),
                out_limbs@.len() == i,
                carry == 0u64 || carry == 1u64,
                Self::limbs_value_spec(out_limbs@) + carry as nat * Self::pow_base_spec(i as nat)
                    == Self::prefix_sum_spec(self.limbs_le@, alen as nat, i as nat)
                        + Self::prefix_sum_spec(rhs.limbs_le@, blen as nat, i as nat),
            decreases n - i,
        {
            let i_old = i;
            let carry_in = carry;
            let ghost i_nat = i_old as nat;
            let a = if i < alen {
                assert(i < self.limbs_le.len());
                self.limbs_le[i] as u64
            } else {
                0u64
            };
            let b = if i < blen {
                assert(i < rhs.limbs_le.len());
                rhs.limbs_le[i] as u64
            } else {
                0u64
            };
            let sum = a + b + carry_in;
            let (digit, next_carry) = if sum >= 4_294_967_296u64 {
                assert(sum == a + b + carry_in);
                assert(a <= 4_294_967_295u64);
                assert(b <= 4_294_967_295u64);
                assert(carry_in <= 1u64);
                assert(sum <= 8_589_934_591u64);
                assert(sum >= 4_294_967_296u64);
                assert(sum - 4_294_967_296u64 <= 4_294_967_295u64);
                let d = (sum - 4_294_967_296u64) as u32;
                (d, 1u64)
            } else {
                assert(sum == a + b + carry_in);
                assert(a <= 4_294_967_295u64);
                assert(b <= 4_294_967_295u64);
                assert(carry_in <= 1u64);
                assert(sum <= 8_589_934_591u64);
                assert(!(sum >= 4_294_967_296u64));
                assert(sum < 4_294_967_296u64);
                assert(sum <= 4_294_967_295u64);
                let d = sum as u32;
                (d, 0u64)
            };
            proof {
                let a_nat = a as nat;
                let b_nat = b as nat;
                let carry_nat = carry_in as nat;
                let digit_nat = digit as nat;
                let next_carry_nat = next_carry as nat;
                assert(i_nat == i_old as nat);
                if i_old < alen {
                    assert(i_old < self.limbs_le.len());
                    assert((i_old as int) < (alen as int));
                    assert(i_nat < alen as nat);
                    assert(i_nat < self.limbs_le@.len());
                    assert(a == self.limbs_le[i_old as int] as u64);
                    assert(a_nat == self.limbs_le@[i_old as int] as nat);
                    assert(a_nat < Self::limb_base_spec());
                    assert(
                        Self::limb_or_zero_spec(self.limbs_le@, alen as nat, i_nat)
                            == self.limbs_le@[i_old as int] as nat
                    );
                    assert(Self::limb_or_zero_spec(self.limbs_le@, alen as nat, i_nat) == a_nat);
                } else {
                    assert(a == 0u64);
                    assert(a_nat == 0);
                    assert(a_nat < Self::limb_base_spec());
                    assert((alen as int) <= (i_old as int));
                    assert(alen as nat <= i_nat);
                    Self::lemma_limb_or_zero_past_logical_len(self.limbs_le@, alen as nat, i_nat);
                    assert(Self::limb_or_zero_spec(self.limbs_le@, alen as nat, i_nat) == a_nat);
                }
                if i_old < blen {
                    assert(i_old < rhs.limbs_le.len());
                    assert((i_old as int) < (blen as int));
                    assert(i_nat < blen as nat);
                    assert(i_nat < rhs.limbs_le@.len());
                    assert(b == rhs.limbs_le[i_old as int] as u64);
                    assert(b_nat == rhs.limbs_le@[i_old as int] as nat);
                    assert(b_nat < Self::limb_base_spec());
                    assert(
                        Self::limb_or_zero_spec(rhs.limbs_le@, blen as nat, i_nat)
                            == rhs.limbs_le@[i_old as int] as nat
                    );
                    assert(Self::limb_or_zero_spec(rhs.limbs_le@, blen as nat, i_nat) == b_nat);
                } else {
                    assert(b == 0u64);
                    assert(b_nat == 0);
                    assert(b_nat < Self::limb_base_spec());
                    assert((blen as int) <= (i_old as int));
                    assert(blen as nat <= i_nat);
                    Self::lemma_limb_or_zero_past_logical_len(rhs.limbs_le@, blen as nat, i_nat);
                    assert(Self::limb_or_zero_spec(rhs.limbs_le@, blen as nat, i_nat) == b_nat);
                }
                assert(carry_in == 0u64 || carry_in == 1u64);
                assert(carry_nat <= 1);
                Self::lemma_add_digit_carry_decompose(a_nat, b_nat, carry_nat);

                assert(sum == a + b + carry_in);
                assert(sum as nat == a_nat + b_nat + carry_nat);
                if sum >= 4_294_967_296u64 {
                    assert(next_carry == 1u64);
                    assert(next_carry_nat == 1);
                    assert(digit as u64 == sum - 4_294_967_296u64);
                    assert(digit_nat == (sum - 4_294_967_296u64) as nat);
                    assert(Self::limb_base_spec() == 4_294_967_296);
                    assert((sum - 4_294_967_296u64) as nat + Self::limb_base_spec() == sum as nat);
                    assert(digit_nat + next_carry_nat * Self::limb_base_spec() == sum as nat);
                } else {
                    assert(next_carry == 0u64);
                    assert(next_carry_nat == 0);
                    assert(digit as u64 == sum);
                    assert(digit_nat == sum as nat);
                    assert(digit_nat + next_carry_nat * Self::limb_base_spec() == sum as nat);
                }
                assert(digit_nat + next_carry_nat * Self::limb_base_spec() == a_nat + b_nat + carry_nat);

                Self::lemma_prefix_sum_step(self.limbs_le@, alen as nat, i_nat);
                Self::lemma_prefix_sum_step(rhs.limbs_le@, blen as nat, i_nat);
                Self::lemma_pow_base_succ(i_nat);
                Self::lemma_add_prefix_step(
                    Self::limbs_value_spec(out_limbs@),
                    Self::prefix_sum_spec(self.limbs_le@, alen as nat, i_nat),
                    Self::prefix_sum_spec(rhs.limbs_le@, blen as nat, i_nat),
                    digit_nat,
                    a_nat,
                    b_nat,
                    carry_nat,
                    next_carry_nat,
                    Self::pow_base_spec(i_nat),
                    Self::pow_base_spec(i_nat + 1),
                );
                Self::lemma_limbs_value_push(out_limbs@, digit);
                assert(out_limbs@.push(digit).len() == i_nat + 1);
                assert(
                    Self::prefix_sum_spec(self.limbs_le@, alen as nat, i_nat + 1)
                        == Self::prefix_sum_spec(self.limbs_le@, alen as nat, i_nat)
                            + Self::limb_or_zero_spec(self.limbs_le@, alen as nat, i_nat)
                                * Self::pow_base_spec(i_nat)
                );
                assert(
                    Self::prefix_sum_spec(rhs.limbs_le@, blen as nat, i_nat + 1)
                        == Self::prefix_sum_spec(rhs.limbs_le@, blen as nat, i_nat)
                            + Self::limb_or_zero_spec(rhs.limbs_le@, blen as nat, i_nat)
                                * Self::pow_base_spec(i_nat)
                );
                assert(
                    Self::prefix_sum_spec(self.limbs_le@, alen as nat, i_nat + 1)
                        == Self::prefix_sum_spec(self.limbs_le@, alen as nat, i_nat)
                            + a_nat * Self::pow_base_spec(i_nat)
                );
                assert(
                    Self::prefix_sum_spec(rhs.limbs_le@, blen as nat, i_nat + 1)
                        == Self::prefix_sum_spec(rhs.limbs_le@, blen as nat, i_nat)
                            + b_nat * Self::pow_base_spec(i_nat)
                );
                assert(
                    Self::limbs_value_spec(out_limbs@.push(digit))
                        + next_carry_nat * Self::pow_base_spec(i_nat + 1)
                        == Self::prefix_sum_spec(self.limbs_le@, alen as nat, i_nat + 1)
                            + Self::prefix_sum_spec(rhs.limbs_le@, blen as nat, i_nat + 1)
                );
            }
            carry = next_carry;
            out_limbs.push(digit);
            i = i + 1;
        }
        assert(i == n);
        assert(out_limbs@.len() == n);
        let ghost n_nat = n as nat;
        let ghost pre_push = out_limbs@;
        proof {
            assert(
                Self::limbs_value_spec(pre_push) + carry as nat * Self::pow_base_spec(n_nat)
                    == Self::prefix_sum_spec(self.limbs_le@, alen_nat, n_nat)
                        + Self::prefix_sum_spec(rhs.limbs_le@, blen_nat, n_nat)
            );
            if alen_nat <= n_nat {
                Self::lemma_prefix_sum_constant_past_logical_len(self.limbs_le@, alen_nat, n_nat);
            }
            if blen_nat <= n_nat {
                Self::lemma_prefix_sum_constant_past_logical_len(rhs.limbs_le@, blen_nat, n_nat);
            }
            Self::lemma_prefix_sum_eq_subrange_value(self.limbs_le@, alen_nat);
            Self::lemma_prefix_sum_eq_subrange_value(rhs.limbs_le@, blen_nat);
            assert(forall|j: int| alen_nat <= j < self.limbs_le@.len() ==> self.limbs_le@[j] == 0u32);
            assert(forall|j: int| blen_nat <= j < rhs.limbs_le@.len() ==> rhs.limbs_le@[j] == 0u32);
            Self::lemma_limbs_value_trim_suffix_zeros(self.limbs_le@, alen_nat);
            Self::lemma_limbs_value_trim_suffix_zeros(rhs.limbs_le@, blen_nat);
            assert(
                Self::prefix_sum_spec(self.limbs_le@, alen_nat, n_nat)
                    == Self::limbs_value_spec(self.limbs_le@)
            );
            assert(
                Self::prefix_sum_spec(rhs.limbs_le@, blen_nat, n_nat)
                    == Self::limbs_value_spec(rhs.limbs_le@)
            );
        }
        if carry != 0u64 {
            out_limbs.push(1u32);
        }
        proof {
            if carry == 0u64 {
                assert(out_limbs@ == pre_push);
                assert(carry as nat == 0);
                assert(
                    Self::limbs_value_spec(out_limbs@)
                        == Self::limbs_value_spec(self.limbs_le@)
                            + Self::limbs_value_spec(rhs.limbs_le@)
                );
            } else {
                assert(carry == 1u64);
                assert(carry as nat == 1);
                Self::lemma_limbs_value_push(pre_push, 1u32);
                assert(out_limbs@ == pre_push.push(1u32));
                assert(
                    Self::limbs_value_spec(out_limbs@)
                        == Self::limbs_value_spec(pre_push) + Self::pow_base_spec(n_nat)
                );
                assert(
                    Self::limbs_value_spec(out_limbs@)
                        == Self::limbs_value_spec(self.limbs_le@)
                            + Self::limbs_value_spec(rhs.limbs_le@)
                );
            }
        }
        let out_limbs = Self::trim_trailing_zero_limbs(out_limbs);
        proof {
            assert(
                Self::limbs_value_spec(out_limbs@)
                    == Self::limbs_value_spec(self.limbs_le@)
                        + Self::limbs_value_spec(rhs.limbs_le@)
            );
        }
        let ghost model = Self::limbs_value_spec(out_limbs@);
        let out = Self::from_parts(out_limbs, Ghost(model));
        proof {
            assert(out.model@ == Self::limbs_value_spec(out.limbs_le@));
            assert(out.model@ == Self::limbs_value_spec(self.limbs_le@) + Self::limbs_value_spec(rhs.limbs_le@));
        }
        out
    }

    fn trimmed_len_exec(limbs: &Vec<u32>) -> (out: usize)
        ensures
            out <= limbs.len(),
            forall|i: int| out <= i < limbs.len() ==> limbs@[i] == 0u32,
            out > 0 ==> limbs@[(out - 1) as int] != 0u32,
    {
        let mut n = limbs.len();
        while n > 0 && limbs[n - 1] == 0u32
            invariant
                n <= limbs.len(),
                forall|i: int| n <= i < limbs.len() ==> limbs@[i] == 0u32,
            decreases n,
        {
            assert(n > 0);
            assert(limbs[(n - 1) as int] == 0u32);
            n = n - 1;
        }
        assert(n <= limbs.len());
        if n > 0 {
            assert(!(n > 0 && limbs[n - 1] == 0u32));
            assert(limbs[n - 1] != 0u32);
            assert(limbs@[(n - 1) as int] != 0u32);
        }
        n
    }

    fn trim_trailing_zero_limbs(limbs: Vec<u32>) -> (out: Vec<u32>)
        ensures
            Self::canonical_limbs_spec(out@),
            Self::limbs_value_spec(out@) == Self::limbs_value_spec(limbs@),
    {
        let n = Self::trimmed_len_exec(&limbs);
        assert(n <= limbs.len());
        let mut out: Vec<u32> = Vec::new();
        let mut i: usize = 0;
        while i < n
            invariant
                i <= n,
                n <= limbs.len(),
                out@ == limbs@.subrange(0, i as int),
            decreases n - i,
        {
            assert(i < limbs.len());
            out.push(limbs[i]);
            i = i + 1;
        }
        proof {
            assert(out@ == limbs@.subrange(0, n as int));
            if n == 0 {
                assert(out@.len() == 0);
                assert(Self::canonical_limbs_spec(out@));
            } else {
                assert(0 < n);
                assert(out@.len() == n);
                assert(limbs@[(n - 1) as int] != 0u32);
                assert(out@[(out@.len() - 1) as int] == limbs@[(n - 1) as int]);
                assert(out@[(out@.len() - 1) as int] != 0u32);
                assert(Self::canonical_limbs_spec(out@));
            }
        }
        proof {
            let ng: nat = n as nat;
            assert(ng <= limbs@.len());
            assert(forall|i: int| ng <= i < limbs@.len() ==> limbs@[i] == 0u32);
            Self::lemma_limbs_value_trim_suffix_zeros(limbs@, ng);
            assert(
                Self::limbs_value_spec(limbs@)
                    == Self::limbs_value_spec(limbs@.subrange(0, n as int))
            );
            assert(out@ == limbs@.subrange(0, n as int));
            assert(
                Self::limbs_value_spec(out@)
                    == Self::limbs_value_spec(limbs@.subrange(0, n as int))
            );
            assert(Self::limbs_value_spec(out@) == Self::limbs_value_spec(limbs@));
        }
        out
    }

    /// Multiplies by one base limb (`2^32`) by prepending a zero low limb.
    fn shift_base_once_total(&self) -> (out: Self)
        ensures
            out.wf_spec(),
            out.model@ == Self::limbs_value_spec(self.limbs_le@) * Self::limb_base_spec(),
    {
        let n = Self::trimmed_len_exec(&self.limbs_le);
        assert(n <= self.limbs_le.len());
        if n == 0 {
            let out = Self::zero();
            proof {
                let ng: nat = n as nat;
                assert(ng == 0);
                assert(ng <= self.limbs_le@.len());
                assert(forall|j: int| ng <= j < self.limbs_le@.len() ==> self.limbs_le@[j] == 0u32);
                Self::lemma_limbs_value_trim_suffix_zeros(self.limbs_le@, ng);
                assert(self.limbs_le@.subrange(0, n as int) == Seq::<u32>::empty());
                assert(Self::limbs_value_spec(Seq::<u32>::empty()) == 0);
                assert(Self::limbs_value_spec(self.limbs_le@) == 0);
                assert(out.model@ == 0);
                assert(out.model@ == Self::limbs_value_spec(self.limbs_le@) * Self::limb_base_spec());
            }
            out
        } else {
            let mut out_limbs: Vec<u32> = Vec::new();
            out_limbs.push(0u32);
            let mut i: usize = 0;
            while i < n
                invariant
                    i <= n,
                    n <= self.limbs_le.len(),
                    out_limbs@ == Seq::<u32>::empty().push(0u32) + self.limbs_le@.subrange(0, i as int),
                decreases n - i,
            {
                assert(i < self.limbs_le.len());
                out_limbs.push(self.limbs_le[i]);
                i = i + 1;
            }
            proof {
                assert(i == n);
                let ghost zero_prefix = Seq::<u32>::empty().push(0u32);
                let ghost trimmed = self.limbs_le@.subrange(0, n as int);
                assert(out_limbs@ == zero_prefix + trimmed);
                assert(zero_prefix.len() == 1);
                assert(Self::limbs_value_spec(zero_prefix) == 0);
                Self::lemma_limbs_value_append(zero_prefix, trimmed);
                assert(
                    Self::limbs_value_spec(out_limbs@)
                        == Self::limbs_value_spec(zero_prefix)
                            + Self::pow_base_spec(zero_prefix.len()) * Self::limbs_value_spec(trimmed)
                );
                assert(Self::pow_base_spec(zero_prefix.len()) == Self::pow_base_spec(1));
                Self::lemma_pow_base_succ(0);
                assert(Self::pow_base_spec(0) == 1);
                assert(Self::pow_base_spec(1) == Self::limb_base_spec() * Self::pow_base_spec(0));
                assert(Self::pow_base_spec(1) == Self::limb_base_spec());
                assert(
                    Self::limbs_value_spec(out_limbs@)
                        == Self::limb_base_spec() * Self::limbs_value_spec(trimmed)
                );
                let ng: nat = n as nat;
                assert(ng <= self.limbs_le@.len());
                assert(forall|j: int| ng <= j < self.limbs_le@.len() ==> self.limbs_le@[j] == 0u32);
                Self::lemma_limbs_value_trim_suffix_zeros(self.limbs_le@, ng);
                assert(Self::limbs_value_spec(self.limbs_le@) == Self::limbs_value_spec(trimmed));
                assert(
                    Self::limbs_value_spec(out_limbs@)
                        == Self::limb_base_spec() * Self::limbs_value_spec(self.limbs_le@)
                );
                let ghost self_val = Self::limbs_value_spec(self.limbs_le@);
                assert(
                    Self::limb_base_spec() * self_val
                        == self_val * Self::limb_base_spec()
                ) by (nonlinear_arith);

                assert(out_limbs@.len() == n + 1);
                assert(self.limbs_le@[(n - 1) as int] != 0u32);
                assert(out_limbs@[(out_limbs@.len() - 1) as int] == self.limbs_le@[(n - 1) as int]);
                assert(out_limbs@[(out_limbs@.len() - 1) as int] != 0u32);
                assert(Self::canonical_limbs_spec(out_limbs@));
            }
            let ghost model = Self::limbs_value_spec(out_limbs@);
            let out = Self::from_parts(out_limbs, Ghost(model));
            proof {
                assert(out.model@ == Self::limbs_value_spec(out.limbs_le@));
                let ghost self_val = Self::limbs_value_spec(self.limbs_le@);
                assert(Self::limb_base_spec() * self_val == self_val * Self::limb_base_spec()) by (nonlinear_arith);
                assert(out.model@ == Self::limb_base_spec() * self_val);
                assert(out.model@ == Self::limbs_value_spec(self.limbs_le@) * Self::limb_base_spec());
            }
            out
        }
    }

    /// Multiplies by one `u32` limb via repeated semantic addition.
    fn mul_by_u32_total(&self, rhs_limb: u32) -> (out: Self)
        ensures
            out.wf_spec(),
            out.model@ == Self::limbs_value_spec(self.limbs_le@) * rhs_limb as nat,
    {
        let mut acc = Self::zero();
        let mut remaining = rhs_limb;
        while remaining > 0
            invariant
                acc.wf_spec(),
                acc.model@ + Self::limbs_value_spec(self.limbs_le@) * (remaining as nat)
                    == Self::limbs_value_spec(self.limbs_le@) * rhs_limb as nat,
            decreases remaining,
        {
            let prev_remaining = remaining;
            let next = acc.add_limbwise_small_total(self);
            remaining = prev_remaining - 1;
            proof {
                let ghost self_val = Self::limbs_value_spec(self.limbs_le@);
                assert(prev_remaining > 0);
                assert(prev_remaining as nat == remaining as nat + 1);
                assert(Self::limbs_value_spec(acc.limbs_le@) == acc.model@);
                assert(Self::limbs_value_spec(next.limbs_le@) == next.model@);
                assert(next.model@ == Self::limbs_value_spec(acc.limbs_le@) + Self::limbs_value_spec(self.limbs_le@));
                assert(next.model@ == acc.model@ + self_val);
                assert(
                    self_val * (prev_remaining as nat)
                        == self_val * ((remaining as nat) + 1)
                );
                assert(
                    self_val * ((remaining as nat) + 1)
                        == self_val * (remaining as nat) + self_val
                ) by (nonlinear_arith);
                assert(
                    next.model@ + self_val * (remaining as nat)
                        == (acc.model@ + self_val) + self_val * (remaining as nat)
                );
                assert(
                    (acc.model@ + self_val) + self_val * (remaining as nat)
                        == acc.model@ + (self_val * (remaining as nat) + self_val)
                ) by (nonlinear_arith);
                assert(
                    acc.model@ + (self_val * (remaining as nat) + self_val)
                        == acc.model@ + self_val * (prev_remaining as nat)
                );
                assert(
                    acc.model@ + self_val * (prev_remaining as nat)
                        == self_val * rhs_limb as nat
                );
                assert(next.model@ + self_val * (remaining as nat) == self_val * rhs_limb as nat);
            }
            acc = next;
        }
        proof {
            let ghost self_val = Self::limbs_value_spec(self.limbs_le@);
            assert(!(remaining > 0));
            assert(remaining == 0);
            assert(remaining as nat == 0);
            assert(acc.model@ + self_val * (remaining as nat) == self_val * rhs_limb as nat);
            assert(acc.model@ == self_val * rhs_limb as nat);
        }
        acc
    }
    /// Total limb-wise multiplication helper used by scalar witness plumbing.
    ///
    /// Computes exact multiplication in little-endian limb space by combining:
    /// - per-limb scalar multiplication (`mul_by_u32_total`)
    /// - base shifting (`shift_base_once_total`)
    /// - semantic accumulation (`add_limbwise_small_total`)
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
            decreases blen - i,
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

    /// Total small-limb division helper used by scalar witness plumbing.
    ///
    /// Computes the floor quotient of `self / rhs` using monotone
    /// multiplication-by-addition accumulation. Returns `0` when `rhs == 0`.
    pub fn div_limbwise_small_total(&self, rhs: &Self) -> (out: Self)
        requires
            self.wf_spec(),
            rhs.wf_spec(),
        ensures
            out.wf_spec(),
            Self::limbs_value_spec(rhs.limbs_le@) == 0 ==> out.model@ == 0,
            Self::limbs_value_spec(rhs.limbs_le@) > 0
                ==> out.model@ * Self::limbs_value_spec(rhs.limbs_le@)
                    <= Self::limbs_value_spec(self.limbs_le@),
            Self::limbs_value_spec(rhs.limbs_le@) > 0
                ==> Self::limbs_value_spec(self.limbs_le@)
                    < (out.model@ + 1) * Self::limbs_value_spec(rhs.limbs_le@),
            Self::limbs_value_spec(rhs.limbs_le@) > 0
                ==> out.model@
                    == Self::limbs_value_spec(self.limbs_le@)
                        / Self::limbs_value_spec(rhs.limbs_le@),
    {
        let ghost self_val = Self::limbs_value_spec(self.limbs_le@);
        let ghost rhs_val = Self::limbs_value_spec(rhs.limbs_le@);
        if rhs.is_zero() {
            let out = Self::zero();
            proof {
                assert(rhs.model@ == rhs_val);
                assert(rhs.model@ == 0);
                assert(rhs_val == 0);
                assert(out.model@ == 0);
            }
            out
        } else {
            let one = Self::from_u32(1);
            let mut q = Self::zero();
            let mut accum = Self::zero();
            let mut next_accum = accum.add_limbwise_small_total(rhs);
            let mut cmp = next_accum.cmp_limbwise_small_total(self);
            proof {
                assert(rhs.model@ == rhs_val);
                assert(rhs.model@ != 0);
                assert(rhs_val > 0);
                assert(self.model@ == self_val);
                assert(q.model@ == 0);
                assert(accum.model@ == 0);
                assert(one.model@ == 1);
                assert(accum.model@ == q.model@ * rhs_val);
                assert(next_accum.model@ == accum.model@ + rhs_val);
                assert(cmp == -1 || cmp == 0 || cmp == 1);
                assert(accum.model@ <= self_val);
                assert(q.model@ <= self_val);
                if cmp == -1 {
                    assert(Self::limbs_value_spec(next_accum.limbs_le@) < Self::limbs_value_spec(self.limbs_le@));
                    assert(next_accum.model@ < self_val);
                    assert(next_accum.model@ <= self_val);
                }
                if cmp == 0 {
                    assert(Self::limbs_value_spec(next_accum.limbs_le@) == Self::limbs_value_spec(self.limbs_le@));
                    assert(next_accum.model@ == self_val);
                    assert(next_accum.model@ <= self_val);
                }
                if cmp == 1 {
                    assert(Self::limbs_value_spec(next_accum.limbs_le@) > Self::limbs_value_spec(self.limbs_le@));
                    assert(self_val < next_accum.model@);
                }
            }

            while cmp <= 0
                invariant
                    q.wf_spec(),
                    accum.wf_spec(),
                    next_accum.wf_spec(),
                    self.wf_spec(),
                    rhs.wf_spec(),
                    one.wf_spec(),
                    one.model@ == 1,
                    rhs_val == rhs.model@,
                    rhs_val > 0,
                    self_val == self.model@,
                    cmp == -1 || cmp == 0 || cmp == 1,
                    cmp <= 0 ==> next_accum.model@ <= self_val,
                    cmp == 1 ==> self_val < next_accum.model@,
                    accum.model@ == q.model@ * rhs_val,
                    next_accum.model@ == accum.model@ + rhs_val,
                    accum.model@ <= self_val,
                    q.model@ <= self_val,
                decreases self_val - q.model@,
            {
                let new_q = q.add_limbwise_small_total(&one);
                let new_accum = next_accum;
                let new_next_accum = new_accum.add_limbwise_small_total(rhs);
                proof {
                    assert(cmp != 1);
                    assert(next_accum.model@ <= self_val);
                    assert(Self::limbs_value_spec(q.limbs_le@) == q.model@);
                    assert(Self::limbs_value_spec(one.limbs_le@) == one.model@);
                    assert(new_q.model@ == q.model@ + one.model@);
                    assert(new_q.model@ == q.model@ + 1);
                    assert(new_accum.model@ == next_accum.model@);
                    assert(new_accum.model@ == accum.model@ + rhs_val);
                    assert(accum.model@ == q.model@ * rhs_val);
                    assert(new_accum.model@ == q.model@ * rhs_val + rhs_val);
                    assert(q.model@ * rhs_val + rhs_val == (q.model@ + 1) * rhs_val)
                        by (nonlinear_arith);
                    assert(new_accum.model@ == (q.model@ + 1) * rhs_val);
                    assert(new_accum.model@ == new_q.model@ * rhs_val);
                    assert(new_accum.model@ <= self_val);
                    assert(rhs_val >= 1);
                    if rhs_val == 1 {
                        assert((q.model@ + 1) * rhs_val == q.model@ + 1);
                    } else {
                        assert(rhs_val > 1);
                        assert(rhs_val == 1 + (rhs_val - 1));
                        assert(
                            (q.model@ + 1) * rhs_val
                                == (q.model@ + 1) * 1 + (q.model@ + 1) * (rhs_val - 1)
                        ) by (nonlinear_arith);
                        assert((q.model@ + 1) * (rhs_val - 1) >= 0);
                        assert((q.model@ + 1) * rhs_val >= q.model@ + 1);
                    }
                    assert((q.model@ + 1) * rhs_val >= q.model@ + 1);
                    assert(q.model@ + 1 <= self_val);
                    assert(new_q.model@ <= self_val);
                    assert(self_val - new_q.model@ < self_val - q.model@);
                    assert(new_next_accum.model@ == new_accum.model@ + rhs_val);
                }
                q = new_q;
                accum = new_accum;
                next_accum = new_next_accum;
                cmp = next_accum.cmp_limbwise_small_total(self);
                proof {
                    assert(cmp == -1 || cmp == 0 || cmp == 1);
                    if cmp == -1 {
                        assert(Self::limbs_value_spec(next_accum.limbs_le@) < Self::limbs_value_spec(self.limbs_le@));
                        assert(next_accum.model@ < self_val);
                        assert(next_accum.model@ <= self_val);
                    }
                    if cmp == 0 {
                        assert(Self::limbs_value_spec(next_accum.limbs_le@) == Self::limbs_value_spec(self.limbs_le@));
                        assert(next_accum.model@ == self_val);
                        assert(next_accum.model@ <= self_val);
                    }
                    if cmp == 1 {
                        assert(Self::limbs_value_spec(next_accum.limbs_le@) > Self::limbs_value_spec(self.limbs_le@));
                        assert(self_val < next_accum.model@);
                    }
                }
            }
            proof {
                assert(!(cmp <= 0));
                assert(cmp == -1 || cmp == 0 || cmp == 1);
                assert(cmp == 1);
                assert(self_val < next_accum.model@);
                assert(accum.model@ == q.model@ * rhs_val);
                assert(next_accum.model@ == accum.model@ + rhs_val);
                assert(q.model@ * rhs_val <= self_val);
                assert(next_accum.model@ == q.model@ * rhs_val + rhs_val);
                assert(q.model@ * rhs_val + rhs_val == (q.model@ + 1) * rhs_val)
                    by (nonlinear_arith);
                assert(next_accum.model@ == (q.model@ + 1) * rhs_val);
                assert(self_val < (q.model@ + 1) * rhs_val);

                assert(q.model@ * rhs_val <= self_val);
                let r = (self_val - q.model@ * rhs_val) as nat;
                assert(r == self_val - q.model@ * rhs_val);
                assert(q.model@ * rhs_val + r == self_val);
                assert(self_val == q.model@ * rhs_val + r);
                assert(q.model@ * rhs_val + r < q.model@ * rhs_val + rhs_val);
                assert(r < rhs_val);

                let xi = self_val as int;
                let di = rhs_val as int;
                lemma_fundamental_div_mod(xi, di);
                lemma_mod_pos_bound(xi, di);
                assert((self_val / rhs_val) as int == xi / di);
                assert((self_val % rhs_val) as int == xi % di);
                let xi = self_val as int;
                let di = rhs_val as int;
                lemma_fundamental_div_mod(xi, di);
                lemma_mod_pos_bound(xi, di);
                assert((self_val / rhs_val) as int == xi / di);
                assert((self_val % rhs_val) as int == xi % di);
                assert(self_val == (self_val / rhs_val) * rhs_val + self_val % rhs_val);
                assert(self_val % rhs_val < rhs_val);
                Self::lemma_div_rem_unique_nat(
                    self_val,
                    rhs_val,
                    q.model@,
                    r,
                    self_val / rhs_val,
                    self_val % rhs_val,
                );
                assert(q.model@ == self_val / rhs_val);
            }
            q
        }
    }

    /// Total small-limb remainder helper used by scalar witness plumbing.
    ///
    /// Computes `self % rhs` with total semantics, returning `0` when `rhs == 0`.
    pub fn rem_limbwise_small_total(&self, rhs: &Self) -> (out: Self)
        requires
            self.wf_spec(),
            rhs.wf_spec(),
        ensures
            out.wf_spec(),
            Self::limbs_value_spec(rhs.limbs_le@) == 0 ==> out.model@ == 0,
            Self::limbs_value_spec(rhs.limbs_le@) > 0 ==> out.model@ < Self::limbs_value_spec(rhs.limbs_le@),
            Self::limbs_value_spec(rhs.limbs_le@) > 0
                ==> out.model@
                    == Self::limbs_value_spec(self.limbs_le@)
                        % Self::limbs_value_spec(rhs.limbs_le@),
    {
        let pair = self.div_rem_limbwise_small_total(rhs);
        let out = pair.1;
        proof {
            let ghost rhs_val = Self::limbs_value_spec(rhs.limbs_le@);
            assert(out.wf_spec());
            if rhs_val == 0 {
                assert(pair.1.model@ == 0);
                assert(out.model@ == 0);
            }
            if rhs_val > 0 {
                assert(pair.1.model@ < rhs_val);
                assert(out.model@ < rhs_val);
                assert(pair.1.model@ == Self::limbs_value_spec(self.limbs_le@) % rhs_val);
                assert(out.model@ == Self::limbs_value_spec(self.limbs_le@) % rhs_val);
            }
        }
        out
    }

    /// Total small-limb quotient/remainder helper used by scalar witness plumbing.
    ///
    /// Returns `(q, r)` where `q = floor(self / rhs)` and `r = self % rhs`.
    /// Uses total semantics `(0, 0)` when `rhs == 0`.
    pub fn div_rem_limbwise_small_total(&self, rhs: &Self) -> (out: (Self, Self))
        requires
            self.wf_spec(),
            rhs.wf_spec(),
        ensures
            out.0.wf_spec(),
            out.1.wf_spec(),
            Self::limbs_value_spec(rhs.limbs_le@) == 0 ==> out.0.model@ == 0 && out.1.model@ == 0,
            Self::limbs_value_spec(rhs.limbs_le@) > 0
                ==> Self::limbs_value_spec(self.limbs_le@)
                    == out.0.model@ * Self::limbs_value_spec(rhs.limbs_le@) + out.1.model@,
            Self::limbs_value_spec(rhs.limbs_le@) > 0
                ==> out.1.model@ < Self::limbs_value_spec(rhs.limbs_le@),
            Self::limbs_value_spec(rhs.limbs_le@) > 0
                ==> out.0.model@
                    == Self::limbs_value_spec(self.limbs_le@)
                        / Self::limbs_value_spec(rhs.limbs_le@),
            Self::limbs_value_spec(rhs.limbs_le@) > 0
                ==> out.1.model@
                    == Self::limbs_value_spec(self.limbs_le@)
                        % Self::limbs_value_spec(rhs.limbs_le@),
    {
        let ghost self_val = Self::limbs_value_spec(self.limbs_le@);
        let ghost rhs_val = Self::limbs_value_spec(rhs.limbs_le@);
        if rhs.is_zero() {
            let q = Self::zero();
            let r = Self::zero();
            proof {
                assert(rhs.model@ == rhs_val);
                assert(rhs.model@ == 0);
                assert(rhs_val == 0);
                assert(q.model@ == 0);
                assert(r.model@ == 0);
            }
            (q, r)
        } else {
            let q = self.div_limbwise_small_total(rhs);
            let prod = q.mul_limbwise_small_total(rhs);
            let r = self.sub_limbwise_small_total(&prod);
            proof {
                assert(rhs.model@ == rhs_val);
                assert(rhs.model@ > 0);
                assert(rhs_val > 0);
                assert(self.model@ == self_val);
                assert(q.model@ * rhs_val <= self_val);
                assert(self_val < (q.model@ + 1) * rhs_val);
                assert(prod.model@ == q.model@ * rhs_val);
                assert(prod.model@ <= self_val);

                assert(Self::limbs_value_spec(self.limbs_le@) == self_val);
                assert(Self::limbs_value_spec(prod.limbs_le@) == prod.model@);

                if self_val <= prod.model@ {
                    assert(self_val == prod.model@);
                    assert(Self::limbs_value_spec(self.limbs_le@) <= Self::limbs_value_spec(prod.limbs_le@));
                    assert(r.model@ == 0);
                    assert(self_val == q.model@ * rhs_val);
                    assert(self_val == q.model@ * rhs_val + r.model@);
                    assert(r.model@ < rhs_val);
                } else {
                    assert(prod.model@ < self_val);
                    assert(Self::limbs_value_spec(prod.limbs_le@) < Self::limbs_value_spec(self.limbs_le@));
                    assert(
                        r.model@
                            == Self::limbs_value_spec(self.limbs_le@)
                                - Self::limbs_value_spec(prod.limbs_le@)
                    );
                    assert(r.model@ == self_val - prod.model@);
                    assert((self_val - prod.model@) + prod.model@ == self_val);
                    assert(r.model@ + prod.model@ == self_val);
                    assert(r.model@ + q.model@ * rhs_val == self_val);
                    assert(self_val == q.model@ * rhs_val + r.model@);
                    assert((q.model@ + 1) * rhs_val == q.model@ * rhs_val + rhs_val)
                        by (nonlinear_arith);
                    assert(self_val < q.model@ * rhs_val + rhs_val);
                    assert(q.model@ * rhs_val + r.model@ < q.model@ * rhs_val + rhs_val);
                    assert(r.model@ < rhs_val);
                }

                if self_val <= prod.model@ {
                    assert(self_val == q.model@ * rhs_val + r.model@);
                } else {
                    assert(self_val == q.model@ * rhs_val + r.model@);
                }

                let xi = self_val as int;
                let di = rhs_val as int;
                let qi = q.model@ as int;
                let ri = r.model@ as int;
                assert(di != 0);
                assert(0 <= ri < di);
                assert(xi == qi * di + ri);
                lemma_fundamental_div_mod_converse(xi, di, qi, ri);
                assert(qi == xi / di);
                assert(ri == xi % di);
                assert((self_val / rhs_val) as int == xi / di);
                assert((self_val % rhs_val) as int == xi % di);
                assert(q.model@ as int == (self_val / rhs_val) as int);
                assert(r.model@ as int == (self_val % rhs_val) as int);
                assert(q.model@ == self_val / rhs_val);
                assert(r.model@ == self_val % rhs_val);
            }
            (q, r)
        }
    }

    /// Total small-limb compare helper used by scalar witness plumbing.
    ///
    /// Returns the exact sign of `(self - rhs)` as `-1/0/1` using full
    /// multi-limb comparison with trailing-zero normalization.
    pub fn cmp_limbwise_small_total(&self, rhs: &Self) -> (out: i8)
        ensures
            out == -1 || out == 0 || out == 1,
            out == -1 ==> Self::limbs_value_spec(self.limbs_le@) < Self::limbs_value_spec(rhs.limbs_le@),
            out == 0 ==> Self::limbs_value_spec(self.limbs_le@) == Self::limbs_value_spec(rhs.limbs_le@),
            out == 1 ==> Self::limbs_value_spec(self.limbs_le@) > Self::limbs_value_spec(rhs.limbs_le@),
            self.limbs_le@ == rhs.limbs_le@ ==> out == 0,
            self.wf_spec() && rhs.wf_spec() && out == 0 ==> self.limbs_le@ == rhs.limbs_le@,
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
                decreases i,
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
                assert(self.wf_spec() && rhs.wf_spec() ==> self.limbs_le@ == rhs.limbs_le@) by {
                    if self.wf_spec() && rhs.wf_spec() {
                        assert(Self::canonical_limbs_spec(self.limbs_le@));
                        assert(Self::canonical_limbs_spec(rhs.limbs_le@));

                        if alen_nat < self.limbs_le@.len() {
                            assert(self.limbs_le@.len() > 0);
                            let last = self.limbs_le@.len() - 1;
                            assert(alen_nat <= last);
                            assert(last < self.limbs_le@.len());
                            assert(self.limbs_le@[last as int] == 0u32);
                            assert(self.limbs_le@[last as int] != 0u32);
                        }
                        assert(alen_nat == self.limbs_le@.len());

                        if blen_nat < rhs.limbs_le@.len() {
                            assert(rhs.limbs_le@.len() > 0);
                            let last = rhs.limbs_le@.len() - 1;
                            assert(blen_nat <= last);
                            assert(last < rhs.limbs_le@.len());
                            assert(rhs.limbs_le@[last as int] == 0u32);
                            assert(rhs.limbs_le@[last as int] != 0u32);
                        }
                        assert(blen_nat == rhs.limbs_le@.len());
                        assert(self.limbs_le@.len() == rhs.limbs_le@.len());
                        assert(self.limbs_le@.subrange(0, alen as int) == self.limbs_le@);
                        assert(rhs.limbs_le@.subrange(0, blen as int) == rhs.limbs_le@);
                        assert(self.limbs_le@ == rhs.limbs_le@);
                    }
                };
            }
            0i8
        }
    }


    /// Total small-limb subtraction helper used by scalar witness plumbing.
    ///
    /// Computes the exact nonnegative difference when `self >= rhs` using full
    /// multi-limb borrow propagation (with trailing-zero normalization).
    /// Returns `0` when `self < rhs`.
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
                decreases alen - i,
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
            decreases n - i,
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
}

impl<'a, 'b> vstd::std_specs::ops::AddSpecImpl<&'b RuntimeBigNatWitness> for &'a RuntimeBigNatWitness {
    open spec fn obeys_add_spec() -> bool {
        false
    }

    open spec fn add_req(self, rhs: &'b RuntimeBigNatWitness) -> bool {
        true
    }

    open spec fn add_spec(self, rhs: &'b RuntimeBigNatWitness) -> Self::Output {
        arbitrary()
    }
}

impl<'a, 'b> vstd::std_specs::ops::SubSpecImpl<&'b RuntimeBigNatWitness> for &'a RuntimeBigNatWitness {
    open spec fn obeys_sub_spec() -> bool {
        false
    }

    open spec fn sub_req(self, rhs: &'b RuntimeBigNatWitness) -> bool {
        true
    }

    open spec fn sub_spec(self, rhs: &'b RuntimeBigNatWitness) -> Self::Output {
        arbitrary()
    }
}

impl<'a, 'b> vstd::std_specs::ops::MulSpecImpl<&'b RuntimeBigNatWitness> for &'a RuntimeBigNatWitness {
    open spec fn obeys_mul_spec() -> bool {
        false
    }

    open spec fn mul_req(self, rhs: &'b RuntimeBigNatWitness) -> bool {
        true
    }

    open spec fn mul_spec(self, rhs: &'b RuntimeBigNatWitness) -> Self::Output {
        arbitrary()
    }
}

impl<'a, 'b> vstd::std_specs::ops::DivSpecImpl<&'b RuntimeBigNatWitness> for &'a RuntimeBigNatWitness {
    open spec fn obeys_div_spec() -> bool {
        false
    }

    open spec fn div_req(self, rhs: &'b RuntimeBigNatWitness) -> bool {
        true
    }

    open spec fn div_spec(self, rhs: &'b RuntimeBigNatWitness) -> Self::Output {
        arbitrary()
    }
}

impl<'a, 'b> vstd::std_specs::ops::RemSpecImpl<&'b RuntimeBigNatWitness> for &'a RuntimeBigNatWitness {
    open spec fn obeys_rem_spec() -> bool {
        false
    }

    open spec fn rem_req(self, rhs: &'b RuntimeBigNatWitness) -> bool {
        true
    }

    open spec fn rem_spec(self, rhs: &'b RuntimeBigNatWitness) -> Self::Output {
        arbitrary()
    }
}

impl<'a, 'b> core::ops::Add<&'b RuntimeBigNatWitness> for &'a RuntimeBigNatWitness {
    type Output = RuntimeBigNatWitness;

    fn add(self, rhs: &'b RuntimeBigNatWitness) -> (out: Self::Output) {
        self.add_limbwise_small_total(rhs)
    }
}

impl<'a, 'b> core::ops::Sub<&'b RuntimeBigNatWitness> for &'a RuntimeBigNatWitness {
    type Output = RuntimeBigNatWitness;

    fn sub(self, rhs: &'b RuntimeBigNatWitness) -> (out: Self::Output) {
        self.sub_limbwise_small_total(rhs)
    }
}

impl<'a, 'b> core::ops::Mul<&'b RuntimeBigNatWitness> for &'a RuntimeBigNatWitness {
    type Output = RuntimeBigNatWitness;

    fn mul(self, rhs: &'b RuntimeBigNatWitness) -> (out: Self::Output) {
        self.mul_limbwise_small_total(rhs)
    }
}

impl<'a, 'b> core::ops::Div<&'b RuntimeBigNatWitness> for &'a RuntimeBigNatWitness {
    type Output = RuntimeBigNatWitness;

    fn div(self, rhs: &'b RuntimeBigNatWitness) -> (out: Self::Output) {
        let lhs_wf = self.copy_small_total();
        let rhs_wf = rhs.copy_small_total();
        lhs_wf.div_limbwise_small_total(&rhs_wf)
    }
}

impl<'a, 'b> core::ops::Rem<&'b RuntimeBigNatWitness> for &'a RuntimeBigNatWitness {
    type Output = RuntimeBigNatWitness;

    fn rem(self, rhs: &'b RuntimeBigNatWitness) -> (out: Self::Output) {
        let lhs_wf = self.copy_small_total();
        let rhs_wf = rhs.copy_small_total();
        lhs_wf.rem_limbwise_small_total(&rhs_wf)
    }
}
}
