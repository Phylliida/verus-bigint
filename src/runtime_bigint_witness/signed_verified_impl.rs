#![cfg(verus_keep_ghost)]

use super::{RuntimeBigIntWitness, RuntimeBigNatWitness};
use vstd::prelude::*;
use vstd::arithmetic::div_mod::{
    lemma_div_is_ordered,
    lemma_fundamental_div_mod_converse,
    lemma_small_mod,
};
use vstd::arithmetic::mul::{
    lemma_mul_equality_converse,
    lemma_mul_inequality,
    lemma_mul_is_commutative,
    lemma_mul_strict_inequality,
};

verus! {
impl RuntimeBigIntWitness {
    pub open spec fn model_from_sign_and_magnitude_spec(is_negative: bool, magnitude_model: nat) -> int {
        if is_negative {
            -(magnitude_model as int)
        } else {
            magnitude_model as int
        }
    }

    pub open spec fn canonical_sign_spec(is_negative: bool, magnitude_model: nat) -> bool {
        !is_negative || magnitude_model > 0
    }

    pub open spec fn abs_model_spec(model: int) -> nat {
        if model < 0 {
            (-model) as nat
        } else {
            model as nat
        }
    }

    pub open spec fn trunc_div_spec(a: int, b: int) -> int
        recommends
            b != 0,
    {
        let abs_a = Self::abs_model_spec(a);
        let abs_b = Self::abs_model_spec(b);
        let q_abs = abs_a / abs_b;
        if (a < 0) != (b < 0) {
            -(q_abs as int)
        } else {
            q_abs as int
        }
    }

    pub open spec fn trunc_rem_spec(a: int, b: int) -> int
        recommends
            b != 0,
    {
        let abs_a = Self::abs_model_spec(a);
        let abs_b = Self::abs_model_spec(b);
        let r_abs = abs_a % abs_b;
        if a < 0 {
            -(r_abs as int)
        } else {
            r_abs as int
        }
    }

    pub open spec fn wf_spec(&self) -> bool {
        &&& self.magnitude.wf_spec()
        &&& Self::canonical_sign_spec(self.is_negative, self.magnitude.model@)
        &&& self.model@ == Self::model_from_sign_and_magnitude_spec(self.is_negative, self.magnitude.model@)
    }

    pub proof fn lemma_abs_model_nonnegative(model: int)
        ensures
            0 <= Self::abs_model_spec(model),
    {
    }

    pub proof fn lemma_abs_model_from_sign_and_magnitude(is_negative: bool, magnitude_model: nat)
        ensures
            Self::abs_model_spec(
                Self::model_from_sign_and_magnitude_spec(is_negative, magnitude_model),
            ) == magnitude_model,
    {
        if is_negative {
            assert(
                Self::model_from_sign_and_magnitude_spec(is_negative, magnitude_model)
                    == -(magnitude_model as int)
            );
            assert(
                Self::abs_model_spec(
                    Self::model_from_sign_and_magnitude_spec(is_negative, magnitude_model),
                ) == (-(-(magnitude_model as int))) as nat
            );
            assert((-(-(magnitude_model as int))) as nat == magnitude_model);
        } else {
            assert(
                Self::model_from_sign_and_magnitude_spec(is_negative, magnitude_model)
                    == magnitude_model as int
            );
            assert(
                Self::abs_model_spec(
                    Self::model_from_sign_and_magnitude_spec(is_negative, magnitude_model),
                ) == (magnitude_model as int) as nat
            );
            assert((magnitude_model as int) as nat == magnitude_model);
        }
    }

    pub proof fn lemma_sign_model_bridge(&self)
        requires
            self.wf_spec(),
        ensures
            Self::abs_model_spec(self.model@) == self.magnitude.model@,
            (self.model@ < 0) <==> self.is_negative,
            (self.model@ == 0) <==> self.magnitude.model@ == 0,
            self.model@ > 0 <==> (!self.is_negative && self.magnitude.model@ > 0),
    {
        Self::lemma_abs_model_from_sign_and_magnitude(self.is_negative, self.magnitude.model@);
        assert(
            Self::abs_model_spec(
                Self::model_from_sign_and_magnitude_spec(self.is_negative, self.magnitude.model@),
            ) == self.magnitude.model@
        );
        assert(self.model@ == Self::model_from_sign_and_magnitude_spec(self.is_negative, self.magnitude.model@));
        assert(Self::abs_model_spec(self.model@) == self.magnitude.model@);

        if self.is_negative {
            assert(self.magnitude.model@ > 0);
            assert(self.model@ == -(self.magnitude.model@ as int));
            assert(self.model@ < 0);
        } else {
            assert(self.model@ == self.magnitude.model@ as int);
            assert(self.model@ >= 0);
        }

        if self.model@ < 0 {
            assert(self.is_negative);
        }
        if self.model@ == 0 {
            assert(self.model@ == Self::abs_model_spec(self.model@) as int);
            assert(Self::abs_model_spec(self.model@) == self.magnitude.model@);
            assert(self.magnitude.model@ == 0);
        }
        if self.magnitude.model@ == 0 {
            assert(!self.is_negative);
            assert(self.model@ == self.magnitude.model@ as int);
            assert(self.model@ == 0);
        }
        if self.model@ > 0 {
            assert(!self.is_negative);
            assert(self.model@ == self.magnitude.model@ as int);
            assert(self.magnitude.model@ > 0);
        }
        if !self.is_negative && self.magnitude.model@ > 0 {
            assert(self.model@ == self.magnitude.model@ as int);
            assert(self.model@ > 0);
        }
    }

    fn from_parts(is_negative: bool, magnitude: RuntimeBigNatWitness, Ghost(model): Ghost<int>) -> (out: Self)
        requires
            magnitude.wf_spec(),
            Self::canonical_sign_spec(is_negative, magnitude.model@),
            model == Self::model_from_sign_and_magnitude_spec(is_negative, magnitude.model@),
        ensures
            out.is_negative == is_negative,
            out.magnitude.wf_spec(),
            out.magnitude.model@ == magnitude.model@,
            out.model@ == model,
            out.wf_spec(),
    {
        let out = RuntimeBigIntWitness { is_negative, magnitude, model: Ghost(model) };
        proof {
            assert(out.is_negative == is_negative);
            assert(out.magnitude.model@ == magnitude.model@);
            assert(out.model@ == model);
            assert(out.magnitude.wf_spec());
            assert(Self::canonical_sign_spec(out.is_negative, out.magnitude.model@));
            assert(
                out.model@
                    == Self::model_from_sign_and_magnitude_spec(
                        out.is_negative,
                        out.magnitude.model@,
                    )
            );
            assert(out.wf_spec());
        }
        out
    }

    pub fn from_sign_and_magnitude(is_negative: bool, magnitude: RuntimeBigNatWitness) -> (out: Self)
        requires
            magnitude.wf_spec(),
        ensures
            out.wf_spec(),
            out.magnitude.model@ == magnitude.model@,
            out.is_negative == (is_negative && magnitude.model@ > 0),
            out.model@
                == Self::model_from_sign_and_magnitude_spec(
                    out.is_negative,
                    out.magnitude.model@,
                ),
            magnitude.model@ == 0 ==> !out.is_negative,
    {
        let ghost magnitude_model = magnitude.model@;
        let magnitude_is_zero = magnitude.is_zero();
        let normalized_negative = if magnitude_is_zero {
            false
        } else {
            is_negative
        };
        let ghost model = Self::model_from_sign_and_magnitude_spec(normalized_negative, magnitude_model);
        let out = Self::from_parts(normalized_negative, magnitude, Ghost(model));
        proof {
            assert(out.magnitude.model@ == magnitude_model);
            assert(out.is_negative == normalized_negative);
            if magnitude_is_zero {
                assert(magnitude_model == 0);
                assert(out.is_negative == false);
                assert(!out.is_negative);
            } else {
                assert(magnitude_model != 0);
                assert(magnitude_model > 0);
                assert(normalized_negative == is_negative);
            }
            assert(out.is_negative == (is_negative && magnitude_model > 0));
            assert(
                out.model@
                    == Self::model_from_sign_and_magnitude_spec(
                        out.is_negative,
                        out.magnitude.model@,
                    )
            );
        }
        out
    }

    pub fn zero() -> (out: Self)
        ensures
            out.wf_spec(),
            out.model@ == 0,
            !out.is_negative,
    {
        let magnitude = RuntimeBigNatWitness::zero();
        let out = Self::from_sign_and_magnitude(false, magnitude);
        proof {
            assert(out.magnitude.model@ == 0);
            assert(out.is_negative == false);
            assert(out.model@ == out.magnitude.model@ as int);
            assert(out.model@ == 0);
        }
        out
    }

    pub fn from_unsigned(magnitude: RuntimeBigNatWitness) -> (out: Self)
        requires
            magnitude.wf_spec(),
        ensures
            out.wf_spec(),
            !out.is_negative,
            out.magnitude.model@ == magnitude.model@,
            out.model@ == magnitude.model@ as int,
    {
        let out = Self::from_sign_and_magnitude(false, magnitude);
        proof {
            assert(!out.is_negative);
            assert(
                out.model@
                    == Self::model_from_sign_and_magnitude_spec(
                        out.is_negative,
                        out.magnitude.model@,
                    )
            );
            assert(out.model@ == out.magnitude.model@ as int);
        }
        out
    }

    pub fn from_u64(x: u64) -> (out: Self)
        ensures
            out.wf_spec(),
            out.model@ == x as int,
    {
        let magnitude = RuntimeBigNatWitness::from_u64(x);
        let out = Self::from_sign_and_magnitude(false, magnitude);
        proof {
            assert(!out.is_negative);
            assert(out.model@ == out.magnitude.model@ as int);
            assert(out.magnitude.model@ == x as nat);
            assert(out.model@ == x as int);
        }
        out
    }

    pub fn from_u32(x: u32) -> (out: Self)
        ensures
            out.wf_spec(),
            out.model@ == x as int,
    {
        let magnitude = RuntimeBigNatWitness::from_u32(x);
        let out = Self::from_sign_and_magnitude(false, magnitude);
        proof {
            assert(!out.is_negative);
            assert(out.model@ == out.magnitude.model@ as int);
            assert(out.magnitude.model@ == x as nat);
            assert(out.model@ == x as int);
        }
        out
    }

    fn magnitude_to_u64_checked(magnitude: &RuntimeBigNatWitness) -> (out: (bool, u64))
        requires
            magnitude.wf_spec(),
        ensures
            out.0 ==> magnitude.model@ == out.1 as nat,
            !out.0 ==> out.1 == 0u64,
    {
        let len = magnitude.limbs_le.len();
        if len == 0 {
            proof {
                assert(magnitude.model@ == RuntimeBigNatWitness::limbs_value_spec(magnitude.limbs_le@));
                assert(magnitude.model@ == 0);
            }
            (true, 0u64)
        } else if len == 1 {
            let lo = magnitude.limbs_le[0];
            proof {
                assert(magnitude.model@ == RuntimeBigNatWitness::limbs_value_spec(magnitude.limbs_le@));
                assert(magnitude.limbs_le@.len() == 1);
                assert(RuntimeBigNatWitness::limbs_value_spec(magnitude.limbs_le@) == magnitude.limbs_le@[0] as nat);
                assert(magnitude.model@ == lo as nat);
            }
            (true, lo as u64)
        } else if len == 2 {
            let lo = magnitude.limbs_le[0];
            let hi = magnitude.limbs_le[1];
            let out_u64 = lo as u64 + hi as u64 * 4_294_967_296u64;
            proof {
                assert(magnitude.model@ == RuntimeBigNatWitness::limbs_value_spec(magnitude.limbs_le@));
                assert(magnitude.limbs_le@.len() == 2);
                assert(magnitude.limbs_le@[0] == lo);
                assert(magnitude.limbs_le@[1] == hi);
                assert(magnitude.limbs_le@.subrange(1, magnitude.limbs_le@.len() as int).len() == 1);
                assert(magnitude.limbs_le@.subrange(1, magnitude.limbs_le@.len() as int)[0] == hi);
                assert(
                    RuntimeBigNatWitness::limbs_value_spec(
                        magnitude.limbs_le@.subrange(1, magnitude.limbs_le@.len() as int),
                    ) == hi as nat
                );
                assert(
                    RuntimeBigNatWitness::limbs_value_spec(magnitude.limbs_le@)
                        == lo as nat + RuntimeBigNatWitness::limb_base_spec() * hi as nat
                );
                assert(RuntimeBigNatWitness::limb_base_spec() == 4_294_967_296);
                assert(
                    out_u64 as nat
                        == lo as nat + 4_294_967_296nat * hi as nat
                );
                assert(magnitude.model@ == out_u64 as nat);
            }
            (true, out_u64)
        } else {
            (false, 0u64)
        }
    }

    pub fn try_to_u64(&self) -> (out: (bool, u64))
        requires
            self.wf_spec(),
        ensures
            out.0 ==> self.model@ == out.1 as int,
            !out.0 ==> out.1 == 0u64,
    {
        if self.is_negative {
            proof {
                assert(self.model@ < 0);
            }
            (false, 0u64)
        } else {
            let mag_out = Self::magnitude_to_u64_checked(&self.magnitude);
            if mag_out.0 {
                let v = mag_out.1;
                proof {
                    assert(self.model@ == self.magnitude.model@ as int);
                    assert(self.magnitude.model@ == v as nat);
                    assert(self.model@ == v as int);
                }
                (true, v)
            } else {
                proof {
                    assert(mag_out.1 == 0u64);
                }
                (false, 0u64)
            }
        }
    }

    pub fn try_to_i64(&self) -> (out: (bool, i64))
        requires
            self.wf_spec(),
        ensures
            out.0 ==> self.model@ == out.1 as int,
            !out.0 ==> out.1 == 0i64,
    {
        let mag_out = Self::magnitude_to_u64_checked(&self.magnitude);
        if !mag_out.0 {
            (false, 0i64)
        } else {
            let abs_u64 = mag_out.1;
            if self.is_negative {
                if abs_u64 > 9_223_372_036_854_775_808u64 {
                    (false, 0i64)
                } else if abs_u64 == 9_223_372_036_854_775_808u64 {
                    let v = -9_223_372_036_854_775_808i64;
                    proof {
                        assert(self.model@ == -(self.magnitude.model@ as int));
                        assert(self.magnitude.model@ == abs_u64 as nat);
                        assert(self.model@ == -(9_223_372_036_854_775_808int));
                        assert(v as int == -(9_223_372_036_854_775_808int));
                        assert(self.model@ == v as int);
                    }
                    (true, v)
                } else {
                    let v = -(abs_u64 as i64);
                    proof {
                        assert(abs_u64 < 9_223_372_036_854_775_808u64);
                        assert(self.model@ == -(self.magnitude.model@ as int));
                        assert(self.magnitude.model@ == abs_u64 as nat);
                        assert(v as int == -((abs_u64 as i64) as int));
                        assert((abs_u64 as i64) as int == abs_u64 as int);
                        assert(v as int == -(abs_u64 as int));
                        assert(self.model@ == v as int);
                    }
                    (true, v)
                }
            } else {
                if abs_u64 > 9_223_372_036_854_775_807u64 {
                    (false, 0i64)
                } else {
                    let v = abs_u64 as i64;
                    proof {
                        assert(self.model@ == self.magnitude.model@ as int);
                        assert(self.magnitude.model@ == abs_u64 as nat);
                        assert(v as int == abs_u64 as int);
                        assert(self.model@ == v as int);
                    }
                    (true, v)
                }
            }
        }
    }

    pub fn sign_char(&self) -> (out: char)
        requires
            self.wf_spec(),
        ensures
            (out == '-') <==> (self.model@ < 0),
            (out == '+') <==> (self.model@ >= 0),
    {
        let out = if self.is_negative { '-' } else { '+' };
        proof {
            if self.is_negative {
                assert(self.model@ < 0);
                assert(out == '-');
            } else {
                assert(self.model@ >= 0);
                assert(out == '+');
            }
            if out == '-' {
                assert(self.is_negative);
                assert(self.model@ < 0);
            }
            if self.model@ < 0 {
                assert(self.is_negative);
                assert(out == '-');
            }
            if out == '+' {
                assert(!self.is_negative);
                assert(self.model@ >= 0);
            }
            if self.model@ >= 0 {
                assert(!self.is_negative);
                assert(out == '+');
            }
        }
        out
    }

    pub fn parse_sign_char_and_u64(sign: char, magnitude: u64) -> (out: (bool, Self))
        ensures
            out.0 ==> (sign == '+' || sign == '-'),
            out.0 ==> out.1.model@ == (if sign == '-' { -(magnitude as int) } else { magnitude as int }),
            !out.0 ==> out.1.model@ == 0,
            out.1.wf_spec(),
    {
        if sign == '+' || sign == '-' {
            let mag = RuntimeBigNatWitness::from_u64(magnitude);
            let signed = Self::from_sign_and_magnitude(sign == '-', mag);
            proof {
                if sign == '-' {
                    assert(signed.model@ == -(signed.magnitude.model@ as int));
                    assert(signed.magnitude.model@ == magnitude as nat);
                    assert(signed.model@ == -(magnitude as int));
                } else {
                    assert(signed.model@ == signed.magnitude.model@ as int);
                    assert(signed.magnitude.model@ == magnitude as nat);
                    assert(signed.model@ == magnitude as int);
                }
            }
            (true, signed)
        } else {
            let z = Self::zero();
            (false, z)
        }
    }

    pub fn from_i64(x: i64) -> (out: Self)
        ensures
            out.wf_spec(),
            out.model@ == x as int,
    {
        if x >= 0 {
            let magnitude = RuntimeBigNatWitness::from_u64(x as u64);
            let out = Self::from_sign_and_magnitude(false, magnitude);
            proof {
                assert(out.model@ == out.magnitude.model@ as int);
                assert(out.magnitude.model@ == x as nat);
                assert(x as int >= 0);
                assert(out.model@ == x as int);
            }
            out
        } else {
            let abs_u64 = if x == -9_223_372_036_854_775_808i64 {
                9_223_372_036_854_775_808u64
            } else {
                (-x) as u64
            };
            let magnitude = RuntimeBigNatWitness::from_u64(abs_u64);
            let out = Self::from_sign_and_magnitude(true, magnitude);
            proof {
                assert(out.model@ == -(out.magnitude.model@ as int));
                assert(out.magnitude.model@ == abs_u64 as nat);
                if x == -9_223_372_036_854_775_808i64 {
                    assert(abs_u64 == 9_223_372_036_854_775_808u64);
                    assert(out.magnitude.model@ == 9_223_372_036_854_775_808nat);
                    assert(out.model@ == -(9_223_372_036_854_775_808int));
                    assert(x as int == -(9_223_372_036_854_775_808int));
                    assert(out.model@ == x as int);
                } else {
                    let neg_x = -x;
                    assert(neg_x > 0);
                    assert(abs_u64 == neg_x as u64);
                    assert(neg_x as int == -(x as int));
                    assert(out.magnitude.model@ == neg_x as nat);
                    assert(out.model@ == -(neg_x as int));
                    assert(out.model@ == x as int);
                }
            }
            out
        }
    }

    pub fn from_i32(x: i32) -> (out: Self)
        ensures
            out.wf_spec(),
            out.model@ == x as int,
    {
        let out = Self::from_i64(x as i64);
        proof {
            assert(out.model@ == (x as i64) as int);
            assert((x as i64) as int == x as int);
            assert(out.model@ == x as int);
        }
        out
    }

    pub fn is_zero(&self) -> (out: bool)
        requires
            self.wf_spec(),
        ensures
            out == (self.model@ == 0),
    {
        let out = self.magnitude.is_zero();
        proof {
            assert(out == (self.magnitude.model@ == 0));
            if out {
                assert(self.magnitude.model@ == 0);
                assert(!self.is_negative);
                assert(self.model@ == self.magnitude.model@ as int);
                assert(self.model@ == 0);
            } else {
                assert(self.magnitude.model@ != 0);
                assert(self.magnitude.model@ > 0);
                if self.is_negative {
                    assert(self.model@ == -(self.magnitude.model@ as int));
                    assert(self.model@ < 0);
                } else {
                    assert(self.model@ == self.magnitude.model@ as int);
                    assert(self.model@ > 0);
                }
                assert(self.model@ != 0);
            }
        }
        out
    }

    pub fn is_negative(&self) -> (out: bool)
        requires
            self.wf_spec(),
        ensures
            out == (self.model@ < 0),
    {
        let out = self.is_negative;
        proof {
            if out {
                assert(self.magnitude.model@ > 0);
                assert(self.model@ == -(self.magnitude.model@ as int));
                assert(self.model@ < 0);
            } else {
                assert(self.model@ == self.magnitude.model@ as int);
                assert(self.model@ >= 0);
            }
        }
        out
    }

    pub fn abs(&self) -> (out: RuntimeBigNatWitness)
        requires
            self.wf_spec(),
        ensures
            out.wf_spec(),
            out.model@ == Self::abs_model_spec(self.model@),
    {
        let out = self.magnitude.copy_small_total();
        proof {
            assert(self.magnitude.model@ == RuntimeBigNatWitness::limbs_value_spec(self.magnitude.limbs_le@));
            assert(out.model@ == RuntimeBigNatWitness::limbs_value_spec(self.magnitude.limbs_le@));
            assert(out.model@ == self.magnitude.model@);
            if self.is_negative {
                assert(self.model@ == -(self.magnitude.model@ as int));
                assert(self.model@ < 0);
                assert(-self.model@ == self.magnitude.model@ as int);
                assert(Self::abs_model_spec(self.model@) == (-self.model@) as nat);
                assert((-self.model@) as nat == self.magnitude.model@);
            } else {
                assert(self.model@ == self.magnitude.model@ as int);
                assert(self.model@ >= 0);
                assert(Self::abs_model_spec(self.model@) == self.model@ as nat);
                assert(self.model@ as nat == self.magnitude.model@);
            }
            assert(out.model@ == Self::abs_model_spec(self.model@));
        }
        out
    }

    pub fn signum(&self) -> (out: i8)
        requires
            self.wf_spec(),
        ensures
            out == -1i8 || out == 0i8 || out == 1i8,
            (out == -1i8) <==> (self.model@ < 0),
            (out == 0i8) <==> (self.model@ == 0),
            (out == 1i8) <==> (self.model@ > 0),
    {
        let magnitude_is_zero = self.magnitude.is_zero();
        let out = if magnitude_is_zero {
            0i8
        } else if self.is_negative {
            -1i8
        } else {
            1i8
        };
        proof {
            assert(magnitude_is_zero == (self.magnitude.model@ == 0));
            if magnitude_is_zero {
                assert(self.magnitude.model@ == 0);
                assert(!self.is_negative);
                assert(self.model@ == self.magnitude.model@ as int);
                assert(self.model@ == 0);
                assert(out == 0i8);
            } else {
                assert(self.magnitude.model@ != 0);
                assert(self.magnitude.model@ > 0);
                if self.is_negative {
                    assert(self.model@ == -(self.magnitude.model@ as int));
                    assert(self.model@ < 0);
                    assert(out == -1i8);
                } else {
                    assert(self.model@ == self.magnitude.model@ as int);
                    assert(self.model@ > 0);
                    assert(out == 1i8);
                }
            }

            if out == -1i8 {
                assert(!magnitude_is_zero);
                assert(self.is_negative);
                assert(self.model@ < 0);
            }
            if self.model@ < 0 {
                assert(!magnitude_is_zero);
                assert(self.is_negative);
                assert(out == -1i8);
            }

            if out == 0i8 {
                assert(magnitude_is_zero);
                assert(self.model@ == 0);
            }
            if self.model@ == 0 {
                assert(magnitude_is_zero);
                assert(out == 0i8);
            }

            if out == 1i8 {
                assert(!magnitude_is_zero);
                assert(!self.is_negative);
                assert(self.model@ > 0);
            }
            if self.model@ > 0 {
                assert(!magnitude_is_zero);
                assert(!self.is_negative);
                assert(out == 1i8);
            }
        }
        out
    }

    pub fn cmp(&self, rhs: &Self) -> (out: i8)
        requires
            self.wf_spec(),
            rhs.wf_spec(),
        ensures
            out == -1i8 || out == 0i8 || out == 1i8,
            (out == -1i8) <==> (self.model@ < rhs.model@),
            (out == 0i8) <==> (self.model@ == rhs.model@),
            (out == 1i8) <==> (self.model@ > rhs.model@),
    {
        if self.is_negative && !rhs.is_negative {
            proof {
                assert(self.magnitude.model@ > 0);
                assert(self.model@ == -(self.magnitude.model@ as int));
                assert(rhs.model@ == rhs.magnitude.model@ as int);
                assert(rhs.model@ >= 0);
                assert(self.model@ < 0);
                assert(self.model@ < rhs.model@);
            }
            -1i8
        } else if !self.is_negative && rhs.is_negative {
            proof {
                assert(self.model@ == self.magnitude.model@ as int);
                assert(rhs.magnitude.model@ > 0);
                assert(rhs.model@ == -(rhs.magnitude.model@ as int));
                assert(self.model@ >= 0);
                assert(rhs.model@ < 0);
                assert(self.model@ > rhs.model@);
            }
            1i8
        } else if !self.is_negative {
            let out = self.magnitude.cmp_limbwise_small_total(&rhs.magnitude);
            proof {
                assert(self.model@ == self.magnitude.model@ as int);
                assert(rhs.model@ == rhs.magnitude.model@ as int);
                if out == -1i8 {
                    assert(self.magnitude.model@ < rhs.magnitude.model@);
                    assert(self.model@ < rhs.model@);
                }
                if out == 0i8 {
                    assert(self.magnitude.model@ == rhs.magnitude.model@);
                    assert(self.model@ == rhs.model@);
                }
                if out == 1i8 {
                    assert(self.magnitude.model@ > rhs.magnitude.model@);
                    assert(self.model@ > rhs.model@);
                }
            }
            out
        } else {
            let mag_cmp = self.magnitude.cmp_limbwise_small_total(&rhs.magnitude);
            let out = if mag_cmp == -1i8 {
                1i8
            } else if mag_cmp == 1i8 {
                -1i8
            } else {
                0i8
            };
            proof {
                assert(self.model@ == -(self.magnitude.model@ as int));
                assert(rhs.model@ == -(rhs.magnitude.model@ as int));
                assert(self.magnitude.model@ > 0);
                assert(rhs.magnitude.model@ > 0);
                if mag_cmp == -1i8 {
                    let a = self.magnitude.model@ as int;
                    let b = rhs.magnitude.model@ as int;
                    assert(self.magnitude.model@ < rhs.magnitude.model@);
                    assert(a < b);
                    assert(-a > -b);
                    assert(self.model@ == -a);
                    assert(rhs.model@ == -b);
                    assert(self.model@ > rhs.model@);
                    assert(out == 1i8);
                }
                if mag_cmp == 0i8 {
                    assert(self.magnitude.model@ == rhs.magnitude.model@);
                    assert(self.model@ == rhs.model@);
                    assert(out == 0i8);
                }
                if mag_cmp == 1i8 {
                    let a = self.magnitude.model@ as int;
                    let b = rhs.magnitude.model@ as int;
                    assert(self.magnitude.model@ > rhs.magnitude.model@);
                    assert(a > b);
                    assert(-a < -b);
                    assert(self.model@ == -a);
                    assert(rhs.model@ == -b);
                    assert(self.model@ < rhs.model@);
                    assert(out == -1i8);
                }
            }
            out
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
        if self.is_negative == rhs.is_negative {
            let magnitude = self.magnitude.add_limbwise_small_total(&rhs.magnitude);
            let out = Self::from_sign_and_magnitude(self.is_negative, magnitude);
            proof {
                assert(self.magnitude.model@ == RuntimeBigNatWitness::limbs_value_spec(self.magnitude.limbs_le@));
                assert(rhs.magnitude.model@ == RuntimeBigNatWitness::limbs_value_spec(rhs.magnitude.limbs_le@));
                assert(out.magnitude.model@ == self.magnitude.model@ + rhs.magnitude.model@);
                if self.is_negative {
                    assert(self.model@ == -(self.magnitude.model@ as int));
                    assert(rhs.model@ == -(rhs.magnitude.model@ as int));
                    assert(out.model@ == -(out.magnitude.model@ as int));
                    assert((self.magnitude.model@ + rhs.magnitude.model@) as int
                        == self.magnitude.model@ as int + rhs.magnitude.model@ as int);
                    assert(out.model@
                        == -((self.magnitude.model@ + rhs.magnitude.model@) as int));
                    assert(
                        -((self.magnitude.model@ + rhs.magnitude.model@) as int)
                            == -(self.magnitude.model@ as int) + -(rhs.magnitude.model@ as int)
                    ) by (nonlinear_arith);
                    assert(out.model@ == self.model@ + rhs.model@);
                } else {
                    assert(self.model@ == self.magnitude.model@ as int);
                    assert(rhs.model@ == rhs.magnitude.model@ as int);
                    assert(out.model@ == out.magnitude.model@ as int);
                    assert((self.magnitude.model@ + rhs.magnitude.model@) as int
                        == self.magnitude.model@ as int + rhs.magnitude.model@ as int);
                    assert(out.model@ == self.model@ + rhs.model@);
                }
            }
            out
        } else {
            let cmp_mag = self.magnitude.cmp_limbwise_small_total(&rhs.magnitude);
            if cmp_mag == 0i8 {
                let out = Self::zero();
                proof {
                    assert(self.magnitude.model@ == rhs.magnitude.model@);
                    if self.is_negative {
                        assert(self.model@ == -(self.magnitude.model@ as int));
                        assert(rhs.model@ == rhs.magnitude.model@ as int);
                        assert(self.model@ + rhs.model@ == 0);
                    } else {
                        assert(self.model@ == self.magnitude.model@ as int);
                        assert(rhs.model@ == -(rhs.magnitude.model@ as int));
                        assert(self.model@ + rhs.model@ == 0);
                    }
                    assert(out.model@ == 0);
                    assert(out.model@ == self.model@ + rhs.model@);
                }
                out
            } else if cmp_mag == 1i8 {
                let magnitude = self.magnitude.sub_limbwise_small_total(&rhs.magnitude);
                let out = Self::from_sign_and_magnitude(self.is_negative, magnitude);
                proof {
                    assert(self.magnitude.model@ > rhs.magnitude.model@);
                    assert(out.magnitude.model@ == self.magnitude.model@ - rhs.magnitude.model@);
                    if self.is_negative {
                        assert(self.model@ == -(self.magnitude.model@ as int));
                        assert(rhs.model@ == rhs.magnitude.model@ as int);
                        assert(out.model@ == -(out.magnitude.model@ as int));
                        assert(out.model@ == -((self.magnitude.model@ - rhs.magnitude.model@) as int));
                        assert(
                            -((self.magnitude.model@ - rhs.magnitude.model@) as int)
                                == -(self.magnitude.model@ as int) + rhs.magnitude.model@ as int
                        ) by (nonlinear_arith);
                        assert(out.model@ == self.model@ + rhs.model@);
                    } else {
                        assert(self.model@ == self.magnitude.model@ as int);
                        assert(rhs.model@ == -(rhs.magnitude.model@ as int));
                        assert(out.model@ == out.magnitude.model@ as int);
                        assert(out.model@ == (self.magnitude.model@ - rhs.magnitude.model@) as int);
                        assert(
                            (self.magnitude.model@ - rhs.magnitude.model@) as int
                                == self.magnitude.model@ as int + -(rhs.magnitude.model@ as int)
                        ) by (nonlinear_arith);
                        assert(out.model@ == self.model@ + rhs.model@);
                    }
                }
                out
            } else {
                let magnitude = rhs.magnitude.sub_limbwise_small_total(&self.magnitude);
                let out = Self::from_sign_and_magnitude(rhs.is_negative, magnitude);
                proof {
                    assert(cmp_mag == -1i8);
                    assert(self.magnitude.model@ < rhs.magnitude.model@);
                    assert(out.magnitude.model@ == rhs.magnitude.model@ - self.magnitude.model@);
                    if self.is_negative {
                        assert(self.model@ == -(self.magnitude.model@ as int));
                        assert(rhs.model@ == rhs.magnitude.model@ as int);
                        assert(!rhs.is_negative);
                        assert(out.model@ == out.magnitude.model@ as int);
                        assert(out.model@ == (rhs.magnitude.model@ - self.magnitude.model@) as int);
                        assert(
                            (rhs.magnitude.model@ - self.magnitude.model@) as int
                                == rhs.magnitude.model@ as int + -(self.magnitude.model@ as int)
                        ) by (nonlinear_arith);
                        assert(out.model@ == self.model@ + rhs.model@);
                    } else {
                        assert(self.model@ == self.magnitude.model@ as int);
                        assert(rhs.model@ == -(rhs.magnitude.model@ as int));
                        assert(rhs.is_negative);
                        assert(out.model@ == -(out.magnitude.model@ as int));
                        assert(out.model@ == -((rhs.magnitude.model@ - self.magnitude.model@) as int));
                        assert(
                            -((rhs.magnitude.model@ - self.magnitude.model@) as int)
                                == self.magnitude.model@ as int + -(rhs.magnitude.model@ as int)
                        ) by (nonlinear_arith);
                        assert(out.model@ == self.model@ + rhs.model@);
                    }
                }
                out
            }
        }
    }

    pub fn sub(&self, rhs: &Self) -> (out: Self)
        requires
            self.wf_spec(),
            rhs.wf_spec(),
        ensures
            out.wf_spec(),
            out.model@ == self.model@ - rhs.model@,
    {
        let rhs_neg = rhs.neg();
        let out = self.add(&rhs_neg);
        proof {
            assert(rhs_neg.model@ == -rhs.model@);
            assert(out.model@ == self.model@ + rhs_neg.model@);
            assert(out.model@ == self.model@ + (-rhs.model@));
            assert(out.model@ == self.model@ - rhs.model@);
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
    {
        let magnitude = self.magnitude.mul_limbwise_small_total(&rhs.magnitude);
        let negative = self.is_negative != rhs.is_negative;
        let out = Self::from_sign_and_magnitude(negative, magnitude);
        proof {
            let a = self.magnitude.model@ as int;
            let b = rhs.magnitude.model@ as int;
            let p = out.magnitude.model@ as int;
            assert(out.magnitude.model@ == self.magnitude.model@ * rhs.magnitude.model@);
            assert(p == (self.magnitude.model@ * rhs.magnitude.model@) as int);
            assert((self.magnitude.model@ * rhs.magnitude.model@) as int == a * b);
            if self.is_negative {
                assert(self.model@ == -a);
            } else {
                assert(self.model@ == a);
            }
            if rhs.is_negative {
                assert(rhs.model@ == -b);
            } else {
                assert(rhs.model@ == b);
            }
            if !self.is_negative && !rhs.is_negative {
                assert(!negative);
                assert(out.is_negative == false);
                assert(out.model@ == p);
                assert(out.model@ == a * b);
                assert(self.model@ * rhs.model@ == a * b);
                assert(out.model@ == self.model@ * rhs.model@);
            } else if self.is_negative && rhs.is_negative {
                assert(!negative);
                assert(out.is_negative == false);
                assert(out.model@ == p);
                assert(out.model@ == a * b);
                assert(self.model@ * rhs.model@ == (-a) * (-b));
                assert((-a) * (-b) == a * b) by (nonlinear_arith);
                assert(out.model@ == self.model@ * rhs.model@);
            } else if self.is_negative {
                assert(negative);
                assert(!rhs.is_negative);
                if out.magnitude.model@ == 0 {
                    assert(out.is_negative == false);
                    assert(out.model@ == 0);
                    assert(p == 0);
                    assert(a * b == 0);
                    assert(self.model@ * rhs.model@ == (-a) * b);
                    assert((-a) * b == -(a * b)) by (nonlinear_arith);
                    assert(self.model@ * rhs.model@ == 0);
                    assert(out.model@ == self.model@ * rhs.model@);
                } else {
                    assert(out.is_negative == true);
                    assert(out.model@ == -p);
                    assert(out.model@ == -(a * b));
                    assert(self.model@ * rhs.model@ == (-a) * b);
                    assert((-a) * b == -(a * b)) by (nonlinear_arith);
                    assert(out.model@ == self.model@ * rhs.model@);
                }
            } else {
                assert(negative);
                assert(!self.is_negative);
                assert(rhs.is_negative);
                if out.magnitude.model@ == 0 {
                    assert(out.is_negative == false);
                    assert(out.model@ == 0);
                    assert(p == 0);
                    assert(a * b == 0);
                    assert(self.model@ * rhs.model@ == a * (-b));
                    assert(a * (-b) == -(a * b)) by (nonlinear_arith);
                    assert(self.model@ * rhs.model@ == 0);
                    assert(out.model@ == self.model@ * rhs.model@);
                } else {
                    assert(out.is_negative == true);
                    assert(out.model@ == -p);
                    assert(out.model@ == -(a * b));
                    assert(self.model@ * rhs.model@ == a * (-b));
                    assert(a * (-b) == -(a * b)) by (nonlinear_arith);
                    assert(out.model@ == self.model@ * rhs.model@);
                }
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
            rhs.model@ != 0 ==> out.model@ == Self::trunc_div_spec(self.model@, rhs.model@),
    {
        let rhs_is_zero = rhs.magnitude.is_zero();
        if rhs_is_zero {
            let out = Self::zero();
            proof {
                assert(rhs.magnitude.model@ == 0);
                assert(rhs.model@ == 0);
                assert(out.model@ == 0);
            }
            out
        } else {
            let q_mag = self.magnitude.div_limbwise_small_total(&rhs.magnitude);
            let q_mag_is_zero = q_mag.is_zero();
            let signs_differ = self.is_negative != rhs.is_negative;
            let q_negative = signs_differ && !q_mag_is_zero;
            let out = Self::from_sign_and_magnitude(q_negative, q_mag);
            proof {
                let abs_a = Self::abs_model_spec(self.model@);
                let abs_b = Self::abs_model_spec(rhs.model@);
                let q_abs = self.magnitude.model@ / rhs.magnitude.model@;
                assert(rhs.magnitude.model@ > 0);
                assert(rhs.model@ != 0);
                assert(abs_a == self.magnitude.model@) by {
                    if self.is_negative {
                        assert(self.model@ == -(self.magnitude.model@ as int));
                        assert(self.model@ < 0);
                        assert(-self.model@ == self.magnitude.model@ as int);
                    } else {
                        assert(self.model@ == self.magnitude.model@ as int);
                        assert(self.model@ >= 0);
                    }
                };
                assert(abs_b == rhs.magnitude.model@) by {
                    if rhs.is_negative {
                        assert(rhs.model@ == -(rhs.magnitude.model@ as int));
                        assert(rhs.model@ < 0);
                        assert(-rhs.model@ == rhs.magnitude.model@ as int);
                    } else {
                        assert(rhs.model@ == rhs.magnitude.model@ as int);
                        assert(rhs.model@ >= 0);
                    }
                };
                assert(out.magnitude.model@ == q_abs);
                assert(q_abs == abs_a / abs_b);
                assert(q_mag_is_zero == (q_abs == 0));
                assert(out.is_negative == (q_negative && q_abs > 0));
                if q_abs == 0 {
                    assert(out.model@ == 0);
                    assert(Self::trunc_div_spec(self.model@, rhs.model@) == 0);
                } else {
                    if signs_differ {
                        assert(q_negative);
                        assert(out.is_negative);
                        assert(out.model@ == -(q_abs as int));
                        assert(Self::trunc_div_spec(self.model@, rhs.model@) == -(q_abs as int));
                    } else {
                        assert(!q_negative);
                        assert(!out.is_negative);
                        assert(out.model@ == q_abs as int);
                        assert(Self::trunc_div_spec(self.model@, rhs.model@) == q_abs as int);
                    }
                }
                assert(out.model@ == Self::trunc_div_spec(self.model@, rhs.model@));
            }
            out
        }
    }

    pub fn rem(&self, rhs: &Self) -> (out: Self)
        requires
            self.wf_spec(),
            rhs.wf_spec(),
        ensures
            out.wf_spec(),
            rhs.model@ == 0 ==> out.model@ == 0,
            rhs.model@ != 0 ==> out.model@ == Self::trunc_rem_spec(self.model@, rhs.model@),
            rhs.model@ != 0 ==> Self::abs_model_spec(out.model@) < Self::abs_model_spec(rhs.model@),
            rhs.model@ != 0 ==> out.model@ == 0 || ((out.model@ < 0) <==> (self.model@ < 0)),
    {
        let rhs_is_zero = rhs.magnitude.is_zero();
        if rhs_is_zero {
            let out = Self::zero();
            proof {
                assert(rhs.magnitude.model@ == 0);
                assert(rhs.model@ == 0);
                assert(out.model@ == 0);
            }
            out
        } else {
            let r_mag = self.magnitude.rem_limbwise_small_total(&rhs.magnitude);
            let r_mag_is_zero = r_mag.is_zero();
            let r_negative = self.is_negative && !r_mag_is_zero;
            let out = Self::from_sign_and_magnitude(r_negative, r_mag);
            proof {
                let abs_a = Self::abs_model_spec(self.model@);
                let abs_b = Self::abs_model_spec(rhs.model@);
                let r_abs = self.magnitude.model@ % rhs.magnitude.model@;
                assert(rhs.magnitude.model@ > 0);
                assert(rhs.model@ != 0);
                assert(abs_a == self.magnitude.model@) by {
                    if self.is_negative {
                        assert(self.model@ == -(self.magnitude.model@ as int));
                        assert(self.model@ < 0);
                        assert(-self.model@ == self.magnitude.model@ as int);
                    } else {
                        assert(self.model@ == self.magnitude.model@ as int);
                        assert(self.model@ >= 0);
                    }
                };
                assert(abs_b == rhs.magnitude.model@) by {
                    if rhs.is_negative {
                        assert(rhs.model@ == -(rhs.magnitude.model@ as int));
                        assert(rhs.model@ < 0);
                        assert(-rhs.model@ == rhs.magnitude.model@ as int);
                    } else {
                        assert(rhs.model@ == rhs.magnitude.model@ as int);
                        assert(rhs.model@ >= 0);
                    }
                };
                assert(out.magnitude.model@ == r_abs);
                assert(r_abs == abs_a % abs_b);
                assert(r_mag_is_zero == (r_abs == 0));
                assert(out.is_negative == (r_negative && r_abs > 0));
                if r_abs == 0 {
                    assert(out.model@ == 0);
                    assert(Self::trunc_rem_spec(self.model@, rhs.model@) == 0);
                } else {
                    if self.is_negative {
                        assert(r_negative);
                        assert(out.is_negative);
                        assert(out.model@ == -(r_abs as int));
                        assert(Self::trunc_rem_spec(self.model@, rhs.model@) == -(r_abs as int));
                    } else {
                        assert(!r_negative);
                        assert(!out.is_negative);
                        assert(out.model@ == r_abs as int);
                        assert(Self::trunc_rem_spec(self.model@, rhs.model@) == r_abs as int);
                    }
                }
                assert(out.model@ == Self::trunc_rem_spec(self.model@, rhs.model@));
                assert(Self::abs_model_spec(out.model@) == out.magnitude.model@) by {
                    if out.is_negative {
                        assert(out.model@ == -(out.magnitude.model@ as int));
                        assert(out.model@ < 0);
                        assert(-out.model@ == out.magnitude.model@ as int);
                        assert(Self::abs_model_spec(out.model@) == (-out.model@) as nat);
                    } else {
                        assert(out.model@ == out.magnitude.model@ as int);
                        assert(out.model@ >= 0);
                        assert(Self::abs_model_spec(out.model@) == out.model@ as nat);
                    }
                };
                assert(Self::abs_model_spec(rhs.model@) == rhs.magnitude.model@) by {
                    if rhs.is_negative {
                        assert(rhs.model@ == -(rhs.magnitude.model@ as int));
                        assert(rhs.model@ < 0);
                        assert(-rhs.model@ == rhs.magnitude.model@ as int);
                        assert(Self::abs_model_spec(rhs.model@) == (-rhs.model@) as nat);
                    } else {
                        assert(rhs.model@ == rhs.magnitude.model@ as int);
                        assert(rhs.model@ >= 0);
                        assert(Self::abs_model_spec(rhs.model@) == rhs.model@ as nat);
                    }
                };
                assert(r_abs < abs_b);
                assert(Self::abs_model_spec(out.model@) < Self::abs_model_spec(rhs.model@));

                if out.model@ == 0 {
                    assert(r_abs == 0);
                } else {
                    if self.model@ < 0 {
                        assert(self.is_negative);
                        assert(out.is_negative);
                        assert(out.model@ < 0);
                    } else {
                        assert(!self.is_negative);
                        assert(!out.is_negative);
                        assert(out.model@ > 0);
                    }
                    assert((out.model@ < 0) <==> (self.model@ < 0));
                }
            }
            out
        }
    }

    pub fn div_rem(&self, rhs: &Self) -> (out: (Self, Self))
        requires
            self.wf_spec(),
            rhs.wf_spec(),
        ensures
            out.0.wf_spec(),
            out.1.wf_spec(),
            rhs.model@ == 0 ==> out.0.model@ == 0 && out.1.model@ == 0,
            rhs.model@ != 0 ==> out.0.model@ == Self::trunc_div_spec(self.model@, rhs.model@),
            rhs.model@ != 0 ==> out.1.model@ == Self::trunc_rem_spec(self.model@, rhs.model@),
            rhs.model@ != 0 ==> self.model@ == out.0.model@ * rhs.model@ + out.1.model@,
            rhs.model@ != 0 ==> Self::abs_model_spec(out.1.model@) < Self::abs_model_spec(rhs.model@),
            rhs.model@ != 0 ==> out.1.model@ == 0 || ((out.1.model@ < 0) <==> (self.model@ < 0)),
    {
        let rhs_is_zero = rhs.magnitude.is_zero();
        if rhs_is_zero {
            let q = Self::zero();
            let r = Self::zero();
            proof {
                assert(rhs.magnitude.model@ == 0);
                assert(rhs.model@ == 0);
                assert(q.model@ == 0);
                assert(r.model@ == 0);
            }
            (q, r)
        } else {
            let qr_mag = self.magnitude.div_rem_limbwise_small_total(&rhs.magnitude);
            let q_mag = qr_mag.0;
            let r_mag = qr_mag.1;
            let q_mag_is_zero = q_mag.is_zero();
            let r_mag_is_zero = r_mag.is_zero();
            let q_negative = (self.is_negative != rhs.is_negative) && !q_mag_is_zero;
            let r_negative = self.is_negative && !r_mag_is_zero;
            let q = Self::from_sign_and_magnitude(q_negative, q_mag);
            let r = Self::from_sign_and_magnitude(r_negative, r_mag);
            proof {
                let abs_a = Self::abs_model_spec(self.model@);
                let abs_b = Self::abs_model_spec(rhs.model@);
                let q_abs = self.magnitude.model@ / rhs.magnitude.model@;
                let r_abs = self.magnitude.model@ % rhs.magnitude.model@;
                assert(rhs.magnitude.model@ > 0);
                assert(rhs.model@ != 0);
                assert(
                    self.magnitude.model@
                        == q_abs * rhs.magnitude.model@ + r_abs
                );
                assert(r_abs < rhs.magnitude.model@);
                assert(abs_a == self.magnitude.model@) by {
                    if self.is_negative {
                        assert(self.model@ == -(self.magnitude.model@ as int));
                        assert(self.model@ < 0);
                        assert(-self.model@ == self.magnitude.model@ as int);
                    } else {
                        assert(self.model@ == self.magnitude.model@ as int);
                        assert(self.model@ >= 0);
                    }
                };
                assert(abs_b == rhs.magnitude.model@) by {
                    if rhs.is_negative {
                        assert(rhs.model@ == -(rhs.magnitude.model@ as int));
                        assert(rhs.model@ < 0);
                        assert(-rhs.model@ == rhs.magnitude.model@ as int);
                    } else {
                        assert(rhs.model@ == rhs.magnitude.model@ as int);
                        assert(rhs.model@ >= 0);
                    }
                };

                assert(q.magnitude.model@ == q_abs);
                assert(r.magnitude.model@ == r_abs);
                assert(q_abs == abs_a / abs_b);
                assert(r_abs == abs_a % abs_b);
                assert(q_mag_is_zero == (q_abs == 0));
                assert(r_mag_is_zero == (r_abs == 0));

                assert(q.is_negative == (q_negative && q_abs > 0));
                if q_abs == 0 {
                    assert(q.model@ == 0);
                    assert(Self::trunc_div_spec(self.model@, rhs.model@) == 0);
                } else if self.is_negative != rhs.is_negative {
                    assert(q.model@ == -(q_abs as int));
                    assert(Self::trunc_div_spec(self.model@, rhs.model@) == -(q_abs as int));
                } else {
                    assert(q.model@ == q_abs as int);
                    assert(Self::trunc_div_spec(self.model@, rhs.model@) == q_abs as int);
                }

                assert(r.is_negative == (r_negative && r_abs > 0));
                if r_abs == 0 {
                    assert(r.model@ == 0);
                    assert(Self::trunc_rem_spec(self.model@, rhs.model@) == 0);
                } else if self.is_negative {
                    assert(r.model@ == -(r_abs as int));
                    assert(Self::trunc_rem_spec(self.model@, rhs.model@) == -(r_abs as int));
                } else {
                    assert(r.model@ == r_abs as int);
                    assert(Self::trunc_rem_spec(self.model@, rhs.model@) == r_abs as int);
                }

                assert(q.model@ == Self::trunc_div_spec(self.model@, rhs.model@));
                assert(r.model@ == Self::trunc_rem_spec(self.model@, rhs.model@));

                assert(Self::abs_model_spec(r.model@) == r.magnitude.model@) by {
                    if r.is_negative {
                        assert(r.model@ == -(r.magnitude.model@ as int));
                        assert(r.model@ < 0);
                        assert(-r.model@ == r.magnitude.model@ as int);
                        assert(Self::abs_model_spec(r.model@) == (-r.model@) as nat);
                    } else {
                        assert(r.model@ == r.magnitude.model@ as int);
                        assert(r.model@ >= 0);
                        assert(Self::abs_model_spec(r.model@) == r.model@ as nat);
                    }
                };
                assert(Self::abs_model_spec(rhs.model@) == rhs.magnitude.model@) by {
                    if rhs.is_negative {
                        assert(rhs.model@ == -(rhs.magnitude.model@ as int));
                        assert(rhs.model@ < 0);
                        assert(-rhs.model@ == rhs.magnitude.model@ as int);
                        assert(Self::abs_model_spec(rhs.model@) == (-rhs.model@) as nat);
                    } else {
                        assert(rhs.model@ == rhs.magnitude.model@ as int);
                        assert(rhs.model@ >= 0);
                        assert(Self::abs_model_spec(rhs.model@) == rhs.model@ as nat);
                    }
                };
                assert(Self::abs_model_spec(r.model@) < Self::abs_model_spec(rhs.model@));

                if r.model@ == 0 {
                    assert(r_abs == 0);
                } else {
                    if self.model@ < 0 {
                        assert(self.is_negative);
                        assert(r.is_negative);
                        assert(r.model@ < 0);
                    } else {
                        assert(!self.is_negative);
                        assert(!r.is_negative);
                        assert(r.model@ > 0);
                    }
                    assert((r.model@ < 0) <==> (self.model@ < 0));
                }

                if self.is_negative {
                    if rhs.is_negative {
                        assert(self.model@ == -(abs_a as int));
                        assert(rhs.model@ == -(abs_b as int));
                        assert(q.model@ * rhs.model@ + r.model@
                            == (q_abs as int) * (-(abs_b as int)) + (-(r_abs as int)));
                        assert((q_abs as int) * (-(abs_b as int)) + (-(r_abs as int))
                            == -((q_abs * abs_b + r_abs) as int)) by (nonlinear_arith);
                        assert((q_abs * abs_b + r_abs) as int == abs_a as int);
                        assert(q.model@ * rhs.model@ + r.model@ == -(abs_a as int));
                        assert(self.model@ == -(abs_a as int));
                    } else {
                        assert(self.model@ == -(abs_a as int));
                        assert(rhs.model@ == abs_b as int);
                        assert(q.model@ * rhs.model@ + r.model@
                            == (-(q_abs as int)) * (abs_b as int) + (-(r_abs as int)));
                        assert((-(q_abs as int)) * (abs_b as int) + (-(r_abs as int))
                            == -((q_abs * abs_b + r_abs) as int)) by (nonlinear_arith);
                        assert((q_abs * abs_b + r_abs) as int == abs_a as int);
                        assert(q.model@ * rhs.model@ + r.model@ == -(abs_a as int));
                        assert(self.model@ == -(abs_a as int));
                    }
                } else {
                    if rhs.is_negative {
                        assert(self.model@ == abs_a as int);
                        assert(rhs.model@ == -(abs_b as int));
                        assert(q.model@ * rhs.model@ + r.model@
                            == (-(q_abs as int)) * (-(abs_b as int)) + (r_abs as int));
                        assert((-(q_abs as int)) * (-(abs_b as int)) + (r_abs as int)
                            == (q_abs * abs_b + r_abs) as int) by (nonlinear_arith);
                        assert((q_abs * abs_b + r_abs) as int == abs_a as int);
                        assert(q.model@ * rhs.model@ + r.model@ == abs_a as int);
                        assert(self.model@ == abs_a as int);
                    } else {
                        assert(self.model@ == abs_a as int);
                        assert(rhs.model@ == abs_b as int);
                        assert(q.model@ * rhs.model@ + r.model@
                            == (q_abs as int) * (abs_b as int) + (r_abs as int));
                        assert((q_abs as int) * (abs_b as int) + (r_abs as int)
                            == (q_abs * abs_b + r_abs) as int) by (nonlinear_arith);
                        assert((q_abs * abs_b + r_abs) as int == abs_a as int);
                        assert(q.model@ * rhs.model@ + r.model@ == abs_a as int);
                        assert(self.model@ == abs_a as int);
                    }
                }
                assert(self.model@ == q.model@ * rhs.model@ + r.model@);
            }
            (q, r)
        }
    }

    /// Signed operation-level wrapper: computes compare output and proves `cmp <= 0 <==> a <= b`.
    pub(crate) fn lemma_cmp_le_zero_iff_le_ops(a: &Self, b: &Self) -> (out: i8)
        requires
            a.wf_spec(),
            b.wf_spec(),
        ensures
            out == -1i8 || out == 0i8 || out == 1i8,
            out == -1i8 ==> a.model@ < b.model@,
            out == 0i8 ==> a.model@ == b.model@,
            out == 1i8 ==> a.model@ > b.model@,
            (out <= 0i8) <==> (a.model@ <= b.model@),
    {
        let out_cmp = a.cmp(b);
        proof {
            if out_cmp <= 0i8 {
                if out_cmp == -1i8 {
                    assert(a.model@ < b.model@);
                } else {
                    assert(out_cmp == 0i8) by {
                        assert(out_cmp == -1i8 || out_cmp == 0i8 || out_cmp == 1i8);
                        assert(out_cmp != -1i8);
                        if out_cmp == 1i8 {
                            assert(out_cmp <= 0i8);
                            assert(false);
                        }
                    };
                    assert(a.model@ == b.model@);
                }
                assert(a.model@ <= b.model@);
            }
            if a.model@ <= b.model@ {
                if a.model@ < b.model@ {
                    assert(out_cmp == -1i8);
                } else {
                    assert(a.model@ == b.model@);
                    assert(out_cmp == 0i8);
                }
                assert(out_cmp <= 0i8);
            }
        }
        out_cmp
    }

    /// Signed operation-level wrapper: computes compare output and proves `cmp < 0 <==> a < b`.
    pub(crate) fn lemma_cmp_lt_zero_iff_lt_ops(a: &Self, b: &Self) -> (out: i8)
        requires
            a.wf_spec(),
            b.wf_spec(),
        ensures
            out == -1i8 || out == 0i8 || out == 1i8,
            out == -1i8 ==> a.model@ < b.model@,
            out == 0i8 ==> a.model@ == b.model@,
            out == 1i8 ==> a.model@ > b.model@,
            (out < 0i8) <==> (a.model@ < b.model@),
    {
        let out_cmp = a.cmp(b);
        proof {
            if out_cmp < 0i8 {
                assert(out_cmp == -1i8) by {
                    assert(out_cmp == -1i8 || out_cmp == 0i8 || out_cmp == 1i8);
                    if out_cmp == 0i8 {
                        assert(out_cmp < 0i8);
                        assert(false);
                    }
                    if out_cmp == 1i8 {
                        assert(out_cmp < 0i8);
                        assert(false);
                    }
                };
                assert(a.model@ < b.model@);
            }
            if a.model@ < b.model@ {
                assert(out_cmp == -1i8);
                assert(out_cmp < 0i8);
            }
        }
        out_cmp
    }

    /// Signed operation-level wrapper: computes compare output and proves `cmp == 0 <==> a == b`.
    pub(crate) fn lemma_cmp_eq_zero_iff_eq_ops(a: &Self, b: &Self) -> (out: i8)
        requires
            a.wf_spec(),
            b.wf_spec(),
        ensures
            out == -1i8 || out == 0i8 || out == 1i8,
            out == -1i8 ==> a.model@ < b.model@,
            out == 0i8 ==> a.model@ == b.model@,
            out == 1i8 ==> a.model@ > b.model@,
            (out == 0i8) <==> (a.model@ == b.model@),
    {
        let out_cmp = a.cmp(b);
        proof {
            if out_cmp == 0i8 {
                assert(a.model@ == b.model@);
            }
            if a.model@ == b.model@ {
                assert(out_cmp == 0i8);
            }
        }
        out_cmp
    }

    /// Signed operation-level wrapper: subtraction is exact; zero result iff operands are equal.
    pub(crate) fn lemma_model_sub_zero_iff_eq_ops(a: &Self, b: &Self) -> (out: Self)
        requires
            a.wf_spec(),
            b.wf_spec(),
        ensures
            out.wf_spec(),
            out.model@ == a.model@ - b.model@,
            (out.model@ == 0) <==> (a.model@ == b.model@),
    {
        let out_sub = a.sub(b);
        proof {
            assert(out_sub.model@ == a.model@ - b.model@);
            if out_sub.model@ == 0 {
                assert(a.model@ - b.model@ == 0);
                assert(a.model@ == b.model@);
            }
            if a.model@ == b.model@ {
                assert(a.model@ - b.model@ == 0);
                assert(out_sub.model@ == 0);
            }
        }
        out_sub
    }

    /// Signed operation-level wrapper: computes `sub(a, b)` and proves exact add inverse.
    pub(crate) fn lemma_model_sub_add_inverse_ops(a: &Self, b: &Self) -> (out: (Self, Self))
        requires
            a.wf_spec(),
            b.wf_spec(),
        ensures
            out.0.wf_spec(),
            out.1.wf_spec(),
            out.0.model@ == a.model@ - b.model@,
            out.1.model@ == out.0.model@ + b.model@,
            out.1.model@ == a.model@,
    {
        let sub_ab = a.sub(b);
        let add_sub_ab_b = sub_ab.add(b);
        proof {
            assert(sub_ab.model@ == a.model@ - b.model@);
            assert(add_sub_ab_b.model@ == sub_ab.model@ + b.model@);
            assert(add_sub_ab_b.model@ == (a.model@ - b.model@) + b.model@);
            assert((a.model@ - b.model@) + b.model@ == a.model@);
            assert(add_sub_ab_b.model@ == a.model@);
        }
        (sub_ab, add_sub_ab_b)
    }

    /// Signed operation-level wrapper: computes `sum = a + b` and proves both subtraction round-trips.
    pub(crate) fn lemma_model_add_sub_round_trip_ops(a: &Self, b: &Self) -> (out: (Self, Self, Self))
        requires
            a.wf_spec(),
            b.wf_spec(),
        ensures
            out.0.wf_spec(),
            out.1.wf_spec(),
            out.2.wf_spec(),
            out.0.model@ == a.model@ + b.model@,
            out.1.model@ == a.model@,
            out.2.model@ == b.model@,
    {
        let sum = a.add(b);
        let sub_sum_b = sum.sub(b);
        let sub_sum_a = sum.sub(a);
        proof {
            assert(sum.model@ == a.model@ + b.model@);
            assert(sub_sum_b.model@ == sum.model@ - b.model@);
            assert(sub_sum_a.model@ == sum.model@ - a.model@);
            assert(sub_sum_b.model@ == (a.model@ + b.model@) - b.model@);
            assert(sub_sum_a.model@ == (a.model@ + b.model@) - a.model@);
            assert((a.model@ + b.model@) - b.model@ == a.model@);
            assert((a.model@ + b.model@) - a.model@ == b.model@);
            assert(sub_sum_b.model@ == a.model@);
            assert(sub_sum_a.model@ == b.model@);
        }
        (sum, sub_sum_b, sub_sum_a)
    }

    /// Signed operation-level wrapper: numerator monotonicity for truncating division with positive divisor.
    pub(crate) fn lemma_model_div_monotonic_pos_ops(a: &Self, b: &Self, d: &Self) -> (out: (Self, Self))
        requires
            a.wf_spec(),
            b.wf_spec(),
            d.wf_spec(),
            a.model@ <= b.model@,
            d.model@ > 0,
        ensures
            out.0.wf_spec(),
            out.1.wf_spec(),
            out.0.model@ == Self::trunc_div_spec(a.model@, d.model@),
            out.1.model@ == Self::trunc_div_spec(b.model@, d.model@),
            out.0.model@ <= out.1.model@,
    {
        let div_a = a.div(d);
        let div_b = b.div(d);
        proof {
            assert(div_a.model@ == Self::trunc_div_spec(a.model@, d.model@));
            assert(div_b.model@ == Self::trunc_div_spec(b.model@, d.model@));
            if b.model@ < 0 {
                assert(a.model@ < 0);
                let aa = (-a.model@) as nat;
                let bb = (-b.model@) as nat;
                let dd = d.model@ as nat;
                assert(aa as int == -a.model@);
                assert(bb as int == -b.model@);
                assert(dd as int == d.model@);
                assert(-b.model@ <= -a.model@);
                assert(bb <= aa);
                lemma_div_is_ordered(bb as int, aa as int, dd as int);
                assert((bb as int) / (dd as int) <= (aa as int) / (dd as int));
                assert((bb / dd) as int == (bb as int) / (dd as int));
                assert((aa / dd) as int == (aa as int) / (dd as int));
                assert((bb / dd) as int <= (aa / dd) as int);
                assert(-((aa / dd) as int) <= -((bb / dd) as int));

                assert(Self::abs_model_spec(a.model@) == aa);
                assert(Self::abs_model_spec(b.model@) == bb);
                assert(Self::abs_model_spec(d.model@) == dd);
                assert((a.model@ < 0) != (d.model@ < 0));
                assert((b.model@ < 0) != (d.model@ < 0));
                assert(Self::trunc_div_spec(a.model@, d.model@) == -((aa / dd) as int));
                assert(Self::trunc_div_spec(b.model@, d.model@) == -((bb / dd) as int));
                assert(Self::trunc_div_spec(a.model@, d.model@) <= Self::trunc_div_spec(b.model@, d.model@));
            } else if a.model@ < 0 {
                assert(b.model@ >= 0);
                let aa = (-a.model@) as nat;
                let bb = b.model@ as nat;
                let dd = d.model@ as nat;
                assert(Self::abs_model_spec(a.model@) == aa);
                assert(Self::abs_model_spec(b.model@) == bb);
                assert(Self::abs_model_spec(d.model@) == dd);
                assert((a.model@ < 0) != (d.model@ < 0));
                assert(!(b.model@ < 0));
                assert(Self::trunc_div_spec(a.model@, d.model@) == -((aa / dd) as int));
                assert(Self::trunc_div_spec(b.model@, d.model@) == (bb / dd) as int);
                assert(0 <= (aa / dd) as int);
                assert(0 <= (bb / dd) as int);
                assert(Self::trunc_div_spec(a.model@, d.model@) <= 0);
                assert(0 <= Self::trunc_div_spec(b.model@, d.model@));
                assert(Self::trunc_div_spec(a.model@, d.model@) <= Self::trunc_div_spec(b.model@, d.model@));
            } else {
                assert(0 <= a.model@);
                assert(0 <= b.model@);
                let aa = a.model@ as nat;
                let bb = b.model@ as nat;
                let dd = d.model@ as nat;
                assert(aa as int == a.model@);
                assert(bb as int == b.model@);
                assert(dd as int == d.model@);
                assert(aa <= bb);
                lemma_div_is_ordered(aa as int, bb as int, dd as int);
                assert((aa as int) / (dd as int) <= (bb as int) / (dd as int));
                assert((aa / dd) as int == (aa as int) / (dd as int));
                assert((bb / dd) as int == (bb as int) / (dd as int));
                assert((aa / dd) as int <= (bb / dd) as int);

                assert(Self::abs_model_spec(a.model@) == aa);
                assert(Self::abs_model_spec(b.model@) == bb);
                assert(Self::abs_model_spec(d.model@) == dd);
                assert(!(a.model@ < 0));
                assert(!(b.model@ < 0));
                assert(Self::trunc_div_spec(a.model@, d.model@) == (aa / dd) as int);
                assert(Self::trunc_div_spec(b.model@, d.model@) == (bb / dd) as int);
                assert(Self::trunc_div_spec(a.model@, d.model@) <= Self::trunc_div_spec(b.model@, d.model@));
            }
            assert(div_a.model@ <= div_b.model@);
        }
        (div_a, div_b)
    }

    /// Signed operation-level wrapper: positive compare implies positive exact subtraction.
    pub(crate) fn lemma_cmp_pos_implies_sub_pos_ops(a: &Self, b: &Self) -> (out: (i8, Self))
        requires
            a.wf_spec(),
            b.wf_spec(),
        ensures
            out.0 == -1i8 || out.0 == 0i8 || out.0 == 1i8,
            out.1.wf_spec(),
            out.1.model@ == a.model@ - b.model@,
            out.0 == 1i8 ==> out.1.model@ > 0,
    {
        let cmp = Self::lemma_cmp_eq_zero_iff_eq_ops(a, b);
        let sub_ab = a.sub(b);
        proof {
            assert(sub_ab.model@ == a.model@ - b.model@);
            if cmp == 1i8 {
                assert(a.model@ > b.model@);
                assert(a.model@ - b.model@ > 0);
                assert(sub_ab.model@ > 0);
            }
        }
        (cmp, sub_ab)
    }

    /// Signed operation-level wrapper: equality compare implies both directional subtractions are zero.
    pub(crate) fn lemma_cmp_eq_implies_bi_sub_zero_ops(a: &Self, b: &Self) -> (out: (i8, Self, Self))
        requires
            a.wf_spec(),
            b.wf_spec(),
        ensures
            out.0 == -1i8 || out.0 == 0i8 || out.0 == 1i8,
            out.1.wf_spec(),
            out.2.wf_spec(),
            out.1.model@ == a.model@ - b.model@,
            out.2.model@ == b.model@ - a.model@,
            out.0 == 0i8 ==> out.1.model@ == 0 && out.2.model@ == 0,
    {
        let cmp = Self::lemma_cmp_eq_zero_iff_eq_ops(a, b);
        let sub_ab = a.sub(b);
        let sub_ba = b.sub(a);
        proof {
            assert(sub_ab.model@ == a.model@ - b.model@);
            assert(sub_ba.model@ == b.model@ - a.model@);
            if cmp == 0i8 {
                assert(a.model@ == b.model@);
                assert(sub_ab.model@ == 0);
                assert(sub_ba.model@ == 0);
            }
        }
        (cmp, sub_ab, sub_ba)
    }

    /// Signed operation-level wrapper: negative compare implies asymmetric exact subtraction signs.
    pub(crate) fn lemma_cmp_neg_implies_asym_sub_ops(a: &Self, b: &Self) -> (out: (i8, Self, Self))
        requires
            a.wf_spec(),
            b.wf_spec(),
        ensures
            out.0 == -1i8 || out.0 == 0i8 || out.0 == 1i8,
            out.1.wf_spec(),
            out.2.wf_spec(),
            out.1.model@ == a.model@ - b.model@,
            out.2.model@ == b.model@ - a.model@,
            out.0 == -1i8 ==> out.1.model@ < 0 && out.2.model@ > 0,
    {
        let cmp = Self::lemma_cmp_eq_zero_iff_eq_ops(a, b);
        let sub_ab = a.sub(b);
        let sub_ba = b.sub(a);
        proof {
            assert(sub_ab.model@ == a.model@ - b.model@);
            assert(sub_ba.model@ == b.model@ - a.model@);
            if cmp == -1i8 {
                assert(a.model@ < b.model@);
                assert(a.model@ - b.model@ < 0);
                assert(b.model@ - a.model@ > 0);
                assert(sub_ab.model@ < 0);
                assert(sub_ba.model@ > 0);
            }
        }
        (cmp, sub_ab, sub_ba)
    }

    /// Signed operation-level wrapper: for `a >= 0`, `d > 0`, remainder is in `[0, d)`.
    pub(crate) fn lemma_model_rem_bounds_nonneg_dividend_pos_divisor_ops(a: &Self, d: &Self) -> (out: Self)
        requires
            a.wf_spec(),
            d.wf_spec(),
            a.model@ >= 0,
            d.model@ > 0,
        ensures
            out.wf_spec(),
            out.model@ == Self::trunc_rem_spec(a.model@, d.model@),
            0 <= out.model@,
            out.model@ < d.model@,
    {
        let r = a.rem(d);
        proof {
            assert(r.model@ == Self::trunc_rem_spec(a.model@, d.model@));
            assert(Self::abs_model_spec(r.model@) < Self::abs_model_spec(d.model@));
            assert(r.model@ == 0 || ((r.model@ < 0) <==> (a.model@ < 0)));
            assert(!(a.model@ < 0));
            if r.model@ == 0 {
                assert(0 <= r.model@);
            } else {
                assert((r.model@ < 0) <==> false);
                assert(!(r.model@ < 0));
                assert(0 <= r.model@);
            }

            assert(Self::abs_model_spec(d.model@) == d.model@ as nat);
            assert((d.model@ as nat) as int == d.model@);
            if r.model@ == 0 {
                assert(r.model@ < d.model@);
            } else {
                assert(0 <= r.model@);
                assert(Self::abs_model_spec(r.model@) == r.model@ as nat);
                assert((r.model@ as nat) < (d.model@ as nat));
                assert(((r.model@ as nat) as int) < ((d.model@ as nat) as int));
                assert((r.model@ as nat) as int == r.model@);
                assert((d.model@ as nat) as int == d.model@);
                assert(r.model@ < d.model@);
            }
        }
        r
    }

    /// Signed operation-level wrapper: for `a <= 0`, `d > 0`, remainder is in `(-d, 0]`.
    pub(crate) fn lemma_model_rem_bounds_nonpos_dividend_pos_divisor_ops(a: &Self, d: &Self) -> (out: Self)
        requires
            a.wf_spec(),
            d.wf_spec(),
            a.model@ <= 0,
            d.model@ > 0,
        ensures
            out.wf_spec(),
            out.model@ == Self::trunc_rem_spec(a.model@, d.model@),
            -d.model@ < out.model@,
            out.model@ <= 0,
    {
        let r = a.rem(d);
        proof {
            assert(r.model@ == Self::trunc_rem_spec(a.model@, d.model@));
            assert(Self::abs_model_spec(r.model@) < Self::abs_model_spec(d.model@));
            assert(r.model@ == 0 || ((r.model@ < 0) <==> (a.model@ < 0)));
            assert(Self::abs_model_spec(d.model@) == d.model@ as nat);
            assert((d.model@ as nat) as int == d.model@);

            if a.model@ == 0 {
                let n = Self::abs_model_spec(d.model@);
                assert(Self::abs_model_spec(a.model@) == 0);
                assert(n > 0);
                lemma_small_mod(0nat, n);
                assert(0nat % n == 0);
                assert(!(a.model@ < 0));
                assert(Self::trunc_rem_spec(a.model@, d.model@)
                    == (Self::abs_model_spec(a.model@) % Self::abs_model_spec(d.model@)) as int);
                assert(Self::trunc_rem_spec(a.model@, d.model@) == (0nat % n) as int);
                assert(Self::trunc_rem_spec(a.model@, d.model@) == 0);
                assert(r.model@ == 0);
            } else {
                assert(a.model@ < 0);
                if r.model@ != 0 {
                    assert((r.model@ < 0) <==> (a.model@ < 0));
                    assert(r.model@ < 0);
                }
            }
            assert(r.model@ <= 0);

            if r.model@ == 0 {
                assert(-d.model@ < 0);
            } else {
                assert(r.model@ < 0);
                assert(Self::abs_model_spec(r.model@) == (-r.model@) as nat);
                assert(((-r.model@) as nat) < (d.model@ as nat));
                assert((((-r.model@) as nat) as int) < ((d.model@ as nat) as int));
                assert(((-r.model@) as nat) as int == -r.model@);
                assert((d.model@ as nat) as int == d.model@);
                assert(-r.model@ < d.model@);
                assert(-d.model@ < r.model@);
            }
        }
        r
    }

    /// Signed shape wrapper: nonzero model implies tight limb-length/value window on magnitude.
    pub(crate) fn lemma_model_len_window_nonzero_ops(a: &Self)
        requires
            a.wf_spec(),
            a.model@ != 0,
        ensures
            a.magnitude.limbs_le@.len() > 0,
            RuntimeBigNatWitness::pow_base_spec((a.magnitude.limbs_le@.len() - 1) as nat)
                <= Self::abs_model_spec(a.model@),
            Self::abs_model_spec(a.model@)
                < RuntimeBigNatWitness::pow_base_spec(a.magnitude.limbs_le@.len()),
    {
        RuntimeBigNatWitness::lemma_model_len_window_nonzero_ops(&a.magnitude);
        proof {
            a.lemma_sign_model_bridge();
            assert(Self::abs_model_spec(a.model@) == a.magnitude.model@);
            assert(a.magnitude.model@ != 0);
            assert(
                RuntimeBigNatWitness::pow_base_spec((a.magnitude.limbs_le@.len() - 1) as nat)
                    <= a.magnitude.model@
            );
            assert(a.magnitude.model@ < RuntimeBigNatWitness::pow_base_spec(a.magnitude.limbs_le@.len()));
        }
    }

    /// Signed shape wrapper: zero model implies empty canonical magnitude limb vector.
    pub(crate) fn lemma_model_zero_implies_len_zero_ops(a: &Self)
        requires
            a.wf_spec(),
            a.model@ == 0,
        ensures
            a.magnitude.limbs_le@.len() == 0,
    {
        RuntimeBigNatWitness::lemma_model_zero_implies_len_zero_ops(&a.magnitude);
        proof {
            a.lemma_sign_model_bridge();
            assert(a.magnitude.model@ == 0);
        }
    }

    /// Signed P3 wrapper: abs-add length bound over magnitudes.
    pub(crate) fn lemma_abs_add_len_bound_ops(a: &Self, b: &Self) -> (out: RuntimeBigNatWitness)
        requires
            a.wf_spec(),
            b.wf_spec(),
        ensures
            out.wf_spec(),
            out.model@ == Self::abs_model_spec(a.model@) + Self::abs_model_spec(b.model@),
            a.magnitude.limbs_le@.len() >= b.magnitude.limbs_le@.len()
                ==> out.limbs_le@.len() <= a.magnitude.limbs_le@.len() + 1,
            b.magnitude.limbs_le@.len() >= a.magnitude.limbs_le@.len()
                ==> out.limbs_le@.len() <= b.magnitude.limbs_le@.len() + 1,
    {
        let out_sum = RuntimeBigNatWitness::lemma_model_add_len_bound_ops(&a.magnitude, &b.magnitude);
        proof {
            a.lemma_sign_model_bridge();
            b.lemma_sign_model_bridge();
            assert(Self::abs_model_spec(a.model@) == a.magnitude.model@);
            assert(Self::abs_model_spec(b.model@) == b.magnitude.model@);
            assert(out_sum.model@ == a.magnitude.model@ + b.magnitude.model@);
            assert(out_sum.model@ == Self::abs_model_spec(a.model@) + Self::abs_model_spec(b.model@));
        }
        out_sum
    }

    /// Signed P3 wrapper: abs-mul length bound over magnitudes.
    pub(crate) fn lemma_abs_mul_len_bound_ops(a: &Self, b: &Self) -> (out: RuntimeBigNatWitness)
        requires
            a.wf_spec(),
            b.wf_spec(),
        ensures
            out.wf_spec(),
            out.model@ == Self::abs_model_spec(a.model@) * Self::abs_model_spec(b.model@),
            out.limbs_le@.len() <= a.magnitude.limbs_le@.len() + b.magnitude.limbs_le@.len(),
    {
        let out_mul = RuntimeBigNatWitness::lemma_model_mul_len_bound_ops(&a.magnitude, &b.magnitude);
        proof {
            a.lemma_sign_model_bridge();
            b.lemma_sign_model_bridge();
            assert(Self::abs_model_spec(a.model@) == a.magnitude.model@);
            assert(Self::abs_model_spec(b.model@) == b.magnitude.model@);
            assert(out_mul.model@ == a.magnitude.model@ * b.magnitude.model@);
            assert(out_mul.model@ == Self::abs_model_spec(a.model@) * Self::abs_model_spec(b.model@));
        }
        out_mul
    }

    /// Signed P3 wrapper: abs-quotient length bound for nonzero divisor.
    pub(crate) fn lemma_abs_div_len_bound_nonzero_ops(a: &Self, d: &Self) -> (out: RuntimeBigNatWitness)
        requires
            a.wf_spec(),
            d.wf_spec(),
            d.model@ != 0,
        ensures
            out.wf_spec(),
            out.model@ == Self::abs_model_spec(a.model@) / Self::abs_model_spec(d.model@),
            out.limbs_le@.len() <= a.magnitude.limbs_le@.len(),
    {
        let out_div = RuntimeBigNatWitness::lemma_model_div_len_bound_pos_ops(&a.magnitude, &d.magnitude);
        proof {
            a.lemma_sign_model_bridge();
            d.lemma_sign_model_bridge();
            assert(Self::abs_model_spec(a.model@) == a.magnitude.model@);
            assert(Self::abs_model_spec(d.model@) == d.magnitude.model@);
            assert(d.magnitude.model@ > 0);
            assert(out_div.model@ == a.magnitude.model@ / d.magnitude.model@);
            assert(out_div.model@ == Self::abs_model_spec(a.model@) / Self::abs_model_spec(d.model@));
        }
        out_div
    }

    /// Signed P3 wrapper: abs-remainder length bound for nonzero divisor.
    pub(crate) fn lemma_abs_rem_len_bound_nonzero_ops(a: &Self, d: &Self) -> (out: RuntimeBigNatWitness)
        requires
            a.wf_spec(),
            d.wf_spec(),
            d.model@ != 0,
        ensures
            out.wf_spec(),
            out.model@ == Self::abs_model_spec(a.model@) % Self::abs_model_spec(d.model@),
            out.limbs_le@.len() <= d.magnitude.limbs_le@.len(),
    {
        let out_rem = RuntimeBigNatWitness::lemma_model_rem_len_bound_pos_ops(&a.magnitude, &d.magnitude);
        proof {
            a.lemma_sign_model_bridge();
            d.lemma_sign_model_bridge();
            assert(Self::abs_model_spec(a.model@) == a.magnitude.model@);
            assert(Self::abs_model_spec(d.model@) == d.magnitude.model@);
            assert(d.magnitude.model@ > 0);
            assert(out_rem.model@ == a.magnitude.model@ % d.magnitude.model@);
            assert(out_rem.model@ == Self::abs_model_spec(a.model@) % Self::abs_model_spec(d.model@));
        }
        out_rem
    }

    /// Arithmetic helper for signed truncating division/remainder cancellation on exact products.
    pub proof fn lemma_trunc_div_rem_mul_cancel(a: int, d: int)
        requires
            d != 0,
        ensures
            Self::trunc_div_spec(a * d, d) == a,
            Self::trunc_rem_spec(a * d, d) == 0,
    {
        let abs_a = Self::abs_model_spec(a);
        let abs_d = Self::abs_model_spec(d);
        let abs_prod = Self::abs_model_spec(a * d);

        if d < 0 {
            assert(abs_d == (-d) as nat);
            assert(-d > 0);
            assert(abs_d > 0);
        } else {
            assert(d > 0);
            assert(abs_d == d as nat);
            assert(abs_d > 0);
        }

        if a < 0 {
            if d < 0 {
                assert(abs_a == (-a) as nat);
                assert(abs_d == (-d) as nat);
                assert(a * d == (-a) * (-d)) by (nonlinear_arith);
                assert(-a > 0);
                assert(-d > 0);
                lemma_mul_strict_inequality(0, -a, -d);
                assert(0 < (-a) * (-d));
                assert(a * d > 0);
                assert(abs_prod == (a * d) as nat);
                assert(abs_prod == ((-a) * (-d)) as nat);
                assert(((-a) * (-d)) as nat == ((-a) as nat) * ((-d) as nat));
            } else {
                assert(d > 0);
                assert(abs_a == (-a) as nat);
                assert(abs_d == d as nat);
                assert(-a > 0);
                lemma_mul_strict_inequality(0, -a, d);
                assert(0 < (-a) * d);
                assert(a * d == -((-a) * d)) by (nonlinear_arith);
                assert(a * d < 0);
                assert(-(a * d) == (-a) * d) by (nonlinear_arith);
                assert(abs_prod == (-(a * d)) as nat);
                assert(abs_prod == ((-a) * d) as nat);
                assert(((-a) * d) as nat == ((-a) as nat) * (d as nat));
            }
        } else {
            if d < 0 {
                assert(abs_a == a as nat);
                assert(abs_d == (-d) as nat);
                assert(-(a * d) == a * (-d)) by (nonlinear_arith);
                if a == 0 {
                    assert(a * d == 0);
                } else {
                    assert(a > 0);
                    assert(-d > 0);
                    lemma_mul_strict_inequality(0, a, -d);
                    assert(0 < a * (-d));
                    assert(a * d == -(a * (-d))) by (nonlinear_arith);
                    assert(a * d < 0);
                }
                assert(a * d <= 0);
                assert(abs_prod == (-(a * d)) as nat);
                assert(abs_prod == (a * (-d)) as nat);
                assert((a * (-d)) as nat == (a as nat) * ((-d) as nat));
            } else {
                assert(d > 0);
                assert(abs_a == a as nat);
                assert(abs_d == d as nat);
                if a == 0 {
                    assert(a * d == 0);
                } else {
                    assert(a > 0);
                    lemma_mul_strict_inequality(0, a, d);
                    assert(0 < a * d);
                }
                assert(a * d >= 0);
                assert(abs_prod == (a * d) as nat);
                assert((a * d) as nat == (a as nat) * (d as nat));
            }
        }
        assert(abs_prod == abs_a * abs_d);

        let xi = (abs_a * abs_d) as int;
        let di = abs_d as int;
        let ai = abs_a as int;
        assert(di > 0);
        assert(di != 0);
        assert(0 <= 0 < di);
        assert(xi == ai * di + 0);
        lemma_fundamental_div_mod_converse(xi, di, ai, 0);
        assert(xi / di == ai);
        assert(xi % di == 0);
        assert(((abs_a * abs_d) / abs_d) as int == xi / di);
        assert(((abs_a * abs_d) % abs_d) as int == xi % di);
        assert((abs_a * abs_d) / abs_d == abs_a);
        assert((abs_a * abs_d) % abs_d == 0);
        assert(abs_prod / abs_d == abs_a);
        assert(abs_prod % abs_d == 0);

        let q_abs = abs_prod / abs_d;
        let r_abs = abs_prod % abs_d;
        assert(q_abs == abs_a);
        assert(r_abs == 0);

        if a == 0 {
            assert(abs_a == 0);
            if a * d < 0 {
                assert(Self::trunc_div_spec(a * d, d) == -(q_abs as int));
                assert(-(q_abs as int) == 0);
            } else {
                assert(Self::trunc_div_spec(a * d, d) == q_abs as int);
                assert(q_abs as int == 0);
            }
            assert(Self::trunc_div_spec(a * d, d) == 0);
            assert(Self::trunc_div_spec(a * d, d) == a);
        } else if a < 0 {
            assert(abs_a == (-a) as nat);
            assert(abs_a as int == -a);
            if d < 0 {
                assert(-a > 0);
                assert(-d > 0);
                lemma_mul_strict_inequality(0, -a, -d);
                assert(0 < (-a) * (-d));
                assert(a * d == (-a) * (-d)) by (nonlinear_arith);
                assert(a * d > 0);
                assert((a * d < 0) == false);
                assert((d < 0) == true);
                assert((a * d < 0) != (d < 0));
            } else {
                assert(d > 0);
                assert(-a > 0);
                lemma_mul_strict_inequality(0, -a, d);
                assert(0 < (-a) * d);
                assert(a * d == -((-a) * d)) by (nonlinear_arith);
                assert(a * d < 0);
                assert((a * d < 0) == true);
                assert((d < 0) == false);
                assert((a * d < 0) != (d < 0));
            }
            assert(Self::trunc_div_spec(a * d, d) == -(q_abs as int));
            assert(Self::trunc_div_spec(a * d, d) == -(abs_a as int));
            assert(Self::trunc_div_spec(a * d, d) == a);
        } else {
            assert(a > 0);
            assert(abs_a == a as nat);
            assert(abs_a as int == a);
            if d < 0 {
                assert(-d > 0);
                lemma_mul_strict_inequality(0, a, -d);
                assert(0 < a * (-d));
                assert(a * d == -(a * (-d))) by (nonlinear_arith);
                assert(a * d < 0);
                assert((a * d < 0) == true);
                assert((d < 0) == true);
                assert(!((a * d < 0) != (d < 0)));
            } else {
                assert(d > 0);
                lemma_mul_strict_inequality(0, a, d);
                assert(0 < a * d);
                assert((a * d < 0) == false);
                assert((d < 0) == false);
                assert(!((a * d < 0) != (d < 0)));
            }
            assert(Self::trunc_div_spec(a * d, d) == q_abs as int);
            assert(Self::trunc_div_spec(a * d, d) == abs_a as int);
            assert(Self::trunc_div_spec(a * d, d) == a);
        }

        if a * d < 0 {
            assert(Self::trunc_rem_spec(a * d, d) == -(r_abs as int));
            assert(-(r_abs as int) == 0);
        } else {
            assert(Self::trunc_rem_spec(a * d, d) == r_abs as int);
            assert(r_abs as int == 0);
        }
        assert(Self::trunc_rem_spec(a * d, d) == 0);
    }

    /// Signed operation-level parity wrapper for div/rem recomposition under nonzero divisors.
    pub(crate) fn lemma_model_div_rem_recompose_nonzero_ops(a: &Self, d: &Self) -> (out: (Self, Self))
        requires
            a.wf_spec(),
            d.wf_spec(),
            d.model@ != 0,
        ensures
            out.0.wf_spec(),
            out.1.wf_spec(),
            out.0.model@ == Self::trunc_div_spec(a.model@, d.model@),
            out.1.model@ == Self::trunc_rem_spec(a.model@, d.model@),
            a.model@ == out.0.model@ * d.model@ + out.1.model@,
            Self::abs_model_spec(out.1.model@) < Self::abs_model_spec(d.model@),
            out.1.model@ == 0 || ((out.1.model@ < 0) <==> (a.model@ < 0)),
    {
        Self::lemma_div_rem_sign_edge_ops(a, d)
    }

    /// Signed operation-level wrapper: exact product/div/rem cancellation for nonzero divisors.
    pub(crate) fn lemma_model_mul_div_rem_cancel_nonzero_ops(a: &Self, d: &Self) -> (out: (Self, Self, Self))
        requires
            a.wf_spec(),
            d.wf_spec(),
            d.model@ != 0,
        ensures
            out.0.wf_spec(),
            out.1.wf_spec(),
            out.2.wf_spec(),
            out.0.model@ == a.model@ * d.model@,
            out.1.model@ == Self::trunc_div_spec(out.0.model@, d.model@),
            out.2.model@ == Self::trunc_rem_spec(out.0.model@, d.model@),
            out.0.model@ == out.1.model@ * d.model@ + out.2.model@,
            out.1.model@ == a.model@,
            out.2.model@ == 0,
    {
        let prod = a.mul(d);
        let qr = prod.div_rem(d);
        proof {
            assert(prod.model@ == a.model@ * d.model@);
            assert(qr.0.model@ == Self::trunc_div_spec(prod.model@, d.model@));
            assert(qr.1.model@ == Self::trunc_rem_spec(prod.model@, d.model@));
            assert(prod.model@ == qr.0.model@ * d.model@ + qr.1.model@);
            Self::lemma_trunc_div_rem_mul_cancel(a.model@, d.model@);
            assert(Self::trunc_div_spec(prod.model@, d.model@) == a.model@);
            assert(Self::trunc_rem_spec(prod.model@, d.model@) == 0);
            assert(qr.0.model@ == a.model@);
            assert(qr.1.model@ == 0);
        }
        (prod, qr.0, qr.1)
    }

    pub(crate) fn lemma_model_add_commutative_ops(a: &Self, b: &Self) -> (out: (Self, Self))
        requires
            a.wf_spec(),
            b.wf_spec(),
        ensures
            out.0.wf_spec(),
            out.1.wf_spec(),
            out.0.model@ == a.model@ + b.model@,
            out.1.model@ == b.model@ + a.model@,
            out.0.model@ == out.1.model@,
    {
        let ab = a.add(b);
        let ba = b.add(a);
        proof {
            assert(ab.model@ == a.model@ + b.model@);
            assert(ba.model@ == b.model@ + a.model@);
            assert(ab.model@ == ba.model@);
        }
        (ab, ba)
    }

    pub(crate) fn lemma_model_add_associative_ops(a: &Self, b: &Self, c: &Self) -> (out: (Self, Self))
        requires
            a.wf_spec(),
            b.wf_spec(),
            c.wf_spec(),
        ensures
            out.0.wf_spec(),
            out.1.wf_spec(),
            out.0.model@ == (a.model@ + b.model@) + c.model@,
            out.1.model@ == a.model@ + (b.model@ + c.model@),
            out.0.model@ == out.1.model@,
    {
        let ab = a.add(b);
        let lhs = ab.add(c);
        let bc = b.add(c);
        let rhs_sum = a.add(&bc);
        proof {
            assert(ab.model@ == a.model@ + b.model@);
            assert(lhs.model@ == ab.model@ + c.model@);
            assert(lhs.model@ == (a.model@ + b.model@) + c.model@);
            assert(bc.model@ == b.model@ + c.model@);
            assert(rhs_sum.model@ == a.model@ + bc.model@);
            assert(rhs_sum.model@ == a.model@ + (b.model@ + c.model@));
            assert((a.model@ + b.model@) + c.model@ == a.model@ + (b.model@ + c.model@));
            assert(lhs.model@ == rhs_sum.model@);
        }
        (lhs, rhs_sum)
    }

    pub(crate) fn lemma_model_mul_commutative_ops(a: &Self, b: &Self) -> (out: (Self, Self))
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
        let ab = a.mul(b);
        let ba = b.mul(a);
        proof {
            assert(ab.model@ == a.model@ * b.model@);
            assert(ba.model@ == b.model@ * a.model@);
            lemma_mul_is_commutative(a.model@, b.model@);
            assert(a.model@ * b.model@ == b.model@ * a.model@);
            assert(ab.model@ == ba.model@);
        }
        (ab, ba)
    }

    pub(crate) fn lemma_model_mul_associative_ops(a: &Self, b: &Self, c: &Self) -> (out: (Self, Self))
        requires
            a.wf_spec(),
            b.wf_spec(),
            c.wf_spec(),
        ensures
            out.0.wf_spec(),
            out.1.wf_spec(),
            out.0.model@ == (a.model@ * b.model@) * c.model@,
            out.1.model@ == a.model@ * (b.model@ * c.model@),
            out.0.model@ == out.1.model@,
    {
        let ab = a.mul(b);
        let lhs = ab.mul(c);
        let bc = b.mul(c);
        let rhs_prod = a.mul(&bc);
        proof {
            assert(ab.model@ == a.model@ * b.model@);
            assert(lhs.model@ == ab.model@ * c.model@);
            assert(lhs.model@ == (a.model@ * b.model@) * c.model@);
            assert(bc.model@ == b.model@ * c.model@);
            assert(rhs_prod.model@ == a.model@ * bc.model@);
            assert(rhs_prod.model@ == a.model@ * (b.model@ * c.model@));
            assert((a.model@ * b.model@) * c.model@ == a.model@ * (b.model@ * c.model@))
                by (nonlinear_arith);
            assert(lhs.model@ == rhs_prod.model@);
        }
        (lhs, rhs_prod)
    }

    pub(crate) fn lemma_model_mul_distributes_over_add_ops(a: &Self, b: &Self, c: &Self) -> (out: (Self, Self))
        requires
            a.wf_spec(),
            b.wf_spec(),
            c.wf_spec(),
        ensures
            out.0.wf_spec(),
            out.1.wf_spec(),
            out.0.model@ == a.model@ * (b.model@ + c.model@),
            out.1.model@ == a.model@ * b.model@ + a.model@ * c.model@,
            out.0.model@ == out.1.model@,
    {
        let b_plus_c = b.add(c);
        let lhs = a.mul(&b_plus_c);
        let ab = a.mul(b);
        let ac = a.mul(c);
        let rhs_sum = ab.add(&ac);
        proof {
            assert(b_plus_c.model@ == b.model@ + c.model@);
            assert(lhs.model@ == a.model@ * b_plus_c.model@);
            assert(lhs.model@ == a.model@ * (b.model@ + c.model@));
            assert(ab.model@ == a.model@ * b.model@);
            assert(ac.model@ == a.model@ * c.model@);
            assert(rhs_sum.model@ == ab.model@ + ac.model@);
            assert(rhs_sum.model@ == a.model@ * b.model@ + a.model@ * c.model@);
            assert(a.model@ * (b.model@ + c.model@) == a.model@ * b.model@ + a.model@ * c.model@)
                by (nonlinear_arith);
            assert(lhs.model@ == rhs_sum.model@);
        }
        (lhs, rhs_sum)
    }

    pub(crate) fn lemma_model_add_monotonic_ops(a: &Self, b: &Self, c: &Self) -> (out: (Self, Self))
        requires
            a.wf_spec(),
            b.wf_spec(),
            c.wf_spec(),
            a.model@ <= b.model@,
        ensures
            out.0.wf_spec(),
            out.1.wf_spec(),
            out.0.model@ == a.model@ + c.model@,
            out.1.model@ == b.model@ + c.model@,
            out.0.model@ <= out.1.model@,
    {
        let ac = a.add(c);
        let bc = b.add(c);
        proof {
            assert(ac.model@ == a.model@ + c.model@);
            assert(bc.model@ == b.model@ + c.model@);
            assert(a.model@ + c.model@ <= b.model@ + c.model@);
            assert(ac.model@ <= bc.model@);
        }
        (ac, bc)
    }

    pub(crate) fn lemma_model_add_strict_monotonic_ops(a: &Self, b: &Self, c: &Self) -> (out: (Self, Self))
        requires
            a.wf_spec(),
            b.wf_spec(),
            c.wf_spec(),
            a.model@ < b.model@,
        ensures
            out.0.wf_spec(),
            out.1.wf_spec(),
            out.0.model@ == a.model@ + c.model@,
            out.1.model@ == b.model@ + c.model@,
            out.0.model@ < out.1.model@,
    {
        let ac = a.add(c);
        let bc = b.add(c);
        proof {
            assert(ac.model@ == a.model@ + c.model@);
            assert(bc.model@ == b.model@ + c.model@);
            assert(a.model@ + c.model@ < b.model@ + c.model@);
            assert(ac.model@ < bc.model@);
        }
        (ac, bc)
    }

    pub(crate) fn lemma_model_add_cancellation_ops(a: &Self, b: &Self, c: &Self) -> (out: (Self, Self))
        requires
            a.wf_spec(),
            b.wf_spec(),
            c.wf_spec(),
            a.model@ + c.model@ == b.model@ + c.model@,
        ensures
            out.0.wf_spec(),
            out.1.wf_spec(),
            out.0.model@ == a.model@ + c.model@,
            out.1.model@ == b.model@ + c.model@,
            a.model@ == b.model@,
    {
        let ac = a.add(c);
        let bc = b.add(c);
        proof {
            assert(ac.model@ == a.model@ + c.model@);
            assert(bc.model@ == b.model@ + c.model@);
            assert(ac.model@ == bc.model@);
            assert(a.model@ == b.model@);
        }
        (ac, bc)
    }

    pub(crate) fn lemma_model_mul_monotonic_nonneg_ops(a: &Self, b: &Self, c: &Self) -> (out: (Self, Self))
        requires
            a.wf_spec(),
            b.wf_spec(),
            c.wf_spec(),
            a.model@ <= b.model@,
            0 <= c.model@,
        ensures
            out.0.wf_spec(),
            out.1.wf_spec(),
            out.0.model@ == a.model@ * c.model@,
            out.1.model@ == b.model@ * c.model@,
            out.0.model@ <= out.1.model@,
    {
        let ac = a.mul(c);
        let bc = b.mul(c);
        proof {
            assert(ac.model@ == a.model@ * c.model@);
            assert(bc.model@ == b.model@ * c.model@);
            lemma_mul_inequality(a.model@, b.model@, c.model@);
            assert(a.model@ * c.model@ <= b.model@ * c.model@);
            assert(ac.model@ <= bc.model@);
        }
        (ac, bc)
    }

    pub(crate) fn lemma_model_mul_strict_monotonic_pos_ops(a: &Self, b: &Self, c: &Self) -> (out: (Self, Self))
        requires
            a.wf_spec(),
            b.wf_spec(),
            c.wf_spec(),
            a.model@ < b.model@,
            0 < c.model@,
        ensures
            out.0.wf_spec(),
            out.1.wf_spec(),
            out.0.model@ == a.model@ * c.model@,
            out.1.model@ == b.model@ * c.model@,
            out.0.model@ < out.1.model@,
    {
        let ac = a.mul(c);
        let bc = b.mul(c);
        proof {
            assert(ac.model@ == a.model@ * c.model@);
            assert(bc.model@ == b.model@ * c.model@);
            lemma_mul_strict_inequality(a.model@, b.model@, c.model@);
            assert(a.model@ * c.model@ < b.model@ * c.model@);
            assert(ac.model@ < bc.model@);
        }
        (ac, bc)
    }

    pub(crate) fn lemma_model_mul_cancellation_pos_ops(a: &Self, b: &Self, c: &Self) -> (out: (Self, Self))
        requires
            a.wf_spec(),
            b.wf_spec(),
            c.wf_spec(),
            0 < c.model@,
            a.model@ * c.model@ == b.model@ * c.model@,
        ensures
            out.0.wf_spec(),
            out.1.wf_spec(),
            out.0.model@ == a.model@ * c.model@,
            out.1.model@ == b.model@ * c.model@,
            a.model@ == b.model@,
    {
        let ac = a.mul(c);
        let bc = b.mul(c);
        proof {
            assert(ac.model@ == a.model@ * c.model@);
            assert(bc.model@ == b.model@ * c.model@);
            assert(ac.model@ == bc.model@);
            lemma_mul_is_commutative(c.model@, a.model@);
            lemma_mul_is_commutative(c.model@, b.model@);
            assert(c.model@ * a.model@ == a.model@ * c.model@);
            assert(c.model@ * b.model@ == b.model@ * c.model@);
            assert(c.model@ * a.model@ == c.model@ * b.model@);
            lemma_mul_equality_converse(c.model@, a.model@, b.model@);
            assert(a.model@ == b.model@);
        }
        (ac, bc)
    }

    pub(crate) fn lemma_neg_add_self_zero_ops(a: &Self) -> (out: (Self, Self))
        requires
            a.wf_spec(),
        ensures
            out.0.wf_spec(),
            out.1.wf_spec(),
            out.0.model@ == -a.model@,
            out.1.model@ == 0,
    {
        let neg_a = a.neg();
        let sum = a.add(&neg_a);
        proof {
            assert(neg_a.model@ == -a.model@);
            assert(sum.model@ == a.model@ + neg_a.model@);
            assert(sum.model@ == a.model@ + (-a.model@));
            assert(sum.model@ == 0);
        }
        (neg_a, sum)
    }

    pub(crate) fn lemma_sub_self_zero_ops(a: &Self) -> (out: Self)
        requires
            a.wf_spec(),
        ensures
            out.wf_spec(),
            out.model@ == 0,
    {
        let out_sub = a.sub(a);
        proof {
            assert(out_sub.model@ == a.model@ - a.model@);
            assert(out_sub.model@ == 0);
        }
        out_sub
    }

    pub(crate) fn lemma_zero_sign_normalization_ops() -> (out: (Self, Self, Self))
        ensures
            out.0.wf_spec(),
            out.0.model@ == 0,
            !out.0.is_negative,
            out.1.wf_spec(),
            out.1.model@ == 0,
            !out.1.is_negative,
            out.2.wf_spec(),
            out.2.model@ == 0,
            !out.2.is_negative,
    {
        let z_mag = RuntimeBigNatWitness::zero();
        let z_from_neg_sign = Self::from_sign_and_magnitude(true, z_mag);
        let z_ctor = Self::zero();
        let z_neg = z_from_neg_sign.neg();
        proof {
            assert(z_from_neg_sign.model@ == 0);
            assert(!z_from_neg_sign.is_negative);
            assert(z_ctor.model@ == 0);
            assert(!z_ctor.is_negative);
            assert(z_neg.model@ == -z_from_neg_sign.model@);
            assert(z_neg.model@ == 0);
            assert(!z_neg.is_negative);
        }
        (z_from_neg_sign, z_ctor, z_neg)
    }

    pub(crate) fn lemma_mixed_sign_arith_ops(a: &Self, b: &Self) -> (out: (Self, Self, Self))
        requires
            a.wf_spec(),
            b.wf_spec(),
            a.model@ >= 0,
            b.model@ <= 0,
        ensures
            out.0.wf_spec(),
            out.1.wf_spec(),
            out.2.wf_spec(),
            out.0.model@ == a.model@ + b.model@,
            out.1.model@ == a.model@ - b.model@,
            out.2.model@ == a.model@ * b.model@,
    {
        let sum = a.add(b);
        let diff = a.sub(b);
        let prod = a.mul(b);
        proof {
            assert(sum.model@ == a.model@ + b.model@);
            assert(diff.model@ == a.model@ - b.model@);
            assert(prod.model@ == a.model@ * b.model@);
        }
        (sum, diff, prod)
    }

    pub(crate) fn lemma_div_rem_sign_edge_ops(a: &Self, d: &Self) -> (out: (Self, Self))
        requires
            a.wf_spec(),
            d.wf_spec(),
            d.model@ != 0,
        ensures
            out.0.wf_spec(),
            out.1.wf_spec(),
            out.0.model@ == Self::trunc_div_spec(a.model@, d.model@),
            out.1.model@ == Self::trunc_rem_spec(a.model@, d.model@),
            a.model@ == out.0.model@ * d.model@ + out.1.model@,
            Self::abs_model_spec(out.1.model@) < Self::abs_model_spec(d.model@),
            out.1.model@ == 0 || ((out.1.model@ < 0) <==> (a.model@ < 0)),
    {
        let qr = a.div_rem(d);
        proof {
            assert(qr.0.model@ == Self::trunc_div_spec(a.model@, d.model@));
            assert(qr.1.model@ == Self::trunc_rem_spec(a.model@, d.model@));
            assert(a.model@ == qr.0.model@ * d.model@ + qr.1.model@);
            assert(Self::abs_model_spec(qr.1.model@) < Self::abs_model_spec(d.model@));
            assert(qr.1.model@ == 0 || ((qr.1.model@ < 0) <==> (a.model@ < 0)));
        }
        qr
    }

    pub fn neg(&self) -> (out: Self)
        requires
            self.wf_spec(),
        ensures
            out.wf_spec(),
            out.magnitude.model@ == self.magnitude.model@,
            out.model@ == -self.model@,
    {
        let magnitude = self.magnitude.copy_small_total();
        let out = Self::from_sign_and_magnitude(!self.is_negative, magnitude);
        proof {
            assert(out.magnitude.model@ == self.magnitude.model@);
            if self.magnitude.model@ == 0 {
                assert(!self.is_negative);
                assert(self.model@ == 0);
                assert(out.model@ == 0);
                assert(out.model@ == -self.model@);
            } else {
                assert(self.magnitude.model@ > 0);
                if self.is_negative {
                    assert(self.model@ == -(self.magnitude.model@ as int));
                    assert(!out.is_negative);
                    assert(out.model@ == self.magnitude.model@ as int);
                    assert(out.model@ == -self.model@);
                } else {
                    assert(self.model@ == self.magnitude.model@ as int);
                    assert(out.is_negative);
                    assert(out.model@ == -(self.magnitude.model@ as int));
                    assert(out.model@ == -self.model@);
                }
            }
        }
        out
    }
}

impl<'a> vstd::std_specs::ops::NegSpecImpl for &'a RuntimeBigIntWitness {
    open spec fn obeys_neg_spec() -> bool {
        false
    }

    open spec fn neg_req(self) -> bool {
        self.wf_spec()
    }

    open spec fn neg_spec(self) -> Self::Output {
        arbitrary()
    }
}

impl<'a> core::ops::Neg for &'a RuntimeBigIntWitness {
    type Output = RuntimeBigIntWitness;

    fn neg(self) -> (out: Self::Output) {
        RuntimeBigIntWitness::neg(self)
    }
}

impl<'a, 'b> vstd::std_specs::ops::AddSpecImpl<&'b RuntimeBigIntWitness> for &'a RuntimeBigIntWitness {
    open spec fn obeys_add_spec() -> bool {
        false
    }

    open spec fn add_req(self, rhs: &'b RuntimeBigIntWitness) -> bool {
        self.wf_spec() && rhs.wf_spec()
    }

    open spec fn add_spec(self, rhs: &'b RuntimeBigIntWitness) -> Self::Output {
        arbitrary()
    }
}

impl<'a, 'b> vstd::std_specs::ops::SubSpecImpl<&'b RuntimeBigIntWitness> for &'a RuntimeBigIntWitness {
    open spec fn obeys_sub_spec() -> bool {
        false
    }

    open spec fn sub_req(self, rhs: &'b RuntimeBigIntWitness) -> bool {
        self.wf_spec() && rhs.wf_spec()
    }

    open spec fn sub_spec(self, rhs: &'b RuntimeBigIntWitness) -> Self::Output {
        arbitrary()
    }
}

impl<'a, 'b> vstd::std_specs::ops::MulSpecImpl<&'b RuntimeBigIntWitness> for &'a RuntimeBigIntWitness {
    open spec fn obeys_mul_spec() -> bool {
        false
    }

    open spec fn mul_req(self, rhs: &'b RuntimeBigIntWitness) -> bool {
        self.wf_spec() && rhs.wf_spec()
    }

    open spec fn mul_spec(self, rhs: &'b RuntimeBigIntWitness) -> Self::Output {
        arbitrary()
    }
}

impl<'a, 'b> vstd::std_specs::ops::DivSpecImpl<&'b RuntimeBigIntWitness> for &'a RuntimeBigIntWitness {
    open spec fn obeys_div_spec() -> bool {
        false
    }

    open spec fn div_req(self, rhs: &'b RuntimeBigIntWitness) -> bool {
        self.wf_spec() && rhs.wf_spec()
    }

    open spec fn div_spec(self, rhs: &'b RuntimeBigIntWitness) -> Self::Output {
        arbitrary()
    }
}

impl<'a, 'b> vstd::std_specs::ops::RemSpecImpl<&'b RuntimeBigIntWitness> for &'a RuntimeBigIntWitness {
    open spec fn obeys_rem_spec() -> bool {
        false
    }

    open spec fn rem_req(self, rhs: &'b RuntimeBigIntWitness) -> bool {
        self.wf_spec() && rhs.wf_spec()
    }

    open spec fn rem_spec(self, rhs: &'b RuntimeBigIntWitness) -> Self::Output {
        arbitrary()
    }
}

impl<'a, 'b> core::ops::Add<&'b RuntimeBigIntWitness> for &'a RuntimeBigIntWitness {
    type Output = RuntimeBigIntWitness;

    fn add(self, rhs: &'b RuntimeBigIntWitness) -> (out: Self::Output) {
        RuntimeBigIntWitness::add(self, rhs)
    }
}

impl<'a, 'b> core::ops::Sub<&'b RuntimeBigIntWitness> for &'a RuntimeBigIntWitness {
    type Output = RuntimeBigIntWitness;

    fn sub(self, rhs: &'b RuntimeBigIntWitness) -> (out: Self::Output) {
        RuntimeBigIntWitness::sub(self, rhs)
    }
}

impl<'a, 'b> core::ops::Mul<&'b RuntimeBigIntWitness> for &'a RuntimeBigIntWitness {
    type Output = RuntimeBigIntWitness;

    fn mul(self, rhs: &'b RuntimeBigIntWitness) -> (out: Self::Output) {
        RuntimeBigIntWitness::mul(self, rhs)
    }
}

impl<'a, 'b> core::ops::Div<&'b RuntimeBigIntWitness> for &'a RuntimeBigIntWitness {
    type Output = RuntimeBigIntWitness;

    fn div(self, rhs: &'b RuntimeBigIntWitness) -> (out: Self::Output) {
        RuntimeBigIntWitness::div(self, rhs)
    }
}

impl<'a, 'b> core::ops::Rem<&'b RuntimeBigIntWitness> for &'a RuntimeBigIntWitness {
    type Output = RuntimeBigIntWitness;

    fn rem(self, rhs: &'b RuntimeBigIntWitness) -> (out: Self::Output) {
        RuntimeBigIntWitness::rem(self, rhs)
    }
}
}
