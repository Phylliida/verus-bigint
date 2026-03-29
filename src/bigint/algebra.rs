use crate::bigint::BigInt;
use verus_algebra::traits::*;
use vstd::prelude::*;

verus! {

impl Equivalence for BigInt {
    open spec fn eqv(self, other: Self) -> bool {
        self.value == other.value
    }

    proof fn axiom_eqv_reflexive(a: Self) {}

    proof fn axiom_eqv_symmetric(a: Self, b: Self) {}

    proof fn axiom_eqv_transitive(a: Self, b: Self, c: Self) {}

    proof fn axiom_eq_implies_eqv(a: Self, b: Self) {}
}

impl AdditiveCommutativeMonoid for BigInt {
    open spec fn zero() -> Self {
        BigInt { value: 0 }
    }

    open spec fn add(self, other: Self) -> Self {
        BigInt { value: self.value + other.value }
    }

    proof fn axiom_add_commutative(a: Self, b: Self) {}

    proof fn axiom_add_associative(a: Self, b: Self, c: Self) {}

    proof fn axiom_add_zero_right(a: Self) {}

    proof fn axiom_add_congruence_left(a: Self, b: Self, c: Self) {}
}

impl AdditiveGroup for BigInt {
    open spec fn neg(self) -> Self {
        BigInt { value: -self.value }
    }

    open spec fn sub(self, other: Self) -> Self {
        BigInt { value: self.value - other.value }
    }

    proof fn axiom_add_inverse_right(a: Self) {}

    proof fn axiom_sub_is_add_neg(a: Self, b: Self) {}

    proof fn axiom_neg_congruence(a: Self, b: Self) {}
}

impl Ring for BigInt {
    open spec fn one() -> Self {
        BigInt { value: 1 }
    }

    open spec fn mul(self, other: Self) -> Self {
        BigInt { value: self.value * other.value }
    }

    proof fn axiom_mul_commutative(a: Self, b: Self) {
        assert(a.value * b.value == b.value * a.value) by(nonlinear_arith);
    }

    proof fn axiom_mul_associative(a: Self, b: Self, c: Self) {
        assert((a.value * b.value) * c.value == a.value * (b.value * c.value)) by(nonlinear_arith);
    }

    proof fn axiom_mul_one_right(a: Self) {}

    proof fn axiom_mul_zero_right(a: Self) {}

    proof fn axiom_mul_distributes_left(a: Self, b: Self, c: Self) {
        assert(a.value * (b.value + c.value) == a.value * b.value + a.value * c.value) by(nonlinear_arith);
    }

    proof fn axiom_one_ne_zero() {}

    proof fn axiom_mul_congruence_left(a: Self, b: Self, c: Self) {}
}

impl PartialOrder for BigInt {
    open spec fn le(self, other: Self) -> bool {
        self.value <= other.value
    }

    proof fn axiom_le_reflexive(a: Self) {}

    proof fn axiom_le_antisymmetric(a: Self, b: Self) {}

    proof fn axiom_le_transitive(a: Self, b: Self, c: Self) {}

    proof fn axiom_le_congruence(a1: Self, a2: Self, b1: Self, b2: Self) {}
}

impl OrderedRing for BigInt {
    open spec fn lt(self, other: Self) -> bool {
        self.value < other.value
    }

    proof fn axiom_le_total(a: Self, b: Self) {}

    proof fn axiom_lt_iff_le_and_not_eqv(a: Self, b: Self) {}

    proof fn axiom_le_add_monotone(a: Self, b: Self, c: Self) {}

    proof fn axiom_le_mul_nonneg_monotone(a: Self, b: Self, c: Self) {
        assert(a.value <= b.value && 0int <= c.value ==> a.value * c.value <= b.value * c.value) by(nonlinear_arith);
    }
}

} //  verus!
