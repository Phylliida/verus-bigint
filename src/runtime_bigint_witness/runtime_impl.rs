#![cfg(not(verus_keep_ghost))]

use super::RuntimeBigNatWitness;

const LIMB_BASE: u64 = 1u64 << 32;

impl RuntimeBigNatWitness {
    fn from_parts(mut limbs_le: Vec<u32>) -> Self {
        while limbs_le.last().copied() == Some(0u32) {
            limbs_le.pop();
        }
        Self { limbs_le }
    }

    fn trimmed_len(limbs: &[u32]) -> usize {
        let mut n = limbs.len();
        while n > 0 && limbs[n - 1] == 0u32 {
            n -= 1;
        }
        n
    }

    pub fn zero() -> Self {
        Self { limbs_le: Vec::new() }
    }

    pub fn from_u32(x: u32) -> Self {
        if x == 0 {
            Self::zero()
        } else {
            Self { limbs_le: vec![x] }
        }
    }

    pub fn from_u64(x: u64) -> Self {
        let lo = x as u32;
        let hi = (x >> 32) as u32;
        Self::from_two_limbs(lo, hi)
    }

    pub fn from_two_limbs(lo: u32, hi: u32) -> Self {
        if hi == 0 {
            return Self::from_u32(lo);
        }
        Self { limbs_le: vec![lo, hi] }
    }

    pub fn add(&self, rhs: &Self) -> Self {
        self.add_limbwise_small_total(rhs)
    }

    pub fn add_limbwise_small(&self, rhs: &Self) -> Self {
        self.add_limbwise_small_total(rhs)
    }

    pub fn add_limbwise_small_total(&self, rhs: &Self) -> Self {
        let n = self.limbs_le.len().max(rhs.limbs_le.len());
        let mut out_limbs: Vec<u32> = Vec::with_capacity(n + 1);
        let mut carry: u64 = 0u64;
        let mut i: usize = 0;
        while i < n {
            let a = if i < self.limbs_le.len() {
                self.limbs_le[i] as u64
            } else {
                0u64
            };
            let b = if i < rhs.limbs_le.len() {
                rhs.limbs_le[i] as u64
            } else {
                0u64
            };
            let sum = a + b + carry;
            out_limbs.push(sum as u32);
            carry = sum >> 32;
            i += 1;
        }
        if carry != 0 {
            out_limbs.push(carry as u32);
        }
        Self::from_parts(out_limbs)
    }

    fn shift_base_once_total(&self) -> Self {
        if self.is_zero() {
            return Self::zero();
        }
        let mut out_limbs: Vec<u32> = Vec::with_capacity(self.limbs_le.len() + 1);
        out_limbs.push(0u32);
        out_limbs.extend_from_slice(&self.limbs_le);
        Self::from_parts(out_limbs)
    }

    fn mul_by_u32_total(&self, rhs_limb: u32) -> Self {
        if rhs_limb == 0 || self.is_zero() {
            return Self::zero();
        }
        let rhs64 = rhs_limb as u64;
        let mut out_limbs: Vec<u32> = Vec::with_capacity(self.limbs_le.len() + 1);
        let mut carry: u64 = 0u64;
        for &a in &self.limbs_le {
            let prod = (a as u64) * rhs64 + carry;
            out_limbs.push(prod as u32);
            carry = prod >> 32;
        }
        if carry != 0 {
            out_limbs.push(carry as u32);
        }
        Self::from_parts(out_limbs)
    }

    pub fn mul(&self, rhs: &Self) -> Self {
        self.mul_limbwise_small_total(rhs)
    }

    pub fn div(&self, rhs: &Self) -> Self {
        self.div_limbwise_small_total(rhs)
    }

    pub fn rem(&self, rhs: &Self) -> Self {
        self.rem_limbwise_small_total(rhs)
    }

    pub fn div_rem(&self, rhs: &Self) -> (Self, Self) {
        self.div_rem_limbwise_small_total(rhs)
    }

    pub fn lemma_model_add_commutative_ops(a: &Self, b: &Self) -> (Self, Self) {
        let add_ab = a.add_limbwise_small_total(b);
        let add_ba = b.add_limbwise_small_total(a);
        (add_ab, add_ba)
    }

    pub fn lemma_model_add_monotonic_ops(a: &Self, b: &Self, c: &Self) -> (Self, Self) {
        let add_ac = a.add_limbwise_small_total(c);
        let add_bc = b.add_limbwise_small_total(c);
        (add_ac, add_bc)
    }

    pub fn lemma_model_add_len_bound_ops(a: &Self, b: &Self) -> Self {
        a.add_limbwise_small_total(b)
    }

    pub fn lemma_model_mul_commutative_ops(a: &Self, b: &Self) -> (Self, Self) {
        let mul_ab = a.mul_limbwise_small_total(b);
        let mul_ba = b.mul_limbwise_small_total(a);
        (mul_ab, mul_ba)
    }

    pub fn lemma_model_mul_monotonic_ops(a: &Self, b: &Self, c: &Self) -> (Self, Self) {
        let mul_ac = a.mul_limbwise_small_total(c);
        let mul_bc = b.mul_limbwise_small_total(c);
        (mul_ac, mul_bc)
    }

    pub fn lemma_model_mul_len_bound_ops(a: &Self, b: &Self) -> Self {
        a.mul_limbwise_small_total(b)
    }

    pub fn lemma_model_len_window_nonzero_ops(_a: &Self) {
    }

    pub fn lemma_model_zero_implies_len_zero_ops(_a: &Self) {
    }

    pub fn lemma_cmp_le_zero_iff_le_ops(a: &Self, b: &Self) -> i8 {
        a.cmp_limbwise_small_total(b)
    }

    pub fn lemma_cmp_lt_zero_iff_lt_ops(a: &Self, b: &Self) -> i8 {
        a.cmp_limbwise_small_total(b)
    }

    pub fn lemma_cmp_eq_zero_iff_eq_ops(a: &Self, b: &Self) -> i8 {
        a.cmp_limbwise_small_total(b)
    }

    pub fn lemma_model_sub_zero_iff_le_ops(a: &Self, b: &Self) -> Self {
        a.sub_limbwise_small_total(b)
    }

    pub fn lemma_model_sub_add_inverse_ge_ops(a: &Self, b: &Self) -> (Self, Self) {
        let sub_ab = a.sub_limbwise_small_total(b);
        let add_sub_ab_b = sub_ab.add_limbwise_small_total(b);
        (sub_ab, add_sub_ab_b)
    }

    pub fn lemma_cmp_pos_implies_sub_pos_ops(a: &Self, b: &Self) -> (i8, Self) {
        let cmp = a.cmp_limbwise_small_total(b);
        let sub_ab = a.sub_limbwise_small_total(b);
        (cmp, sub_ab)
    }

    pub fn lemma_cmp_eq_implies_bi_sub_zero_ops(a: &Self, b: &Self) -> (i8, Self, Self) {
        let cmp = a.cmp_limbwise_small_total(b);
        let sub_ab = a.sub_limbwise_small_total(b);
        let sub_ba = b.sub_limbwise_small_total(a);
        (cmp, sub_ab, sub_ba)
    }

    pub fn lemma_cmp_neg_implies_asym_sub_ops(a: &Self, b: &Self) -> (i8, Self, Self) {
        let cmp = a.cmp_limbwise_small_total(b);
        let sub_ab = a.sub_limbwise_small_total(b);
        let sub_ba = b.sub_limbwise_small_total(a);
        (cmp, sub_ab, sub_ba)
    }

    pub fn lemma_model_add_sub_round_trip_ops(a: &Self, b: &Self) -> (Self, Self, Self) {
        let sum = a.add_limbwise_small_total(b);
        let sub_sum_b = sum.sub_limbwise_small_total(b);
        let sub_sum_a = sum.sub_limbwise_small_total(a);
        (sum, sub_sum_b, sub_sum_a)
    }

    pub fn lemma_model_div_monotonic_pos_ops(a: &Self, b: &Self, d: &Self) -> (Self, Self) {
        let div_a = a.div_limbwise_small_total(d);
        let div_b = b.div_limbwise_small_total(d);
        (div_a, div_b)
    }

    pub fn lemma_model_div_len_bound_pos_ops(a: &Self, d: &Self) -> Self {
        a.div_limbwise_small_total(d)
    }

    pub fn lemma_model_rem_upper_bound_pos_ops(a: &Self, d: &Self) -> Self {
        a.rem_limbwise_small_total(d)
    }

    pub fn lemma_model_rem_len_bound_pos_ops(a: &Self, d: &Self) -> Self {
        a.rem_limbwise_small_total(d)
    }

    pub fn lemma_model_mul_div_rem_cancel_pos_ops(a: &Self, d: &Self) -> (Self, Self, Self) {
        let prod = a.mul_limbwise_small_total(d);
        let q = prod.div_limbwise_small_total(d);
        let r = prod.rem_limbwise_small_total(d);
        (prod, q, r)
    }

    pub fn lemma_model_div_rem_recompose_pos_ops(a: &Self, d: &Self) -> (Self, Self) {
        a.div_rem_limbwise_small_total(d)
    }

    pub fn mul_limbwise_small_total(&self, rhs: &Self) -> Self {
        let mut acc = Self::zero();
        let mut shifted = self.copy_small_total();
        for &limb in &rhs.limbs_le {
            let term = shifted.mul_by_u32_total(limb);
            acc = acc.add_limbwise_small_total(&term);
            shifted = shifted.shift_base_once_total();
        }
        acc
    }

    pub fn div_limbwise_small_total(&self, rhs: &Self) -> Self {
        if rhs.is_zero() {
            return Self::zero();
        }
        if self.cmp_limbwise_small_total(rhs) < 0 {
            return Self::zero();
        }

        let one = Self::from_u32(1);
        let mut quotient = Self::zero();
        let mut remainder = self.copy_small_total();

        while remainder.cmp_limbwise_small_total(rhs) >= 0 {
            let mut chunk = rhs.copy_small_total();
            let mut chunk_q = one.copy_small_total();

            loop {
                let doubled_chunk = chunk.add_limbwise_small_total(&chunk);
                if remainder.cmp_limbwise_small_total(&doubled_chunk) < 0 {
                    break;
                }
                chunk = doubled_chunk;
                chunk_q = chunk_q.add_limbwise_small_total(&chunk_q);
            }

            remainder = remainder.sub_limbwise_small_total(&chunk);
            quotient = quotient.add_limbwise_small_total(&chunk_q);
        }

        quotient
    }

    pub fn rem_limbwise_small_total(&self, rhs: &Self) -> Self {
        if rhs.is_zero() {
            return Self::zero();
        }
        let quotient = self.div_limbwise_small_total(rhs);
        let product = quotient.mul_limbwise_small_total(rhs);
        self.sub_limbwise_small_total(&product)
    }

    pub fn div_rem_limbwise_small_total(&self, rhs: &Self) -> (Self, Self) {
        if rhs.is_zero() {
            return (Self::zero(), Self::zero());
        }
        let quotient = self.div_limbwise_small_total(rhs);
        let product = quotient.mul_limbwise_small_total(rhs);
        let remainder = self.sub_limbwise_small_total(&product);
        (quotient, remainder)
    }

    pub fn cmp_limbwise_small_total(&self, rhs: &Self) -> i8 {
        let alen = Self::trimmed_len(&self.limbs_le);
        let blen = Self::trimmed_len(&rhs.limbs_le);
        if alen > blen {
            return 1i8;
        }
        if alen < blen {
            return -1i8;
        }
        let mut i = alen;
        while i > 0 {
            let idx = i - 1;
            let a = self.limbs_le[idx];
            let b = rhs.limbs_le[idx];
            if a > b {
                return 1i8;
            }
            if a < b {
                return -1i8;
            }
            i -= 1;
        }
        0i8
    }

    pub fn sub_limbwise_small_total(&self, rhs: &Self) -> Self {
        if self.cmp_limbwise_small_total(rhs) <= 0 {
            return Self::zero();
        }
        let alen = Self::trimmed_len(&self.limbs_le);
        let blen = Self::trimmed_len(&rhs.limbs_le);
        let mut out_limbs: Vec<u32> = Vec::with_capacity(alen);
        let mut borrow: u64 = 0u64;
        let mut i: usize = 0;
        while i < alen {
            let a = self.limbs_le[i] as u64;
            let b = if i < blen {
                rhs.limbs_le[i] as u64
            } else {
                0u64
            };
            let need = b + borrow;
            if a >= need {
                out_limbs.push((a - need) as u32);
                borrow = 0u64;
            } else {
                out_limbs.push((LIMB_BASE + a - need) as u32);
                borrow = 1u64;
            }
            i += 1;
        }
        debug_assert_eq!(borrow, 0u64);
        Self::from_parts(out_limbs)
    }

    pub fn copy_small_total(&self) -> Self {
        Self::from_parts(self.limbs_le.clone())
    }

    pub fn is_zero(&self) -> bool {
        self.limbs_le.is_empty()
    }

    pub fn limbs_le(&self) -> &[u32] {
        &self.limbs_le
    }
}
