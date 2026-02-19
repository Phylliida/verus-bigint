use super::RuntimeBigNatWitness;
#[cfg(all(feature = "rug-oracle", not(verus_keep_ghost)))]
use rug::Integer;

fn assert_limbs(x: &RuntimeBigNatWitness, expected: &[u32]) {
    assert_eq!(x.limbs_le(), expected);
}

#[test]
fn basic_runtime_big_nat_ops() {
    let a = RuntimeBigNatWitness::from_u32(7);
    let b = RuntimeBigNatWitness::from_u32(9);
    let sum = a.add(&b);
    let prod = a.mul(&b);
    let quot = b.div(&a);
    let rem = b.rem(&a);
    let (q_pair, r_pair) = b.div_rem(&a);
    let small_sum = a.add_limbwise_small(&b);
    let two_limbs = RuntimeBigNatWitness::from_two_limbs(5, 3);
    assert_limbs(&sum, &[16]);
    assert_limbs(&small_sum, &[16]);
    assert_limbs(&prod, &[63]);
    assert_limbs(&quot, &[1]);
    assert_limbs(&rem, &[2]);
    assert_limbs(&q_pair, &[1]);
    assert_limbs(&r_pair, &[2]);
    assert_limbs(&two_limbs, &[5, 3]);
    assert!(!sum.is_zero());
    assert!(RuntimeBigNatWitness::zero().is_zero());
}

#[test]
fn add_and_mul_cross_limb_carry() {
    let a = RuntimeBigNatWitness::from_two_limbs(u32::MAX, u32::MAX);
    let one = RuntimeBigNatWitness::from_u32(1);
    let two = RuntimeBigNatWitness::from_u32(2);

    let sum = a.add_limbwise_small_total(&one);
    assert_limbs(&sum, &[0, 0, 1]);

    let prod = a.mul_limbwise_small_total(&two);
    assert_limbs(&prod, &[u32::MAX - 1, u32::MAX, 1]);
}

#[test]
fn cmp_and_sub_total_behavior() {
    let base = RuntimeBigNatWitness::from_two_limbs(0, 1);
    let one = RuntimeBigNatWitness::from_u32(1);

    assert_eq!(base.cmp_limbwise_small_total(&one), 1);
    assert_eq!(one.cmp_limbwise_small_total(&base), -1);
    assert_eq!(one.cmp_limbwise_small_total(&one), 0);

    let diff = base.sub_limbwise_small_total(&one);
    assert_limbs(&diff, &[u32::MAX]);

    let non_negative_floor = one.sub_limbwise_small_total(&base);
    assert_limbs(&non_negative_floor, &[]);
}

#[test]
fn div_total_behavior() {
    let sixty_three = RuntimeBigNatWitness::from_u32(63);
    let nine = RuntimeBigNatWitness::from_u32(9);
    let seven = sixty_three.div_limbwise_small_total(&nine);
    let zero_rem = sixty_three.rem_limbwise_small_total(&nine);
    assert_limbs(&seven, &[7]);
    assert_limbs(&zero_rem, &[]);

    let hundred = RuntimeBigNatWitness::from_u32(100);
    let three = RuntimeBigNatWitness::from_u32(3);
    let thirty_three = hundred.div(&three);
    let one = hundred.rem(&three);
    let (q_pair, r_pair) = hundred.div_rem(&three);
    assert_limbs(&thirty_three, &[33]);
    assert_limbs(&one, &[1]);
    assert_limbs(&q_pair, &[33]);
    assert_limbs(&r_pair, &[1]);

    let two_pow_32 = RuntimeBigNatWitness::from_two_limbs(0, 1);
    let two_pow_31 = RuntimeBigNatWitness::from_u32(1u32 << 31);
    let two = two_pow_32.div(&two_pow_31);
    let zero_rem_2 = two_pow_32.rem(&two_pow_31);
    assert_limbs(&two, &[2]);
    assert_limbs(&zero_rem_2, &[]);

    let one = RuntimeBigNatWitness::from_u32(1);
    let big = RuntimeBigNatWitness::from_two_limbs(0, 1);
    let zero_when_smaller = one.div(&big);
    let rem_when_smaller = one.rem(&big);
    assert_limbs(&zero_when_smaller, &[]);
    assert_limbs(&rem_when_smaller, &[1]);

    let zero_divisor = RuntimeBigNatWitness::zero();
    let zero_on_divide_by_zero = big.div(&zero_divisor);
    let zero_on_rem_by_zero = big.rem(&zero_divisor);
    let (zero_div_q, zero_div_r) = big.div_rem(&zero_divisor);
    assert_limbs(&zero_on_divide_by_zero, &[]);
    assert_limbs(&zero_on_rem_by_zero, &[]);
    assert_limbs(&zero_div_q, &[]);
    assert_limbs(&zero_div_r, &[]);
}

#[test]
fn constructors_canonicalize_zero() {
    let z0 = RuntimeBigNatWitness::from_u32(0);
    let z1 = RuntimeBigNatWitness::from_u64(0);
    let z2 = RuntimeBigNatWitness::from_two_limbs(0, 0);
    assert_limbs(&z0, &[]);
    assert_limbs(&z1, &[]);
    assert_limbs(&z2, &[]);
}

#[cfg(all(feature = "rug-oracle", not(verus_keep_ghost)))]
fn witness_from_canonical_limbs(mut limbs_le: Vec<u32>) -> RuntimeBigNatWitness {
    while limbs_le.last().copied() == Some(0) {
        limbs_le.pop();
    }
    RuntimeBigNatWitness { limbs_le }
}

#[cfg(all(feature = "rug-oracle", not(verus_keep_ghost)))]
fn witness_to_integer(x: &RuntimeBigNatWitness) -> Integer {
    let mut out = Integer::from(0);
    for &limb in x.limbs_le().iter().rev() {
        out <<= 32;
        out += limb;
    }
    out
}

#[cfg(all(feature = "rug-oracle", not(verus_keep_ghost)))]
fn integer_to_limbs_le(value: &Integer) -> Vec<u32> {
    if value == &0 {
        return Vec::new();
    }

    let mut n = value.clone();
    let mut out = Vec::new();
    while n != 0 {
        out.push(n.to_u32_wrapping());
        n >>= 32;
    }
    out
}

#[cfg(all(feature = "rug-oracle", not(verus_keep_ghost)))]
fn integer_cmp_i8(a: &Integer, b: &Integer) -> i8 {
    if a < b {
        -1
    } else if a > b {
        1
    } else {
        0
    }
}

#[cfg(all(feature = "rug-oracle", not(verus_keep_ghost)))]
fn assert_pair_matches_oracle(a: &RuntimeBigNatWitness, b: &RuntimeBigNatWitness) {
    let a_oracle = witness_to_integer(a);
    let b_oracle = witness_to_integer(b);

    let add_expected = Integer::from(&a_oracle + &b_oracle);
    let add_expected_limbs = integer_to_limbs_le(&add_expected);
    let add = a.add(b);
    let add_total = a.add_limbwise_small_total(b);
    assert_eq!(add.limbs_le(), add_expected_limbs.as_slice());
    assert_eq!(add_total.limbs_le(), add_expected_limbs.as_slice());

    let mul_expected = Integer::from(&a_oracle * &b_oracle);
    let mul_expected_limbs = integer_to_limbs_le(&mul_expected);
    let mul = a.mul(b);
    let mul_total = a.mul_limbwise_small_total(b);
    assert_eq!(mul.limbs_le(), mul_expected_limbs.as_slice());
    assert_eq!(mul_total.limbs_le(), mul_expected_limbs.as_slice());

    let cmp_expected = integer_cmp_i8(&a_oracle, &b_oracle);
    assert_eq!(a.cmp_limbwise_small_total(b), cmp_expected);

    let sub_expected = if a_oracle > b_oracle {
        Integer::from(&a_oracle - &b_oracle)
    } else {
        Integer::from(0)
    };
    let sub_expected_limbs = integer_to_limbs_le(&sub_expected);
    let sub = a.sub_limbwise_small_total(b);
    assert_eq!(sub.limbs_le(), sub_expected_limbs.as_slice());

    let div_expected = if b_oracle == 0 {
        Integer::from(0)
    } else {
        Integer::from(&a_oracle / &b_oracle)
    };
    let div_expected_limbs = integer_to_limbs_le(&div_expected);
    let div = a.div(b);
    let div_total = a.div_limbwise_small_total(b);
    assert_eq!(div.limbs_le(), div_expected_limbs.as_slice());
    assert_eq!(div_total.limbs_le(), div_expected_limbs.as_slice());

    let rem_expected = if b_oracle == 0 {
        Integer::from(0)
    } else {
        Integer::from(&a_oracle % &b_oracle)
    };
    let rem_expected_limbs = integer_to_limbs_le(&rem_expected);
    let rem = a.rem(b);
    let rem_total = a.rem_limbwise_small_total(b);
    assert_eq!(rem.limbs_le(), rem_expected_limbs.as_slice());
    assert_eq!(rem_total.limbs_le(), rem_expected_limbs.as_slice());

    let (div_rem_q, div_rem_r) = a.div_rem(b);
    let (div_rem_q_total, div_rem_r_total) = a.div_rem_limbwise_small_total(b);
    assert_eq!(div_rem_q.limbs_le(), div_expected_limbs.as_slice());
    assert_eq!(div_rem_q_total.limbs_le(), div_expected_limbs.as_slice());
    assert_eq!(div_rem_r.limbs_le(), rem_expected_limbs.as_slice());
    assert_eq!(div_rem_r_total.limbs_le(), rem_expected_limbs.as_slice());
}

#[cfg(all(feature = "rug-oracle", not(verus_keep_ghost)))]
fn xorshift64(state: &mut u64) -> u64 {
    let mut x = *state;
    x ^= x << 13;
    x ^= x >> 7;
    x ^= x << 17;
    *state = x;
    x
}

#[cfg(all(feature = "rug-oracle", not(verus_keep_ghost)))]
fn random_limbs(state: &mut u64) -> Vec<u32> {
    let len = (xorshift64(state) % 7) as usize;
    let mut limbs = Vec::with_capacity(len);
    for _ in 0..len {
        limbs.push(xorshift64(state) as u32);
    }
    if !limbs.is_empty() && (xorshift64(state) & 1) == 0 {
        let last = limbs.len() - 1;
        limbs[last] = 0;
    }
    limbs
}

#[test]
#[cfg(all(feature = "rug-oracle", not(verus_keep_ghost)))]
fn oracle_differential_fixed_vectors() {
    let vectors = vec![
        (vec![], vec![]),
        (vec![0], vec![0]),
        (vec![1], vec![]),
        (vec![u32::MAX], vec![1]),
        (vec![0, 1], vec![u32::MAX]),
        (vec![u32::MAX, u32::MAX], vec![u32::MAX, u32::MAX]),
        (vec![1, 2, 3, 4], vec![5, 6, 7]),
        (vec![0, 0, 42, 0, 0], vec![u32::MAX, 1, 0]),
        (vec![u32::MAX, 0, u32::MAX, 1], vec![1, 1, 1, 1]),
    ];

    for (a_limbs, b_limbs) in vectors {
        let a = witness_from_canonical_limbs(a_limbs);
        let b = witness_from_canonical_limbs(b_limbs);
        assert_pair_matches_oracle(&a, &b);
        assert_pair_matches_oracle(&b, &a);
    }
}

#[test]
#[cfg(all(feature = "rug-oracle", not(verus_keep_ghost)))]
fn oracle_differential_pseudorandom_pairs() {
    let mut state = 0xD0E0_CAFE_F00D_BAADu64;
    for _ in 0..256 {
        let a = witness_from_canonical_limbs(random_limbs(&mut state));
        let b = witness_from_canonical_limbs(random_limbs(&mut state));
        assert_pair_matches_oracle(&a, &b);
    }
}
