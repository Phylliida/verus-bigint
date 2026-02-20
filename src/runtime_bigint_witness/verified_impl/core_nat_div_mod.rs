verus! {
impl RuntimeBigNatWitness {
    pub proof fn lemma_div_rem_unique_nat(x: nat, d: nat, q1: nat, r1: nat, q2: nat, r2: nat)
        requires
            d > 0,
            x == q1 * d + r1,
            r1 < d,
            x == q2 * d + r2,
            r2 < d,
        ensures
            q1 == q2,
            r1 == r2,
    {
        let xi = x as int;
        let di = d as int;
        let q1i = q1 as int;
        let r1i = r1 as int;
        let q2i = q2 as int;
        let r2i = r2 as int;

        assert(di != 0);
        assert(0 <= r1i < di);
        assert(0 <= r2i < di);
        assert(xi == q1i * di + r1i);
        assert(xi == q2i * di + r2i);

        lemma_fundamental_div_mod_converse(xi, di, q1i, r1i);
        lemma_fundamental_div_mod_converse(xi, di, q2i, r2i);
        assert(q1i == xi / di);
        assert(q2i == xi / di);
        assert(q1i == q2i);
        assert(r1i == xi % di);
        assert(r2i == xi % di);
        assert(r1i == r2i);
        assert(q1 == q2);
        assert(r1 == r2);
    }

    pub proof fn lemma_mod_zero_implies_multiple_nat(x: nat, d: nat) -> (k: nat)
        requires
            d > 0,
            x % d == 0,
        ensures
            x == k * d,
    {
        let xi = x as int;
        let di = d as int;
        lemma_fundamental_div_mod(xi, di);
        assert((x % d) as int == xi % di);
        assert(xi % di == 0);
        assert(xi == di * (xi / di) + xi % di);
        assert(xi == di * (xi / di));
        assert((x / d) as int == xi / di);
        assert(xi == di * ((x / d) as int));
        assert(di * ((x / d) as int) == ((x / d) as int) * di) by (nonlinear_arith);
        assert(xi == ((x / d) as int) * di);
        assert(x == (x / d) * d);
        let k = x / d;
        assert(x == k * d);
        k
    }

    pub proof fn lemma_multiple_implies_mod_zero_nat(x: nat, d: nat, k: nat)
        requires
            d > 0,
            x == k * d,
        ensures
            x % d == 0,
    {
        let xi = x as int;
        let di = d as int;
        let ki = k as int;
        assert(di != 0);
        assert(0 <= 0 < di);
        assert(xi == ki * di + 0);
        lemma_fundamental_div_mod_converse(xi, di, ki, 0);
        assert(xi % di == 0);
        assert((x % d) as int == xi % di);
        assert(x % d == 0);
    }

    pub proof fn lemma_div_rem_shift_by_multiple_nat(x: nat, d: nat, k: nat)
        requires
            d > 0,
        ensures
            (x + k * d) / d == x / d + k,
            (x + k * d) % d == x % d,
    {
        let xi = x as int;
        let di = d as int;
        let ki = k as int;
        let x_shift = x + k * d;
        let x_shift_i = x_shift as int;

        lemma_fundamental_div_mod(xi, di);
        let qi = xi / di;
        let ri = xi % di;
        assert((x / d) as int == qi);
        assert((x % d) as int == ri);
        assert(0 <= ri < di);

        assert(x_shift_i == xi + ki * di);
        assert(xi == di * (xi / di) + xi % di);
        assert(di * qi + ri == di * (xi / di) + xi % di);
        assert(di * qi == qi * di) by (nonlinear_arith);
        assert(xi == qi * di + ri);
        assert(x_shift_i == (qi * di + ri) + ki * di);
        assert((qi * di + ri) + ki * di == (qi + ki) * di + ri) by (nonlinear_arith);
        assert(x_shift_i == (qi + ki) * di + ri);
        lemma_fundamental_div_mod_converse(x_shift_i, di, qi + ki, ri);
        assert(x_shift_i / di == qi + ki);
        assert(x_shift_i % di == ri);

        assert((x_shift / d) as int == x_shift_i / di);
        assert((x_shift % d) as int == x_shift_i % di);
        assert((x / d + k) as int == (x / d) as int + k as int);
        assert((x / d + k) as int == qi + ki);
        assert((x_shift / d) as int == (x / d + k) as int);
        assert((x_shift % d) as int == (x % d) as int);
        assert(x_shift / d == x / d + k);
        assert(x_shift % d == x % d);
    }

    pub proof fn lemma_mul_div_rem_cancel_nat(a: nat, d: nat)
        requires
            d > 0,
        ensures
            (a * d) / d == a,
            (a * d) % d == 0,
    {
        let xi = (a * d) as int;
        let di = d as int;
        let ai = a as int;
        assert(di != 0);
        assert(0 <= 0 < di);
        assert(xi == ai * di + 0);
        lemma_fundamental_div_mod_converse(xi, di, ai, 0);
        assert(xi / di == ai);
        assert(xi % di == 0);
        assert(((a * d) / d) as int == xi / di);
        assert(((a * d) % d) as int == xi % di);
        assert(((a * d) / d) as int == a as int);
        assert((a * d) / d == a);
        assert((a * d) % d == 0);
    }

    pub proof fn lemma_div_add_bounds_nat(a: nat, b: nat, d: nat)
        requires
            d > 0,
        ensures
            a / d + b / d <= (a + b) / d,
            (a + b) / d <= a / d + b / d + 1,
    {
        let qa = a / d;
        let qb = b / d;
        let qsum = (a + b) / d;
        let ra = a % d;
        let rb = b % d;

        let ai = a as int;
        let bi = b as int;
        let di = d as int;
        let qai = qa as int;
        let qbi = qb as int;
        let qsi = qsum as int;
        let rai = ra as int;
        let rbi = rb as int;

        lemma_fundamental_div_mod(ai, di);
        lemma_fundamental_div_mod(bi, di);
        lemma_fundamental_div_mod((a + b) as int, di);

        assert(di > 0);
        assert(ai == di * qai + rai);
        assert(bi == di * qbi + rbi);
        assert(0 <= rai < di);
        assert(0 <= rbi < di);

        assert(a == qa * d + ra);
        assert(b == qb * d + rb);
        assert(a + b == (qa * d + ra) + (qb * d + rb));
        assert((qa * d + ra) + (qb * d + rb) == (qa + qb) * d + (ra + rb)) by (nonlinear_arith);
        assert(a + b == (qa + qb) * d + (ra + rb));

        assert(0 <= ra + rb);
        assert(ra + rb < d + d);
        let base = (qa + qb) * d;
        let li = (ra + rb) as int;
        let ri = (d + d) as int;
        let bi = base as int;
        assert(li < ri);
        assert(bi + li < bi + ri);
        assert((base + (ra + rb)) as int == bi + li);
        assert((base + (d + d)) as int == bi + ri);
        let lhs_i = (base + (ra + rb)) as int;
        let rhs_i = (base + (d + d)) as int;
        assert(lhs_i < rhs_i);
        assert(base + (ra + rb) < base + (d + d));
        assert(a + b < (qa + qb) * d + (d + d));
        assert((qa + qb) * d + (d + d) == (qa + qb + 2) * d) by (nonlinear_arith);
        assert(a + b < (qa + qb + 2) * d);

        assert(d * (qa + qb) == (qa + qb) * d) by (nonlinear_arith);
        assert((qa + qb) * d <= (qa + qb) * d + (ra + rb));
        assert((qa + qb) * d <= a + b);
        lemma_div_is_ordered((d * (qa + qb)) as int, (a + b) as int, di);
        assert(((d * (qa + qb)) as int) / di <= ((a + b) as int) / di);
        Self::lemma_mul_div_rem_cancel_nat(qa + qb, d);
        assert((d * (qa + qb)) / d == ((qa + qb) * d) / d);
        assert((d * (qa + qb)) / d == qa + qb);
        assert(((d * (qa + qb)) / d) as int == ((d * (qa + qb)) as int) / di);
        assert(((a + b) / d) as int == ((a + b) as int) / di);
        assert((qa + qb) as int <= ((a + b) / d) as int);
        assert(qa + qb <= (a + b) / d);

        lemma_multiply_divide_lt((a + b) as int, di, (qa + qb + 2) as int);
        assert(((a + b) as int) / di < (qa + qb + 2) as int);
        let qsum_i = ((a + b) / d) as int;
        let qbound_i = (qa + qb + 2) as int;
        assert(qsum_i < qbound_i);
        assert((a + b) / d < qa + qb + 2);
        if (a + b) / d > qa + qb + 1 {
            assert((a + b) / d >= qa + qb + 2);
            assert((a + b) / d < qa + qb + 2);
            assert(false);
        }
        assert((a + b) / d <= qa + qb + 1);
    }

    pub proof fn lemma_model_div_shift_by_multiple_pos(a: &Self, d: &Self, k: nat)
        requires
            a.wf_spec(),
            d.wf_spec(),
            d.model@ > 0,
        ensures
            (a.model@ + k * d.model@) / d.model@ == a.model@ / d.model@ + k,
    {
        Self::lemma_div_rem_shift_by_multiple_nat(a.model@, d.model@, k);
    }

    pub proof fn lemma_model_rem_shift_by_multiple_pos(a: &Self, d: &Self, k: nat)
        requires
            a.wf_spec(),
            d.wf_spec(),
            d.model@ > 0,
        ensures
            (a.model@ + k * d.model@) % d.model@ == a.model@ % d.model@,
    {
        Self::lemma_div_rem_shift_by_multiple_nat(a.model@, d.model@, k);
    }

    pub proof fn lemma_div_monotonic_in_divisor_nat(x: nat, d1: nat, d2: nat)
        requires
            d1 > 0,
            d1 <= d2,
        ensures
            x / d2 <= x / d1,
    {
        let xi = x as int;
        let d1i = d1 as int;
        let d2i = d2 as int;

        assert(0 <= xi);
        assert(0 < d1i);
        assert(d1i <= d2i);
        assert(1 <= d1i <= d2i);
        lemma_div_is_ordered_by_denominator(xi, d1i, d2i);
        assert(xi / d1i >= xi / d2i);
        assert((x / d1) as int == xi / d1i);
        assert((x / d2) as int == xi / d2i);
        assert((x / d1) as int >= (x / d2) as int);
        assert(x / d2 <= x / d1);
    }

    pub proof fn lemma_model_div_monotonic_in_divisor_pos(a: &Self, d1: &Self, d2: &Self)
        requires
            a.wf_spec(),
            d1.wf_spec(),
            d2.wf_spec(),
            0 < d1.model@ <= d2.model@,
        ensures
            a.model@ / d2.model@ <= a.model@ / d1.model@,
    {
        Self::lemma_div_monotonic_in_divisor_nat(a.model@, d1.model@, d2.model@);
    }

    pub proof fn lemma_mod_add_compat_nat(x: nat, y: nat, m: nat)
        requires
            m > 0,
        ensures
            (x + y) % m == ((x % m) + (y % m)) % m,
    {
        let xi = x as int;
        let yi = y as int;
        let mi = m as int;
        lemma_add_mod_noop(xi, yi, mi);
        assert((x % m) as int == xi % mi);
        assert((y % m) as int == yi % mi);
        assert(((x + y) % m) as int == (xi + yi) % mi);
        assert((((x % m) + (y % m)) % m) as int == ((xi % mi) + (yi % mi)) % mi);
        assert(((xi % mi) + (yi % mi)) % mi == (xi + yi) % mi);
        assert((((x % m) + (y % m)) % m) as int == ((x + y) % m) as int);
        assert((x + y) % m == ((x % m) + (y % m)) % m);
    }

    pub proof fn lemma_model_add_mod_compat(a: &Self, b: &Self, m: &Self)
        requires
            a.wf_spec(),
            b.wf_spec(),
            m.wf_spec(),
            m.model@ > 0,
        ensures
            (a.model@ + b.model@) % m.model@
                == ((a.model@ % m.model@) + (b.model@ % m.model@)) % m.model@,
    {
        Self::lemma_mod_add_compat_nat(a.model@, b.model@, m.model@);
    }

    pub proof fn lemma_mod_mul_compat_nat(x: nat, y: nat, m: nat)
        requires
            m > 0,
        ensures
            (x * y) % m == ((x % m) * (y % m)) % m,
    {
        let xi = x as int;
        let yi = y as int;
        let mi = m as int;
        lemma_mul_mod_noop(xi, yi, mi);
        assert((x % m) as int == xi % mi);
        assert((y % m) as int == yi % mi);
        assert(((x * y) % m) as int == (xi * yi) % mi);
        assert((((x % m) * (y % m)) % m) as int == (((xi % mi) * (yi % mi)) % mi));
        assert((((xi % mi) * (yi % mi)) % mi) == (xi * yi) % mi);
        assert((((x % m) * (y % m)) % m) as int == ((x * y) % m) as int);
        assert((x * y) % m == ((x % m) * (y % m)) % m);
    }

    pub proof fn lemma_model_mul_mod_compat(a: &Self, b: &Self, m: &Self)
        requires
            a.wf_spec(),
            b.wf_spec(),
            m.wf_spec(),
            m.model@ > 0,
        ensures
            (a.model@ * b.model@) % m.model@
                == ((a.model@ % m.model@) * (b.model@ % m.model@)) % m.model@,
    {
        Self::lemma_mod_mul_compat_nat(a.model@, b.model@, m.model@);
    }

    pub proof fn lemma_mod_congruence_add_nat(a: nat, b: nat, c: nat, m: nat)
        requires
            m > 0,
            a % m == b % m,
        ensures
            (a + c) % m == (b + c) % m,
    {
        Self::lemma_mod_add_compat_nat(a, c, m);
        Self::lemma_mod_add_compat_nat(b, c, m);
        assert((a + c) % m == ((a % m) + (c % m)) % m);
        assert((b + c) % m == ((b % m) + (c % m)) % m);
        assert(((a % m) + (c % m)) % m == ((b % m) + (c % m)) % m);
        assert((a + c) % m == (b + c) % m);
    }

    pub proof fn lemma_model_mod_congruence_add(a: &Self, b: &Self, c: &Self, m: &Self)
        requires
            a.wf_spec(),
            b.wf_spec(),
            c.wf_spec(),
            m.wf_spec(),
            m.model@ > 0,
            a.model@ % m.model@ == b.model@ % m.model@,
        ensures
            (a.model@ + c.model@) % m.model@ == (b.model@ + c.model@) % m.model@,
    {
        Self::lemma_mod_congruence_add_nat(a.model@, b.model@, c.model@, m.model@);
    }

    pub proof fn lemma_mod_congruence_mul_nat(a: nat, b: nat, c: nat, m: nat)
        requires
            m > 0,
            a % m == b % m,
        ensures
            (a * c) % m == (b * c) % m,
    {
        Self::lemma_mod_mul_compat_nat(a, c, m);
        Self::lemma_mod_mul_compat_nat(b, c, m);
        assert((a * c) % m == ((a % m) * (c % m)) % m);
        assert((b * c) % m == ((b % m) * (c % m)) % m);
        assert(((a % m) * (c % m)) % m == ((b % m) * (c % m)) % m);
        assert((a * c) % m == (b * c) % m);
    }

    pub proof fn lemma_model_mod_congruence_mul(a: &Self, b: &Self, c: &Self, m: &Self)
        requires
            a.wf_spec(),
            b.wf_spec(),
            c.wf_spec(),
            m.wf_spec(),
            m.model@ > 0,
            a.model@ % m.model@ == b.model@ % m.model@,
        ensures
            (a.model@ * c.model@) % m.model@ == (b.model@ * c.model@) % m.model@,
    {
        Self::lemma_mod_congruence_mul_nat(a.model@, b.model@, c.model@, m.model@);
    }
}
}
