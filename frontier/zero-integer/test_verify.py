"""Finite differential checks against exact Fraction arithmetic.

These tests guard implementation mistakes. The analytic remainder arguments
are documented separately; tests cannot replace those arguments.
"""
from fractions import Fraction as F
from random import Random
import unittest

import verify as v


def contains(interval, x):
    return F(interval.lo, v.SCALE) <= x <= F(interval.hi, v.SCALE)


def log_ratio_reference(n, d, terms=80):
    z = F(n - d, n + d)
    total = 2 * sum((z**(2*j+1) / (2*j+1) for j in range(terms)), F())
    tail = 2 * z**(2*terms+1) / ((2*terms+1) * (1-z*z))
    return total, total + tail


class VerificationTests(unittest.TestCase):
    def test_interval_arithmetic_exact_corners(self):
        rng = Random(731203)
        for _ in range(600):
            aa = sorted((rng.randrange(-1000, 1000), rng.randrange(-1000, 1000)))
            bb = sorted((rng.randrange(-1000, 1000), rng.randrange(-1000, 1000)))
            da, db = rng.randrange(1, 1000), rng.randrange(1, 1000)
            a = v.Interval(v.Interval.rational(aa[0], da).lo,
                           v.Interval.rational(aa[1], da).hi)
            b = v.Interval(v.Interval.rational(bb[0], db).lo,
                           v.Interval.rational(bb[1], db).hi)
            xs = [F(a.lo, v.SCALE), F(a.hi, v.SCALE),
                  F(a.lo + a.hi, 2*v.SCALE)]
            ys = [F(b.lo, v.SCALE), F(b.hi, v.SCALE),
                  F(b.lo + b.hi, 2*v.SCALE)]
            for x in xs:
                self.assertTrue(contains(a.square(), x*x))
                for y in ys:
                    self.assertTrue(contains(a+b, x+y))
                    self.assertTrue(contains(a-b, x-y))
                    self.assertTrue(contains(a*b, x*y))
                    if b.lo > 0 or b.hi < 0:
                        self.assertTrue(contains(a/b, x/y))

    def test_log_against_long_exact_series(self):
        rng = Random(90117)
        for n in [1, 2, 3, 19, 19000, 10**32, 10**162] + [rng.randrange(1, 1000000) for _ in range(30)]:
            k = n.bit_length() - 1
            l0, u0 = log_ratio_reference(2, 1)
            l1, u1 = log_ratio_reference(n, 1 << k)
            result = v.log_integer(n)
            self.assertTrue(contains(result, k*l0+l1))
            self.assertTrue(contains(result, k*u0+u1))
        for n in range(1, 100):
            self.assertLess(v.log_integer(n).hi, v.log_integer(n+1).lo)

    def test_square_root_integer_inequalities(self):
        for n in [0, 1, 2, 3, 4, 19000, 1000000, 10**162]:
            r = v.square_root(n)
            self.assertLessEqual(r.lo*r.lo, n*v.SCALE*v.SCALE)
            self.assertGreaterEqual(r.hi*r.hi, n*v.SCALE*v.SCALE)

    def test_exp_against_exact_series(self):
        for x in [F(0), F(1, 100), F(1, 2), F(1), F(3), F(7)]:
            term = total = F(1)
            for k in range(1, 121):
                term *= x/k
                total += term
            next_term = term*x/121
            upper = total + next_term/(1-x/122)
            z = v.exponential(v.Interval.rational(x.numerator, x.denominator))
            self.assertTrue(contains(z, total))
            self.assertTrue(contains(z, upper))
            negative = v.exponential(-v.Interval.rational(x.numerator, x.denominator))
            self.assertTrue(contains(negative, 1/total))
            self.assertTrue(contains(negative, 1/upper))

    def test_prime_sieve_against_trial_division(self):
        expected = [n for n in range(2, 5000)
                    if all(n % d for d in range(2, v.isqrt(n)+1))]
        self.assertEqual(v.primes_below(5000), expected)
        self.assertEqual(v.primes_below(2), [])

    def test_polynomial_compilation_against_truncated_cubes(self):
        points = set(v.BREAKS)
        points.update(F(i, 1000) for i in range(1001))
        for t in points:
            exact = v.f_fraction(t)
            z = v.test_function(v.Interval.rational(t.numerator, t.denominator))
            self.assertTrue(contains(z, exact), (t, z, exact))
        self.assertEqual(v.f_fraction(F(0)), 1)
        self.assertEqual(v.f_fraction(F(1)), 0)
        # Explicitly straddle every piece boundary with a true interval.
        for t in v.BREAKS[1:-1]:
            eps = F(1, 10**12)
            z = v.Interval(v.Interval.rational((t-eps).numerator, (t-eps).denominator).lo,
                           v.Interval.rational((t+eps).numerator, (t+eps).denominator).hi)
            for x in (t-eps, t, t+eps):
                self.assertTrue(contains(v.test_function(z), v.f_fraction(x)))

    def test_gamma_bound_coefficients_and_constants(self):
        # For y=1/(2n+1), A_{n+1}-A_n has coefficient 4j/(2j+1)
        # while (n^-2-(n+1)^-2)/12 has coefficient 4j/3.
        for j in range(1, 100):
            self.assertLessEqual(F(4*j, 2*j+1), F(4*j, 3))
        pi, gamma = v.constants()
        self.assertTrue(pi.lo > 3*v.SCALE and pi.hi < 4*v.SCALE)
        self.assertTrue(gamma.lo > 0 and gamma.hi < v.SCALE)
        self.assertLess(gamma.hi-gamma.lo, v.SCALE//10**9)


if __name__ == "__main__":
    unittest.main()
