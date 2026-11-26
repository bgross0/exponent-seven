#!/usr/bin/env python3
"""Integer-interval certificate for the unsmoothed Haar bridge row.

The row is X=30000, Qmin=10**32, Qmax=2**135, v=[1,-1].
All mathematical arithmetic comes from the independently tested stdlib-only
interval implementation in ../zero-integer/verify.py. No Lean claim.
"""

from fractions import Fraction
from pathlib import Path
import json
import sys
import time

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "zero-integer"))
from verify import (Interval, SCALE, OUTPUT_SCALE, LOG2, constants, logarithm,
                    log_integer, primes_below, square_root)


def haar(t):
    """For 0<=t<=1, f(tL) = max(1-3t, t-1)."""
    first, second = 1 - 3*t, t - 1
    return Interval(max(first.lo, second.lo), max(first.hi, second.hi))


def overlap(a, b, c, d):
    return max(Fraction(), min(b, d) - max(a, c))


def check_kernel_shape():
    """Compare with the four exact interval overlaps defining autocorrelation."""
    zero, half, one = Fraction(), Fraction(1, 2), Fraction(1)
    for i in range(1001):
        t = Fraction(i, 1000)
        exact = (overlap(zero, half, -t, half-t)
                 + overlap(half, one, half-t, one-t)
                 - overlap(zero, half, half-t, one-t)
                 - overlap(half, one, -t, half-t))
        result = haar(Interval.rational(t.numerator, t.denominator))
        if not Fraction(result.lo, SCALE) <= exact <= Fraction(result.hi, SCALE):
            raise ArithmeticError(f"Haar autocorrelation check failed at {t}")
    # The only interior corner is also checked with an interval across it.
    eps = Fraction(1, 10**12)
    lower, upper = half-eps, half+eps
    interval = Interval(Interval.rational(lower.numerator, lower.denominator).lo,
                        Interval.rational(upper.numerator, upper.denominator).hi)
    value = haar(interval)
    for t in (lower, half, upper):
        exact = max(1-3*t, t-1)
        if not Fraction(value.lo, SCALE) <= exact <= Fraction(value.hi, SCALE):
            raise ArithmeticError("Haar corner enclosure failed")


def check():
    start = time.monotonic()
    X, Qmin, Qmax = 30000, 10**32, 2**135
    gate = 4 * X**7
    if not gate < Qmin <= Qmax:
        raise ValueError("invalid row bounds")
    check_kernel_shape()
    L = log_integer(X)
    pi, gamma = constants()
    P = Interval.exact(0)
    terms = 0
    for p in primes_below(X):
        lp = log_integer(p)
        n, k, sign = p, 1, -1
        while n < X:
            P = P + (2*sign*lp) * haar((k*lp)/L) / square_root(n)
            n, k, sign = n*p, k+1, -sign
            terms += 1
    J = 14 / (3*L)
    constant = logarithm(pi) + gamma - pi/2 + 3*LOG2
    logq = 135*LOG2
    margin = P - J + constant - logq
    if margin.lo <= 0:
        raise ArithmeticError(f"nonpositive bridge margin: {margin}")
    coarse_margin = P - 4 + constant - logq
    if L.lo < SCALE or coarse_margin.lo <= 0:
        raise ArithmeticError("the existing-Jplus coarse profile did not pass")
    return {
        "status": "positive outward integer interval; not a Lean theorem",
        "kernel": "autocorrelation of stepFn(log X, [1,-1])",
        "X": X, "Qmin": str(Qmin), "Qmax": str(Qmax),
        "gate_4_X_pow_7": str(gate),
        "gate_gap_Qmin_minus_4_X_pow_7": str(Qmin-gate),
        "prime_power_terms": terms,
        "arithmetic_scale": str(SCALE), "output_scale": OUTPUT_SCALE,
        "prime_sum": P.enclosure(),
        "J_upper_enclosure": J.enclosure(),
        "log_Qmax": logq.enclosure(),
        "log_pi_minus_psi_three_quarters": constant.enclosure(),
        "margin": margin.enclosure(),
        "coarse_Jplus_profile": {
            "J_upper_bound": 4,
            "required_log_X_lower_bound": 1,
            "log_X_enclosure": L.enclosure(),
            "margin": coarse_margin.enclosure(),
        },
        "kernel_reference_check": "1001 exact overlap evaluations and a straddling interval",
        "elapsed_seconds": round(time.monotonic()-start, 3),
    }


if __name__ == "__main__":
    print(json.dumps(check(), indent=2))
