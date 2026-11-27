#!/usr/bin/env python3
"""Rational interval certificate that L(E433.a1 twisted by -71, 1) is positive.

Standard library only; no floating-point arithmetic enters the certificate.
The analytical interpretation uses modularity/Fricke functional equation and
Hasse's coefficient bound, explained in README.md. This is not a Lean proof.
"""

from __future__ import annotations

import argparse
from fractions import Fraction
import hashlib
import json
from math import isqrt
from pathlib import Path

# Adapted from eligibility/arithmetic/check_twist_lvalue.py for the distinct
# curve433a1. The reduction formula, bad prime, twist model and conductor
# below are independently screened in screen.py; no rational points are used.

TERMS = 6000
D = -71
N = 433 * 71**2
SCALE = 10**40


def floor_fraction(value):
    return value.numerator // value.denominator


def ceil_fraction(value):
    return -((-value.numerator) // value.denominator)


def ceil_div(a, b):
    assert b > 0
    return -((-a) // b)


def encode_fraction(value):
    return {"numerator": str(value.numerator), "denominator": str(value.denominator)}


def fixed_decimal(value):
    sign = "-" if value < 0 else ""
    value = abs(value)
    return f"{sign}{value // SCALE}.{value % SCALE:040d}"


def atan_reciprocal_bounds(q, terms=40):
    assert q > 1
    total = sum((Fraction((-1) ** k, (2 * k + 1) * q ** (2 * k + 1)) for k in range(terms)), Fraction(0))
    remainder = Fraction(1, (2 * terms + 1) * q ** (2 * terms + 1))
    return (total, total + remainder) if terms % 2 == 0 else (total - remainder, total)


def exp_minus_bounds(x, terms=20):
    """Alternating Taylor bound for 0<x<1; rational endpoints only."""
    assert 0 < x < 1 and terms % 2 == 0
    total = Fraction(0)
    term = Fraction(1)
    for k in range(terms):
        total += (-1) ** k * term
        term *= x / (k + 1)
    return total, total + term


def exponential_base_bounds():
    a5lo, a5hi = atan_reciprocal_bounds(5)
    a239lo, a239hi = atan_reciprocal_bounds(239)
    # Machin's exact identity: pi=16*atan(1/5)-4*atan(1/239).
    pi_lo, pi_hi = 16 * a5lo - 4 * a239hi, 16 * a5hi - 4 * a239lo
    assert 3 < pi_lo < pi_hi < 4
    root_integer = isqrt(N * SCALE**2)
    assert root_integer**2 < N * SCALE**2 < (root_integer + 1) ** 2
    sqrt_lo = Fraction(root_integer, SCALE)
    sqrt_hi = Fraction(root_integer + 1, SCALE)
    c_lo, c_hi = 2 * pi_lo / sqrt_hi, 2 * pi_hi / sqrt_lo
    r_lower = exp_minus_bounds(c_hi)[0]
    r_upper = exp_minus_bounds(c_lo)[1]
    lo = floor_fraction(r_lower * SCALE)
    hi = ceil_fraction(r_upper * SCALE)
    assert 0 < lo < hi < SCALE
    return lo, hi, {
        "pi_identity": "pi=16*atan(1/5)-4*atan(1/239)",
        "arctangent_terms_each": 40,
        "pi_bounds": [encode_fraction(pi_lo), encode_fraction(pi_hi)],
        "sqrt_N_integer_bound_scaled": [str(root_integer), str(root_integer + 1)],
        "exp_minus_taylor_terms": 20,
        "r_definition": "exp(-2*pi/sqrt(N))",
        "r_scaled_bounds": [str(lo), str(hi)],
    }


def legendre(n, p):
    r = pow(n % p, (p - 1) // 2, p)
    return -1 if r == p - 1 else r


def coefficients(bound):
    smallest = list(range(bound + 1))
    primes = []
    for p in range(2, bound + 1):
        if smallest[p] == p:
            primes.append(p)
            for k in range(p * p, bound + 1, p):
                if smallest[k] == k:
                    smallest[k] = p
    ap = {}
    for p in primes:
        if p == 433:
            # Split multiplicative reduction: a_433=+1.
            ap[p] = 1
        elif p == 2:
            ap[p] = 3 - (1 + sum((y * y + x*y - x**3 - 1) % 2 == 0 for x in range(2) for y in range(2)))
        else:
            # For fixed x, 1+Legendre(x^2+4*x^3+4,p) solutions y.
            ap[p] = -sum(legendre(x*x + 4*x**3 + 4, p) for x in range(p))
        if p != 433:
            assert ap[p] ** 2 <= 4 * p
    an = [0] * (bound + 1)
    an[1] = 1
    for n in range(2, bound + 1):
        p = smallest[n]
        m = n // p
        if m % p or p == 433:
            an[n] = ap[p] * an[m]
        else:
            an[n] = ap[p] * an[m] - p * an[m // p]
    twisted = [a * legendre(n, 71) for n, a in enumerate(an)]
    assert all(abs(a) <= 2 * n for n, a in enumerate(twisted))
    return ap, twisted


def invariants(ainvs):
    a1, a2, a3, a4, a6 = ainvs
    b2, b4, b6 = a1 * a1 + 4 * a2, 2 * a4 + a1 * a3, a3 * a3 + 4 * a6
    b8 = a1 * a1 * a6 + 4 * a2 * a6 - a1 * a3 * a4 + a2 * a3 * a3 - a4 * a4
    c4, c6 = b2 * b2 - 24 * b4, -b2**3 + 36 * b2 * b4 - 216 * b6
    delta = -b2 * b2 * b8 - 8 * b4**3 - 27 * b6 * b6 + 9 * b2 * b4 * b6
    assert c4**3 - c6**2 == 1728 * delta
    return c4, c6, delta


def certificate():
    twist_model = [1, -18, 0, 0, -357911]
    c4, c6, delta = invariants(twist_model)
    assert (c4, c6, delta) == (D**2, -865 * D**3, -433 * D**6)
    assert N == 2182753 and legendre(-433, 71) == 1
    lo, hi, transcendental = exponential_base_bounds()
    ap, an = coefficients(TERMS)
    power_lo = power_hi = SCALE
    sum_lo = sum_hi = 0
    for n in range(1, TERMS + 1):
        power_lo = power_lo * lo // SCALE
        power_hi = ceil_div(power_hi * hi, SCALE)
        coefficient = 2 * an[n]
        if coefficient >= 0:
            sum_lo += coefficient * power_lo // n
            sum_hi += ceil_div(coefficient * power_hi, n)
        else:
            sum_lo += coefficient * power_hi // n
            sum_hi += ceil_div(coefficient * power_lo, n)
    next_power_hi = ceil_div(power_hi * hi, SCALE)
    # |a_n|<=d(n)*sqrt(n)<=2*n, so the omitted central-series tail is
    # at most 4*r^(TERMS+1)/(1-r). All rounding here is outwards.
    tail_scaled = ceil_div(4 * next_power_hi * SCALE, SCALE - hi)
    result_lo, result_hi = sum_lo - tail_scaled, sum_hi + tail_scaled
    assert 0 < result_lo < result_hi
    coefficients_digest = hashlib.sha256(json.dumps(an, separators=(",", ":")).encode()).hexdigest()
    return {
        "format": "bsd-second-pilot-twist-lvalue-interval-v1",
        "status": "Exact rational arithmetic completed; mathematical interpretation uses the standard analytic theorems listed below, not Lean kernel checking.",
        "base_curve": "433.a1",
        "twist_discriminant": D,
        "twist_integral_model": twist_model,
        "twist_invariants": {"c4": c4, "c6": c6, "discriminant": delta},
        "conductor": N,
        "conductor_explanation": "Good away from71,433; quadratic twist of good reduction has I_0* and conductor exponent2 at71; multiplicative reduction has conductor exponent1 at433. The displayed discriminant valuations6,1 ensure minimality.",
        "root_number": 1,
        "root_number_explanation": "w(E)=(-1 at infinity)*(-1 at split multiplicative433)=+1; w(E^D)=w(E)*chi_D(-433)=+1, since gcd(D,433)=1.",
        "twisting_character": "chi_-71(n)=Legendre(n,71), including0 at multiples of71",
        "analytic_identity": "L(E^D,1)=2*sum(n>=1,a_n(E^D)*exp(-2*pi*n/sqrt(N))/n)",
        "analytic_inputs": [
            "Modularity of the rational elliptic curve, with the stated conductor and Fricke sign+1.",
            "Mellin transform and Fricke functional equation at the arithmetic center1.",
            "Hasse/Frobenius bounds and Euler-factor multiplicativity: |a_n|<=d(n)*sqrt(n)<=2*n.",
            "Machin's arctangent identity and alternating-series remainder bounds.",
        ],
        "terms": TERMS,
        "scale": str(SCALE),
        "transcendental_bounds": transcendental,
        "finite_sum_scaled_bounds": [str(sum_lo), str(sum_hi)],
        "finite_sum_decimal_bounds": [fixed_decimal(sum_lo), fixed_decimal(sum_hi)],
        "tail_bound_formula": "4*r^(terms+1)/(1-r)",
        "tail_scaled_upper_bound": str(tail_scaled),
        "tail_decimal_upper_bound": fixed_decimal(tail_scaled),
        "central_L_scaled_bounds": [str(result_lo), str(result_hi)],
        "central_L_decimal_bounds": [fixed_decimal(result_lo), fixed_decimal(result_hi)],
        "positive_lower_bound": result_lo > 0,
        "coefficient_count_including_a0": len(an),
        "coefficients_canonical_json_sha256": coefficients_digest,
        "prime_traces_base_curve": [[p, a] for p, a in ap.items()],
        "twisted_coefficients_a0_through_a6000": an,
        "does_not_establish": [
            "Nonvanishing of L(E/K,chi,1) for a chosen nontrivial ring-class character.",
            "A rank upper bound, localization injectivity, a generalized Kato class, or any BSD formula.",
            "A Lean formalization of the analytic identity or its interval evaluation.",
        ],
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--check", type=Path)
    args = parser.parse_args()
    data = certificate()
    if args.check:
        assert json.loads(args.check.read_text()) == data, "Certificate differs from fresh exact recomputation"
        print(f"PASS: exact rational recomputation agrees with {args.check}")
    elif args.output:
        args.output.write_text(json.dumps(data, indent=2, sort_keys=True) + "\n")
        print(f"Wrote {args.output}")
        print("L(E^(-71),1) lies in [" + ", ".join(data["central_L_decimal_bounds"]) + "]")
    else:
        print(json.dumps(data, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
