#!/usr/bin/env python3
"""Exact finite arithmetic for E389.a1, K=Q(sqrt(-71)), p=29.

Python standard library only. The output is an arithmetic certificate, not a
Lean proof of the Galois, reduction, or class-number interpretation theorems.
Run without arguments to print JSON; --output writes it; --check recomputes it.
"""

from __future__ import annotations

import argparse
from fractions import Fraction
import json
from math import gcd, isqrt
from pathlib import Path

AINVS = (0, 1, 1, -2, 0)


def is_prime(n: int) -> bool:
    return n >= 2 and all(n % d for d in range(2, isqrt(n) + 1))


def on_curve(point, modulus=None):
    if point is None:
        return True
    x, y = point
    value = y * y + y - x**3 - x * x + 2 * x
    return value % modulus == 0 if modulus else value == 0


def add_points(left, right, modulus=None):
    """Chord/tangent law for y^2+y=x^3+x^2-2x; None means infinity."""
    if left is None:
        return right
    if right is None:
        return left
    x, y = left
    u, v = right
    if x == u and ((y + v + 1) % modulus == 0 if modulus else y + v + 1 == 0):
        return None

    def divide(a, b):
        return a * pow(b, -1, modulus) % modulus if modulus else Fraction(a, b)

    if left == right:
        slope = divide(3 * x * x + 2 * x - 2, 2 * y + 1)
    else:
        slope = divide(v - y, u - x)
    x3 = slope * slope - 1 - x - u
    y3 = -slope * (x3 - x) - y - 1
    result = (x3 % modulus, y3 % modulus) if modulus else (x3, y3)
    assert on_curve(result, modulus)
    return result


def multiply(n, point, modulus=None):
    assert n >= 0 and on_curve(point, modulus)
    result = None
    while n:
        if n & 1:
            result = add_points(result, point, modulus)
        point = add_points(point, point, modulus)
        n >>= 1
    return result


def finite_points(ell):
    assert is_prime(ell) and 389 % ell
    return [None] + [
        (x, y) for x in range(ell) for y in range(ell) if on_curve((x, y), ell)
    ]


def encode_point(point):
    return "O" if point is None else list(point)


def encode_fraction(value):
    value = Fraction(value)
    return {"numerator": str(value.numerator), "denominator": str(value.denominator)}


def legendre(a, ell):
    assert is_prime(ell) and ell > 2
    residue = pow(a % ell, (ell - 1) // 2, ell)
    return -1 if residue == ell - 1 else residue


def reduced_forms(discriminant):
    """Enumerate all reduced primitive positive definite forms of given D<0."""
    assert discriminant < 0 and discriminant % 4 in (0, 1)
    forms = []
    bound = isqrt((-discriminant) // 3)
    for a in range(1, bound + 1):
        for b in range(-a, a + 1):
            if (b * b - discriminant) % (4 * a):
                continue
            c = (b * b - discriminant) // (4 * a)
            if a > c or gcd(gcd(a, b), c) != 1:
                continue
            if (abs(b) == a or a == c) and b < 0:
                continue
            forms.append([a, b, c])
    return forms


def certificate():
    a1, a2, a3, a4, a6 = AINVS
    b2 = a1 * a1 + 4 * a2
    b4 = 2 * a4 + a1 * a3
    b6 = a3 * a3 + 4 * a6
    b8 = a1 * a1 * a6 + 4 * a2 * a6 - a1 * a3 * a4 + a2 * a3 * a3 - a4 * a4
    c4 = b2 * b2 - 24 * b4
    c6 = -b2**3 + 36 * b2 * b4 - 216 * b6
    delta = -b2 * b2 * b8 - 8 * b4**3 - 27 * b6 * b6 + 9 * b2 * b4 * b6
    assert (b2, b4, b6, b8, c4, c6, delta) == (4, -4, 1, -3, 112, -856, 389)
    assert c4**3 - c6**2 == 1728 * delta
    assert all(is_prime(n) for n in (3, 7, 11, 29, 71, 389))

    counts = {}
    for ell in (2, 3, 7, 11, 29):
        points = finite_points(ell)
        counts[str(ell)] = {
            "points": [encode_point(point) for point in points],
            "order": len(points),
            "frobenius_trace": ell + 1 - len(points),
        }
    assert [counts[str(ell)]["order"] for ell in (2, 3, 7, 11, 29)] == [5, 6, 13, 16, 36]
    assert gcd(counts["3"]["order"], counts["7"]["order"]) == 1

    squares29 = sorted({x * x % 29 for x in range(29)})
    frob3_roots = [x for x in range(29) if (x * x + 2 * x + 3) % 29 == 0]
    assert 21 not in squares29 and not frob3_roots

    splitting = {}
    for ell in (3, 29, 389):
        roots = [x for x in range(ell) if (x * x - x + 18) % ell == 0]
        splitting[str(ell)] = {"legendre_minus71": legendre(-71, ell), "omega_roots": roots}
    assert splitting["29"]["omega_roots"] == [13, 17]
    assert splitting["389"]["legendre_minus71"] == -1
    assert splitting["3"]["legendre_minus71"] == 1

    forms = reduced_forms(-71)
    assert forms == [[1, 1, 18], [2, -1, 9], [2, 1, 9], [3, -1, 6], [3, 1, 6], [4, -3, 5], [4, 3, 5]]
    assert gcd(71, 389 * 29) == 1 and 7 % 29 != 0

    p11 = finite_points(11)
    double_pairs = [(point, multiply(2, point, 11)) for point in p11]
    doubled = {result for _, result in double_pairs}
    P = (0, 0)
    Q = (1, 0)
    assert add_points(P, Q) == (Fraction(-2), Fraction(-1))
    sum11 = add_points(P, Q, 11)
    assert sum11 == (9, 10)
    assert len(doubled) == 4
    assert all(point not in doubled for point in (P, Q, sum11))

    rational_P = (Fraction(0), Fraction(0))
    point36 = multiply(36, rational_P)
    assert point36 is not None
    z36 = -point36[0] / point36[1]
    assert z36.denominator % 29
    zmod = z36.numerator * pow(z36.denominator, -1, 29**2) % (29**2)
    assert zmod == 203 and zmod % 29 == 0 and zmod != 0

    return {
        "format": "bsd-localization-exact-eligibility-v1",
        "scope": "Exact finite arithmetic; interpretation uses the standard theorems stated in README.md. No BSD or rank upper bound is claimed.",
        "curve": {
            "lmfdb_label": "389.a1",
            "ainvs": list(AINVS),
            "equation": "y^2+y=x^3+x^2-2*x",
            "b2_b4_b6_b8": [b2, b4, b6, b8],
            "c4": c4,
            "c6": c6,
            "discriminant": delta,
            "j_invariant": {"numerator": c4**3, "denominator": delta},
            "discriminant_identity_both_sides": 1728 * delta,
            "primes_verified_by_trial_division": [3, 7, 11, 29, 71, 389],
        },
        "finite_reductions": counts,
        "prime29": {"good": delta % 29 != 0, "a29": -6, "ordinary": (-6) % 29 != 0, "nonanomalous": 36 % 29 != 0},
        "bad_prime389": {
            "v_discriminant": 1,
            "c4_mod389": c4 % 389,
            "minus_c6_mod389": (-c6) % 389,
            "sqrt_minus_c6_mod389": 95,
            "sqrt_check": 95**2 % 389 == (-c6) % 389,
            "residual_prime29_does_not_divide_v_discriminant": 1 % 29 != 0,
            "interpretation": "Split multiplicative I_1; nontrivial unipotent inertia on E[29] by the Tate-curve ramification criterion, not a theorem proved by this script.",
        },
        "field": {
            "discriminant": -71,
            "integral_generator_polynomial": [18, -1, 1],
            "splitting": splitting,
            "gcd_discriminant_Np": gcd(71, 389 * 29),
            "reduction_a_bound": isqrt(71 // 3),
            "reduced_primitive_positive_definite_forms": forms,
            "form_count": len(forms),
            "class_group_interpretation": "C_7, by the classical reduced-form/class-group bijection.",
        },
        "residual_irreducibility": {
            "witness_good_prime": 3,
            "frobenius_polynomial_constant_to_leading": [3, 2, 1],
            "discriminant_mod29": 21,
            "squares_mod29": squares29,
            "roots_mod29": frob3_roots,
            "interpretation": "Irreducible Frobenius polynomial excludes an F_29-invariant line. Together with nontrivial unipotent inertia at389 this excludes invariant lines even over algebraic closure. Prime3 splits in K and389 is unramified in K, so the same argument applies over K.",
        },
        "rational_points": {
            "P": [0, 0],
            "Q": [1, 0],
            "P_plus_Q": [-2, -1],
            "on_curve": all(on_curve(point) for point in (P, Q, (-2, -1))),
            "torsion_exclusion": {"good_primes": [3, 7], "group_orders": [6, 13], "gcd": 1},
            "independence_mod2": {
                "prime": 11,
                "doubling_table": [[encode_point(a), encode_point(b)] for a, b in double_pairs],
                "doubling_image": [encode_point(point) for point in p11 if point in doubled],
                "P_Q_PplusQ_not_doubles": [True, True, True],
            },
        },
        "localization_crosscheck": {
            "point": "[36]P",
            "x": encode_fraction(point36[0]),
            "y": encode_fraction(point36[1]),
            "parameter": "z=-x/y",
            "z": encode_fraction(z36),
            "modulus": 29**2,
            "z_mod841": zmod,
            "z_valuation29": 1,
            "interpretation": "Independent group-law replication only. The separate logic/ artifact owns the formal-log inference.",
        },
        "primary_identity_source": "https://www.lmfdb.org/EllipticCurve/Q/data/389.a1",
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--check", type=Path)
    args = parser.parse_args()
    data = certificate()
    if args.check:
        assert json.loads(args.check.read_text()) == data, "Certificate differs from fresh exact recomputation"
        print(f"PASS: independently recomputed every arithmetic field in {args.check}")
    elif args.output:
        args.output.write_text(json.dumps(data, indent=2, sort_keys=True) + "\n")
        print(f"Wrote {args.output}")
    else:
        print(json.dumps(data, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
