#!/usr/bin/env python3
"""Exact finite input certificate for the pilot's big 5-adic Galois image.

The arithmetic and finite group computations are executable. Their Tate-curve
and closed-group interpretations are the mathematical arguments in README.md.
"""

from __future__ import annotations

import argparse
from collections import deque
from fractions import Fraction
from itertools import product
import json
from math import gcd, isqrt
from pathlib import Path


ROOT = Path(__file__).resolve().parent
P = 5
IDENTITY = (1, 0, 0, 1)
UPPER = (1, 1, 0, 1)
LOWER = (1, 0, 1, 1)


def prime(n):
    return n >= 2 and all(n % d for d in range(2, isqrt(n) + 1))


def mul(a, b):
    return ((a[0]*b[0]+a[1]*b[2]) % P,
            (a[0]*b[1]+a[1]*b[3]) % P,
            (a[2]*b[0]+a[3]*b[2]) % P,
            (a[2]*b[1]+a[3]*b[3]) % P)


def det(a):
    return (a[0]*a[3]-a[1]*a[2]) % P


def generated(generators):
    seen = {IDENTITY}
    queue = deque(seen)
    while queue:
        a = queue.popleft()
        for b in generators:
            c = mul(a, b)
            if c not in seen:
                seen.add(c)
                queue.append(c)
    return seen


def invariant_data():
    a1, a2, a3, a4, a6 = 0, 1, 1, -2, 0
    b2 = a1*a1+4*a2
    b4 = 2*a4+a1*a3
    b6 = a3*a3+4*a6
    b8 = a1*a1*a6+4*a2*a6-a1*a3*a4+a2*a3*a3-a4*a4
    c4 = b2*b2-24*b4
    c6 = -b2**3+36*b2*b4-216*b6
    delta = -b2*b2*b8-8*b4**3-27*b6*b6+9*b2*b4*b6
    assert c4**3-c6**2 == 1728*delta
    return {"ainvs": [a1, a2, a3, a4, a6], "c4": c4, "c6": c6,
            "discriminant": delta, "j": str(Fraction(c4**3, delta))}


def count(ell):
    assert prime(ell) and ell != 389
    points = [(x, y) for x in range(ell) for y in range(ell)
              if (y*y+y-x**3-x*x+2*x) % ell == 0]
    return {"affine_points": [list(v) for v in points],
            "order_including_infinity": len(points)+1,
            "trace": ell-len(points)}


def reduced_forms(D):
    result = []
    for a in range(1, isqrt((-D)//3)+1):
        for b in range(-a, a+1):
            if (b*b-D) % (4*a):
                continue
            c = (b*b-D)//(4*a)
            if a > c or gcd(gcd(a, b), c) != 1:
                continue
            if (abs(b) == a or a == c) and b < 0:
                continue
            result.append([a, b, c])
    return result


def certificate():
    inv = invariant_data()
    assert inv["c4"] == 112 and inv["c6"] == -856
    assert inv["discriminant"] == 389 and prime(389)
    assert inv["c4"] % 389 != 0 and inv["discriminant"] % (389**2) != 0
    assert Fraction(inv["j"]).denominator == 389
    counts = {str(ell): count(ell) for ell in (3, 5)}
    assert counts["3"]["trace"] == -2 and counts["5"]["trace"] == -3
    roots = [x for x in range(P) if (x*x+2*x+3) % P == 0]
    assert roots == []
    discr = ((-2)**2-4*3) % P
    assert discr == 2 and discr not in {x*x % P for x in range(P)}

    all_gl = {a for a in product(range(P), repeat=4) if det(a) != 0}
    all_sl = {a for a in all_gl if det(a) == 1}
    assert len(all_gl) == 480 and len(all_sl) == 120
    assert generated((UPPER, LOWER)) == all_sl

    # Once the inertia transvection is put in this standard basis, the
    # actual Frobenius matrix is ONE of these twenty matrices. Check ALL
    # possibilities; no simultaneous basis choice is silently assumed.
    possible_frobenius = sorted(a for a in all_gl
                               if (a[0]+a[3]) % P == (-2) % P and det(a) == 3)
    assert len(possible_frobenius) == 20
    generation = []
    for a in possible_frobenius:
        group = generated((UPPER, a))
        assert group == all_gl
        generation.append({"matrix": list(a), "generated_order": len(group)})

    # These contrast cases demonstrate the two actual image inputs matter.
    assert len(generated((IDENTITY, possible_frobenius[0]))) < 480
    reducible_frobenius = (1, 0, 0, 3)
    assert len(generated((UPPER, reducible_frobenius))) < 480

    omega_roots5 = [x for x in range(5) if (x*x-x+18) % 5 == 0]
    omega_roots389 = [x for x in range(389) if (x*x-x+18) % 389 == 0]
    forms = reduced_forms(-71)
    assert omega_roots5 == [2, 4] and omega_roots389 == []
    assert len(forms) == 7 and gcd(5*389, 71) == 1
    assert pow(389, 1, 71) != 0 and prime(71)
    assert counts["5"]["trace"] % 5 == 2
    return {
        "status": "PASS",
        "curve": inv,
        "point_counts": counts,
        "residual_frobenius3": {"characteristic_polynomial": [3, 2, 1],
                                "discriminant_mod5": discr, "roots_mod5": roots},
        "finite_group_certificate": {
            "transvection": list(UPPER), "SL2_order": len(all_sl),
            "GL2_order": len(all_gl), "all_possible_frobenius_matrices": generation,
            "all_generated_groups_equal_GL2": True,
            "identity_instead_of_transvection_order": len(generated((IDENTITY, possible_frobenius[0]))),
            "reducible_frobenius_contrast_order": len(generated((UPPER, reducible_frobenius)))},
        "field_hypothesis_inputs": {"discriminant": -71, "reduced_forms": forms,
                                    "class_number": len(forms), "omega_roots_mod5": omega_roots5,
                                    "omega_roots_mod389": omega_roots389,
                                    "gcd_pN_D": gcd(5*389, 71)},
        "scope": "Exact point counts, curve invariants, splitting inputs and finite group generation. The Tate-uniformization interpretation, absolute irreducibility, and passage from residual image to the closed 5-adic image are proved using the stated mathematical inputs in README.md. This checker does not compute an infinite Galois group or formalize those theorems in Lean.",
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    result = certificate()
    if args.check:
        assert result == json.loads((ROOT / "result.json").read_text())
        print(json.dumps({"status": "PASS", "finite_frobenius_cases": 20}))
    else:
        out = json.dumps(result, indent=2, sort_keys=True)+"\n"
        if args.output:
            args.output.write_text(out)
        else:
            print(out, end="")


if __name__ == "__main__":
    main()
