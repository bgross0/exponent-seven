#!/usr/bin/env python3
"""Exact leading cyclotomic height certificate, in Sage's sign convention.

The sigma-function and global-height bridges are documented in README.md.
This does not compute an anticyclotomic height or a diagonal-class jet.
"""

import argparse
from fractions import Fraction as Q
import json
from math import gcd, isqrt
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "logic"))
from verify_logic import add, multiply, on_curve, rational_mod, valuation


def point_record(point, n=9):
    multiple = multiply(n, point)
    assert multiple is not None and on_curve(multiple)
    x, y = multiple
    d = isqrt(x.denominator)
    assert d*d == x.denominator and y.denominator == d**3
    a, b = x.numerator, y.numerator
    assert gcd(a, d) == gcd(b, d) == 1
    t = -x/y
    assert valuation(t.numerator, 5)-valuation(t.denominator, 5) >= 1
    unit = t/d
    assert unit.numerator % 5 and unit.denominator % 5
    # Explicitly check nonsingular reduction at the only bad prime.
    if d % 389:
        xr, yr = rational_mod(x, 389), rational_mod(y, 389)
        assert (2*yr+1) % 389 or (3*xr*xr+2*xr-2) % 389
    # For a1=0, sigma(t)/t is in 1+t^2 Z_5[[t]]. It has zero log mod25.
    # Iwasawa log(u) = log(u^4)/4 = (u^4-1)/4 mod25 for a 5-adic unit.
    unit_mod_25 = rational_mod(unit, 25)
    log_unit = ((pow(unit_mod_25, 4, 25)-1)*pow(4, -1, 25)) % 25
    assert log_unit % 5 == 0
    height = -2*log_unit*pow(n*n, -1, 25) % 25
    return {
        "point": [str(z) for z in point], "multiple": n,
        "multiple_coordinates": [str(x), str(y)],
        "denominator_d": str(d), "formal_parameter": str(t),
        "unit_t_over_d_mod_25": unit_mod_25,
        "log_unit_mod_25": log_unit,
        "height_mod_25": height,
        "log_point_div_5_mod_5": rational_mod(t/5, 5)*pow(n, -1, 5) % 5,
    }


def compute():
    P, Qp, A = (Q(0), Q(0)), (Q(1), Q(0)), (Q(-1), Q(1))
    assert add(A, P) == Qp
    count = 1+sum((y*y+y-x*x*x-x*x+2*x) % 5 == 0
                  for x in range(5) for y in range(5))
    assert count == 9
    b2, b4, b6, b8 = 4, -4, 1, -3
    disc = -b2*b2*b8-8*b4**3-27*b6*b6+9*b2*b4*b6
    assert disc == 389
    rows = {name: point_record(point) for name, point in
            [("P", P), ("Q", Qp), ("A=Q-P", A), ("P+Q", add(P, Qp))]}
    hp, hq = rows["P"]["height_mod_25"], rows["Q"]["height_mod_25"]
    hpq = (rows["P+Q"]["height_mod_25"]-hp-hq)*pow(2, -1, 25) % 25
    matrix = [[hp, hpq], [hpq, hq]]
    assert matrix == [[0, 15], [15, 20]]
    assert rows["A=Q-P"]["height_mod_25"] == (hp+hq-2*hpq) % 25
    # Published Sage matrix is in basis (A,Q). Change to (Q-A,Q)=(P,Q).
    sage_aq_mod25 = [[15, 5], [5, 20]]
    aa, aq, qq = sage_aq_mod25[0][0], sage_aq_mod25[0][1], sage_aq_mod25[1][1]
    converted = [[(aa-2*aq+qq) % 25, (qq-aq) % 25], [(qq-aq) % 25, qq]]
    assert matrix == converted
    normalized = [[v//5 for v in row] for row in matrix]
    up, uq = (rows[name]["log_point_div_5_mod_5"] for name in ("P", "Q"))
    assert (up, uq) == (1, 3)
    strict = [uq, -up]
    strict_height = sum(strict[i]*normalized[i][j]*strict[j]
                        for i in range(2) for j in range(2)) % 5
    determinant = (normalized[0][0]*normalized[1][1]-normalized[0][1]**2) % 5
    assert strict_height == determinant == 1
    return {
        "status": "PASS", "prime": 5, "height_modulus": 25,
        "model": [0, 1, 1, -2, 0], "discriminant": disc,
        "finite_field_point_count": count,
        "height_normalization": "-2/n^2 log_5(sigma(t(nB))/d(nB)); Sage convention",
        "points": rows, "basis": ["P=(0,0)", "Q=(1,0)"],
        "height_pairing_matrix_mod_25": matrix,
        "normalized_height_pairing_matrix_mod_5": normalized,
        "determinant_div_25_mod_5": determinant,
        "strict_vector": {
            "definition": "R=(log(Q)/5)*P-(log(P)/5)*Q",
            "coordinates_mod_5": strict,
            "self_height_div_5_mod_5": strict_height,
            "self_height_valuation": 1,
        },
        "published_sage_comparison": {
            "basis": ["A=(-1,1)", "Q=(1,0)"],
            "height_matrix_mod_25": sage_aq_mod25,
            "basis_relation": "A=Q-P",
            "independent_exact_calculation_agrees": True,
        },
        "scope": "Cyclotomic height only; no anticyclotomic Bockstein comparison or nonzero reflected logarithm is asserted",
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", type=Path)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = compute()
    if args.check:
        assert json.loads(args.check.read_text()) == result
    encoded = json.dumps(result, indent=2, sort_keys=True)+"\n"
    if args.output:
        args.output.write_text(encoded)
    print(encoded, end="")


if __name__ == "__main__":
    main()
