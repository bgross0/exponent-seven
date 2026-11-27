#!/usr/bin/env python3
"""Exact formal algebra for the complementary regulator specification.

This verifies finite polynomial identities over Q.  It does not compute a
Galois cohomology class, a diagonal-cycle jet, or the pilot's finite logarithm.
Run directly to print JSON; use --output PATH to save the same result.
"""

from __future__ import annotations

import argparse
from fractions import Fraction as Q
import json
from pathlib import Path


PREC = 7


def poly(*coeffs):
    return tuple(Q(c) for c in coeffs) + (Q(0),) * (PREC - len(coeffs))


ZERO, ONE, T = poly(), poly(1), poly(0, 1)


def add(a, b):
    return tuple(x + y for x, y in zip(a, b))


def neg(a):
    return tuple(-x for x in a)


def mul(a, b):
    return tuple(sum(a[j] * b[i-j] for j in range(i+1)) for i in range(PREC))


def scale(a, c):
    return tuple(Q(c) * x for x in a)


def compose(a, t_of_s):
    out = ZERO
    for c in reversed(a):
        out = add(mul(out, t_of_s), scale(ONE, c))
    return out


def dot(row, vec):
    out = ZERO
    for a, b in zip(row, vec):
        out = add(out, mul(a, b))
    return out


def matvec(mat, vec):
    return tuple(dot(row, vec) for row in mat)


def ord_t(a):
    return next((i for i, c in enumerate(a) if c), None)


def encode(q):
    q = Q(q)
    return str(q.numerator) if q.denominator == 1 else f"{q.numerator}/{q.denominator}"


def quad_mul(x, y):
    """Q[F]/(F^2+3F+5), represented by (constant, F coefficient)."""
    a, b = x
    c, d = y
    return a*c - 5*b*d, a*d + b*c - 3*b*d


def quad_inv(x):
    a, b = x
    norm = a*a - 3*a*b + 5*b*b
    assert norm
    return (a - 3*b) / norm, -b / norm


def run():
    F = (ZERO, ONE)
    G = (ONE, ZERO)
    a = poly(2, -1, 3)
    H = (poly(4, 1), poly(-3, 2))
    Gprime = tuple(add(g, add(mul(a, f), mul(T, h)))
                   for g, f, h in zip(G, F, H))

    P = ((ZERO, ONE), (poly(0, 7, 2), poly(0, 3, 1)))
    det_P = add(mul(P[0][0], P[1][1]), neg(mul(P[0][1], P[1][0])))
    assert ord_t(det_P) == 1 and det_P[1] == -7
    lam = (ZERO, ONE)
    lam_prime = (poly(0, 4, 1), poly(1, 2, -1))
    singular = poly(0, 0, 1, 2)
    t_of_s = poly(0, 3, 5)
    U = ((poly(2, 1), poly(1, 3)),
         (poly(1, 2), poly(1, -1)))
    # lambda_0 U(0)^(-1), since U(0)=[[2,1],[1,1]].
    transported_lam = (poly(-1), poly(2))

    rows = []
    for B in (Q(0), Q(1), Q(-3), Q(7, 5)):
        y = (scale(T, B), singular)
        assert dot(F, y) == singular
        assert dot(G, y)[1] == B
        assert dot(Gprime, y)[1] == B
        py = matvec(P, y)
        assert all(ord_t(z) is None or ord_t(z) >= 2 for z in py)
        extracted = dot(lam, py)[2] / 7
        assert extracted == B
        assert dot(lam_prime, py)[2] / 7 == B

        # Any regular change of output basis only contributes U(0) to degree 2.
        py_s = tuple(compose(z, t_of_s) for z in py)
        analytic_fixture = matvec(U, py_s)
        raw_second = dot(transported_lam, analytic_fixture)[2]
        assert raw_second / (7 * 3**2) == B
        rows.append({
            "finite_log": encode(B),
            "singular_series_coefficients": [encode(q) for q in singular],
            "complementary_second_coefficient": encode(dot(lam, py)[2]),
            "changed_coordinate_second_coefficient": encode(raw_second),
            "finite_log_recovered": encode(extracted),
        })

    # CH's j=0 Euler operator for phi=F/5, trace(F)=-3, det(F)=5.
    # zeta=(1-F/5)*(1-F^(-1))^(-1)*omega=(20-13F)/45*omega.
    I, FF = (Q(1), Q(0)), (Q(0), Q(1))
    Finv = quad_inv(FF)
    one_minus_Finv = (I[0]-Finv[0], I[1]-Finv[1])
    one_minus_Fover5 = (Q(1), Q(-1, 5))
    A_phi = quad_mul(one_minus_Finv, quad_inv(one_minus_Fover5))
    zeta_operator = (Q(20, 45), Q(-13, 45))
    assert quad_mul(A_phi, zeta_operator) == I
    assert quad_mul(one_minus_Fover5, quad_inv(one_minus_Finv)) == zeta_operator

    # Columns: +++, -++, +-+, ++-.  Each ordinary dominant map kills +++.
    quotient_matrix = ((0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1))
    assert all(row[0] == 0 for row in quotient_matrix)
    # Restriction to E-block (+++, -++): g and h projections both vanish.
    assert quotient_matrix[1][:2] == (0, 0)
    assert quotient_matrix[2][:2] == (0, 0)

    return {
        "status": "PASS",
        "scope": "Exact rational formal algebra; no arithmetic nonvanishing claim",
        "truncation_modulus": f"t^{PREC}",
        "checks": {
            "entire_singular_series_does_not_determine_finite_log": True,
            "regular_lift_independence": True,
            "complementary_vector_extraction": True,
            "annihilator_extension_independence": True,
            "weight_coordinate_and_output_basis_change": True,
            "CH_j0_annihilator_operator_for_E389_at_5": True,
            "ordinary_branch_deepest_line_kernel": True,
        },
        "regulator_det_coefficients": [encode(q) for q in det_P],
        "calibration_c_P": "7",
        "coordinate_linear_term": "3",
        "zeta_operator_in_Q_F": [encode(q) for q in zeta_operator],
        "fixtures": rows,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    rendered = json.dumps(run(), indent=2) + "\n"
    if args.output:
        args.output.write_text(rendered)
    print(rendered, end="")


if __name__ == "__main__":
    main()
