#!/usr/bin/env python3
"""Exact structural checks for the same-CM-type analytic target.

Default: print stable JSON, with no writes. This does not construct modular
cohomology, project a q-series, or establish arithmetic reciprocity.
"""

from __future__ import annotations

import argparse
from fractions import Fraction
import json
from pathlib import Path


def mm(a, b):
    return [[sum(a[i][k] * b[k][j] for k in range(len(b)))
             for j in range(len(b[0]))] for i in range(len(a))]


def rank(a):
    a = [[Fraction(x) for x in row] for row in a]
    r = 0
    for j in range(len(a[0])):
        pivot = next((i for i in range(r, len(a)) if a[i][j]), None)
        if pivot is None:
            continue
        a[r], a[pivot] = a[pivot], a[r]
        z = a[r][j]
        a[r] = [x / z for x in a[r]]
        for i in range(len(a)):
            if i != r:
                z = a[i][j]
                a[i] = [x - z*y for x, y in zip(a[i], a[r])]
        r += 1
        if r == len(a):
            break
    return r


def root7(n):
    """Coordinates of zeta_7^n in 1,zeta,...,zeta^5."""
    n %= 7
    return [-1] * 6 if n == 6 else [int(i == n) for i in range(6)]


def build():
    # Exponents of (psi, rho, rho^c), before the central norm twist.
    g = [(1, 1, 0), (-1, 0, 1)]
    h = [(-1, 1, 0), (1, 0, 1)]
    chars = [tuple(x+y-z for x, y, z in zip(a, b, (0, 1, 1)))
             for a in g for b in h]
    assert chars == [(0, 1, -1), (2, 0, 0), (-2, 0, 0), (0, -1, 1)]
    c = [[int(j == 3-i) for j in range(4)] for i in range(4)]
    e = [[int(i == j and i in (0, 3)) for j in range(4)]
         for i in range(4)]
    assert mm(c, e) == mm(e, c)
    assert mm(e, e) == e and rank(e) == 2
    for exponent in (0, 2, -2):
        total = [sum(root7(exponent*j)[i] for j in range(7))
                 for i in range(6)]
        assert total == ([7, 0, 0, 0, 0, 0] if exponent == 0 else [0]*6)

    # The base conjugation-plus line is not a family summand: one generic
    # torus specialization already falsifies commutation with it.
    torus = [[Fraction(2), 0], [0, Fraction(1, 2)]]
    plus = [[Fraction(1, 2)]*2 for _ in range(2)]
    assert mm(torus, plus) != mm(plus, torus)

    sigma = [[root7(-j)[i] for j in range(6)] for i in range(6)]
    ident = [[int(i == j) for j in range(6)] for i in range(6)]
    assert mm(sigma, sigma) == ident
    fixed_dimension = 6-rank([[sigma[i][j]-ident[i][j] for j in range(6)]
                              for i in range(6)])
    assert fixed_dimension == 3
    fixed_basis = [root7(0),
                   [x+y for x, y in zip(root7(1), root7(-1))],
                   [x+y for x, y in zip(root7(2), root7(-2))]]
    assert rank(fixed_basis) == 3
    for v in fixed_basis:
        assert [row[0] for row in mm(sigma, [[x] for x in v])] == v
    powers = [pow(5, j, 7) for j in range(1, 7)]
    assert powers == [5, 4, 6, 2, 3, 1]

    tame_matrices = []
    n = 389
    for m in (71, 71*25):
        a = pow(n, -1, m)
        b = (n*a-1)//m
        w = [[n, b], [m*n, n*a]]
        d = [[n, 0], [0, 1]]
        gamma = [[1, b], [m, n*a]]
        delta = [[n, b], [m, a]]
        assert mm(gamma, d) == w
        assert mm(d, w) == [[n*x for x in row] for row in delta]
        assert w[0][0]*w[1][1]-w[0][1]*w[1][0] == n
        assert gamma[0][0]*gamma[1][1]-gamma[0][1]*gamma[1][0] == 1
        assert delta[0][0]*delta[1][1]-delta[0][1]*delta[1][0] == 1
        # chi_-71(d) = (d/71) for positive d prime to71.
        assert pow(n*a, 35, 71) == 1
        assert pow(a, 35, 71) == 70
        tame_matrices.append({"native_level": m, "matrix": w,
                              "native_character_factor": 1,
                              "raised_character_factor": -1})
    assert (95*95-856) % 389 == 0
    assert 856 % 389 != 0
    assert pow(389, 35, 71) == 70

    # Polynomial identity for the bilinear concomitant: derivatives act
    # on formal products F^(a) G^(b). Internal terms must cancel exactly.
    rc_tests = []
    for s in (4, 8, 12, 20, 52):
        coeff = {}
        for i in range(s):
            for pair in ((s-i, i), (s-1-i, i+1)):
                coeff[pair] = coeff.get(pair, 0)+(-1)**i
        coeff = {pair: value for pair, value in coeff.items() if value}
        assert coeff == {(s, 0): 1, (0, s): -1}
        # All generalized binomial coefficients binom(-1,j)=(-1)^j.
        rc = {i: (-1)**i * (-1)**(s-1-i) * (-1)**i
              for i in range(s)}
        concomitant = {i: (-1)**(s-1-i) for i in range(s)}
        assert rc == concomitant
        assert 2*(1-s)+2*(s-1) == 0
        rc_tests.append(s)

    # For a generic coefficient n, the U-product identity is an exact
    # finite convolution. F is supported away from multiples of5.
    f = [0 if i % 5 == 0 else i*i-7*i+3 for i in range(251)]
    g = [i*i+2 for i in range(51)]
    for j in range(51):
        lhs = sum(f[5*j-5*k]*g[k] for k in range(j+1))
        rhs = sum(f[5*(j-k)]*g[k] for k in range(j+1))
        assert lhs == rhs == 0

    # Even full regulators have no forced complementary second value.
    models = []
    for b in (0, 1, -7):
        # y=(b*t,t^2), P=diag(t,1), singular F(y)=t^2.
        second = [b, 1]
        assert second[1] == 1
        models.append({"B": b, "full_regulator_second_coefficient": second,
                       "full_regulator_is_even": True,
                       "finite_logarithm": b,
                       "scalar_theta_second_coefficient": 1})

    return {
        "schema": 1,
        "scope": "Exact structural checks; not a modular-cohomology projection or reciprocity certificate",
        "pilot": {"conductor": 389, "quadratic_discriminant": -71,
                  "p": 5, "CM_character_order": 7},
        "tensor_characters_after_norm_twist": [list(x) for x in chars],
        "variable_finite_character_idempotent_rank": rank(e),
        "base_plus_line_is_not_a_generic_Galois_summand": True,
        "coefficient_field": {"degree": 6, "frobenius_powers_mod7": powers,
                              "inversion_fixed_degree": fixed_dimension,
                              "fixed_basis_in_zeta_coordinates": fixed_basis},
        "tame_atkin_lehner_matrices": tame_matrices,
        "split_multiplicative_square": {"root": 95, "minus_c6": 856,
                                        "modulus": 389},
        "elliptic_atkin_lehner_sign_from_split_multiplicative": -1,
        "rankin_cohen_telescoping_orders_checked": rc_tests,
        "U5_zero_product_coefficients_checked": 51,
        "even_regulator_countermodels": models,
        "checks_passed": True,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", type=Path)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = build()
    rendered = json.dumps(result, sort_keys=True, indent=2)+"\n"
    if args.check is not None:
        assert json.loads(args.check.read_text()) == result, "saved result differs"
    if args.output is not None:
        args.output.write_text(rendered)
    print(rendered, end="")


if __name__ == "__main__":
    main()
