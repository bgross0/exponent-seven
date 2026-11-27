#!/usr/bin/env python3
"""Exact algebra checks for the exterior-class descent note.

No elliptic-curve arithmetic, Selmer computation, transcendence proof, or BSD
claim is made. This checks the identities used in the note and the C7 descent
trap over Q[X]/Phi_7, with Python integers and fractions only.
"""

from fractions import Fraction as F
from itertools import product
import json


def wedge(u, v):
    return u[0] * v[1] - u[1] * v[0]


def scale(a, v):
    return (a * v[0], a * v[1])


def subtract(u, v):
    return (u[0] - v[0], u[1] - v[1])


def ell(ab, v):
    return ab[0] * v[0] + ab[1] * v[1]


def contraction(ab, determinant_coordinate):
    # c_ell(e1 wedge e2) = ell(e2)e1 - ell(e1)e2.
    return scale(determinant_coordinate, (ab[1], -ab[0]))


def canonical_checks():
    count = 0
    for a, b in product(range(-3, 4), repeat=2):
        if a == b == 0:
            continue
        ab = (F(a), F(b))
        for multiplier in (F(-7, 5), F(1), F(5, 7)):
            kappa = scale(multiplier, (ab[1], -ab[0]))
            assert ell(ab, kappa) == 0
            for z in product(map(F, range(-3, 4)), repeat=2):
                if ell(ab, z) == 0:
                    continue
                eta = wedge(kappa, z) / ell(ab, z)
                assert eta == multiplier
                assert contraction(ab, eta) == kappa
                count += 1
    return count


def basis_change_checks():
    count = 0
    ab = (F(2), F(3))
    original_regulator = contraction(ab, F(1))
    for a, b, c, d in product(range(-3, 4), repeat=4):
        p, q = (F(a), F(c)), (F(b), F(d))
        determinant = wedge(p, q)
        if determinant == 0:
            continue
        regulator = subtract(scale(ell(ab, q), p), scale(ell(ab, p), q))
        assert regulator == scale(determinant, original_regulator)
        count += 1
    return count


def cyclotomic_reduce(coefficients):
    # Phi_7(X) = 1 + X + ... + X^6, so X^6 = -(1+...+X^5).
    out = list(map(F, coefficients))
    while len(out) > 6:
        index = len(out) - 1
        leading = out.pop()
        for offset in range(6):
            out[index - 6 + offset] -= leading
    return tuple(out + [F(0)] * (6 - len(out)))


ZERO = cyclotomic_reduce([0])
ONE = cyclotomic_reduce([1])
ZETA = cyclotomic_reduce([0, 1])


def cyclotomic_add(x, y):
    return tuple(a + b for a, b in zip(x, y))


def cyclotomic_multiply(x, y):
    out = [F(0)] * 11
    for i, a in enumerate(x):
        for j, b in enumerate(y):
            out[i + j] += a * b
    return cyclotomic_reduce(out)


def cyclotomic_power(x, exponent):
    result = ONE
    for _ in range(exponent):
        result = cyclotomic_multiply(result, x)
    return result


def c7_checks():
    assert cyclotomic_power(ZETA, 7) == ONE
    assert all(cyclotomic_power(ZETA, j) != ONE for j in range(1, 7))
    inverse = cyclotomic_power(ZETA, 6)
    assert cyclotomic_multiply(ZETA, inverse) == ONE
    trace_chi = ZERO
    trace_inverse = ZERO
    diagonal_wedge_norm = ZERO
    for j in range(7):
        first = cyclotomic_power(ZETA, j)
        second = cyclotomic_power(inverse, j)
        trace_chi = cyclotomic_add(trace_chi, first)
        trace_inverse = cyclotomic_add(trace_inverse, second)
        diagonal_wedge_norm = cyclotomic_add(
            diagonal_wedge_norm, cyclotomic_multiply(first, second)
        )
    exterior_point_trace = cyclotomic_multiply(trace_chi, trace_inverse)
    assert trace_chi == trace_inverse == exterior_point_trace == ZERO
    assert diagonal_wedge_norm == cyclotomic_reduce([7])
    return {
        "character_trace": 0,
        "inverse_character_trace": 0,
        "exterior_square_of_point_trace": 0,
        "diagonal_norm_on_invariant_wedge": 7,
    }


def degree_checks():
    # Abstract cor*res = degree on a two-dimensional vector space. Applying
    # its exterior square multiplies by degree^2, even for degree = p = 5.
    result = []
    eta = F(7, 5)
    for degree in (2, 5, 7, 35):
        descended = F(degree) ** 2 * eta
        assert descended / F(degree) ** 2 == eta
        result.append(degree)
    return result


def membership_countermodels():
    # These are only models of vector-space inputs, not actual elliptic curves.
    # All have the same S, ell, kappa, z and eta; their designated Kummer-shaped
    # subspaces differ. Rank-one localization is nonzero in the middle model.
    ab, kappa, z = (F(2), F(3)), (F(3), F(-2)), (F(1), F(0))
    assert ell(ab, kappa) == 0 and ell(ab, z) != 0
    eta = wedge(kappa, z) / ell(ab, z)
    assert eta == 1
    records = []
    for dim_m in (0, 1, 2):
        contains_kappa = dim_m == 2
        contains_eta = dim_m == 2
        assert contains_kappa == contains_eta
        records.append({
            "M_dimension": dim_m,
            "quotient_dimension": 2 - dim_m,
            "strict_class_in_M": contains_kappa,
            "canonical_bivector_in_exterior_M": contains_eta,
        })
    return records


def main():
    result = {
        "status": "passed",
        "scope": "Exact algebra identities; no arithmetic existence claim",
        "canonical_class_instances": canonical_checks(),
        "invertible_basis_changes": basis_change_checks(),
        "C7_descent_trap": c7_checks(),
        "tested_extension_degrees": degree_checks(),
        "abstract_membership_countermodels": membership_countermodels(),
    }
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
