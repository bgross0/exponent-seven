#!/usr/bin/env python3
"""Exact arithmetic for the localization audit, using Python's stdlib only.

This is not a Lean proof or an implementation of a theta element. The formal
group argument connecting z([36]P) to log(P) is proved in AUDIT.md.
"""

from fractions import Fraction as Q
from math import comb
import json


# E: y^2+y = x^3+x^2-2x. None is the identity.
def on_curve(point):
    if point is None:
        return True
    x, y = point
    return y*y + y == x*x*x + x*x - 2*x


def add(left, right):
    assert on_curve(left) and on_curve(right)
    if left is None:
        return right
    if right is None:
        return left
    x, y = left
    u, v = right
    if x == u:
        if y + v + 1 == 0:
            return None
        slope = (3*x*x + 2*x - 2)/(2*y + 1)
        intercept = (-x*x*x - 2*x - y)/(2*y + 1)
    else:
        slope = (v-y)/(u-x)
        intercept = (y*u-v*x)/(u-x)
    result_x = slope*slope - 1 - x - u
    result = (result_x, -slope*result_x - intercept - 1)
    assert on_curve(result)
    return result


def multiply(n, point):
    assert n >= 0 and on_curve(point)
    result = None
    while n:
        if n & 1:
            result = add(result, point)
        point = add(point, point)
        n //= 2
    return result


def valuation(integer, prime):
    assert integer != 0
    result = 0
    while integer % prime == 0:
        result += 1
        integer //= prime
    return result


def rational_mod(value, modulus):
    return value.numerator * pow(value.denominator, -1, modulus) % modulus


def exact_localization_certificate():
    p = 29
    modulus = p*p
    count = 1 + sum(
        (y*y + y - x*x*x - x*x + 2*x) % p == 0
        for x in range(p) for y in range(p)
    )
    assert count == 36
    a_p = p + 1 - count
    assert a_p == -6 and a_p % p != 0
    # Standard integral Weierstrass discriminant, calculated independently.
    b2, b4, b6, b8 = 4, -4, 1, -3
    discriminant = -b2*b2*b8 - 8*b4**3 - 27*b6*b6 + 9*b2*b4*b6
    assert discriminant == 389 and discriminant % p != 0
    point = (Q(0), Q(0))
    multiple = multiply(count, point)
    assert multiple is not None
    x, y = multiple
    z = -x/y
    val_x = valuation(x.numerator, p) - valuation(x.denominator, p)
    val_y = valuation(y.numerator, p) - valuation(y.denominator, p)
    val_z = valuation(z.numerator, p) - valuation(z.denominator, p)
    assert (val_x, val_y, val_z) == (-2, -3, 1)
    z_residue = rational_mod(z, modulus)
    assert z_residue == 203
    log_p_residue = z_residue * pow(count, -1, modulus) % modulus
    assert log_p_residue == 29
    # A second multiplication path exercises exact addition without reusing
    # the double-and-add accumulation for the final result.
    repeated = None
    for _ in range(count):
        repeated = add(repeated, point)
    assert repeated == multiple
    return {
        "model": [0, 1, 1, -2, 0],
        "point": [0, 0],
        "prime": p,
        "discriminant": discriminant,
        "finite_field_point_count": count,
        "a_p": a_p,
        "multiple": count,
        "valuation_x_y_z": [val_x, val_y, val_z],
        "z_numerator": str(z.numerator),
        "z_denominator": str(z.denominator),
        "z_mod_p_squared": z_residue,
        "log_P_mod_p_squared_given_formal_group_lemma": log_p_residue,
        "independent_addition_paths_agree": True,
    }


def rank(matrix, width):
    rows = [[Q(entry) for entry in row] for row in matrix]
    assert all(len(row) == width for row in rows)
    lead = 0
    for column in range(width):
        pivot = next((i for i in range(lead, len(rows)) if rows[i][column]), None)
        if pivot is None:
            continue
        rows[lead], rows[pivot] = rows[pivot], rows[lead]
        pivot_value = rows[lead][column]
        rows[lead] = [entry/pivot_value for entry in rows[lead]]
        for i in range(len(rows)):
            if i != lead:
                coefficient = rows[i][column]
                rows[i] = [a-coefficient*b for a, b in zip(rows[i], rows[lead])]
        lead += 1
        if lead == len(rows):
            break
    return lead


def exact_countermodels():
    e1, e2 = (Q(1), Q(0)), (Q(0), Q(1))
    localization_matrix = [[1, 0]]
    kappa = e2
    height_matrix = [[0, -1], [1, 0]]
    loc = lambda vector: vector[0]
    height = lambda x, y: x[1]*y[0]-x[0]*y[1]
    assert rank(localization_matrix, 2) == 1
    assert kappa != (0, 0) and loc(kappa) == 0
    assert rank(height_matrix, 2) == 2
    # Basis checks establish the identities for every vector by linearity.
    for x in [e1, e2]:
        assert height(kappa, x) == loc(x)
        for y in [e1, e2]:
            assert height(x, y) == -height(y, x)
    cases = []
    for mw_basis, quotient_matrix in [([], [[1, 0], [0, 1]]), ([e1], [[0, 1]])]:
        mw_dimension = rank(mw_basis, 2)
        quotient_dimension = rank(quotient_matrix, 2)
        assert mw_dimension + quotient_dimension == 2
        for v in mw_basis:
            assert all(sum(a*b for a, b in zip(row, v)) == 0 for row in quotient_matrix)
        # Thus image(M) equals the quotient map's kernel, by dimension.
        cases.append({
            "selmer_model_dimension": 2,
            "mw_model_dimension": mw_dimension,
            "sha_tate_model_dimension": quotient_dimension,
            "localization_rank": 1,
            "kappa": [0, 1],
            "kappa_in_localization_kernel": True,
            "kappa_in_mw_model": False,
            "exact_sequence_checked": True,
        })
    return {
        "base_field": "Q; also valid after extension to Q_p",
        "interpretation": "Abstract inference countermodels, not elliptic curves or BSD counterexamples",
        "height_matrix": height_matrix,
        "leading_term_identity_on_basis": True,
        "cases": cases,
    }


def first_nonzero_coefficient(coefficients):
    return next(i for i, c in enumerate(coefficients) if c)


def finite_precision_obstruction():
    p, precision = 29, 2
    modulus = p**precision
    polynomials = [[0, 0, 1], [modulus, 0, 1], [0, modulus, 1]]
    reductions = [[a % modulus for a in row] for row in polynomials]
    orders = [first_nonzero_coefficient(row) for row in polynomials]
    assert reductions == [[0, 0, 1]]*3
    assert orders == [2, 0, 1]
    # The low coefficient well-definedness in the level-p^n quotient.
    for n in [1, 2, 3]:
        for k in [1, 2]:
            assert comb(p**n, k) % (p**n) == 0
    return {
        "prime": p,
        "modulus": modulus,
        "coefficient_vectors": polynomials,
        "identical_reduction": reductions[0],
        "exact_T_orders": orders,
        "level_relation_low_coefficient_divisibility_checked_n": [1, 2, 3],
    }


def main():
    result = {
        "status": "exact arithmetic checks passed; theoretical bridges are in AUDIT.md, not formalized",
        "localization": exact_localization_certificate(),
        "countermodels": exact_countermodels(),
        "finite_precision": finite_precision_obstruction(),
        "not_proved_here": [
            "a finite theta coefficient or its identification with the infinite theta element",
            "nonvanishing of auxiliary complex L-values",
            "generalized Kato-class nonvanishing for the example",
            "Kummer membership of a generalized Kato class",
            "any new uniform implication from analytic rank two to Mordell-Weil rank two",
        ],
    }
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
