#!/usr/bin/env python3
"""Exact finite-lift calculations for derived Selmer obstruction models.

No arithmetic theorem is asserted here.  The inputs are explicit two-term
complexes over Q[[t]], and every calculation uses fractions.Fraction.

Run: python3 bockstein_lifts.py --output bockstein-results.json
"""

from __future__ import annotations

import argparse
from fractions import Fraction as F
import json
from pathlib import Path


def rref(rows, ncols):
    """Return exact reduced row echelon form and its pivot columns."""
    a = [[F(x) for x in row] for row in rows]
    if any(len(row) != ncols for row in a):
        raise ValueError("Inconsistent row length")
    pivots = []
    i = 0
    for j in range(ncols):
        pivot = next((k for k in range(i, len(a)) if a[k][j]), None)
        if pivot is None:
            continue
        a[i], a[pivot] = a[pivot], a[i]
        divisor = a[i][j]
        a[i] = [x / divisor for x in a[i]]
        for k in range(len(a)):
            if k != i and a[k][j]:
                factor = a[k][j]
                a[k] = [x - factor * y for x, y in zip(a[k], a[i])]
        pivots.append(j)
        i += 1
        if i == len(a):
            break
    return a, pivots


def kernel(rows, ncols):
    reduced, pivots = rref(rows, ncols)
    vectors = []
    for j in range(ncols):
        if j in pivots:
            continue
        v = [F(0)] * ncols
        v[j] = F(1)
        for i, p in enumerate(pivots):
            v[p] = -reduced[i][j]
        vectors.append(v)
    return vectors


def span_basis(vectors, ncols):
    reduced, pivots = rref(vectors, ncols)
    return reduced[:len(pivots)]


def block_matrix(coefficients, order):
    """Matrix for D(t)x(t)=0 modulo t**order, with coefficient-order blocks."""
    if order < 1 or not coefficients:
        raise ValueError("A positive order and a nonempty coefficient list are required")
    b = len(coefficients[0])
    a = len(coefficients[0][0])
    if any(len(d) != b or any(len(row) != a for row in d) for d in coefficients):
        raise ValueError("All coefficient matrices must have the same dimensions")
    rows = [[F(0)] * (a * order) for _ in range(b * order)]
    for k in range(order):
        for j in range(k + 1):
            degree = k - j
            if degree < len(coefficients):
                for output in range(b):
                    for source in range(a):
                        rows[k * b + output][j * a + source] = F(coefficients[degree][output][source])
    return rows, a


def liftable_constants(coefficients, order):
    """Find exactly which x_0 admit some jet x_0+...+x_(n-1)t**(n-1)."""
    rows, a = block_matrix(coefficients, order)
    jets = kernel(rows, a * order)
    # Verify returned witnesses in the original finite system, independently
    # of how the row-reduction routine represented it.
    for jet in jets:
        assert all(sum(c * x for c, x in zip(row, jet)) == 0 for row in rows)
    constants = span_basis([jet[:a] for jet in jets], a)
    return {
        "modulus_power": order,
        "jet_kernel_dimension": len(jets),
        "constant_image_dimension": len(constants),
        "constant_image_basis": [[str(x) for x in v] for v in constants],
    }


# Small exact polynomial functions, solely for the semilinear reflection
# identities below. Coefficients are stored in increasing powers of t.
def trim(p):
    p = [F(c) for c in p]
    while p and not p[-1]:
        p.pop()
    return p


def add(p, q):
    out = [F(0)] * max(len(p), len(q))
    for i, x in enumerate(p):
        out[i] += x
    for i, x in enumerate(q):
        out[i] += x
    return trim(out)


def scale(p, scalar):
    return trim([F(scalar) * x for x in p])


def multiply(p, q):
    if not p or not q:
        return []
    out = [F(0)] * (len(p) + len(q) - 1)
    for i, x in enumerate(p):
        for j, y in enumerate(q):
            out[i + j] += x * y
    return trim(out)


def reflect(p):
    return trim([(-1)**i * x for i, x in enumerate(p)])


def valuation(p):
    return next((i for i, x in enumerate(p) if x), None)


def reflected_model(a):
    """c(t)=-t, c(e+) = e+, c(e-)=-e-, F_p=(t**2,1).

    kappa=(a,-t**2*a) satisfies F_p(kappa)=0. The opposite defect has
    exact order 2 for any unit a. The reflected derivative may have zero
    or nonzero constant term despite the same order-2 leading defect.
    """
    t2 = [F(0), F(0), F(1)]
    kappa = [trim(a), scale(multiply(t2, a), -1)]
    conjugate = [reflect(kappa[0]), scale(reflect(kappa[1]), -1)]
    defect = add(multiply(t2, conjugate[0]), conjugate[1])
    assert add(multiply(t2, kappa[0]), kappa[1]) == []
    numerator = [add(kappa[i], scale(conjugate[i], -1)) for i in range(2)]
    assert all(not p or p[0] == 0 for p in numerator)
    derivative = [trim(p[1:]) for p in numerator]
    # The quotient is c-invariant; in particular its constant term is +.
    assert reflect(derivative[0]) == derivative[0]
    assert scale(reflect(derivative[1]), -1) == derivative[1]
    return {
        "input_a": [str(x) for x in a],
        "opposite_defect_valuation": valuation(defect),
        "opposite_defect_leading_coefficient": str(defect[valuation(defect)]),
        "numerator_valuation": min(valuation(p) for p in numerator if p),
        "derived_constant": [str(p[0] if p else 0) for p in derivative],
        "derived_polynomials": [[str(x) for x in p] for p in derivative],
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    zero = [[0, 0], [0, 0]]
    models = {
        "diag(t,t^2)": [zero, [[1, 0], [0, 0]], [[0, 0], [0, 1]]],
        "diag(t^2,0)": [zero, zero, [[1, 0], [0, 0]]],
        "t^2*J": [zero, zero, [[0, 1], [-1, 0]]],
        "coupled([[1,t],[0,t^2]])": [[[1, 0], [0, 0]], [[0, 1], [0, 0]], [[0, 0], [0, 1]]],
    }
    expected = {
        "diag(t,t^2)": [2, 1, 0, 0],
        "diag(t^2,0)": [2, 2, 1, 1],
        "t^2*J": [2, 2, 0, 0],
        "coupled([[1,t],[0,t^2]])": [1, 1, 0, 0],
    }
    results = {}
    for name, coefficients in models.items():
        levels = [liftable_constants(coefficients, n) for n in range(1, 5)]
        assert [level["constant_image_dimension"] for level in levels] == expected[name]
        results[name] = {"differential_coefficients": coefficients, "levels": levels}
    reflection = [reflected_model([F(1)]), reflected_model([F(1), F(1)])]
    assert [r["opposite_defect_valuation"] for r in reflection] == [2, 2]
    assert [r["opposite_defect_leading_coefficient"] for r in reflection] == ["2", "2"]
    assert [r["derived_constant"] for r in reflection] == [["0", "0"], ["2", "0"]]
    output = {
        "status": "Exact rational algebraic models only; not an elliptic-curve nonvanishing proof",
        "finite_lift_models": results,
        "reflected_derivative_models": reflection,
        "all_checks_passed": True,
    }
    rendered = json.dumps(output, indent=2) + "\n"
    if args.output:
        args.output.write_text(rendered)
    print(rendered)


if __name__ == "__main__":
    main()
