#!/usr/bin/env python3
"""Recompute and verify an exact Hecke projector for E=389.a1.

This is a certificate in the proper weight-two cohomology representation.
It does not convert an overconvergent q-expansion to a de Rham class.
"""
import argparse
from fractions import Fraction
import json
from math import gcd, lcm
from pathlib import Path
import sys

import sympy as sp

from manin import PrimeManin, kernel_mod

ROOT = Path(__file__).resolve().parent


def v5(n):
    n = abs(int(n))
    if not n:
        raise ValueError("valuation of zero is not a finite integer")
    out = 0
    while n % 5 == 0:
        out += 1
        n //= 5
    return out


def rational_matrix(rows):
    return sp.Matrix([[sp.Rational(x) for x in row] for row in rows])


def strings(matrix):
    return [[str(x) for x in row] for row in matrix.tolist()]


def integer_matrix(matrix):
    assert all(x.q == 1 for x in matrix)
    return [[int(x) for x in row] for row in matrix.tolist()]


def horner_matrix(coefficients, matrix):
    """Integer Horner evaluation with a sparse right multiplier."""
    n = len(matrix)
    sparse = [[(j, a) for j, a in enumerate(row) if a] for row in matrix]
    value = [[0]*n for _ in range(n)]
    for coefficient in coefficients:
        nxt = [[0]*n for _ in range(n)]
        for i, row in enumerate(value):
            for k, a in enumerate(row):
                if a:
                    for j, b in sparse[k]:
                        nxt[i][j] += a*b
        for i in range(n):
            nxt[i][i] += coefficient
        value = nxt
    return sp.Matrix(value)


def elliptic_trace(p):
    """Exact point count on y^2+y=x^3+x^2-2x, including infinity."""
    points = 1 + sum((y*y+y-x*x*x-x*x+2*x) % p == 0
                     for x in range(p) for y in range(p))
    return p+1-points


def compute(witness):
    module = PrimeManin(389, exact=True)
    n = module.dimension
    assert n == 65
    assert module.free == witness["basis_free_manin_indices"]
    # The chosen presentation is a valid Z_(5) lattice: no elimination
    # denominator is divisible by 5. Recompute modulo 5 independently.
    assert all(gcd(Fraction(x).denominator, 5) == 1
               for row in module.reduction.values() for x in row.values())
    mod5 = PrimeManin(389, digits=1)
    assert mod5.free == module.free
    for i, row in module.reduction.items():
        reduced = {j: int(Fraction(x).numerator *
                          pow(Fraction(x).denominator, -1, 5) % 5)
                   for j, x in row.items()}
        assert {j: x for j, x in reduced.items() if x} == mod5.reduction[i]

    T2 = rational_matrix(module.hecke(2))
    assert T2 == rational_matrix(module.hecke_two_merel())
    T3 = rational_matrix(module.hecke(3))
    T5 = rational_matrix(module.hecke(5))
    C = rational_matrix(module.conjugation())
    I = sp.eye(n)
    assert T2*T3 == T3*T2
    assert T2*T5 == T5*T2
    assert C*C == I and T2*C == C*T2 and T3*C == C*T3
    for p, T in [(2, T2), (3, T3), (5, T5)]:
        b = sp.Matrix([module.boundary_row()])
        assert b*T == (p+1)*b
        assert elliptic_trace(p) == {2: -2, 3: -2, 5: -3}[p]

    E = rational_matrix(witness["E"])
    L = rational_matrix(witness["L"])
    assert E.shape == L.shape == (n, 2)
    assert E.rank() == L.rank() == 2
    assert (T2+2*I).to_DM().rank() == n-2
    assert (T2+2*I)*E == sp.zeros(n, 2)
    assert L.T*(T2+2*I) == sp.zeros(2, n)
    pairing = L.T*E
    assert strings(pairing) == witness["pairing"]
    assert pairing.det() != 0
    P = E*pairing.inv()*L.T
    assert P*P == P and sp.trace(P) == 2
    assert T2*P == P*T2 == -2*P
    assert T3*P == P*T3 == -2*P
    assert T5*P == P*T5 == -3*P
    assert b*P == sp.zeros(1, n)
    assert C*P == P*C and sp.trace(C*P) == 0
    # Since C^2=1 on this rank-two image, trace zero means dimensions 1+1.
    denominator = lcm(*(int(x.q) for x in P))
    assert denominator == 40
    bad_entries = [(i, j, P[i, j]) for i in range(n) for j in range(n)
                   if v5(P[i, j].q) == 1]
    assert bad_entries
    i, j, value = bad_entries[0]

    poly = witness["polynomial_projector"]
    assert poly["operator"] == "T2+4*T3"
    coefficients = poly["coefficients_high_to_low"]
    assert len(coefficients) == 33 and coefficients[0] == 1
    at_target = 0
    for c in coefficients:
        assert isinstance(c, int)
        at_target = -10*at_target+c
    assert at_target == poly["value_at_minus_10"]
    assert at_target == 4991964896182583587087694480
    assert v5(at_target) == 1
    A = integer_matrix(T2+4*T3)
    assert horner_matrix(coefficients, A) == at_target*P

    t2mod = [[int(x) % 5 for x in row] for row in T2.tolist()]
    t3mod = [[int(x) % 5 for x in row] for row in T3.tolist()]
    eq2 = [[(x+2*(i == j)) % 5 for j, x in enumerate(row)]
           for i, row in enumerate(t2mod)]
    eq3 = [[(x+2*(i == j)) % 5 for j, x in enumerate(row)]
           for i, row in enumerate(t3mod)]
    dimensions = {"T2": len(kernel_mod(eq2, n, 5)),
                  "T2_and_T3": len(kernel_mod(eq2+eq3, n, 5))}
    assert dimensions == {"T2": 7, "T2_and_T3": 2}

    # Small levels exercise both cusp reduction and the independent formula.
    regression = {}
    for level, dimension in [(11, 3), (23, 5), (37, 5)]:
        small = PrimeManin(level, exact=True)
        assert small.dimension == dimension
        assert small.hecke(2) == small.hecke_two_merel()
        regression[str(level)] = dimension

    return {
        "status": "PASS",
        "curve": [0, 1, 1, -2, 0],
        "level": 389,
        "relative_dimension": n,
        "boundary_dimension": b.rank(),
        "cuspidal_dimension": n-b.rank(),
        "elliptic_factor_dimension": 2,
        "elliptic_factor_conjugation_dimensions": {"plus": 1, "minus": 1},
        "point_count_hecke_eigenvalues": {str(p): elliptic_trace(p) for p in (2, 3, 5)},
        "mod5_target_kernel_dimensions": dimensions,
        "projector_least_denominator_in_manin_lattice": denominator,
        "precision_loss_witness": {
            "zero_based_row": i, "zero_based_column": j, "entry": str(value),
            "5_adic_valuation": -1},
        "polynomial_degree": 32,
        "polynomial_operator": poly["operator"],
        "polynomial_value_at_target": at_target,
        "polynomial_denominator_5_adic_valuation": 1,
        "polynomial_identity_verified": "q(T2+4*T3)=q(-10)*P",
        "small_level_relative_dimensions": regression,
        "scope": "Exact proper weight-two Hecke projector; at most one digit of "
                 "5-adic loss on a Hecke-stable integral lattice. No overconvergent "
                 "reduction, crystalline coordinate identification, vector L-value, "
                 "or nonzero reflected logarithm is asserted."
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args()
    witness = json.loads((ROOT/"witness.json").read_text())
    result = compute(witness)
    if args.check:
        assert result == json.loads((ROOT/"result.json").read_text())
    if args.write:
        (ROOT/"result.json").write_text(json.dumps(result, indent=2, sort_keys=True)+"\n")
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
