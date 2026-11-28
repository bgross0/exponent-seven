#!/usr/bin/env python3
"""Regenerate and check the exact degree-seven horizontal correspondence.

Run from any directory:
    python scripts/generate_horizontal71.py

Optional JSON export:
    python scripts/generate_horizontal71.py --json /tmp/horizontal71.json

Requires SymPy. All arithmetic is exact over QQ and ZZ. The generator finds
the quadratic gcd of H71(Y) and Phi2(a,Y) in (QQ[a]/H71(a))[Y], clears its
denominators, and verifies two identities over ZZ[X,Y]. The emitted data are
checked against BSDHorizontal71.lean. Lean proves the identities independently
with `ring`; neither this program nor SymPy is a trusted proof oracle.

This checks polynomial correspondences. It does not prove an analytic CM
identification or a modular-isogeny interpretation of the polynomials.
"""

from __future__ import annotations

import argparse
import ast
import json
from math import gcd
from pathlib import Path
import re

from sympy import Poly, QQ, ZZ, expand, ilcm, symbols
import sympy


FORMAL = Path(__file__).resolve().parents[1]
MODULUS = 433**4


def lean_list(path: Path, name: str):
    """Read a literal List definition; no Lean expressions are evaluated."""
    text = path.read_text()
    match = re.search(rf"^def {re.escape(name)}\s*:.*?:=\s*", text, re.M)
    if match is None:
        raise ValueError(f"Missing literal definition {name} in {path}")
    start = text.index("[", match.end())
    depth = 0
    for end in range(start, len(text)):
        depth += (text[end] == "[") - (text[end] == "]")
        if depth == 0:
            return ast.literal_eval(text[start : end + 1])
    raise ValueError(f"Unterminated list {name} in {path}")


def compute_certificate(coefficients: list[int]) -> dict:
    x, y = symbols("x y")
    h = Poly.from_list(coefficients[::-1], x, domain=QQ)
    extension = QQ.alg_field_from_poly(h, "a")
    a = extension.unit
    phi_in_extension = Poly.from_list(
        [
            extension.one,
            -a**2 + 1488*a - 162000,
            1488*a**2 + 40773375*a + 8748000000,
            a**3 - 162000*a**2 + 8748000000*a - 157464000000000,
        ],
        y,
        domain=extension,
    )
    h_in_extension = Poly.from_list(
        [extension.convert(c) for c in coefficients[::-1]], y, domain=extension
    )
    horizontal = phi_in_extension.gcd(h_in_extension)
    cofactor = h_in_extension.exquo(horizontal)
    vertical = phi_in_extension.exquo(horizontal)
    assert (horizontal.degree(), cofactor.degree(), vertical.degree()) == (2, 5, 1)
    denominator = int(ilcm(*[
        c.denominator
        for polynomial in (horizontal, cofactor, vertical)
        for coefficient in polynomial.rep.to_list()
        for c in coefficient.to_list()
    ]))

    def integer_lift(polynomial):
        return expand(sum(
            sum(int(c*denominator)*x**j
                for j, c in enumerate(coefficient.to_list()[::-1])) * y**i
            for i, coefficient in enumerate(polynomial.rep.to_list()[::-1])
        ))

    q, s, ell = map(integer_lift, (horizontal, cofactor, vertical))
    phi = (x**3 + y**3 - x**2*y**2 + 1488*(x**2*y + x*y**2)
           - 162000*(x**2 + y**2) + 40773375*x*y
           + 8748000000*(x + y) - 157464000000000)
    coefficient_ring = ZZ.poly_ring(y)
    hx = Poly(h.as_expr(), x, domain=coefficient_ring)
    modular_remainder, residual1 = Poly(
        denominator**2*phi - q*ell, x, domain=coefficient_ring
    ).div(hx)
    class_remainder, residual2 = Poly(
        denominator**2*h.as_expr().subs(x, y) - q*s,
        x,
        domain=coefficient_ring,
    ).div(hx)
    assert residual1.is_zero and residual2.is_zero
    assert expand(denominator**2*phi - q*ell - h.as_expr()*modular_remainder.as_expr()) == 0
    assert expand(denominator**2*h.as_expr().subs(x, y)
                  - q*s - h.as_expr()*class_remainder.as_expr()) == 0

    def rows(expression):
        polynomial = Poly(expression, y, domain=ZZ.poly_ring(x))
        return [[int(c) for c in Poly(row, x).all_coeffs()[::-1]]
                for row in polynomial.all_coeffs()[::-1]]

    return {
        "commonDenominator": denominator,
        "horizontalCoefficients": rows(q),
        "cofactorCoefficients": rows(s),
        "verticalCoefficients": rows(ell),
        "modularRemainderCoefficients": rows(modular_remainder.as_expr()),
        "classRemainderCoefficients": rows(class_remainder.as_expr()),
    }


def check_residues(data, coefficients, roots, graph):
    def add(a, b):
        return ((a[0]+b[0]) % MODULUS, (a[1]+b[1]) % MODULUS)

    def mul(a, b):
        return ((a[0]*b[0]+5*a[1]*b[1]) % MODULUS,
                (a[0]*b[1]+a[1]*b[0]) % MODULUS)

    def integer_horner(cs, a):
        value = (0, 0)
        for c in cs[::-1]:
            value = add(mul(value, a), (c % MODULUS, 0))
        return value

    def bivariate_horner(cs, a, b):
        value = (0, 0)
        for row in cs[::-1]:
            value = add(mul(value, b), integer_horner(row, a))
        return value

    def norm(a):
        return (a[0]**2 - 5*a[1]**2) % MODULUS

    def phi2(a, b):
        a2, a3 = mul(a, a), mul(mul(a, a), a)
        cs = [
            add(add(a3, mul((-162000 % MODULUS, 0), a2)),
                add(mul((8748000000 % MODULUS, 0), a),
                    (-157464000000000 % MODULUS, 0))),
            add(add(mul((1488, 0), a2), mul((40773375 % MODULUS, 0), a)),
                (8748000000 % MODULUS, 0)),
            add(add(mul((-1 % MODULUS, 0), a2), mul((1488, 0), a)),
                (-162000 % MODULUS, 0)),
            (1, 0),
        ]
        value = (0, 0)
        for c in cs[::-1]:
            value = add(mul(value, b), c)
        return value

    d = data["commonDenominator"]
    q = data["horizontalCoefficients"]
    derivative_q = [q[1], [2*d]]
    derivative_h = [i*c for i, c in enumerate(coefficients)][1:]
    assert gcd(d, MODULUS) == 1
    assert [[j for j in range(7)
             if bivariate_horner(q, roots[i], roots[j]) == (0, 0)]
            for i in range(7)] == graph
    assert all(gcd(norm(bivariate_horner(derivative_q, roots[i], roots[j])), MODULUS) == 1
               for i in range(7) for j in graph[i])
    assert all(gcd(norm(integer_horner(derivative_h, a)), MODULUS) == 1 for a in roots)
    assert all(gcd(norm(phi2(roots[i], roots[j])), MODULUS) == 1
               for i in range(7) for j in range(7) if j not in graph[i])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json", type=Path, help="Also write the exact coefficient certificate")
    args = parser.parse_args()
    h = lean_list(FORMAL / "BSDHenselWitness.lean", "candidate71Coefficients")
    roots = lean_list(FORMAL / "BSDFiniteWitness.lean", "cm71Roots433")
    graph = lean_list(FORMAL / "BSDFiniteWitness.lean", "cm71Graph433")
    assert len(h) == 8 and h[-1] == 1 and len(roots) == len(graph) == 7
    data = compute_certificate(h)
    source = FORMAL / "BSDHorizontal71.lean"
    denominator = re.search(r"^def commonDenominator : ℕ := (\d+)$", source.read_text(), re.M)
    assert denominator and int(denominator.group(1)) == data["commonDenominator"]
    for name, value in data.items():
        if name != "commonDenominator":
            assert lean_list(source, name) == value, f"Lean coefficient mismatch: {name}"
    check_residues(data, h, roots, graph)
    if args.json:
        args.json.write_text(json.dumps(data, indent=2) + "\n")
    print(json.dumps({
        "status": "passed",
        "sympy_version": sympy.__version__,
        "exact_integer_polynomial_identities": 2,
        "denominator_mod433": data["commonDenominator"] % 433,
        "directed_edges_with_simple_roots": sum(map(len, graph)),
        "nonedges_with_unit_Phi2": 49-sum(map(len, graph)),
        "H71_derivative_units": len(roots),
        "Lean_coefficients_match": True,
    }, indent=2))


if __name__ == "__main__":
    main()
