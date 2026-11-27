#!/usr/bin/env python3
"""Exact algebra behind the tame-trace audit; no modular projection claimed.

Default: print deterministic JSON, without writing files.
Use --check PATH to compare a saved result; --output PATH to save one.
All calculations use Python's standard library.
"""
import argparse
from fractions import Fraction
import json
from math import prod
from pathlib import Path


def val5(x):
    x = Fraction(x)
    if x == 0:
        return None
    n, d = x.numerator, x.denominator
    v = 0
    while n % 5 == 0:
        n //= 5
        v += 1
    while d % 5 == 0:
        d //= 5
        v -= 1
    return v


def det(A):
    return A[0][0]*A[1][1] - A[0][1]*A[1][0]


def mm(A, B):
    return [[sum(A[i][k]*B[k][j] for k in range(len(B)))
             for j in range(len(B[0]))] for i in range(len(A))]


def frac_json(x):
    x = Fraction(x)
    return {"numerator": str(x.numerator),
            "denominator": str(x.denominator), "valuation5": val5(x)}


def mul_linear(poly, root):
    out = [0] * (len(poly)+1)
    for j, c in enumerate(poly):
        out[j] -= root*c
        out[j+1] += c
    return out


def interpolation(m):
    degree = m+1
    nodes = [6**(4*j)-1 for j in range(degree+1)]
    weights = []
    for j, a in enumerate(nodes):
        poly = [1]
        for i, b in enumerate(nodes):
            if i != j:
                poly = mul_linear(poly, b)
        denom = prod(a-b for i, b in enumerate(nodes) if i != j)
        weights.append(Fraction(poly[2], denom))

    # Lagrange coefficient is exact through the interpolation degree.
    for n in range(degree+1):
        c = sum(w*(a**n) for w, a in zip(weights, nodes))
        assert c == (1 if n == 2 else 0)
    # These finite tests accompany, rather than replace, the general proof.
    tail_checks = []
    for n in range(degree+1, degree+7):
        c = sum(w*(a**n) for w, a in zip(weights, nodes))
        v = val5(c)
        assert v is None or v >= n-2
        tail_checks.append({"monomial_degree": n,
                            "coefficient_valuation5": v,
                            "proved_lower_bound": n-2})
    loss = max(0, -min(val5(w) for w in weights if w))
    return {
        "target_digits": m,
        "number_of_values": len(nodes),
        "weights_k": [1+4*j for j in range(degree+1)],
        "weight_coordinate_nodes": [str(a) for a in nodes],
        "max_input_precision_loss": loss,
        "required_input_digits_before_other_denominators": m+loss,
        "lagrange_W2_weights": [frac_json(w) for w in weights],
        "finite_tail_checks": tail_checks,
    }


def compute():
    r, N = 71, 389
    count = 1 + sum(
        (y*y+y-x*x*x-x*x+2*x) % r == 0
        for x in range(r) for y in range(r)
    )
    ar = r+1-count
    assert count == 82 and ar == -10
    assert pow(5, 35, 71) == 1 and pow(389, 35, 71) == 70
    index = N+1
    genus = 1 + Fraction(index, 12) - Fraction(2, 4) - Fraction(2, 2)
    assert genus == 32 and (2*index)//12 == 65
    G = [[72, ar], [ar, 72]]
    Ginv = [[Fraction(72, 5084), Fraction(10, 5084)],
            [Fraction(10, 5084), Fraction(72, 5084)]]
    assert det(G) == 5084 and val5(det(G)) == 0
    assert mm(G, Ginv) == [[1, 0], [0, 1]]
    assert mm(G, [[1], [1]]) == [[62], [62]]
    assert mm(G, [[1], [-1]]) == [[82], [-82]]
    assert mm(G, [[10], [72]]) == [[0], [5084]]
    raw = [[72, Fraction(ar, r)], [ar, Fraction(72, r)]]
    assert mm(raw, [[1, 0], [0, r]]) == G

    W = [[71, -23], [27619, -8946]]
    B = [[1, 23], [0, 71]]
    sigma = [[1, 0], [389, 1]]
    assert det(W) == 71
    assert mm(W, B) == [[71*x for x in row] for row in sigma]
    # Right lower rows identify the 72 left cosets modulo Gamma0(71N).
    # sigma*T^a has lower row (N,Na+1); projectively these are all finite
    # points of P1(F71), and identity supplies (0,1).
    finite = {(N*a+1)*pow(N, -1, r) % r for a in range(r)}
    assert len(finite) == 71

    a, b = 6**4-1, 6**8-1
    # P1=W(W-a): zeros at 0,a, yet second coefficient is one.
    P1 = mul_linear(mul_linear([1], 0), a)
    assert P1[2] == 1
    # P2=W(W-a)(W-b): zeros at 0,a,b, second coefficient val5=1.
    P2 = mul_linear(P1, b)
    assert P2[2] == -(a+b) and val5(P2[2]) == 1

    interpolations = [interpolation(m) for m in (1, 2, 5, 12)]
    last = interpolations[-1]
    assert last["number_of_values"] == 14
    assert last["weights_k"][-1] == 53
    assert last["max_input_precision_loss"] == 4
    assert last["required_input_digits_before_other_denominators"] == 16

    return {
        "format": "tame-trace-independent-audit-v1",
        "all_checks_passed": True,
        "arithmetic": {"prime": r, "curve_point_count": count,
                       "frobenius_trace": ar,
                       "chi_minus71_at5": pow(5, 35, 71),
                       "chi_minus71_at389": -1 if pow(389, 35, 71) == 70 else 1},
        "geometric_gram": G,
        "gram_determinant": det(G),
        "target_geometry": {"index": index, "genus": int(genus),
                            "proper_de_Rham_dimension": 2*int(genus),
                            "classical_S2_dimension": int(genus)},
        "raw_q_gram": [[frac_json(a) for a in row] for row in raw],
        "fricke_plus_recovery_scalar": frac_json(Fraction(1, 62)),
        "fricke_matrix": W,
        "cusp_matrix": sigma,
        "number_of_left_cosets": len(finite)+1,
        "trace_input_bounds": {
            "raw_4096_guaranteed_traced_bound": 4096//71,
            "level389_classical_weight2_sturm_bound": 65,
            "raw_bound_for_traced12675": 71*12675,
        },
        "low_weight_counterexamples": {
            "weight1_and5_same_values_W2_difference": 1,
            "weight1_5_9_same_values_W2_difference": str(P2[2]),
            "three_node_difference_valuation5": val5(P2[2]),
        },
        "interpolation": interpolations,
        "scope": "Exact finite algebra and arithmetic; not an actual de Rham projection.",
        "not_verified_by_this_script": [
            "The published overconvergent and Fricke comparison theorems.",
            "An actual level-389 elliptic projection of a trace jet.",
            "The full regulator comparison with the global generalized Kato class.",
            "Integral output-lattice bounds after cohomological projection.",
        ],
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", type=Path)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = compute()
    if args.check is not None:
        if json.loads(args.check.read_text()) != result:
            raise SystemExit(f"Result mismatch: {args.check}")
    encoded = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.output is not None:
        args.output.write_text(encoded)
    print(encoded, end="")


if __name__ == "__main__":
    main()
