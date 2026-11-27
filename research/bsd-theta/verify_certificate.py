#!/usr/bin/env python3
"""Independently check the exact CM/theta arithmetic in the accompanying data.

This verifier does not import either discovery script. The complete check
reconstructs the two class polynomials with rigorous complex ball arithmetic,
then uses only integers for finite-field, Hensel, graph, and moment checks.
Classical CM, Jacquet--Langlands, and theta interpolation theorems remain
mathematical dependencies, described in research/theta-certificate.md.
"""

from __future__ import annotations

import argparse
import datetime as dt
import hashlib
import json
import math
import subprocess
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent
Q = 389


def require(condition, message):
    if not condition:
        raise ValueError(message)


def read_json(path):
    return json.loads(path.read_text())


def mul(x, y, modulus):
    return ((x[0] * y[0] + 2 * x[1] * y[1]) % modulus,
            (x[0] * y[1] + x[1] * y[0]) % modulus)


def add(x, y, modulus):
    return ((x[0] + y[0]) % modulus, (x[1] + y[1]) % modulus)


def polynomial_value(coeffs, x, modulus):
    value = (0, 0)
    for c in reversed(coeffs):
        c = c if isinstance(c, (list, tuple)) else (c, 0)
        value = add(mul(value, x, modulus), c, modulus)
    return value


def polynomial_from_roots(roots, modulus):
    coeffs = [(1, 0)]
    for x in roots:
        new = [(0, 0)] * (len(coeffs) + 1)
        for k, c in enumerate(coeffs):
            prod = mul(c, (-x[0], -x[1]), modulus)
            new[k] = add(new[k], prod, modulus)
            new[k + 1] = add(new[k + 1], c, modulus)
        coeffs = new
    return coeffs


def phi2_coefficients(x, modulus):
    x2 = mul(x, x, modulus)
    x3 = mul(x2, x, modulus)
    def lin(*terms):
        return (sum(c * z[0] for c, z in terms) % modulus,
                sum(c * z[1] for c, z in terms) % modulus)
    return [
        lin((1, x3), (-162000, x2), (8748000000, x), (-157464000000000, (1, 0))),
        lin((1488, x2), (40773375, x), (8748000000, (1, 0))),
        lin((-1, x2), (1488, x), (-162000, (1, 0))),
        (1, 0),
    ]


def rank_mod(matrix, prime):
    a = [[int(v) % prime for v in row] for row in matrix]
    row = 0
    for col in range(len(a[0])):
        pivot = next((i for i in range(row, len(a)) if a[i][col]), None)
        if pivot is None:
            continue
        a[row], a[pivot] = a[pivot], a[row]
        inverse = pow(a[row][col], -1, prime)
        a[row] = [v * inverse % prime for v in a[row]]
        for i in range(row + 1, len(a)):
            multiple = a[i][col]
            a[i] = [(x - multiple * y) % prime for x, y in zip(a[i], a[row])]
        row += 1
        if row == len(a):
            break
    return row


def reduced_forms(discriminant):
    require(discriminant < 0 and discriminant % 4 in (0, 1), "Invalid discriminant")
    forms = []
    for a in range(1, math.isqrt(-discriminant // 3) + 1):
        for b in range(-a, a + 1):
            numerator = b * b - discriminant
            if numerator % (4 * a):
                continue
            c = numerator // (4 * a)
            if a > c or math.gcd(a, math.gcd(b, c)) != 1:
                continue
            if (abs(b) == a or a == c) and b < 0:
                continue
            forms.append((a, b, c))
    return forms


def reconstruct_class_polynomial(discriminant, precision=16384):
    from flint import acb, acb_poly, arb, ctx
    forms = reduced_forms(discriminant)
    with ctx.workprec(precision):
        root_d = arb(-discriminant).sqrt()
        js = [(acb(-b, root_d) / (2 * a)).modular_j() for a, b, c in forms]
        ball_polynomial = acb_poly.from_roots(js)
        integers = ball_polynomial.unique_fmpz_poly()
        require(integers is not None, "Ball precision does not isolate unique integer coefficients")
        coeffs = [int(c) for c in integers.coeffs()]
        require(len(coeffs) == len(forms) + 1, "Class polynomial degree mismatch")
        return coeffs, {"D": discriminant, "class_number": len(forms),
                        "working_bits": precision, "unique_integer_polynomial": True}


def point_count(p):
    return 1 + sum((y * y + y - x * x * x - x * x + 2 * x) % p == 0
                   for x in range(p) for y in range(p))


def verify_supersingular(data):
    require(pow(2, (Q - 1) // 2, Q) == Q - 1, "Quadratic extension is not a field")
    js = [tuple(j) for j in data["supersingular_j"]]
    roots = [tuple(r) for r in data["deuring_roots"]]
    require(len(js) == 33 and len(set(js)) == 33, "Expected 33 distinct supersingular invariants")
    require(len(roots) == 194 and len(set(roots)) == 194, "Incomplete Deuring polynomial roots")
    deuring = [math.comb(194, k) ** 2 % Q for k in range(195)]
    derived_js = set()
    for x in roots:
        require(polynomial_value(deuring, x, Q) == (0, 0), "Invalid Deuring root")
        x2 = mul(x, x, Q)
        numerator_base = add(add(x2, (-x[0], -x[1]), Q), (1, 0), Q)
        numerator = mul(mul(numerator_base, numerator_base, Q), numerator_base, Q)
        denominator = mul(x2, mul((x[0] - 1, x[1]), (x[0] - 1, x[1]), Q), Q)
        a, b = denominator
        norm_inverse = pow((a * a - 2 * b * b) % Q, -1, Q)
        inverse = (a * norm_inverse % Q, -b * norm_inverse % Q)
        j = mul(numerator, inverse, Q)
        derived_js.add((256 * j[0] % Q, 256 * j[1] % Q))
    require(derived_js == set(js), "Incorrect list of supersingular invariants")
    matrix = data["brandt_T2_function_matrix"]
    require(len(matrix) == 33 and all(len(row) == 33 for row in matrix), "Bad Brandt matrix shape")
    for i, row in enumerate(matrix):
        require(all(type(v) is int and 0 <= v <= 3 for v in row) and sum(row) == 3,
                "Invalid isogeny multiplicities")
        multiset = [js[j] for j, v in enumerate(row) for _ in range(v)]
        require(polynomial_from_roots(multiset, Q) == phi2_coefficients(js[i], Q),
                "Brandt row is not the complete modular polynomial factorization")
    require(len(data["primitive_eigenvectors"]) == 1, "Expected one declared eigenvector")
    vector = data["primitive_eigenvectors"][0]
    require(len(vector) == 33 and math.gcd(*vector) == 1, "Nonprimitive eigenfunction")
    require(all(sum(matrix[i][j] * vector[j] for j in range(33)) == -2 * vector[i]
                for i in range(33)), "Incorrect exact Hecke eigenfunction")
    shifted = [[matrix[i][j] + 2 * (i == j) for j in range(33)] for i in range(33)]
    require(rank_mod(shifted, 101) == 32, "Hecke eigenline is not certified unique over Q")
    require(3 - point_count(2) == -2, "Wrong curve Hecke eigenvalue")
    lookup = dict(zip(js, vector))
    require(all(lookup[(a, -b % Q)] == lookup[(a, b)] for a, b in js),
            "Unexpected Frobenius action")
    h71 = data["hilbert_class_polynomial_D_minus71_ascending"]
    cm = [j for j in js if polynomial_value(h71, j, Q) == (0, 0)]
    require(len(cm) == 7, "CM reductions are not seven distinct roots")
    require(polynomial_from_roots(cm, Q) == [(c % Q, 0) for c in h71], "Bad CM factorization")
    cm_values = [lookup[j] for j in cm]
    require(sum(cm_values) == 0 and len(set(cm_values)) > 1,
            "Auxiliary C7 Fourier nonvanishing certificate failed")
    return lookup, {"vertices": 33, "Deuring_roots": 194, "rational_eigenline_dimension": 1,
                    "CM_order7_values": cm_values}


def valuation(x, bound):
    if x == 0:
        return bound
    v = 0
    while x % Q == 0:
        x //= Q
        v += 1
    return v


def pair_valuation(x, bound):
    return min(valuation(x[0], bound), valuation(x[1], bound))


def verify_hensel(coeffs, lifts, precision=4):
    require(len(coeffs) == 141 and coeffs[-1] == 1 and len(lifts) == 140,
            "Wrong class polynomial or root count")
    derivative = [i * coeffs[i] for i in range(1, len(coeffs))]
    result = []
    for r in lifts:
        s = pair_valuation(polynomial_value(derivative, r, Q ** 80), 80)
        h = pair_valuation(polynomial_value(coeffs, r, Q ** 80), 80)
        require(h > 2 * s and h - s >= precision, "Insufficient certified Hensel precision")
        result.append((h, s))
    reductions = [(a % Q ** precision, b % Q ** precision) for a, b in lifts]
    require(len(set(reductions)) == 140, "Hensel root balls are not pairwise disjoint")
    return reductions, result


def verify_jet(coeffs, lifts, data, lookup):
    precision = data["root_precision_exponent"]
    require(precision == 4, "Unreviewed comparison precision")
    reductions, hensel = verify_hensel(coeffs, lifts, precision)
    modulus = Q ** precision
    graph = [[j for j, y in enumerate(reductions)
              if polynomial_value(phi2_coefficients(x, modulus), y, modulus) == (0, 0)]
             for x in reductions]
    require(all(len(row) == 2 for row in graph), "CM horizontal neighbors not uniquely isolated")
    require(graph == data["horizontal_2_isogeny_adjacency"], "Stored horizontal graph differs")
    cycle = data["class_generator_cycle"]
    require(sorted(cycle) == list(range(140)), "CM cycle is not a permutation")
    require(all(cycle[(i + 1) % 140] in graph[cycle[i]] for i in range(140)),
            "CM class labeling does not follow the horizontal cycle")
    weights = [lookup[(reductions[i][0] % Q, reductions[i][1] % Q)] for i in cycle]
    require(weights == data["CM_function_weights_in_cycle_order"], "Incorrect CM function weights")
    grouped = [sum(weights[j::5]) for j in range(5)]
    moments = [sum(grouped[j] * math.comb(j, k) for j in range(5)) for k in range(3)]
    require(grouped == data["raw_Gamma1_coefficients"], "Incorrect finite-level coefficients")
    require([v % 5 for v in moments] == data["raw_quadratic_jet_mod5"], "Incorrect coefficient residues")
    require(moments[2] % 5 != 0, "Quadratic coefficient vanishes modulo 5")
    norm_jet = [sum(math.comb(j, k) for j in range(5)) % 5 for k in range(3)]
    require(norm_jet == [0, 0, 0], "Old-level correction affects the quadratic jet")
    return {"CM_classes": 140, "comparison_precision": "389^4",
            "max_derivative_valuation": max(s for h, s in hensel),
            "min_certified_root_precision": min(h - s for h, s in hensel),
            "raw_group_ring_coefficients": grouped, "exact_moments": moments,
            "moments_mod5": [v % 5 for v in moments], "old_level_norm_jet_mod5": norm_jet,
            "unit_root_mod5": 2,
            "regularization_convention": "Chida-Hsieh section 4.2; class-cycle generator; primitive phi as recorded",
            "regularized_quadratic_residue_mod5": moments[2] * pow(2, -2, 5) % 5,
            "invariant_conclusion": "quadratic coefficient is a 5-adic unit; numerical residue depends on normalization"}


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--gp", help="Also replay the exact PARI arithmetic and modular-symbol audit")
    parser.add_argument("--output", default="evidence/certificate-verification.json")
    args = parser.parse_args(argv)
    started = time.monotonic()
    ss = read_json(ROOT / "data/supersingular-389.json")
    cm = read_json(ROOT / "data/cm-jet-p5.json")
    coeffs = read_json(ROOT / "data/H-minus44375-coeffs.json")
    lifts = read_json(ROOT / "data/CM-minus44375-lifts32.json")
    polynomials = []
    for d, expected in [(-71, ss["hilbert_class_polynomial_D_minus71_ascending"]), (-44375, coeffs)]:
        reconstructed, report = reconstruct_class_polynomial(d)
        require(reconstructed == expected, "Independent rigorous CM reconstruction disagrees")
        polynomials.append(report)
    lookup, ss_report = verify_supersingular(ss)
    jet_report = verify_jet(coeffs, lifts, cm, lookup)
    counts = {str(p): point_count(p) for p in (2, 3, 5, 7, 29)}
    require(counts == {"2": 5, "3": 6, "5": 9, "7": 13, "29": 36}, "Curve point count mismatch")
    b2, b4, b6, b8 = 4, -4, 1, -3
    discriminant = -b2 * b2 * b8 - 8 * b4 ** 3 - 27 * b6 ** 2 + 9 * b2 * b4 * b6
    c4, c6 = b2 ** 2 - 24 * b4, -b2 ** 3 + 36 * b2 * b4 - 216 * b6
    require((discriminant, c4, c6) == (389, 112, -856), "Curve invariant mismatch")
    require(pow((-c6) % Q, (Q - 1) // 2, Q) == 1, "Multiplicative reduction is not split")
    require(pow((-8) % 5, 2, 5) == 4 and pow((-8) % 29, 14, 29) == 28,
            "Residual irreducibility witness failed")
    require(pow((-71) % 5, 2, 5) == 1 and pow((-71) % Q, (Q - 1) // 2, Q) == Q - 1,
            "Wrong splitting conditions")
    audit = read_json(ROOT / "data/arithmetic-audit.json")
    symbols = audit["modular_symbols"]
    characters = [1 if pow(a, 35, 71) == 1 else -1 for a in range(1, 71)]
    require(characters == symbols["twist_kronecker_weights_a1_to70"], "Wrong quadratic character")
    twist_sum = sum(x * y for x, y in zip(characters, symbols["twist_cusp_values_a1_to70"]))
    require(twist_sum == -4, "Twist modular-symbol nonvanishing failed")
    pari_replay = "not requested; see recorded independent audit"
    if args.gp:
        result = subprocess.run([args.gp, "-fq", "-s", "256M", "scripts/arithmetic_audit.gp"],
                                cwd=ROOT, capture_output=True, text=True)
        require(result.returncode == 0 and "***" not in result.stderr,
                "PARI replay failed: " + result.stderr)
        require("PARI_ARITHMETIC_AUDIT_PASS" in result.stdout, "PARI pass marker absent")
        pari_replay = "PASS"
    import flint
    input_files = ["verify_certificate.py", "data/supersingular-389.json", "data/cm-jet-p5.json",
                   "data/H-minus44375-coeffs.json", "data/CM-minus44375-lifts32.json",
                   "data/arithmetic-audit.json"]
    report = {"result": "PASS", "recorded_utc": dt.datetime.now(dt.timezone.utc).isoformat(),
              "python_flint_version": flint.__version__,
              "scope": "Exact computational certificate; classical arithmetic bridges are documented, not end-to-end formalized",
              "class_polynomial_reconstruction": polynomials, "supersingular": ss_report,
              "theta_jet": jet_report, "curve_point_counts": counts,
              "quadratic_twist_modular_symbol_sum": twist_sum, "PARI_replay": pari_replay,
              "input_sha256": {name: hashlib.sha256((ROOT / name).read_bytes()).hexdigest() for name in input_files},
              "seconds": round(time.monotonic() - started, 3)}
    target = ROOT / args.output
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    try:
        main()
    except (ValueError, KeyError, ImportError) as exc:
        print(f"CERTIFICATE REJECTED: {exc}", file=sys.stderr)
        raise SystemExit(1)
