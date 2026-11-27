#!/usr/bin/env python3
"""Independent small consequences of the separate E433 CM certificate.

This checks the eigenline, period values, cyclotomic norm, finite theta
coefficients, and the rigorous twist interval. The full CM root/graph and
class-polynomial certification belongs to second_theta's separate verifier.
The Gross special-value and theta interpolation interpretations are written
mathematical dependencies in README.md, not outputs of Python arithmetic.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
from functools import reduce
from hashlib import sha256
import json
from math import comb, gcd, prod
from pathlib import Path

ROOT = Path(__file__).resolve().parent
THETA = ROOT.parent / "second_theta" / "certificate.json"


def rank(matrix):
    a = [[Fraction(x) for x in row] for row in matrix]
    r = 0
    for j in range(len(a[0])):
        pivot = next((i for i in range(r,len(a)) if a[i][j]), None)
        if pivot is None:
            continue
        a[r], a[pivot] = a[pivot], a[r]
        for i in range(r+1,len(a)):
            q = a[i][j]/a[r][j]
            for k in range(j,len(a[0])):
                a[i][k] -= q*a[r][k]
        r += 1
        if r == len(a):
            break
    return r


def determinant(matrix):
    a = [[Fraction(x) for x in row] for row in matrix]
    sign = 1
    for j in range(len(a)):
        pivot = next((i for i in range(j,len(a)) if a[i][j]), None)
        if pivot is None:
            return Fraction(0)
        if pivot != j:
            a[j], a[pivot] = a[pivot], a[j]
            sign = -sign
        for i in range(j+1,len(a)):
            q = a[i][j]/a[j][j]
            for k in range(j,len(a)):
                a[i][k] -= q*a[j][k]
    return sign*prod(a[i][i] for i in range(len(a)))


def reduce_phi7(poly):
    a = list(poly)+[0]*max(0,6-len(poly))
    for j in range(len(a)-1,5,-1):
        value = a[j]
        for k in range(7):
            a[j-6+k] -= value
    return a[:6]


def period_norm(poly):
    columns = [reduce_phi7([0]*j+list(poly)) for j in range(6)]
    matrix = [[columns[j][i] for j in range(6)] for i in range(6)]
    return determinant(matrix), matrix


def certificate():
    source = json.loads(THETA.read_text())
    screen = json.loads((ROOT / "result.json").read_text())
    twist = json.loads((ROOT / "twist-lvalue.json").read_text())
    assert source["curve"]["ainvs"] == screen["chosen_curve"]["ainvs"] == [1,0,0,0,1]
    ss = source["supersingular"]
    js = [tuple(j) for j in ss["supersingular_j"]]
    phi = ss["primitive_eigenfunction"]
    B = ss["T2_matrix"]
    assert len(js) == len(set(js)) == len(phi) == len(B) == 36
    assert (0,0) not in js and (1728 % 433,0) not in js
    assert all(len(row) == 36 and sum(row) == 3 for row in B)
    assert all(B[i][j] == B[j][i] for i in range(36) for j in range(36))
    assert reduce(gcd,phi) == 1
    assert ss["T2_eigenvalue"] == -1
    assert all(sum(B[i][j]*phi[j] for j in range(36)) == -phi[i] for i in range(36))
    eigenspace_matrix = [[B[i][j]+int(i==j) for j in range(36)] for i in range(36)]
    assert rank(eigenspace_matrix) == 35
    cm = {v["discriminant"]: v for v in source["CM"]}
    cyclic_values = {}
    for discriminant, h in [(-71,7),(-44375,140)]:
        data = cm[discriminant]
        assert data["class_number"] == h
        cycle = data["generator_cycle"]
        assert sorted(cycle) == list(range(h))
        values = [phi[js.index(tuple(x % 433 for x in root))] for root in data["root_lifts"]]
        cyclic_values[discriminant] = [values[i] for i in cycle]
        assert cyclic_values[discriminant] == data["CM_values"]
    seven = cyclic_values[-71]
    assert sum(seven) == 0 and len(set(seven)) > 1
    norm, multiplication_matrix = period_norm(seven)
    assert norm == 49
    grouped = [sum(v for i,v in enumerate(cyclic_values[-44375]) if i % 5 == j) for j in range(5)]
    raw = [sum(comb(i,j)*grouped[i] for i in range(j,5)) for j in range(5)]
    assert grouped == cm[-44375]["grouped_coefficients"] == [0,1,-2,1,0]
    assert raw == cm[-44375]["raw_T_coefficients"] == [0,0,1,1,0]
    # The only lower-level correction is a scalar times Phi5(gamma),
    # possibly translated. Mod5 its expansion starts at T^4.
    norm5 = [sum(comb(i,j) for i in range(j,5)) for j in range(5)]
    assert [x % 5 for x in norm5] == [0,0,0,0,1]
    relation = [0]+[comb(5,j) for j in range(1,6)]
    assert [x % 5 for x in relation] == [0,0,0,0,0,1]
    assert screen["anomalous_prime_audit"]["ordinary_root_mod25"] % 5 == 1
    lo, hi = map(int, twist["central_L_scaled_bounds"])
    assert 0 < lo < hi and twist["conductor"] == 2182753
    assert twist["base_curve"] == "433.a1" and twist["twist_discriminant"] == -71
    return {
        "schema": "bsd-second-pilot-toric-consequences-v1", "status": "PASS",
        "T2_eigenvalue": -1, "T2_minus_eigenspace_dimension": 1,
        "primitive_eigenfunction": phi,
        "all_supersingular_automorphism_weights": 1,
        "CM7_values_in_certified_cycle_order": seven,
        "trivial_period": 0, "nontrivial_period_polynomial_coefficients": seven,
        "cyclotomic_multiplication_matrix": multiplication_matrix,
        "norm_of_order7_period": 49,
        "nontrivial_order7_periods_are_5adic_units": True,
        "raw_grouped_coefficients": grouped, "raw_T_coefficients": raw,
        "raw_group_ring_factorization": "gamma*(gamma−1)^2",
        "ordinary_regularization_quadratic_residue_mod5": 1,
        "lower_level_norm_element_T_coefficients": norm5,
        "finite_quotient_relation_T_coefficients": relation,
        "twist_L_interval": twist["central_L_decimal_bounds"],
        "arithmetic_implications_with_written_source_theorems": {
            "L_E_K_trivial_at1": "0 by Gross's exact period identity",
            "L_E_twist_minus71_at1": "positive by the separate rational interval certificate",
            "L_E_at1": "0 by the trivial-character factorization and the nonzero twist factor",
            "all_nontrivial_order7_auxiliary_L_values": "nonzero by the exact period norm49 and Gross's formula",
            "theta_order_at_augmentation": "2 after exact constant and linear vanishing and ordinary level compatibility, as explained in README.md"},
        "input_sha256": {"second_theta/certificate.json": sha256(THETA.read_bytes()).hexdigest(),
                         "second_pilot/result.json": sha256((ROOT / "result.json").read_bytes()).hexdigest(),
                         "second_pilot/twist-lvalue.json": sha256((ROOT / "twist-lvalue.json").read_bytes()).hexdigest()},
        "scope": "Independent small exact consequences. Full class-polynomial, root and graph certification is a separate input; special-value and theta interpolation identities are mathematical theorems, not checked by this executable. No rational-point or finite-Sha input, no full localization theorem."}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = certificate()
    if args.check:
        assert result == json.loads((ROOT / "toric-consequences.json").read_text())
        print("PASS: eigenline, seven-period norm49, raw theta T²+T³, and positive twist interval")
    elif args.output:
        args.output.write_text(json.dumps(result,indent=2,sort_keys=True)+"\n")
        print(f"Wrote {args.output}")
    else:
        print(json.dumps(result,indent=2,sort_keys=True))


if __name__ == "__main__":
    main()
