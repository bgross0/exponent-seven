#!/usr/bin/env python3
"""Check exact bound arithmetic for the written infinite Katz comparison.

This instantiates the proved inequalities with actual certificate data.
It does not replace the geometric/source-provenance arguments in the note.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path


HERE = Path(__file__).resolve().parent


def ceil_div(n, d):
    return -((-n)//d)


def g(j):
    return ceil_div(5*j-11, 6)-j//6


def input_coordinate_bound(i):
    return max(0, ceil_div(20*i-58, 25)-4)-i//6


def valuation(n, cap=100):
    if n == 0:
        return cap
    result = 0
    while n % 5 == 0:
        result += 1
        n //= 5
    return result


def compute():
    paths = {
        "actual_projection": HERE/"actual-cm-finite-projection.json",
        "actual_matrix_replay": HERE/"actual-katz-replay.json",
        "Euler_transfer": HERE.parent/"cm_product_transfer/transfer-result.json",
    }
    data = {key: json.loads(path.read_text()) for key, path in paths.items()}
    projection = data["actual_projection"]
    matrix = data["actual_matrix_replay"]["matrix_certificate_replay"]
    m = matrix["matrix_digits"]
    fit_guard = matrix["inverse_minor_guard"]
    basis_digits = matrix["coordinate_digits"]+fit_guard
    assert (m, basis_digits, fit_guard) == (6, 8, 1)
    assert projection["fit_guard"] == fit_guard
    assert projection["coordinate_digits"] == basis_digits-fit_guard

    # The formulas prove the shifts for every integer; residue blocks below
    # check the constants and minima needed by the actual cutoff.
    assert [g(j) for j in range(6)] == [-1, -1, 0, 1, 2, 3]
    assert all(g(j+6) == g(j)+4 for j in range(6))
    assert min(g(j) for j in range(2, 8)) == 0
    output_tail = min(g(j) for j in range(11, 17))
    assert output_tail == 7
    assert all(input_coordinate_bound(i+30) == input_coordinate_bound(i)+19
               for i in range(8, 38))
    input_minimum = min(input_coordinate_bound(i) for i in range(38))
    input_tail = min(input_coordinate_bound(i) for i in range(11, 41))
    assert (input_minimum, input_tail) == (-1, 2)
    tail_q_gain = 11//6
    y_tail = input_minimum+output_tail
    y_qtail = y_tail+tail_q_gain
    y_head_error = min(basis_digits, y_qtail)-fit_guard
    assert (y_tail, y_qtail, y_head_error) == (6, 7, 6)

    rows = []
    for index, name in enumerate(("alpha", "beta")):
        h = index
        source = projection["projection"]["stabilization_coefficients"][name]
        raw = [source[f"W2_xi{i}"] for i in range(3)]
        fixture = source["U_f_"+name]
        precision = raw[0]["precision"]
        kernel_digits = m-projection["dual_guards"][name]
        eta = min(row["precision"]["row_valuation_lower_bound"] for row in raw)
        rho = precision["normalization_row_valuation_lower_bound"]
        denominator_valuation = raw[0]["denominator_exponent"]
        assert all(row["denominator_exponent"] == denominator_valuation for row in raw)
        numerator_valuation = min(valuation(row["residue"]) for row in raw)
        assert output_tail-h >= m
        # Once the unknown head valuation is bootstrapped to >=0, the initial
        # error is already above rho. Substitution gives the stronger bound.
        initial_normalizer_error = min(basis_digits, output_tail-h+tail_q_gain)-fit_guard
        assert initial_normalizer_error > rho
        r_tail = rho+output_tail-h
        r_head_error = min(basis_digits, r_tail+tail_q_gain)-fit_guard
        numerator_digits = min(y_head_error, kernel_digits+eta, y_tail-h)
        denominator_digits = min(r_head_error, kernel_digits+rho, r_tail-h)
        assert numerator_digits == precision["numerator_digits"]
        assert denominator_digits == precision["denominator_digits"]
        assert denominator_digits > denominator_valuation
        quotient_digits = min(numerator_digits-denominator_valuation,
                              denominator_digits+numerator_valuation-2*denominator_valuation)
        assert quotient_digits == min(row["absolute_digits"] for row in raw)
        quotient_valuation = numerator_valuation-denominator_valuation
        five_r = data["Euler_transfer"]["five_times_R_eigenvalues_U_alpha_beta"][index]
        r_valuation = min(map(valuation, five_r))-1
        assert r_valuation == data["Euler_transfer"]["R_eigenvalue_valuations_U_alpha_beta"][index]
        r_precision = 7  # 5R is known modulo5^8, followed by division by5.
        target_digits = min(quotient_digits+r_valuation,
                            r_precision+quotient_valuation)
        target = projection["projection"]["target_depleted_stabilization_coefficients"][name]
        assert target_digits == min(target[f"W2_xi{i}"]["absolute_digits"] for i in range(3))
        rows.append({"direction": name, "eigenvalue_valuation": h,
                     "head_kernel_digits": kernel_digits, "tail_dual_valuation_bound": -h,
                     "input_head_valuation": eta, "normalizer_head_valuation": rho,
                     "normalizer_tail_bound": r_tail, "normalizer_head_error_bound": r_head_error,
                     "numerator_digits": numerator_digits, "denominator_digits": denominator_digits,
                     "numerator_valuation": numerator_valuation, "denominator_valuation": denominator_valuation,
                     "undepleted_coefficient_digits": quotient_digits,
                     "Euler_factor_valuation": r_valuation,
                     "depleted_coefficient_digits": target_digits,
                     "depleted_coefficient_valuation": quotient_valuation+r_valuation})
    assert [row["depleted_coefficient_digits"] for row in rows] == [3, 1]
    assert [row["depleted_coefficient_valuation"] for row in rows] == [-1, -2]
    return {
        "status": "PASS", "head_pole_cutoff": 10,
        "output_column_bound_residues_mod6": [g(j) for j in range(6)],
        "output_column_bound_shift_per6": 4,
        "tail_output_column_bound": output_tail,
        "CM_coordinate_bound_shift_per30_after_index8": 19,
        "CM_global_coordinate_bound": input_minimum, "CM_tail_coordinate_bound": input_tail,
        "U_CM_tail_coordinate_bound": y_tail, "U_CM_q_tail_bound": y_qtail,
        "U_CM_fitted_head_error_bound": y_head_error,
        "actual_precision_table": rows,
        "accepted_Sage_runtime_source_sha256": "6292ef3c2e20c2456058fdac25ecb1576e9abdace4c47a3aae13b1469f58703a",
        "source_sha256": {key: hashlib.sha256(path.read_bytes()).hexdigest() for key, path in paths.items()},
        "scope": "Exact arithmetic instantiation of INFINITE_KATZ_BRIDGE.md using actual finite certificates. Geometric Katz splitting, source-based head provenance, Banach continuity, and the published U radius theorem are mathematical premises established in the written proof, not inferred by this finite arithmetic checker. Arithmetic regulator and global-class comparisons remain separate.",
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true")
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    result = compute()
    path = HERE/"infinite-katz-bounds.json"
    if args.check:
        assert result == json.loads(path.read_text())
    text = json.dumps(result, indent=2, sort_keys=True)+"\n"
    if args.write:
        path.write_text(text)
    print(text, end="")


if __name__ == "__main__":
    main()
