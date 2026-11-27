#!/usr/bin/env python3
"""Exact Q(zeta_7) period reduction; no CM or L-value identification is performed."""

import argparse
import json


def check_vector(values):
    if not isinstance(values, list) or len(values) != 7:
        raise ValueError("Supply a JSON list of exactly seven integers.")
    if not all(isinstance(x, int) and not isinstance(x, bool) for x in values):
        raise ValueError("All seven values must be exact integers, not floats or booleans.")
    return values


def reduce_phi7(coefficients):
    coefficients = list(coefficients)
    while len(coefficients) < 6:
        coefficients.append(0)
    for degree in range(len(coefficients)-1, 5, -1):
        top = coefficients[degree]
        coefficients[degree] = 0
        for offset in range(6):
            coefficients[degree-6+offset] -= top
    return coefficients[:6]


def multiply_mod_phi7(left, right):
    product = [0]*(len(left)+len(right)-1)
    for i, a in enumerate(left):
        for j, b in enumerate(right):
            product[i+j] += a*b
    return reduce_phi7(product)


def period_remainder(values, character_power):
    check_vector(values)
    if character_power not in range(1, 7):
        raise ValueError("A nontrivial character power must be between one and six.")
    permuted = [0]*7
    for i, value in enumerate(values):
        permuted[(character_power*i) % 7] += value
    return reduce_phi7(permuted)


def analyze(values):
    values = check_vector(values)
    remainders = [period_remainder(values, j) for j in range(1, 7)]
    nonzero = [any(row) for row in remainders]
    constant = len(set(values)) == 1
    assert nonzero == [not constant]*6
    unequal_pair = next(([i, j] for i in range(7) for j in range(i+1, 7)
                         if values[i] != values[j]), None)
    norm = [1, 0, 0, 0, 0, 0]
    for row in remainders:
        norm = multiply_mod_phi7(norm, row)
    assert norm[1:] == [0]*5
    assert (norm[0] != 0) == (not constant)
    # Conjugate pairs imply a positive norm for a nonzero algebraic number.
    assert norm[0] >= 0
    return {
        "values": values,
        "sum_of_values": sum(values),
        "all_values_equal": constant,
        "unequal_pair_indices": unequal_pair,
        "period_remainders_j_1_to_6": remainders,
        "all_nontrivial_periods_nonzero_over_Q_zeta7": not constant,
        "cyclotomic_norm": norm[0],
        "geometric_validation_performed": False,
        "L_value_nonvanishing_certified": False,
        "missing_bridge": "Verified Gross CM evaluations, eigenfunction identification, and applicable nonzero toric-period formula",
    }


def fixtures():
    cases = [
        ("zero_vector", [0]*7, 0),
        ("constant_nonzero_fault", [5]*7, 0),
        ("unit_period", [1, 0, 0, 0, 0, 0, 0], 1),
        ("balanced_one_minus_zeta", [1, -1, 0, 0, 0, 0, 0], 7),
        ("invisible_mod_29_but_nonzero", [29, 0, 0, 0, 0, 0, 0], 29**6),
    ]
    results = []
    for name, values, expected_norm in cases:
        result = analyze(values)
        assert result["cyclotomic_norm"] == expected_norm
        # Check invariance under cyclic shift and a new class-group generator.
        for shift in range(7):
            shifted = values[shift:]+values[:shift]
            assert analyze(shifted)["cyclotomic_norm"] == expected_norm
        for generator in range(1, 7):
            permuted = [values[(generator*i) % 7] for i in range(7)]
            assert analyze(permuted)["cyclotomic_norm"] == expected_norm
        result["fixture_name"] = name
        result["actual_Gross_data"] = False
        results.append(result)
    for bad in [[], [1]*6, [1]*8, [1.0]*7, [True]*7, "1234567"]:
        try:
            analyze(bad)
        except ValueError:
            pass
        else:
            raise AssertionError("Invalid vector accepted")
    return {"status": "Exact cyclotomic fixtures passed; no curve-specific periods computed", "fixtures": results}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--values-json", help="JSON list of exactly seven integral period coefficients")
    args = parser.parse_args()
    if args.values_json is None:
        result = fixtures()
    else:
        try:
            result = analyze(json.loads(args.values_json))
        except (ValueError, json.JSONDecodeError) as error:
            parser.error(str(error))
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
