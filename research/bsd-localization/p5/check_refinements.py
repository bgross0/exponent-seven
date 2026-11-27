#!/usr/bin/env python3
"""Small exact refinements of the independently audited p=5 BSD pilot.

This uses the existing rational group law and cyclotomic arithmetic, and an
extracted seven-point graph. It does not rerun CM geometry or Lean checking.
"""

import argparse
from fractions import Fraction
import json
from math import comb
from pathlib import Path
import runpy


HERE = Path(__file__).resolve().parent
BASE = HERE.parent
LOGIC = runpy.run_path(str(BASE / "logic/verify_logic.py"))
CYCLO = runpy.run_path(str(BASE / "logic/c7_period.py"))


def cycle_values(matrix, values):
    assert len(matrix) == len(values) == 7
    assert all(len(row) == 7 and sum(row) == 2 for row in matrix)
    assert all(matrix[i][j] == matrix[j][i] and matrix[i][j] in (0, 1)
               for i in range(7) for j in range(7))
    cycle, previous, current = [0], None, 0
    while True:
        candidates = [j for j, edge in enumerate(matrix[current]) if edge and j != previous]
        next_vertex = min(candidates)
        if next_vertex == 0:
            break
        assert next_vertex not in cycle
        cycle.append(next_vertex)
        previous, current = current, next_vertex
    assert len(cycle) == 7
    return cycle, [values[i] for i in cycle]


def log_mod_25(point):
    point = tuple(map(Fraction, point))
    multiple = LOGIC["multiply"](9, point)
    assert multiple is not None
    z = -multiple[0] / multiple[1]
    numerator, denominator = z.numerator, z.denominator
    v = LOGIC["valuation"](numerator, 5) - LOGIC["valuation"](denominator, 5)
    assert v >= 1
    z_mod = LOGIC["rational_mod"](z, 25)
    return {"point": [int(a) for a in point], "multiple": 9,
            "z_numerator": str(numerator), "z_denominator": str(denominator),
            "valuation_z": v, "z_mod_25": z_mod,
            "log_mod_25_given_integral_formal_log": z_mod * pow(9, -1, 25) % 25}


def verify():
    inputs = json.loads((HERE / "inputs.json").read_text())
    count = 1 + sum((y*y+y-x*x*x-x*x+2*x) % 5 == 0
                    for x in range(5) for y in range(5))
    assert count == 9 and 6 - count == -3
    omega_roots = [x for x in range(5) if (x*x-x+18) % 5 == 0]
    assert omega_roots == [2, 4]
    assert not any((x*x+2*x+3) % 5 == 0 for x in range(5))
    roots_25 = [a for a in range(25) if (a*a+3*a+5) % 25 == 0]
    unit_roots = [a for a in roots_25 if a % 5]
    assert unit_roots == [7]

    frobenius_orbit = [pow(5, j, 7) for j in range(6)]
    assert len(set(frobenius_orbit)) == 6 and pow(5, 6, 7) == 1
    # The real cubic Hecke field is also not Q5; p-stabilizing requires degree6.
    real_cubic_values = [(t**3+t*t-2*t-1) % 5 for t in range(5)]
    assert all(real_cubic_values)

    cycle, values = cycle_values(inputs["CM_induced_T2"], inputs["CM_values_in_saved_j_order"])
    periods = CYCLO["analyze"](values)
    assert values == [-1, 0, -1, 1, 0, 0, 1]
    assert periods["cyclotomic_norm"] == 49
    # Explicit inverse of this period in F5[X]/Phi7, stronger than a decimal.
    inverse_mod_5 = [3, 2, 1, 1, 2, 3]
    product = CYCLO["multiply_mod_phi7"](values, inverse_mod_5)
    assert [a % 5 for a in product] == [1, 0, 0, 0, 0, 0]
    for remainder in periods["period_remainders_j_1_to_6"]:
        assert any(a % 5 for a in remainder)
    # The saved j-order does not specify a class-group character. It happens
    # to give norm7, which must not be confused with the actual cycle norm49.
    arbitrary_order_norm = CYCLO["analyze"](inputs["CM_values_in_saved_j_order"])["cyclotomic_norm"]
    assert arbitrary_order_norm == 7

    logs = [log_mod_25([0, 0]), log_mod_25([1, 0])]
    assert [x["log_mod_25_given_integral_formal_log"] for x in logs] == [5, 15]
    strict_line_coordinates_mod_5 = [logs[1]["log_mod_25_given_integral_formal_log"] // 5,
                                    -logs[0]["log_mod_25_given_integral_formal_log"] // 5]
    assert strict_line_coordinates_mod_5 == [3, -1]

    grouped = inputs["raw_Gamma1_coefficients"]
    moments = [sum(comb(j, k) * b for j, b in enumerate(grouped)) for k in range(3)]
    assert grouped == [5, -1, -1, 5, -8] and moments == [0, -20, -34]
    norm_element = [sum(comb(j, k) for j in range(5)) % 5 for k in range(5)]
    assert norm_element == [0, 0, 0, 0, 1]
    regularized_quadratic_residue = moments[2] * pow(2, -2, 5) % 5
    assert regularized_quadratic_residue == 4

    # A coefficient trace is not a faithful descent operation on vectors:
    # Tr(zeta-zeta^2)=(-1)-(-1)=0 while zeta-zeta^2 != 0.
    trace_zero_coefficients = [0, 1, -1, 0, 0, 0]
    trace = 6 * trace_zero_coefficients[0] - sum(trace_zero_coefficients[1:])
    assert trace == 0 and any(trace_zero_coefficients)

    return {
        "status": "PASS: exact p5 arithmetic and consequences of supplied CM data",
        "input_provenance": inputs["source_files"],
        "curve": {"a_invariants": [0, 1, 1, -2, 0], "points_mod_5": count,
                  "a5": -3, "unit_root_mod_25": 7, "omega_roots_mod_5": omega_roots},
        "coefficient_field": {"Q5_zeta7_degree": 6, "unramified": True,
                              "Frobenius_orbit_of_zeta_exponents": frobenius_orbit,
                              "real_Hecke_field_cubic_values_mod_5": real_cubic_values},
        "actual_CM_cycle": {"local_indices": cycle, "values": values,
                            "cyclotomic_norm": 49, "all_six_periods_are_5_adic_units": True,
                            "inverse_period_coefficients_mod_5": inverse_mod_5,
                            "saved_j_order_norm_not_a_toric_norm": arbitrary_order_norm},
        "localization": logs,
        "strict_regulator_vector_coefficients_mod_5": strict_line_coordinates_mod_5,
        "theta_from_supplied_grouped_data": {"raw_coefficients": grouped,
                                             "moments": moments,
                                             "norm_element_T_coefficients_mod_5": norm_element,
                                             "regularized_quadratic_coefficient_mod_5": 4},
        "trace_descent_fault_case": {"coefficients_in_1_zeta_through_zeta5": trace_zero_coefficients,
                                     "field_trace": trace, "nonzero_element": True},
        "scope": "The input archive establishes CM/theta identifications. This refinement checks the extracted cycle, period units, coefficient field, and local logs; it does not rerun the full CM proof or claim Lean verification."
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--check", type=Path)
    args = parser.parse_args()
    result = verify()
    if args.check:
        assert json.loads(args.check.read_text()) == result
        print("PASS: p5 refinement certificate matches exact recomputation")
    elif args.output:
        args.output.write_text(json.dumps(result, indent=2) + "\n")
        print("Wrote " + str(args.output))
    else:
        print(json.dumps(result, indent=2))
