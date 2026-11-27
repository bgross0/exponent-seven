#!/usr/bin/env python3
"""Exact regressions for finite projection and its precision theorem.

Uses the actual saved crystalline operator for the two-slope regression.
Other fixtures are identified as abstract linear algebra, not CM values.
"""
from __future__ import annotations

import argparse
import copy
from fractions import Fraction
import hashlib
import json
from math import isqrt
from pathlib import Path

import numpy as np

from finite_projection import (CertificateError, array, matmul_mod, dual_kernel,
    verify_dual_kernel, solve_integral, verify_integral_solution, quotient_ball,
    normalize_projection, ball_contains_integer, combine_balls, valuation)
from project_capsule import (prepare_inputs, projections, verify_certificate,
                             transfer_eigenvalues, cubic_mul)


ROOT = Path(__file__).resolve().parent


def fraction_valuation(x, p):
    x = Fraction(x)
    return valuation(x.numerator, p, 1000)-valuation(x.denominator, p, 1000)


def rejected(thunk):
    try:
        thunk()
    except CertificateError:
        return True
    return False


def elliptic_subspace_adapter_regression():
    """Actual elliptic q-series in a deliberately restricted 2D model.

    This tests the producer/consumer interface without pretending to supply
    the 1333-dimensional Katz geometry or the actual CM input.
    """
    p, m, md, ell, td = 5, 7, 9, 8, 12
    bound = 5*ell
    ap = {}
    for prime in range(2, bound):
        if all(prime % d for d in range(2, isqrt(prime)+1)):
            count = 1+sum((y*y+y-x*x*x-x*x+2*x) % prime == 0
                          for x in range(prime) for y in range(prime))
            ap[prime] = prime+1-count
    assert ap[5] == -3
    coeff = [0, 1]
    for n in range(2, bound):
        value, remaining = 1, n
        for prime in ap:
            if remaining % prime:
                continue
            exponent = 0
            while remaining % prime == 0:
                remaining //= prime; exponent += 1
            prev, current = 1, ap[prime]
            for _ in range(2, exponent+1):
                prev, current = current, ap[prime]*current-prime*prev
            value *= current
            if remaining == 1:
                break
        assert remaining == 1
        coeff.append(value)
    alpha = 2
    for d in range(1, td):
        alpha = next(alpha+t*p**d for t in range(p)
                     if ((alpha+t*p**d)**2+3*(alpha+t*p**d)+5) % p**(d+1) == 0)
    beta = (-3-alpha) % p**td
    ff = {}
    for name, other in (("alpha", beta), ("beta", alpha)):
        ff[name] = [(coeff[n]-(other*coeff[n//5] if n % 5 == 0 else 0)) % p**td
                    for n in range(bound)]
    capsule = {"schema": "katz-matrix-gate-v1",
        "parameters": {"prime": p, "level": 389, "weight": 2, "matrix_digits": m},
        "mdash": md, "elldash": ell,
        "row_operator_A_mod_5m": [[alpha % p**m, 0], [0, beta % p**m]],
        "Katz_E_mod_5mdash": [[a % p**md for a in ff[name]] for name in ("alpha", "beta")],
        "classical_fixtures": {"alpha": alpha % p**md, "beta": beta % p**md,
                               "f_alpha": [a % p**md for a in ff["alpha"]],
                               "f_beta": [a % p**md for a in ff["beta"]]}}
    known = [(7, 11), (13, 17), (19, 23)]
    orders = [[[0, 0, 0] for _ in range(bound)] for _ in range(3)]
    for n in range(bound):
        orders[2][n] = [(a*ff["alpha"][n]+b*ff["beta"][n]) % p**td for a, b in known]
    trace = {"schema": "E389-Kminus71-cubic-averaged-trace-v1",
             "coefficient_ring": {"digits": td}, "q_precision": {"largest_coefficient": bound-1},
             "averaged_trace_orders_0_1_2": orders}
    inp = prepare_inputs(capsule, trace, 0)
    fit = solve_integral(inp["fit_matrix"], inp["rhs"], p, md)
    duals = {name: dual_kernel(inp["operator"], inp["roots"][name], p, m)
             for name in ("alpha", "beta")}
    cert = {"fit": fit, "effective_matrix_digits": m, "dual_functionals": duals,
            "projection": projections(inp, fit, duals)}
    verify_certificate(inp, cert)
    for i, (aa, bb) in enumerate(known):
        assert ball_contains_integer(cert["projection"]["stabilization_coefficients"]["alpha"][f"W2_xi{i}"], aa)
        assert ball_contains_integer(cert["projection"]["stabilization_coefficients"]["beta"][f"W2_xi{i}"], bb)
    assert all(all(row) for row in cert["projection"]["predicted_lower_zero_diagnostics"].values())
    # Exercise the separate undepleted-product interface. The same constructed
    # input is now explicitly regarded as Qplus, so its H output must change
    # by the nontrivial cubic Euler multiplier; raw inputs are not identified.
    product_trace = copy.deepcopy(trace)
    product_trace["schema"] = "E389-Kminus71-undepleted-cubic-trace-v1"
    product_inputs = prepare_inputs(capsule, product_trace, 0, "undepleted-product")
    product_projection = projections(product_inputs, fit, duals)
    five_r, transfer_digits = transfer_eigenvalues(product_inputs)
    transfer_counts = 0
    transfer_precisions = {}
    for idx, name in enumerate(("alpha", "beta")):
        expected_numerators = cubic_mul(five_r[name], [known[j][idx] for j in range(3)], p**transfer_digits)
        transfer_precisions[name] = []
        for j, numerator in enumerate(expected_numerators):
            ball = product_projection["target_depleted_stabilization_coefficients"][name][f"W2_xi{j}"]
            d, prec = ball["denominator_exponent"], ball["absolute_digits"]
            assert d >= 1
            assert (ball["residue"]-numerator*p**(d-1)) % p**(prec+d) == 0
            transfer_precisions[name].append(prec)
            transfer_counts += 1
    assert all(all(row) for row in product_projection["predicted_lower_zero_diagnostics"].values())
    return {"actual_curve_q_bound": bound-1, "basis_dimension": 2,
            "known_second_coefficient_pairs": [list(pair) for pair in known],
            "fitted_columns": len(inp["labels"]), "fit_guard": fit["inverse_minor"]["guard"],
            "classical_fixture_checks": cert["projection"]["classical_fixture_checks"],
            "separate_undepleted_transfer_coefficients_checked": transfer_counts,
            "undepleted_target_absolute_digits": transfer_precisions,
            "scope": "End-to-end adapter regression on actual elliptic q-series in a restricted two-dimensional model; not the full Katz capsule or actual CM trace"}


def compute():
    p, digits = 5, 8
    modulus = p**digits
    # Actual pilot operator and the independently saved crystalline calibration.
    path = ROOT.parent/"de_rham_strategy/result.json"
    saved = json.loads(path.read_text())
    m = saved["calibration_digits"]
    q = p**m
    a = np.asarray(saved["U_matrix"], dtype=np.int64).T
    c = np.asarray(saved["stabilizations_to_omega_eta_columns"], dtype=np.int64)
    roots = {name: saved[name] for name in ("alpha", "beta")}
    duals = {name: dual_kernel(a, roots[name], p, m) for name in roots}
    fixtures = {name: c[:, i]*roots[name] % q for i, name in enumerate(roots)}
    h = (7*c[:, 0]+11*c[:, 1]) % q
    uh = matmul_mod(h[None, :], a, q)[0]
    projection = {name: normalize_projection(uh, fixtures[name], duals[name], m, m, p)
                  for name in roots}
    assert ball_contains_integer(projection["alpha"], 7)
    assert ball_contains_integer(projection["beta"], 11)
    converted = [combine_balls(list(projection.values()), row, m, p) for row in c]
    assert all(ball_contains_integer(b, int(h[i])) for i, b in enumerate(converted))

    # A coupled congruent eigenpacket. The kernel has guard zero, but the
    # primitive left and right eigenvectors pair to -25, costing two digits.
    # The denominator's uncertainty causes a second two-digit loss when
    # the target numerator is a unit.
    lam = 3
    aa = [[lam, 1], [0, lam+25]]
    dd = dual_kernel(aa, lam, p, digits)
    rr = [-25, 1]
    hh = [1, 0]
    answer = normalize_projection(hh, rr, dd, digits, digits, p)
    assert dd["inverse_minor"]["guard"] == 0
    assert answer["absolute_digits"] == digits-4
    assert answer["denominator_exponent"] == 2
    epsilon = p**digits
    perturbed_b = [[-epsilon, 1], [-25*epsilon, 25]]
    perturbed_w = [1, epsilon]
    assert all(sum(perturbed_b[i][j]*perturbed_w[j] for j in range(2)) == 0 for i in range(2))
    assert all(sum(rr[i]*perturbed_b[i][j] for i in range(2)) == 0 for j in range(2))
    exact0, exact1 = Fraction(-1, 25), Fraction(1, -25+epsilon)
    actual_difference = fraction_valuation(exact1-exact0, p)
    assert actual_difference == digits-4
    # Same matrices modulo 5^digits, same exact left normalization row,
    # but normalized outputs differ before the naive digits-2 precision.
    naive_digits = digits-dd["inverse_minor"]["guard"]-2
    assert actual_difference < naive_digits

    # The M-c direction bound is itself sharp for a congruence of depth two.
    congruent = dual_kernel([[lam, 0], [0, lam+25]], lam, p, digits)
    assert congruent["direction_digits"] == digits-2
    assert congruent["inverse_minor"]["guard"] == 2
    perturbation_kernel = [1, -p**(digits-2)]
    assert p**digits*perturbation_kernel[0]+25*perturbation_kernel[1] == 0

    # The coordinate-fit certificate covers all equations, including extra rows.
    fit_a = [[1, 0], [0, 25], [1, 25]]
    fit_x = [[3, 17], [7, 31]]
    fit_rhs = matmul_mod(fit_a, fit_x, modulus)
    fit = solve_integral(fit_a, fit_rhs, p, digits)
    assert fit["coordinate_digits"] == 6
    assert np.all((array(fit["coordinates"], modulus)-array(fit_x, modulus)) % p**6 == 0)

    # Randomized but deterministic unimodular scrambling exercises pivot
    # permutations, nonunit pivots, and rectangular coordinate fits.
    scrambled = []
    for n in (2, 3, 5, 8):
        rng = np.random.default_rng(38971+n)
        left = np.eye(n, dtype=np.int64)
        right = left.copy()
        for _ in range(24):
            i, j = map(int, rng.choice(n, 2, replace=False))
            left[i] = (left[i]+int(rng.integers(-11, 12))*left[j]) % modulus
            i, j = map(int, rng.choice(n, 2, replace=False))
            right[:, i] = (right[:, i]+int(rng.integers(-11, 12))*right[:, j]) % modulus
        exponents = [i % 3 for i in range(n-1)]
        diagonal = np.diag([p**d for d in exponents]+[0])
        matrix = matmul_mod(matmul_mod(left, diagonal, modulus), right, modulus)
        dual = dual_kernel(matrix, 0, p, digits)
        assert dual["inverse_minor"]["guard"] == max(exponents)
        diagonal[-1, -1] = p**3
        matrix = matmul_mod(matmul_mod(left, diagonal, modulus), right, modulus)
        x = rng.integers(0, modulus, size=(n, 4), dtype=np.int64)
        rhs = matmul_mod(matrix, x, modulus)
        fit_random = solve_integral(matrix, rhs, p, digits)
        assert fit_random["inverse_minor"]["guard"] == 3
        assert np.all((array(fit_random["coordinates"], modulus)-x) % p**5 == 0)
        scrambled.append({"dimension": n, "dual_guard": max(exponents), "fit_guard": 3})

    bad_inverse = copy.deepcopy(dd)
    bad_inverse["inverse_minor"]["scaled_inverse"][0][0] += 1
    bad_kernel = copy.deepcopy(dd)
    bad_kernel["primitive_vector"][1] += 1
    bad_fit = copy.deepcopy(fit)
    bad_fit["coordinates"][0][0] += 1
    bad_rhs = fit_rhs.copy(); bad_rhs[-1, 0] += 1
    negative = {
        "corrupted_inverse": rejected(lambda: verify_dual_kernel(aa, bad_inverse, p)),
        "corrupted_kernel": rejected(lambda: verify_dual_kernel(aa, bad_kernel, p)),
        "corrupted_coordinate": rejected(lambda: verify_integral_solution(fit_a, fit_rhs, bad_fit, p)),
        "inconsistent_extra_equation": rejected(lambda: solve_integral(fit_a, bad_rhs, p, digits)),
        "repeated_target_eigenvalue": rejected(lambda: dual_kernel([[3, 0], [0, 3]], 3, p, digits)),
        "unresolved_congruence_at_available_precision": rejected(lambda: dual_kernel([[3, 0], [0, 3+p**digits]], 3, p, digits)),
        "unresolved_zero_normalization": rejected(lambda: quotient_ball(1, 0, digits, digits, p)),
        "integer_overflow_contract": rejected(lambda: array([[1]], 5**16)),
    }
    assert all(negative.values())
    return {
        "status": "PASS", "actual_crystalline_two_slope_regression": {
            "source_sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
            "operator_basis": "row coordinates in omega,eta; transpose of saved column operator",
            "known_stabilization_coefficients": [7, 11],
            "recovered_balls": projection, "converted_omega_eta": converted,
            "scope": "Actual pilot crystalline operator; input is a known elliptic linear combination, not the CM jet"},
        "sharp_normalization_counterexample": {
            "matrix_digits": digits, "primitive_kernel_guard": 0,
            "normalization_valuation": 2, "numerator_valuation": 0,
            "naive_absolute_digits": naive_digits,
            "certified_absolute_digits": answer["absolute_digits"],
            "actual_compatible_perturbation_difference_valuation": actual_difference,
            "same_exact_normalization_row": rr,
            "scope": "Exact rank-one linear-algebra counterexample, not an arithmetic counterexample"},
        "sharp_kernel_direction_guard": congruent["inverse_minor"]["guard"],
        "elliptic_subspace_adapter_regression": elliptic_subspace_adapter_regression(),
        "rectangular_fit_guard": fit["inverse_minor"]["guard"],
        "scrambled_local_elimination_checks": scrambled,
        "corrupted_and_unsupported_input_rejections": negative,
        "scope": "Finite kernel/fit/normalization certificates and genuine crystalline calibration. No Katz capsule, CM de Rham projection, input-tail bound, or nonzero localization is supplied by this test."}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args()
    result = compute()
    if args.check:
        assert result == json.loads((ROOT/"result.json").read_text())
    if args.write:
        (ROOT/"result.json").write_text(json.dumps(result, indent=2, sort_keys=True)+"\n")
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
