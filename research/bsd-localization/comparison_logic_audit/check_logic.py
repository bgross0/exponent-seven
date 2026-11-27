#!/usr/bin/env python3
"""Exact comparison algebra, sharp countermodels, and corrected pilot ratio."""
from __future__ import annotations

import argparse
from fractions import Fraction as Q
import hashlib
import json
from pathlib import Path


HERE = Path(__file__).resolve().parent
ROOT = HERE.parent


def quadratic_product(x, y):
    # F^2 = -3F-5 in Q[F].
    a, b = map(Q, x)
    c, d = map(Q, y)
    return [a*c-5*b*d, a*d+b*c-3*b*d]


def quadratic_determinant(x):
    a, b = map(Q, x)
    return a*a-3*a*b+5*b*b


def quadratic_adjoint(x):
    # F^dagger=5F^-1=-3-F.
    a, b = map(Q, x)
    return [a-3*b, -b]


def cubic_product(x, y, modulus):
    # Reduce each monomial separately with xi^3=1+2xi-xi^2.
    powers = [[1, 0, 0], [0, 1, 0], [0, 0, 1]]
    for _ in range(2):
        a, b, c = powers[-1]
        powers.append([c, a+2*c, b-c])
    return [sum(x[i]*y[j]*powers[i+j][k]
                for i in range(3) for j in range(3)) % modulus
            for k in range(3)]


def valuation5(x, cap=20):
    if not x:
        return cap
    result = 0
    while x % 5 == 0:
        x //= 5
        result += 1
    return result


def coefficients_for_model(a, m):
    # P_m=diag(t^m,1), y=(a*t,t^2), retained through degree4.
    output = [[0, 0] for _ in range(5)]
    output[m+1][0] = a
    output[2][1] = 1
    return output


def compute():
    A = [Q(59, 45), Q(13, 45)]
    A_inverse = [Q(20, 45), Q(-13, 45)]
    assert quadratic_product(A, A_inverse) == [1, 0]
    assert quadratic_product(A_inverse, A) == [1, 0]
    assert quadratic_determinant(A) == 1
    assert quadratic_adjoint(A) == A_inverse

    # A successful complementary coefficient detects the finite class.
    simple = coefficients_for_model(3, 1)
    assert simple[2] == [3, 1]
    # Removing simple determinant only destroys the converse.
    double = coefficients_for_model(1, 2)
    assert double[2] == [0, 1] and double[3] == [1, 0]
    zero = coefficients_for_model(0, 1)
    assert zero[2][0] == 0

    # Unit change on a three-dimensional abstract global module, with
    # c=diag(1,1,-1) and t->-t. The first plus coordinate is locally strict.
    kappa0 = [1, 0, 0]
    kappa1 = [2, 3, 4]
    x0 = [2*kappa1[0], 2*kappa1[1], 0]
    u0, u1 = 3, 5
    kappa1_new = [u0*x+u1*y for x, y in zip(kappa1, kappa0)]
    x0_new = [2*kappa1_new[0], 2*kappa1_new[1], 0]
    assert x0_new == [u0*x+2*u1*y for x, y in zip(x0, kappa0)]
    assert x0_new[1] == u0*x0[1] and x0_new != [u0*x for x in x0]

    # v=(1,u), u^2=2, sigma(u)=-u: det(v,Tr v)=-2u.
    trace_determinant_in_1_u_basis = [0, -2]
    assert trace_determinant_in_1_u_basis != [0, 0]
    # For F=[[0,-5],[1,-3]], det((1,1),(I+F)(1,1))=3.
    frobenius_average = [-4, -1]
    assert frobenius_average[1]-frobenius_average[0] == 3

    ratio_path = ROOT/"projection_backend/cubic-ratio-result.json"
    calibration_path = ROOT/"de_rham_strategy/result.json"
    crystalline_path = ROOT/"local_crystalline/result.json"
    ratio = json.loads(ratio_path.read_text())
    calibration = json.loads(calibration_path.read_text())
    crystalline = json.loads(crystalline_path.read_text())
    modulus = ratio["five_times_ratio"]["modulus"]
    assert modulus == 125
    raw_ratio = ratio["five_times_ratio"]["residue"]
    assert raw_ratio == [109, 75, 106]
    a2_numerator = ratio["finite_depleted_alpha_W2"]["numerator"]
    b2_numerator = ratio["finite_depleted_beta_W2"]["numerator"]
    assert cubic_product(a2_numerator, raw_ratio, modulus) == [n % modulus for n in b2_numerator]

    alpha, beta = calibration["alpha"] % modulus, calibration["beta"] % modulus
    assert [alpha, beta] == [32, 90]
    assert (alpha+beta+3) % modulus == 0 and (alpha*beta-5) % modulus == 0
    # K0(F) is a scalar times (5*tau+11)+2*(tau+1)*F.
    # The F eigenvalue on f_alpha is beta, and on f_beta it is alpha.
    # Thus the correction to b/a is k(alpha)/k(beta).
    tau = [1, -1, -1]
    def k_numerator(root):
        out = [(5+2*root)*t for t in tau]
        out[0] += 11+2*root
        return [n % modulus for n in out]
    numerator, denominator = k_numerator(alpha), k_numerator(beta)
    assert numerator == [19, 56, 56]
    assert denominator == [1, 65, 65]
    denominator_inverse = [101, 110, 10]
    assert cubic_product(denominator, denominator_inverse, modulus) == [1, 0, 0]
    correction = cubic_product(numerator, denominator_inverse, modulus)
    assert correction == [79, 1, 91]
    corrected_ratio = cubic_product(correction, raw_ratio, modulus)
    assert corrected_ratio == [21, 0, 0]

    zeta = crystalline["interpolation_annihilator"]["vector_in_twisted_omega_eta_basis"]
    inverse_C = calibration["inverse_conversion"]
    coordinate_modulus = calibration["modulus"]
    coordinates = [sum(inverse_C[i][j]*zeta[j] for j in range(2)) % coordinate_modulus
                   for i in range(2)]
    assert coordinates == [19330, 67476]
    assert valuation5(coordinates[0]) == 1 and valuation5(coordinates[1]) == 0
    scaled_denominator = coordinates[0]//5
    zeta_scaled_ratio = coordinates[1]*pow(scaled_denominator, -1, modulus) % modulus
    assert zeta_scaled_ratio == 86
    difference = [(corrected_ratio[0]-zeta_scaled_ratio) % modulus, *corrected_ratio[1:]]
    assert difference == [60, 0, 0]
    assert min(valuation5(n, 3) for n in difference) == 1
    # Same diagnostic through the previously supplied conditional preimage line.
    previous_difference = ratio["provisional_line_diagnostic"]["scaled_ratio_difference_mod125"]
    assert cubic_product(correction, previous_difference, modulus) == difference

    return {
        "status": "PASS",
        "pilot_base_operator": {
            "A_phi_coefficients_I_F": list(map(str, A)),
            "inverse_coefficients_I_F": list(map(str, A_inverse)),
            "determinant": "1",
            "adjoint_equals_inverse": True,
        },
        "nonvanishing_models": {
            "simple_zero_quadratic_vector": simple[2],
            "double_zero_quadratic_vector": double[2],
            "double_zero_cubic_vector": double[3],
            "double_zero_finite_logarithm": 1,
            "scope": "A nonzero complementary quadratic coefficient is sufficient without determinant order1; a zero coefficient is inconclusive.",
        },
        "unit_rescaling_model": {
            "u0_u1": [u0, u1], "strict_kappa0": kappa0,
            "x0": x0, "rescaled_x0": x0_new,
            "logarithm_before_after": [x0[1], x0_new[1]],
        },
        "averaging_countermodels": {
            "quadratic_trace_determinant_in_1_u_basis": trace_determinant_in_1_u_basis,
            "I_plus_F_image_of_1_1": frobenius_average,
            "I_plus_F_line_determinant": 3,
        },
        "conditional_corrected_ratio": {
            "modulus": modulus,
            "U_roots_alpha_beta": [alpha, beta],
            "K0_eigenvalue_ratio_numerator": numerator,
            "K0_eigenvalue_ratio_denominator": denominator,
            "denominator_inverse_witness": denominator_inverse,
            "K0_eigenvalue_ratio": correction,
            "original_five_b_over_a": raw_ratio,
            "corrected_five_b_over_a": corrected_ratio,
            "zeta_stabilization_coordinates_mod5_7": coordinates,
            "zeta_five_b_over_a": zeta_scaled_ratio,
            "scaled_ratio_difference": difference,
            "difference_valuation": 1,
            "scope": "Exact conditional K0 normalization diagnostic. Rationality is observed at available precision only. Arithmetic identification and an exact rational-descent theorem are not inferred by this checker.",
        },
        "source_sha256": {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
                          for p in [ratio_path, calibration_path, crystalline_path]},
        "scope": "Exact pilot adjoint algebra, independent cubic cancellation, and abstract logical countermodels. The general determinant-free implication is proved in README.md. No global comparison, full arithmetic local identification, or new Lean proof is certified by this executable.",
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true")
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    result = compute()
    path = HERE/"result.json"
    if args.check:
        assert result == json.loads(path.read_text())
    output = json.dumps(result, indent=2, sort_keys=True)+"\n"
    if args.write:
        path.write_text(output)
    print(output, end="")


if __name__ == "__main__":
    main()
