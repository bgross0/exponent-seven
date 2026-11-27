#!/usr/bin/env python3
"""Exact cubic ratio and precision from the actual finite projection balls."""
from __future__ import annotations

import argparse
import hashlib
import itertools
import json
from pathlib import Path


HERE = Path(__file__).resolve().parent


def multiply(a, b, modulus):
    # Independent polynomial reduction: xi^3 = 1+2xi-xi^2.
    out = [0]*5
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i+j] += x*y
    for degree in (4, 3):
        coefficient = out[degree]
        out[degree] = 0
        out[degree-3] += coefficient
        out[degree-2] += 2*coefficient
        out[degree-1] -= coefficient
    return [x % modulus for x in out[:3]]


def inverse(a, modulus):
    answer = next(list(v) for v in itertools.product(range(5), repeat=3)
                  if multiply(a, v, 5) == [1, 0, 0])
    precision = 5
    while precision < modulus:
        precision = min(precision*precision, modulus)
        product = multiply(a, answer, precision)
        answer = multiply(answer, [2-product[0], -product[1], -product[2]], precision)
    assert multiply(a, answer, modulus) == [1, 0, 0]
    return answer


def valuation(n, cap=100):
    if n == 0:
        return cap
    result = 0
    while n % 5 == 0:
        result += 1
        n //= 5
    return result


def cubic_ball(balls):
    assert len(balls) == 3 and all(b["p"] == 5 for b in balls)
    absolute = min(b["absolute_digits"] for b in balls)
    denominator = max(b["denominator_exponent"] for b in balls)
    modulus = 5**(absolute+denominator)
    numerator = [b["residue"]*5**(denominator-b["denominator_exponent"]) % modulus
                 for b in balls]
    common = min(valuation(x, absolute+denominator) for x in numerator)
    assert common < absolute+denominator, "The cubic element is not certified nonzero"
    numerator = [x//5**common for x in numerator]
    denominator -= common
    assert any(x % 5 for x in numerator)
    return {"numerator": numerator, "denominator_exponent": denominator,
            "absolute_digits": absolute, "valuation": -denominator}


def compute():
    projection_path = HERE/"actual-cm-finite-projection.json"
    projection = json.loads(projection_path.read_text())
    target = projection["projection"]["target_depleted_stabilization_coefficients"]
    alpha = cubic_ball([target["alpha"][f"W2_xi{i}"] for i in range(3)])
    beta = cubic_ball([target["beta"][f"W2_xi{i}"] for i in range(3)])
    assert alpha == {"numerator": [418, 150, 83], "denominator_exponent": 1,
                     "absolute_digits": 3, "valuation": -1}
    assert beta == {"numerator": [14, 27, 124], "denominator_exponent": 2,
                    "absolute_digits": 1, "valuation": -2}
    # A monic cubic without a root modulo5 is irreducible. Its discriminant49
    # is a unit, so this coefficient basis is integral in the unramified field.
    assert all((x**3+x*x-2*x-1) % 5 for x in range(5))
    discriminant = 1**2*(-2)**2-4*(-2)**3-4*1**3*(-1)-27*(-1)**2+18*1*(-2)*(-1)
    assert discriminant == 49
    a, b = alpha["numerator"], beta["numerator"]
    a_digits = alpha["absolute_digits"]+alpha["denominator_exponent"]
    b_digits = beta["absolute_digits"]+beta["denominator_exponent"]
    assert 1+alpha["denominator_exponent"]-beta["denominator_exponent"] == 0
    ratio_digits = min(a_digits, b_digits)
    modulus = 5**ratio_digits
    inverse_a = inverse(a, modulus)
    ratio = multiply(b, inverse_a, modulus)
    assert ratio == [109, 75, 106]
    assert multiply(a, ratio, modulus) == [x % modulus for x in b]
    # Sharpness: b2 -> b2+5 stays in the original beta ball, but shifts
    # 5*b2/a2 at valuation3. Thus these balls alone do not determine a fourth digit.
    larger_modulus = modulus*5
    lifted0 = multiply(b, inverse(a, larger_modulus), larger_modulus)
    altered_b = [b[0]+5**b_digits, b[1], b[2]]
    lifted1 = multiply(altered_b, inverse(a, larger_modulus), larger_modulus)
    difference = [(x-y) % larger_modulus for x, y in zip(lifted1, lifted0)]
    assert min(valuation(x, ratio_digits+1) for x in difference) == ratio_digits

    # A separately supplied provisional local line. This is a normalization
    # diagnostic only; no arithmetic bad-line identification is assumed here.
    calibration_path = HERE.parent/"de_rham_strategy/result.json"
    calibration = json.loads(calibration_path.read_text())
    inverse_conversion = calibration["inverse_conversion"]
    supplied_omega_eta = [[14297, 10250, 10250], [2899, 48585, 48585]]
    candidate = [[sum(inverse_conversion[i][j]*supplied_omega_eta[j][k] for j in range(2)) % 5**7
                  for k in range(3)] for i in range(2)]
    assert candidate == [[1780, 31595, 31595], [67664, 66785, 66785]]
    assert min(map(valuation, candidate[0])) == 1
    candidate_denominator = [x//5 for x in candidate[0]]
    candidate_ratio = multiply(candidate[1], inverse(candidate_denominator, 5**6), 5**6)
    assert candidate_ratio == [10869, 6950, 11446]
    candidate_difference = [(x-y) % modulus for x, y in zip(ratio, candidate_ratio)]
    assert candidate_difference == [115, 0, 35]
    difference_valuation = min(valuation(x, ratio_digits) for x in candidate_difference)
    assert difference_valuation == 1
    return {
        "status": "PASS", "coefficient_polynomial": "xi^3+xi^2-2xi-1",
        "polynomial_discriminant": discriminant, "irreducible_mod5": True,
        "finite_depleted_alpha_W2": alpha, "finite_depleted_beta_W2": beta,
        "five_times_ratio": {"residue": ratio, "modulus": modulus,
                             "absolute_digits": ratio_digits, "valuation": 0,
                             "inverse_denominator_witness": inverse_a},
        "ratio_beta_over_alpha": {"numerator": ratio, "denominator": 5,
                                  "absolute_digits": ratio_digits-1, "valuation": -1},
        "fourth_digit_not_implied": {"admissible_beta_perturbation": "+5",
                                    "scaled_ratio_change_valuation": ratio_digits,
                                    "difference_mod625": difference},
        "provisional_line_diagnostic": {
            "supplied_omega_eta_mod5_7": supplied_omega_eta,
            "converted_stabilization_coordinates_mod5_7": candidate,
            "five_times_candidate_ratio_mod5_6": candidate_ratio,
            "scaled_ratio_difference_mod125": candidate_difference,
            "scaled_ratio_difference_valuation": difference_valuation,
            "unscaled_ratio_difference_valuation": difference_valuation-1,
            "scope": "Exact comparison with supplied provisional K^-1*zeta coordinates only; local reciprocity, common-class, and period premises are not proved here."},
        "source_sha256": {"actual_projection": hashlib.sha256(projection_path.read_bytes()).hexdigest(),
                          "elliptic_calibration": hashlib.sha256(calibration_path.read_bytes()).hexdigest()},
        "scope": "Consequences of the saved finite projection balls. Infinite Katz identification and arithmetic regulator interpretation require their own arguments.",
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true")
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    result = compute()
    destination = HERE/"cubic-ratio-result.json"
    if args.check:
        assert result == json.loads(destination.read_text())
    text = json.dumps(result, indent=2, sort_keys=True)+"\n"
    if args.write:
        destination.write_text(text)
    print(text, end="")


if __name__ == "__main__":
    main()
