#!/usr/bin/env python3
"""Exact 5-adic local logarithms for the 389.a1 rank-two pilot.

All arithmetic uses Python integers and fractions. This is a finite-precision
certificate with a mathematical tail bound, not a new global-class construction
or a Lean proof. See README.md for the formal differential and precision proof.
"""

import argparse
from fractions import Fraction
import importlib.util
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location("bsd_exact_group_law", ROOT / "logic/verify_logic.py")
GROUP = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(GROUP)
P = (Fraction(0), Fraction(0))
Q = (Fraction(1), Fraction(0))
PRIME = 5


def valuation(n, prime=PRIME):
    if n == 0:
        raise ValueError("valuation of zero is not a finite integer")
    n = abs(n)
    answer = 0
    while n % prime == 0:
        answer += 1
        n //= prime
    return answer


def convolution_at(left, right, degree):
    if degree < 0:
        return 0
    return sum(left[i] * right[degree-i] for i in range(degree+1))


def differential_coefficients(length):
    """dx/(2y+1) = sum c[n] t^n dt, t=-x/y; exact recurrence."""
    if length < 1:
        raise ValueError("positive length required")
    v = []
    for n in range(length):
        value = int(n == 0)
        value += v[n-2] if n >= 2 else 0
        value += convolution_at(v, v, n-3)
        value -= 2 * convolution_at(v, v, n-4)
        v.append(value)
    numerator = [(n+2) * v[n] for n in range(length)]
    denominator = [2*v[n] - convolution_at(v, v, n-3) for n in range(length)]
    c = []
    for n in range(length):
        residual = numerator[n] - sum(denominator[i]*c[n-i] for i in range(1, n+1))
        assert residual % 2 == 0
        c.append(residual // 2)
    assert c[:min(5, length)] == [1, 0, 1, 2, -3][:min(5, length)]
    # Verify the polynomial identities defining both the curve parametrization
    # and invariant differential, independently of their recurrence layout.
    for n in range(length):
        rhs = int(n == 0) + (v[n-2] if n >= 2 else 0)
        rhs += convolution_at(v, v, n-3) - 2*convolution_at(v, v, n-4)
        assert v[n] == rhs
        assert convolution_at(denominator, c, n) == numerator[n]
    return c


def formal_log(t, digits):
    """Return log(t) modulo 5^digits, with tail valuation >= digits."""
    if digits < 2:
        raise ValueError("at least two absolute digits required")
    vt = valuation(t.numerator) - valuation(t.denominator)
    assert vt >= 1 and t.denominator % PRIME != 0
    # Terms n >= 2*digits satisfy n-v_5(n) >= digits. Compute earlier terms.
    last = 2*digits-1
    coefficients = differential_coefficients(last)
    extra = max(valuation(n) for n in range(1, last+1))
    working_modulus = PRIME ** (digits+extra)
    modulus = PRIME ** digits
    residue = t.numerator * pow(t.denominator, -1, working_modulus) % working_modulus
    answer = 0
    power = 1
    for n in range(1, last+1):
        power = power*residue % working_modulus
        exponent = valuation(n)
        ppart = PRIME**exponent
        numerator = coefficients[n-1]*power % working_modulus
        assert numerator % ppart == 0
        answer += (numerator // ppart) * pow(n // ppart, -1, modulus)
        answer %= modulus
    return answer


def point_log(point, digits, multiplier=9):
    assert multiplier % PRIME != 0
    multiple = GROUP.multiply(multiplier, point)
    assert multiple is not None
    x, y = multiple
    parameter = -x/y
    result = formal_log(parameter, digits) * pow(multiplier, -1, PRIME**digits) % PRIME**digits
    return result, parameter


def unit_root(digits):
    alpha = 2
    modulus = PRIME
    for _ in range(1, digits):
        next_modulus = modulus * PRIME
        alpha = (alpha - (alpha*alpha + 3*alpha + 5) * pow(2*alpha+3, -1, next_modulus)) % next_modulus
        modulus = next_modulus
    assert (alpha*alpha + 3*alpha + 5) % modulus == 0
    return alpha


def compute(normalized_digits=30):
    if normalized_digits < 2:
        raise ValueError("at least two normalized digits required")
    absolute_digits = normalized_digits+1
    absolute_modulus = PRIME**absolute_digits
    normalized_modulus = PRIME**normalized_digits
    lp, tp = point_log(P, absolute_digits)
    lq, tq = point_log(Q, absolute_digits)
    assert lp % 25 == 5 and lq % 25 == 15
    assert valuation(lp) == valuation(lq) == 1
    up, uq = lp//5, lq//5
    ratio = uq * pow(up, -1, normalized_modulus) % normalized_modulus
    assert (ratio*lp-lq) % absolute_modulus == 0
    # Distinct formal-neighborhood multiples and a genuine additivity check
    # expose differential-sign, division and precision mistakes.
    lp18, _ = point_log(P, absolute_digits, multiplier=18)
    lq18, _ = point_log(Q, absolute_digits, multiplier=18)
    assert lp18 == lp and lq18 == lq
    sum_log, _ = point_log(GROUP.add(P, Q), absolute_digits)
    negative_p = (P[0], -P[1]-1)
    difference_log, _ = point_log(GROUP.add(Q, negative_p), absolute_digits)
    assert sum_log == (lp+lq) % absolute_modulus
    assert difference_log == (lq-lp) % absolute_modulus
    # A shorter independent truncation also agrees after reducing precision.
    assert point_log(P, 6)[0] == lp % 5**6
    assert point_log(Q, 6)[0] == lq % 5**6
    rows = []
    for d in sorted(set([1, 2, 5, 10, 20, normalized_digits])):
        if d > normalized_digits:
            continue
        modulus = PRIME**d
        rows.append({"normalized_digits": d, "modulus": modulus,
                     "log_P_div_5": up % modulus, "log_Q_div_5": uq % modulus,
                     "ratio_log_Q_over_log_P": ratio % modulus})
    alpha = unit_root(absolute_digits)
    # The p-cleared height factor (p-alpha)*alpha/(alpha-1) is a unit.
    height_factor = (5-alpha)*alpha*pow(alpha-1, -1, absolute_modulus) % absolute_modulus
    assert alpha % 25 == 7 and height_factor % 5 == 1
    return {
        "status": "PASS",
        "scope": "Exact finite-precision local arithmetic; tail and interpretation proved in README; no global derived class computed",
        "curve_ainvariants": [0, 1, 1, -2, 0],
        "differential": "dx/(2y+1)", "prime": PRIME,
        "points": {"P": [0, 0], "Q": [1, 0]},
        "formal_parameter": "t=-x/y",
        "differential_coefficients_first_12": differential_coefficients(12),
        "absolute_digits": absolute_digits,
        "normalized_digits": normalized_digits,
        "log_P_mod_5_to_absolute_digits": lp,
        "log_Q_mod_5_to_absolute_digits": lq,
        "normalized_log_P": up, "normalized_log_Q": uq,
        "strict_line": {"basis": ["P", "Q"], "normalized_vector": [ratio, -1],
                        "modulus": normalized_modulus,
                        "exact_definition": "(log(Q)/log(P))*P-Q in E(Q) tensor Q_5"},
        "precision_table": rows,
        "formal_parameters_9_times_points": {
            "P": {"numerator": str(tp.numerator), "denominator": str(tp.denominator)},
            "Q": {"numerator": str(tq.numerator), "denominator": str(tq.denominator)}},
        "unit_root_alpha": alpha,
        "p_cleared_height_factor": height_factor,
        "validation": {"multipliers_9_and_18_agree": True, "P_plus_Q_additivity": True,
                       "Q_minus_P_additivity": True, "independent_lower_precision_agrees": True,
                       "quadratic_log_remainders_zero_mod_25": True},
        "tail_bound": {"first_omitted_log_degree": 2*absolute_digits,
                       "lower_bound_on_omitted_valuation": absolute_digits,
                       "reason": "v_5(t)>=1 and integral differential coefficients; n-v_5(n)>=n/2"}
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--normalized-digits", type=int, default=30)
    parser.add_argument("--check", type=Path)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = compute(args.normalized_digits)
    if args.check:
        assert json.loads(args.check.read_text()) == result, "Saved local certificate differs"
    encoded = json.dumps(result, indent=2, sort_keys=True)+"\n"
    if args.output:
        args.output.write_text(encoded)
    print(encoded, end="")


if __name__ == "__main__":
    main()
