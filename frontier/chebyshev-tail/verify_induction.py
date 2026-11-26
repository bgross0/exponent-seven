"""Exact integer/rational certificate for the dyadic induction in DERIVATION.md.

No floating-point arithmetic or third-party package is used. This verifies
the finite algebraic inequalities conditional on the displayed analytic
Chebyshev/Abel bounds; it does not certify those analytic bounds in Lean.
"""

from fractions import Fraction as F
import json


def encode(x):
    x = F(x)
    return {"numerator": str(x.numerator), "denominator": str(x.denominator)}


def verify():
    n0 = 19
    c_lo, c_hi = F(2, 3), F(7, 10)
    growth = F(7, 5)

    # These comparisons imply the corresponding positive real-root bounds.
    root_facts = {
        "sqrt_2_greater_than_7_over_5": growth**2 < 2,
        "fourth_root_2_less_than_6_over_5": F(6, 5)**4 > 2,
        "sixth_root_2_less_than_6_over_5": F(6, 5)**6 > 2,
        "2_to_19_over_4_less_than_27": 2**19 < 27**4,
        "2_to_19_over_6_less_than_9": 2**19 < 9**6,
        "2_to_19_over_4_greater_than_16": 2**19 > 16**4,
    }
    assert all(root_facts.values())

    # Optional elementary series certificate for the log(2) constants.
    # Identity to justify analytically: log2=2*sum_{k>=0}3^(-2k-1)/(2k+1).
    # k>=2 tail is <=(2/5)*3^-5/(1-1/9).
    log2_lower = F(2, 3)
    log2_upper = F(2, 3) + F(2, 81) + F(1, 540)
    assert c_lo <= log2_lower < log2_upper < c_hi

    main_lower = 8 * 512 * growth
    errors = {
        "E1": (3 * c_hi * n0 + 8) * 27,
        "E2": F(48 * 9),
        "E3": F(11, 54) * c_hi**2 * n0**3,
        "E4": (F(55, 6) + c_hi) * c_hi * n0**2,
        "E5": (11 * c_hi + 8) * n0,
        "E6": F(n0) * (2 * c_hi * n0 + 8) / 16,
        "E7": 14 / (3 * c_lo),
    }
    error_sum = sum(errors.values(), F(0))
    slack = main_lower - error_sum
    assert slack == F(5235581, 10800)
    assert slack > 0

    # Optional integration profile: J<=4 from the existing Jplus theorem.
    # Replace E5 by (11c+12)n and remove E7.
    coarse_errors = dict(errors)
    coarse_errors["E5"] = (11 * c_hi + 12) * n0
    del coarse_errors["E7"]
    coarse_slack = main_lower - sum(coarse_errors.values(), F(0))
    assert coarse_slack == F(4490381, 10800)
    assert coarse_slack > 0

    ratio = F(n0 + 1, n0)
    growth_bounds = {
        "E1": ratio * F(6, 5),
        "E2": F(6, 5),
        "E3": ratio**3,
        "E4": ratio**2,
        "E5": ratio,
        "E6": ratio**2,
        "E7": F(1),
    }
    assert all(0 <= x < growth for x in growth_bounds.values())

    q_uniform = 2**135
    q_bridge_min = 10**32
    x_bridge = 30000
    norm_gate = 4 * x_bridge**7
    assert norm_gate < q_bridge_min < q_uniform
    return {
        "arithmetic": "stdlib fractions.Fraction and Python integers only",
        "base_n": n0,
        "log2_lower": encode(c_lo),
        "log2_upper": encode(c_hi),
        "log2_series_upper": encode(log2_upper),
        "log2_series_identity": "analytic obligation; alternatively use Mathlib log_two bounds",
        "root_facts": root_facts,
        "main_lower": encode(main_lower),
        "error_upper_bounds": {k: encode(v) for k, v in errors.items()},
        "error_sum_upper": encode(error_sum),
        "base_slack_lower": encode(slack),
        "coarse_J4_profile": {
            "error_upper_bounds": {k: encode(v) for k, v in coarse_errors.items()},
            "base_slack_lower": encode(coarse_slack),
            "status": "same induction, E5 enlarged by 4n and E7 omitted",
        },
        "main_growth_lower": encode(growth),
        "error_growth_upper_bounds": {k: encode(v) for k, v in growth_bounds.items()},
        "uniform_q_cutoff": str(q_uniform),
        "finite_bridge": {
            "X": x_bridge,
            "Qmin": str(q_bridge_min),
            "Qmax": str(q_uniform),
            "four_times_X_to_seven": str(norm_gate),
            "gate_passes": True,
        },
        "status": "all exact arithmetic checks passed; analytic derivation and Lean integration remain",
    }


if __name__ == "__main__":
    print(json.dumps(verify(), indent=2))
