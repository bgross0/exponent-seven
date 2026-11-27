#!/usr/bin/env python3
"""Run the same exact Frobenius method against a published 37a1 E2 value."""
import json
from frobenius import compute


def compute_calibration():
    result = compute(digits=6, f_coefficients=(1, -4, 0, 4))
    s = result["unit_root_line"]["vector_in_omega_eta_basis"][0]
    expected_e2 = 2+4*5+2*5**3+5**4+3*5**5
    actual_e2 = -12*s % 5**6
    assert actual_e2 == expected_e2 == 10272
    return {
        "status": "PASS", "curve": "37a1", "prime": 5, "modulus": 5**6,
        "frobenius_matrix": result["frobenius_matrix"],
        "unit_root_line_coefficient": s,
        "computed_E2": actual_e2, "published_E2": expected_e2,
        "source": "Sage official padic_E2 documentation; model y^2=x^3-x+1/4",
        "purpose": "Independent published normalization and precision calibration",
    }


if __name__ == "__main__":
    print(json.dumps(compute_calibration(), indent=2, sort_keys=True))
