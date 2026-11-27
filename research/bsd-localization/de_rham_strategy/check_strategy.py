#!/usr/bin/env python3
"""Exact, standard-library checks for the de Rham strategy.

This checks the *existing* elliptic Frobenius calibration, pole-model
dimensions, and the cup/trace constants. It does not project a CM input.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent


def mm(a, b, mod):
    return [[sum(a[i][k] * b[k][j] for k in range(2)) % mod
             for j in range(2)] for i in range(2)]


def det(a, mod):
    return (a[0][0] * a[1][1] - a[0][1] * a[1][0]) % mod


def inv(a, mod):
    d = pow(det(a, mod), -1, mod)
    return [[d * a[1][1] % mod, -d * a[0][1] % mod],
            [-d * a[1][0] % mod, d * a[0][0] % mod]]


def dimension(k):
    """M_k(Gamma_0(389)), even k >= 2: g=32,c=2,e2=2,e3=0."""
    assert k >= 2 and k % 2 == 0
    return 31 * (k - 1) + k + 2 * (k // 4)


def run():
    src = HERE.parent / "local_crystalline" / "result.json"
    raw = src.read_bytes()
    fdata = json.loads(raw)
    p = fdata["prime"]
    assert p == 5 and fdata["absolute_digits"] == 8
    source_mod = fdata["modulus"]
    mod = source_mod // 5
    f = [[int(x) % mod for x in row] for row in fdata["frobenius_matrix"]]
    assert all(row[0] % 5 == 0 for row in fdata["frobenius_matrix"])
    fomega_over5 = [row[0] // 5 % mod for row in fdata["frobenius_matrix"]]
    alpha = fdata["ordinary_unit_root"] % mod
    beta = (-3 - alpha) % mod
    assert (alpha * beta - 5) % mod == 0
    assert alpha % 5 != 0 and beta % 5 == 0
    # Columns are [f_alpha], [f_beta], with f_alpha=f-beta*V_5 f.
    c = [[(1 - beta * fomega_over5[0]) % mod,
          (1 - alpha * fomega_over5[0]) % mod],
         [(-beta * fomega_over5[1]) % mod,
          (-alpha * fomega_over5[1]) % mod]]
    assert det(c, mod) % 5 != 0
    ci = inv(c, mod)
    ident = [[1, 0], [0, 1]]
    assert mm(c, ci, mod) == ident
    assert mm(ci, c, mod) == ident
    # U=5 F^-1=-F-3. Its slopes have the opposite labels to F.
    u = [[(-f[i][j] - (3 if i == j else 0)) % mod
          for j in range(2)] for i in range(2)]
    assert mm(f, u, mod) == [[5, 0], [0, 5]]
    assert mm(u, c, mod) == mm(c, [[alpha, 0], [0, beta]], mod)
    assert mm(f, c, mod) == mm(c, [[beta, 0], [0, alpha]], mod)
    assert det(c, mod) == ((beta - alpha) * fomega_over5[1]) % mod

    dims = {str(k): dimension(k) for k in [2, 4, 6, 10, 14, 42, 78]}
    assert dims["4"] == 99 and dims["10"] == 293
    assert dims["10"] - (dims["4"] - 1) == 195
    for n in range(2, 21):
        assert dimension(4*n+2) - dimension(4*n-4) + 1 == 195
    # Local primitive, ramification 3 at j=0, and Delta/E6^2=-1/1728.
    cup_trace_constant = Fraction(-9, 1) * Fraction(1, 3) * Fraction(-1, 1728)
    assert cup_trace_constant == Fraction(1, 576)
    jobs = []
    for m in [2, 3, 6, 12]:
        n = (6 * (m + 1)) // 4
        kmax = 2 + 4*n
        sturm = (390 * kmax) // 12
        jobs.append({"matrix_digits": m, "katz_n": n,
                     "top_classical_weight": kmax,
                     "matrix_dimension": dimension(kmax),
                     "sturm_bound": sturm,
                     "basis_working_digits": m + (n + 5)//6,
                     "q_precision_exclusive": 5 * sturm,
                     "safe_trace_largest_coefficient": 5 * sturm})
    return {
        "status": "passed_exact_algebra_checks",
        "scope": "Calibration and finite model only; no projected CM jet computed.",
        "frobenius_source_sha256": hashlib.sha256(raw).hexdigest(),
        "source_digits": 8, "calibration_digits": 7, "modulus": mod,
        "basis": ["omega=dx/(2y+1)", "eta=x*omega"],
        "normalization": "Identify the elliptic modular differential [f] with omega.",
        "alpha": alpha, "beta": beta,
        "Fomega_over5": fomega_over5,
        "stabilizations_to_omega_eta_columns": c,
        "inverse_conversion": ci,
        "conversion_determinant": det(c, mod),
        "conversion_additional_digits_lost": 0,
        "U_matrix": u,
        "checks": {"inverse_both_orders": True, "U_equals_5F_inverse": True,
                   "U_eigenbasis": True, "F_eigenbasis_labels_swapped": True,
                   "conversion_determinant_unit": True,
                   "pole_core_dimension_195": True,
                   "cup_trace_factor_1_over_576": True},
        "classical_dimensions": dims,
        "katz_job_parameters": jobs,
        "backend_executed_here": False,
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--write", action="store_true")
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    result = run()
    dst = HERE / "result.json"
    if args.check:
        assert json.loads(dst.read_text()) == result
    if args.write:
        dst.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps(result, indent=2, sort_keys=True))
