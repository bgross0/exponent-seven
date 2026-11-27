#!/usr/bin/env python3
"""Exercise the matrix fitter on actual elliptic q-series in a small space.

This is an exact regression for the new interface, not a full Katz matrix.
The contracted basis (5f,25V5f) has a genuine inverse-minor loss of two
digits and a known integral U5 matrix, so the precision guard is exercised.
"""
from __future__ import annotations

import argparse
import copy
import json
from math import isqrt
from pathlib import Path

from finite_projection import CertificateError
from katz_matrix_fit import fit_katz_matrix, verify_katz_matrix, write_json


def coefficients(precision):
    primes = [p for p in range(2, precision)
              if all(p % d for d in range(2, isqrt(p)+1))]
    ap = {p: p-sum((y*y+y-x*x*x-x*x+2*x) % p == 0
                   for x in range(p) for y in range(p)) for p in primes}
    assert ap[5] == -3
    answer = [0, 1]
    for n in range(2, precision):
        value, remainder = 1, n
        for p in primes:
            if remainder % p:
                continue
            exponent = 0
            while remainder % p == 0:
                exponent += 1
                remainder //= p
            a0, a1 = 1, ap[p]
            for _ in range(2, exponent+1):
                a0, a1 = a1, ap[p]*a1-p*a0
            value *= a1
            if remainder == 1:
                break
        assert remainder == 1
        answer.append(value)
    return answer


def rejects(operation):
    try:
        operation()
    except CertificateError:
        return True
    return False


def compute():
    elldash, basis_digits, matrix_digits = 8, 8, 6
    f = coefficients(5*elldash)
    vf = [f[n//5] if n % 5 == 0 else 0 for n in range(5*elldash)]
    e = [[5*x for x in f], [25*x for x in vf]]
    certificate = fit_katz_matrix(e, elldash=elldash, basis_digits=basis_digits,
                                  matrix_digits=matrix_digits)
    report = verify_katz_matrix(e, certificate)
    assert certificate["inverse_minor_guard"] == 2
    assert certificate["certified_coordinate_digits"] == 6
    modulus = 5**matrix_digits
    expected = [[-3 % modulus, -1 % modulus], [5, 0]]
    assert certificate["row_operator_A_mod_5m"] == expected
    bad_operator = copy.deepcopy(certificate)
    bad_operator["row_operator_A_mod_5m"][0][0] += 1
    bad_inverse = copy.deepcopy(certificate)
    bad_inverse["coordinate_fit"]["inverse_minor"]["scaled_inverse"][0][0] += 1
    bad_sample = copy.deepcopy(e)
    bad_sample[0][35] += 1
    negative = {
        "corrupted_operator": rejects(lambda: verify_katz_matrix(e, bad_operator)),
        "corrupted_inverse": rejects(lambda: verify_katz_matrix(e, bad_inverse)),
        "inconsistent_U_sample": rejects(lambda: fit_katz_matrix(
            bad_sample, elldash=elldash, basis_digits=basis_digits, matrix_digits=matrix_digits)),
        "overclaimed_matrix_precision": rejects(lambda: fit_katz_matrix(
            e, elldash=elldash, basis_digits=basis_digits, matrix_digits=matrix_digits+1)),
    }
    assert all(negative.values())
    result = {"status": "PASS", "curve": "y^2+y=x^3+x^2-2x",
              "basis": ["5f", "25V5f"], "known_U_row_matrix": [[-3, -1], [5, 0]],
              "q_precision_exclusive": 40, "basis_digits": basis_digits,
              "matrix_digits": matrix_digits, "inverse_minor_guard": 2,
              "finite_equations_checked": report["finite_equations_checked"],
              "rejection_checks": negative,
              "scope": "Exact actual elliptic q-series regression in a restricted two-dimensional contracted lattice; not the full level389 Katz matrix or a CM projection."}
    return result, e, certificate


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--check", type=Path)
    parser.add_argument("--fixture-dir", type=Path)
    args = parser.parse_args()
    result, e, certificate = compute()
    if args.check:
        assert result == json.loads(args.check.read_text())
    if args.output:
        args.output.write_text(json.dumps(result, indent=2, sort_keys=True)+"\n")
    if args.fixture_dir:
        write_json(args.fixture_dir/"elliptic-restricted-basis.json.gz",
                   {"schema": "restricted-elliptic-regression-v1",
                    "parameters": {"matrix_digits": 6}, "elldash": 8, "mdash": 8,
                    "Katz_E_mod_5mdash": e, "scope": result["scope"]})
        write_json(args.fixture_dir/"elliptic-restricted-fit.json.gz", certificate)
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
