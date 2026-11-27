#!/usr/bin/env python3
"""Replay the actual level389 matrix fit and short low-weight checkpoints.

This uses ordinary Python/NumPy and checks saved witnesses, not Sage's
elimination routines. It does not infer a CM projection or analytic tail.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import sys

import numpy as np

from finite_projection import array, require
from katz_matrix_fit import read_json, verify_katz_matrix
from replay_pole_core import replay_basis, independent_pilot_eigenform


def compute(root):
    used, bases, reports = [], {}, []
    records = {}
    for weight in (2, 4, 6):
        path = root/"short-bases-389"/f"M{weight}-basis.json.gz"
        record = read_json(path); used.append(path)
        require(record["metadata"]["level"] == 389, "Wrong short-basis level")
        require(record["dimension"] == 31*(weight-1)+weight+2*(weight//4),
                "Wrong classical dimension")
        require(record["q_precision_exclusive"] > (390*weight)//12,
                "Short basis does not cover the independently computed Sturm bound")
        basis, report = replay_basis(record, bases)
        bases[weight], records[weight] = basis, record
        reports.append(report)
    independent = independent_pilot_eigenform(bases[2], records[2]["pivot_columns"])
    print("Actual M2/M4/M6 product, Serre and saturation replay passed", file=sys.stderr, flush=True)

    capsule_path = root/"katz"/"katz-capsule.json.gz"
    fit_path = root/"katz"/"katz-matrix-fit.json.gz"
    capsule, fit = read_json(capsule_path), read_json(fit_path)
    used += [capsule_path, fit_path]
    require(capsule["schema"] == "katz-matrix-gate-v1", "Wrong matrix capsule schema")
    parameters = capsule["parameters"]
    require((parameters["prime"], parameters["level"], parameters["weight"],
             parameters["matrix_digits"]) == (5, 389, 2, 6), "Wrong pilot matrix parameters")
    require((capsule["elldash"], capsule["mdash"]) == (1366, 8), "Wrong basis precision")
    require((fit["elldash"], fit["basis_digits"], fit["matrix_digits"]) == (1366, 8, 6),
            "Matrix sidecar and capsule precision differ")
    require(len(capsule["Katz_E_mod_5mdash"]) == 1333, "Wrong basis dimension")
    require(all(len(row) == 6830 for row in capsule["Katz_E_mod_5mdash"]), "Wrong basis q-depth")
    matrix_report = verify_katz_matrix(capsule["Katz_E_mod_5mdash"], fit)
    require(np.array_equal(array(capsule["row_operator_A_mod_5m"], 5**6),
                           array(fit["row_operator_A_mod_5m"], 5**6)),
            "The gated capsule has a different operator from the verified sidecar")
    require(matrix_report["inverse_minor_guard"] == 1 and
            matrix_report["coordinate_digits"] == 7, "Unexpected certified matrix precision")

    fixtures = capsule["classical_fixtures"]
    alpha, beta = fixtures["alpha"], fixtures["beta"]
    require(alpha % 5 == 2 and beta % 5 == 0 and beta % 25 != 0, "Wrong slope labels")
    require((alpha+beta+3) % 5**8 == 0 and (alpha*beta-5) % 5**8 == 0,
            "Classical roots fail the elliptic polynomial")
    for name, eigenvalue in (("alpha", alpha), ("beta", beta)):
        series = fixtures["f_"+name]
        require(len(series) == 6830 and series[0] == 0 and series[1] == 1,
                "Wrong classical fixture normalization")
        require(all((series[5*j]-eigenvalue*series[j]) % 5**8 == 0 for j in range(1366)),
                "Classical fixture U5 identity failed")
    print("Actual1333-dimensional matrix sidecar and capsule replay passed", file=sys.stderr, flush=True)
    return {
        "status": "PASS", "artifact": "katz-success-8726d59",
        "short_basis_q_precision_exclusive": 390,
        "short_classical_basis_replays": reports,
        "independent_pilot_eigenform": independent,
        "matrix_certificate_replay": matrix_report,
        "gated_capsule_operator_equals_verified_sidecar": True,
        "basis_q_precision_exclusive": 6830,
        "classical_fixture_U5_identities_checked": 2732,
        "classical_fixture_q1_normalizations_verified": True,
        "classical_fixture_root_polynomial": "X^2+3X+5",
        "source_sha256": {str(path.relative_to(root)): hashlib.sha256(path.read_bytes()).hexdigest()
                          for path in used},
        "scope": "Independent finite witness replay of the actual level389 Katz matrix and short product/Serre/saturation construction. M2 coefficients inherit their modular-space provenance from Sage; the elliptic row is independently matched by point counts. No CM input fit, geometric infinite-operator comparison, analytic tail, nonzero localization, or global BSD conclusion is inferred.",
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--artifact-root", type=Path, required=True)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--check", type=Path)
    args = parser.parse_args()
    result = compute(args.artifact_root)
    if args.check:
        assert result == json.loads(args.check.read_text())
    payload = json.dumps(result, indent=2, sort_keys=True)+"\n"
    if args.output:
        args.output.write_text(payload)
    print(payload, end="")


if __name__ == "__main__":
    main()
