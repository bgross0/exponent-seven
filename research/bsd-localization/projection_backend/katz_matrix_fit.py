#!/usr/bin/env python3
"""Certify the finite weight-two U5 matrix from a saved Katz basis.

For k=k0=2 the weight-twist factor is exactly one. Thus the required row
matrix A is characterized by E_short.T * A.T = U(E).T. This module uses
bounded integer NumPy arithmetic and the existing inverse-minor checker;
it neither computes modular forms nor assumes an infinite U comparison.
"""
from __future__ import annotations

import argparse
import gzip
import hashlib
import json
from pathlib import Path
import sys
import time

import numpy as np

from finite_projection import (
    array, matmul_mod, require, solve_integral, verify_integral_solution,
)


SCOPE = (
    "Finite weight-two U5 coordinate fit. Every sampled q-coefficient and "
    "a two-sided scaled inverse minor are checked. The matrix is uniquely "
    "determined to the reported precision among compatible exact integral "
    "coordinate solutions. An infinite-operator comparison, omitted-tail "
    "bound, and geometric lattice identification remain separate obligations."
)


def checked_basis(e, *, elldash, basis_digits, matrix_digits, prime):
    require(prime == 5, "This adapter is restricted to U5")
    require(isinstance(elldash, int) and elldash > 0, "Invalid coefficient count")
    require(isinstance(matrix_digits, int) and isinstance(basis_digits, int)
            and 0 < matrix_digits <= basis_digits, "Invalid precision request")
    e = array(e, prime**basis_digits)
    require(e.ndim == 2 and 0 < e.shape[0] <= elldash, "Invalid Katz basis shape")
    require(e.shape[1] > prime*(elldash-1), "Basis does not include every U5 sample")
    return e


def basis_digest(e, prime, basis_digits):
    """Bind the residue matrix using an explicit platform-independent format."""
    canonical = np.ascontiguousarray(e, dtype="<i8")
    digest = hashlib.sha256()
    header = ["katz-residue-matrix-le-i64-v1", prime, basis_digits,
              int(e.shape[0]), int(e.shape[1])]
    digest.update((json.dumps(header, separators=(",", ":"))+"\n").encode())
    digest.update(memoryview(canonical).cast("B"))
    return digest.hexdigest()


def finite_equation(e, elldash, prime):
    return e[:, :elldash].T, e[:, prime*np.arange(elldash)].T


def fit_katz_matrix(e, *, elldash, basis_digits, matrix_digits, prime=5):
    """Return a JSON-serializable matrix and finite fit certificate.

    e is a rectangular list/NumPy array of residues, with basis vectors
    as rows and q-coefficients as columns. No Sage objects are required.
    The returned key ``row_operator_A_mod_5m`` has the existing capsule's
    convention c -> cA; ``coordinate_fit`` retains the higher precision
    coordinates and inverse-minor witness for independent replay.
    """
    e = checked_basis(e, elldash=elldash, basis_digits=basis_digits,
                      matrix_digits=matrix_digits, prime=prime)
    left, right = finite_equation(e, elldash, prime)
    fit = solve_integral(left, right, prime, basis_digits)
    require(fit["coordinate_digits"] >= matrix_digits,
            "Inverse-minor guard leaves fewer digits than requested for A")
    modulus = prime**matrix_digits
    operator = array(fit["coordinates"], modulus).T
    require(np.array_equal(matmul_mod(operator, e[:, :elldash], modulus),
                           e[:, prime*np.arange(elldash)] % modulus),
            "Reduced row-operator identity failed")
    return {
        "schema": "katz-matrix-fit-v1", "prime": prime, "weight": 2,
        "weight_residue": 2, "weight_twist_exponent": 0,
        "basis_digits": basis_digits, "matrix_digits": matrix_digits,
        "elldash": elldash, "dimension": int(e.shape[0]),
        "q_precision_exclusive": int(e.shape[1]),
        "basis_residue_sha256": basis_digest(e, prime, basis_digits),
        "basis_digest_format": "JSON header followed by C-order little-endian signed int64 residues",
        "row_operator_A_mod_5m": operator.tolist(), "coordinate_fit": fit,
        "certified_coordinate_digits": fit["coordinate_digits"],
        "inverse_minor_guard": fit["inverse_minor"]["guard"],
        "checks": {"full_finite_identity_at_basis_precision": True,
                   "full_finite_identity_at_matrix_precision": True,
                   "two_sided_scaled_inverse_minor": True,
                   "compatible_integral_coordinate_uniqueness": True},
        "scope": SCOPE,
    }


def verify_katz_matrix(e, certificate):
    """Verify the fit and precision without rerunning Gaussian elimination."""
    require(certificate.get("schema") == "katz-matrix-fit-v1", "Wrong fit schema")
    prime = certificate["prime"]
    elldash = certificate["elldash"]
    basis_digits, matrix_digits = certificate["basis_digits"], certificate["matrix_digits"]
    require((certificate["weight"], certificate["weight_residue"],
             certificate["weight_twist_exponent"]) == (2, 2, 0),
            "Only the untwisted weight-two equation is certified")
    e = checked_basis(e, elldash=elldash, basis_digits=basis_digits,
                      matrix_digits=matrix_digits, prime=prime)
    require((certificate["dimension"], certificate["q_precision_exclusive"]) == e.shape,
            "Basis shape does not match the receipt")
    require(certificate["basis_residue_sha256"] == basis_digest(e, prime, basis_digits),
            "Basis residue digest mismatch")
    left, right = finite_equation(e, elldash, prime)
    fit = certificate["coordinate_fit"]
    require(fit["input_digits"] == basis_digits, "Fit uses a different input precision")
    digits = verify_integral_solution(left, right, fit, prime)
    require(digits >= matrix_digits, "Fit does not certify the requested matrix precision")
    require(certificate["certified_coordinate_digits"] == digits and
            certificate["inverse_minor_guard"] == basis_digits-digits,
            "Incorrect reported precision or inverse guard")
    modulus = prime**matrix_digits
    operator = array(certificate["row_operator_A_mod_5m"], modulus)
    require(operator.shape == (e.shape[0], e.shape[0]), "Wrong row-operator shape")
    require(np.array_equal(operator, array(fit["coordinates"], modulus).T),
            "Operator is not the transpose of the fitted coordinates")
    require(np.array_equal(matmul_mod(operator, e[:, :elldash], modulus),
                           e[:, prime*np.arange(elldash)] % modulus),
            "Finite U5(E)=A E identity failed")
    return {"status": "PASS", "dimension": int(e.shape[0]),
            "matrix_digits": matrix_digits, "coordinate_digits": digits,
            "inverse_minor_guard": basis_digits-digits,
            "finite_equations_checked": int(e.shape[0])*elldash,
            "scope": SCOPE}


def read_json(path):
    data = path.read_bytes()
    if path.suffix == ".gz":
        data = gzip.decompress(data)
    return json.loads(data)


def write_json(path, value):
    payload = (json.dumps(value, sort_keys=True, separators=(",", ":"))+"\n").encode()
    path.parent.mkdir(parents=True, exist_ok=True)
    if path.suffix == ".gz":
        payload = gzip.compress(payload, mtime=0)
    path.write_bytes(payload)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--basis", type=Path, required=True,
                        help="JSON/gzip containing Katz_E_mod_5mdash, elldash and mdash")
    parser.add_argument("--matrix-digits", type=int,
                        help="Override parameters.matrix_digits in the basis checkpoint")
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--output", type=Path, help="Write a new fit certificate")
    mode.add_argument("--verify", type=Path, help="Verify an existing fit certificate")
    args = parser.parse_args()
    source = read_json(args.basis)
    e = source["Katz_E_mod_5mdash"]
    started = time.monotonic()
    if args.verify:
        certificate = read_json(args.verify)
        require(certificate["basis_digits"] == int(source["mdash"]) and
                certificate["elldash"] == int(source["elldash"]),
                "Source and certificate precision metadata differ")
        if args.matrix_digits is not None:
            require(certificate["matrix_digits"] == args.matrix_digits,
                    "Certificate matrix precision differs from the explicit request")
        report = verify_katz_matrix(e, certificate)
    else:
        matrix_digits = args.matrix_digits
        if matrix_digits is None:
            matrix_digits = int(source["parameters"]["matrix_digits"])
        certificate = fit_katz_matrix(e, elldash=int(source["elldash"]),
                                      basis_digits=int(source["mdash"]),
                                      matrix_digits=matrix_digits)
        write_json(args.output, certificate)
        report = {"status": "finite_matrix_fit_constructed", "output": str(args.output),
                  "dimension": certificate["dimension"],
                  "matrix_digits": certificate["matrix_digits"],
                  "coordinate_digits": certificate["certified_coordinate_digits"],
                  "inverse_minor_guard": certificate["inverse_minor_guard"],
                  "scope": SCOPE}
    print(json.dumps(report, indent=2, sort_keys=True))
    print(f"Elapsed: {time.monotonic()-started:.3f} seconds", file=sys.stderr)


if __name__ == "__main__":
    main()
