#!/usr/bin/env python3
"""Check finite projective line separation; never certify arithmetic provenance.

Standard Python only. Input vectors are claimed primitive integral lifts in
an unramified coefficient ring, known coordinatewise modulo p**N. The checker
validates the finite data and computes their determinant. It cannot establish
the stated analytic precision or identify either vector with a Galois class.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import sys


SCHEMA = "bsd-projective-line-separation/v1"
MAX_PRIME = 2**31 - 1
MAX_PRECISION = 1024
MAX_DEGREE = 64


class CertificateError(ValueError):
    """The supplied certificate is not in the supported exact format."""


def _integer(value, label, lower=None, upper=None):
    if type(value) is not int:
        raise CertificateError(f"{label} must be an integer, not a Boolean or float")
    if lower is not None and value < lower:
        raise CertificateError(f"{label} must be at least {lower}")
    if upper is not None and value > upper:
        raise CertificateError(f"{label} exceeds the supported bound {upper}")
    return value


def _text(value, label):
    if not isinstance(value, str) or not value.strip():
        raise CertificateError(f"{label} must be a nonempty string")
    return value


def _mapping(value, label, keys):
    if not isinstance(value, dict):
        raise CertificateError(f"{label} must be an object")
    if set(value) != set(keys):
        raise CertificateError(f"{label} must have exactly the keys {sorted(keys)}")
    return value


def is_prime(n):
    """Deterministic trial division; the format bounds n by 2**31-1."""
    if n < 2:
        return False
    if n % 2 == 0:
        return n == 2
    divisor = 3
    while divisor * divisor <= n:
        if n % divisor == 0:
            return False
        divisor += 2
    return True


def _trim(poly):
    poly = list(poly)
    while poly and poly[-1] == 0:
        poly.pop()
    return poly


def _remainder(poly, modulus_poly, modulus):
    """Polynomial remainder; divisor leading coefficient must be a unit."""
    a = _trim([x % modulus for x in poly])
    b = _trim([x % modulus for x in modulus_poly])
    if not b:
        raise CertificateError("zero polynomial divisor")
    inverse = pow(b[-1], -1, modulus)
    while len(a) >= len(b):
        shift = len(a) - len(b)
        scale = a[-1] * inverse % modulus
        for i, coefficient in enumerate(b):
            a[shift + i] = (a[shift + i] - scale * coefficient) % modulus
        a = _trim(a)
    return a


def _multiply(a, b, modulus_poly, modulus):
    if not a or not b:
        return []
    product = [0] * (len(a) + len(b) - 1)
    for i, ai in enumerate(a):
        for j, bj in enumerate(b):
            product[i + j] = (product[i + j] + ai * bj) % modulus
    return _remainder(product, modulus_poly, modulus)


def _power(base, exponent, modulus_poly, modulus):
    value = [1]
    base = _remainder(base, modulus_poly, modulus)
    while exponent:
        if exponent & 1:
            value = _multiply(value, base, modulus_poly, modulus)
        base = _multiply(base, base, modulus_poly, modulus)
        exponent >>= 1
    return value


def _subtract(a, b, modulus):
    return _trim([
        ((a[i] if i < len(a) else 0) - (b[i] if i < len(b) else 0)) % modulus
        for i in range(max(len(a), len(b)))
    ])


def _gcd(a, b, p):
    a, b = _trim(a), _trim(b)
    while b:
        a, b = b, _remainder(a, b, p)
    if not a:
        return []
    scale = pow(a[-1], -1, p)
    return [(x * scale) % p for x in a]


def _prime_divisors(n):
    divisors = set()
    candidate = 2
    while candidate * candidate <= n:
        if n % candidate == 0:
            divisors.add(candidate)
            while n % candidate == 0:
                n //= candidate
        candidate += 1
    if n > 1:
        divisors.add(n)
    return divisors


def is_irreducible(modulus_poly, p):
    """Rabin's exact finite-field criterion, including degree one."""
    f = _trim([x % p for x in modulus_poly])
    degree = len(f) - 1
    if degree < 1 or f[-1] != 1:
        return False
    x = _remainder([0, 1], f, p)
    frobenius_powers = [x]
    for _ in range(degree):
        frobenius_powers.append(_power(frobenius_powers[-1], p, f, p))
    if frobenius_powers[degree] != x:
        return False
    for prime_divisor in _prime_divisors(degree):
        polynomial = _subtract(frobenius_powers[degree // prime_divisor], x, p)
        if _gcd(polynomial, f, p) != [1]:
            return False
    return True


def _vector(value, label, degree, modulus, p, basis_id):
    _mapping(value, label, {"basis_id", "coordinates", "normalization"})
    if value["basis_id"] != basis_id:
        raise CertificateError(f"{label}.basis_id differs from the common basis")
    _text(value["normalization"], f"{label}.normalization")
    coordinates = value["coordinates"]
    if not isinstance(coordinates, list) or len(coordinates) != 2:
        raise CertificateError(f"{label}.coordinates must contain two field coordinates")
    for i, coordinate in enumerate(coordinates):
        if not isinstance(coordinate, list) or len(coordinate) != degree:
            raise CertificateError(f"{label}.coordinates[{i}] must have {degree} coefficients")
        for j, coefficient in enumerate(coordinate):
            _integer(coefficient, f"{label}.coordinates[{i}][{j}]", 0, modulus - 1)
    if all(coefficient % p == 0 for coordinate in coordinates for coefficient in coordinate):
        raise CertificateError(f"{label} is not a primitive integral projective representative")
    return coordinates


def check_certificate(data):
    _mapping(data, "certificate", {
        "schema", "ring", "basis_id", "error_ideal", "analytic",
        "exceptional", "source_bindings",
    })
    if data["schema"] != SCHEMA:
        raise CertificateError(f"unsupported schema; expected {SCHEMA}")
    ring = _mapping(data["ring"], "ring", {"p", "precision", "modulus_polynomial"})
    p = _integer(ring["p"], "ring.p", 3, MAX_PRIME)
    if not is_prime(p):
        raise CertificateError("ring.p must be an odd prime")
    precision = _integer(ring["precision"], "ring.precision", 1, MAX_PRECISION)
    f = ring["modulus_polynomial"]
    if not isinstance(f, list) or not 2 <= len(f) <= MAX_DEGREE + 1:
        raise CertificateError(f"modulus_polynomial must have degree 1 through {MAX_DEGREE}")
    for i, coefficient in enumerate(f):
        _integer(coefficient, f"modulus_polynomial[{i}]")
    if f[-1] != 1:
        raise CertificateError("modulus_polynomial must be monic over the integers")
    if not is_irreducible(f, p):
        raise CertificateError("modulus_polynomial is reducible modulo p")
    degree = len(f) - 1
    modulus = p**precision
    basis_id = _text(data["basis_id"], "basis_id")
    if data["error_ideal"] != "p^N O_L^2":
        raise CertificateError("error_ideal must be the stated coordinatewise p^N O_L^2 claim")
    bindings = _mapping(data["source_bindings"], "source_bindings", {
        "analytic_leading_term", "exceptional_line", "common_basis", "precision",
    })
    for role, binding in bindings.items():
        _text(binding, f"source_bindings.{role}")
    a = _vector(data["analytic"], "analytic", degree, modulus, p, basis_id)
    b = _vector(data["exceptional"], "exceptional", degree, modulus, p, basis_id)
    determinant = _subtract(
        _multiply(a[0], b[1], f, modulus),
        _multiply(a[1], b[0], f, modulus),
        modulus,
    )
    determinant += [0] * (degree - len(determinant))
    nonzero = any(determinant)
    valuation = None
    if nonzero:
        valuation = precision
        for coefficient in determinant:
            if coefficient:
                order = 0
                while coefficient % p == 0:
                    coefficient //= p
                    order += 1
                valuation = min(valuation, order)
    return {
        "schema": SCHEMA,
        "status": "CERTIFIED_DISTINCT" if nonzero else "INCONCLUSIVE",
        "p": p,
        "precision": precision,
        "unramified_degree": degree,
        "basis_id": basis_id,
        "determinant_residue": determinant,
        "determinant_valuation": valuation,
        "determinant_valuation_lower_bound": valuation if nonzero else precision,
        "finite_checks": {
            "prime": True,
            "irreducible_mod_p": True,
            "canonical_residues": True,
            "common_basis_ids": True,
            "both_representatives_primitive": True,
        },
        "scope": (
            "Finite arithmetic only. If the supplied common-basis and coordinatewise "
            "precision claims are proved, CERTIFIED_DISTINCT proves the two true lines "
            "differ. INCONCLUSIVE does not prove equality."
        ),
        "unverified_mathematical_obligations": [
            "The stated analytic coefficient is the first nonzero coefficient of the true germ.",
            "The exceptional vector represents the source-derived exceptional line in the same basis.",
            "Both normalizations and coordinate error bounds are mathematically justified.",
            "The global, Selmer, theta-order, and full-comparison hypotheses of README.md hold.",
        ],
        "source_bindings": bindings,
    }


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("certificate", type=Path)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args(argv)
    try:
        raw = args.certificate.read_bytes()
        data = json.loads(raw)
        result = check_certificate(data)
        result["certificate_sha256"] = hashlib.sha256(raw).hexdigest()
        exit_code = 0 if result["status"] == "CERTIFIED_DISTINCT" else 2
    except (CertificateError, OSError, json.JSONDecodeError) as exc:
        result = {"schema": SCHEMA, "status": "INVALID", "error": str(exc)}
        exit_code = 1
    output = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.write_text(output)
    sys.stdout.write(output)
    return exit_code


if __name__ == "__main__":
    raise SystemExit(main())
