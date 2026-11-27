#!/usr/bin/env python3
"""Exact arithmetic and projection for Pic(Z + 29^m O_{Q(sqrt(-71))}).

The mathematical argument is in README.md. This script checks its finite
arithmetic inputs and implements pushforward of an already validated theta
coefficient stream. It does NOT generate Gross points or theta coefficients.
Python standard library only; no floating point is used.
"""

from __future__ import annotations

import argparse
import json
from math import comb, gcd, isqrt
from pathlib import Path
from typing import Iterable


P = 29
D = -71
TAME_ORDER = 196


def reduced_forms(discriminant: int) -> list[list[int]]:
    """All primitive reduced positive definite forms, canonical boundary sign."""
    out = []
    for a in range(1, isqrt((-discriminant) // 3) + 1):
        for b in range(-a, a + 1):
            if (b * b - discriminant) % (4 * a):
                continue
            c = (b * b - discriminant) // (4 * a)
            if a > c or gcd(gcd(a, abs(b)), c) != 1:
                continue
            if (abs(b) == a or a == c) and b < 0:
                continue
            out.append([a, b, c])
    return out


def reduce_form(a: int, b: int, c: int) -> list[int]:
    """Proper reduction by determinant-one substitutions, with boundary sign."""
    discriminant = b * b - 4 * a * c
    assert discriminant < 0 and a > 0
    while True:
        q = (a - b) // (2 * a)
        b, c = b + 2 * a * q, a * q * q + b * q + c
        assert b * b - 4 * a * c == discriminant
        if a > c:
            a, b, c = c, -b, a
            continue
        if abs(b) == a or a == c:
            b = abs(b)
        assert -a < b <= a <= c or -a < b <= a == c
        return [a, b, c]


def class_cycle() -> dict:
    """Ordered reduced forms for powers of a=(2,omega), and the primes over29."""
    root = 0  # The chosen root omega=0 modulo2.
    orbit = [[1, 1, 18]]
    for exponent in range(1, 8):
        norm = 2**exponent
        if exponent > 1:
            candidates = [root, root + norm // 2]
            roots = [r for r in candidates if (r * r - r + 18) % norm == 0]
            assert len(roots) == 1
            root = roots[0]
        b = 2 * root - 1
        assert (b * b + 71) % (4 * norm) == 0
        orbit.append(reduce_form(norm, b, (b * b + 71) // (4 * norm)))
    assert orbit[0] == orbit[-1] and len({tuple(f) for f in orbit[:-1]}) == 7
    primes = []
    for r in (13, 17):
        b = 2 * r - 1
        form = reduce_form(29, b, (b * b + 71) // (4 * 29))
        primes.append({"omega_residue": r, "reduced_form": form,
                       "class_exponent_of_a": orbit.index(form)})
    assert [item["class_exponent_of_a"] for item in primes] == [4, 3]
    # A separate ideal factorization checks the orientation:
    # beta=7+3*omega has norm8*29, lies over omega=1 at2 and omega=17 at29.
    assert 7 * 7 + 7 * 3 + 18 * 3 * 3 == 8 * 29
    assert (7 + 3 * 0) % 2 == 1 and (7 + 3 * 1) % 2 == 0
    assert (7 + 3 * 17) % 29 == 0 and (7 + 3 * 13) % 29 != 0
    return {"forms_in_a_power_order": orbit[:-1],
            "seventh_power_returns_identity": True, "primes_above_29": primes,
            "independent_factorization_witness": {
                "beta_coordinates": [7, 3], "beta_norm": 232,
                "ideal_identity": "(7+3*omega) = conjugate(a)^3 * p17"}}


def lift_root(root: int, precision: int) -> int:
    """Hensel lift a root of x^2-x+18 from F29 to Z/29^precision."""
    if precision < 1:
        raise ValueError("precision must be positive")
    if (root * root - root + 18) % P:
        raise ValueError("not a root modulo 29")
    root %= P
    modulus = P
    for _ in range(1, precision):
        derivative = (2 * root - 1) % P
        digit = -((root * root - root + 18) // modulus) * pow(derivative, -1, P)
        root += (digit % P) * modulus
        modulus *= P
        assert (root * root - root + 18) % modulus == 0
    return root


def alpha_ratio(precision: int) -> tuple[int, int, int]:
    """Ratio of the two local values of alpha=10+omega."""
    modulus = P**precision
    r1, r2 = lift_root(13, precision), lift_root(17, precision)
    return r1, r2, (10 + r1) * pow(10 + r2, -1, modulus) % modulus


def local_unit_order(value: int, precision: int) -> int:
    """Exact order in (Z/29^precision)^*, whose order is 28*29^(precision-1)."""
    modulus = P**precision
    if gcd(value, modulus) != 1:
        raise ValueError("not a unit")
    order = 28 * P ** (precision - 1)
    assert pow(value, order, modulus) == 1
    for ell in (2, 7, P):
        while order % ell == 0 and pow(value, order // ell, modulus) == 1:
            order //= ell
    return order


def level(m: int) -> dict[str, int]:
    """m is the conductor exponent, not the exponent of the wild quotient."""
    if m < 1:
        raise ValueError("the m=0 class group is a separate level")
    wild = P ** (m - 1)
    total = TAME_ORDER * wild
    # Idempotent exponents for the Sylow factors, in the full cyclic group.
    e_wild = 0 if wild == 1 else TAME_ORDER * pow(TAME_ORDER, -1, wild) % total
    e_tame = (1 - e_wild) % total
    assert e_wild % TAME_ORDER == 0 and e_wild % wild == 1 % wild
    assert e_tame % TAME_ORDER == 1 and e_tame % wild == 0
    assert (e_wild * e_wild - e_wild) % total == 0
    assert (e_tame * e_tame - e_tame) % total == 0
    return {
        "conductor_exponent_m": m,
        "conductor": P**m,
        "wild_exponent_n": m - 1,
        "wild_order": wild,
        "tame_order": TAME_ORDER,
        "ring_class_number": total,
        "wild_idempotent_exponent": e_wild,
        "tame_idempotent_exponent": e_tame,
    }


def project_cycle(coefficients: Iterable[int], m: int, modulus: int | None = None) -> list[int]:
    """Push forward a COMPLETE ordered cycle c_i [a]^i to the trivial tame branch.

    Input must have exactly |G_m| coefficients, in exponent order 0..|G_m|-1
    for a=(2,omega). Output index j means the j-th power of the image of a in
    G_m/Delta. This sums, rather than averages, all 196 entries in each fiber.
    The code validates cycle length; the producer must certify coefficient
    meaning, generator orientation, eigenform normalization, and Gross points.
    """
    data = level(m)
    if modulus is not None and modulus <= 1:
        raise ValueError("modulus must exceed one")
    wild, total = data["wild_order"], data["ring_class_number"]
    output = [0] * wild
    count = 0
    for i, coefficient in enumerate(coefficients):
        if i >= total:
            raise ValueError("coefficient stream has extra entries")
        if not isinstance(coefficient, int):
            raise TypeError("coefficients must be integers")
        j = i % wild
        output[j] += coefficient
        if modulus is not None:
            output[j] %= modulus
        count += 1
    if count != total:
        raise ValueError(f"incomplete cycle: got {count}, need {total}")
    return output


def jet_precision_gate(m: int, precision: int, degree: int) -> dict:
    """Can a quotient group-ring element determine this truncated T-series?

    Checks that ((1+T)^|Gamma|-1) vanishes modulo (29^precision,T^(degree+1)).
    This is a compatibility check for the downstream jet implementation, not
    an implementation of theta coefficients or exact lower-order vanishing.
    """
    if precision < 1 or degree < 0:
        raise ValueError("positive precision and nonnegative degree required")
    wild = level(m)["wild_order"]
    modulus = P**precision
    residues = [comb(wild, j) % modulus for j in range(1, min(degree, wild) + 1)]
    return {
        "conductor_exponent_m": m,
        "coefficient_modulus": modulus,
        "maximum_T_degree": degree,
        "relation_coefficient_residues": residues,
        "well_defined": all(r == 0 for r in residues),
    }


def verify() -> dict:
    forms = reduced_forms(D)
    assert len(forms) == 7
    cycle = class_cycle()
    assert sorted(cycle["forms_in_a_power_order"]) == forms
    # omega^2=omega-18. Multiplication by alpha=10+omega has determinant128.
    multiplication_matrix = [[10, -18], [1, 11]]
    assert 10 * 11 - (-18) == 128
    assert (10 + 0) % 2 == 0 and (10 + 1) % 2 == 1
    # Alpha generates a^7: it has norm2^7 and is not in the conjugate prime.
    r1, r2, ratio = alpha_ratio(2)
    assert (r1, r2, ratio) == (477, 365, 322)
    assert local_unit_order(ratio % P, 1) == 28
    residue = pow(ratio, 28, P * P)
    assert residue == 610 == 1 + 21 * P

    rows = []
    for m in range(1, 5):
        a, b, rho = alpha_ratio(m)
        order = local_unit_order(rho, m)
        assert order == 28 * P ** (m - 1)
        rows.append({**level(m), "omega_roots": [a, b], "alpha_ratio": rho,
                     "alpha_ratio_order": order})

    # Risk-oriented fixture: a principal-Hilbert-class restriction gives a
    # false nonzero value, while the full trivial-tame projection cancels.
    # These are SYNTHETIC coefficients, not measured theta coefficients.
    m = 3
    wild, total = level(m)["wild_order"], level(m)["ring_class_number"]
    sparse = {0: 1, wild: -1}
    full = project_cycle((sparse.get(i, 0) for i in range(total)), m, P * P)
    principal_only = project_cycle(
        (sparse.get(i, 0) if i % 7 == 0 else 0 for i in range(total)), m, P * P
    )
    assert not any(full)
    assert principal_only[0] == 1 and sum(principal_only) == 1
    length_errors_detected = 0
    for stream in ([0] * (196 - 1), [0] * (196 + 1)):
        try:
            project_cycle(stream, 1)
        except ValueError:
            length_errors_detected += 1
    assert length_errors_detected == 2

    unsafe = jet_precision_gate(2, 2, 2)
    safe = jet_precision_gate(3, 2, 2)
    first_attempt = jet_precision_gate(2, 1, 2)
    assert unsafe["relation_coefficient_residues"] == [29, 406]
    assert not unsafe["well_defined"] and safe["well_defined"]
    assert first_attempt["well_defined"]
    return {
        "status": "PASS: exact finite arithmetic and synthetic projection checks",
        "not_computed": ["Gross-point coefficients", "theta T^2 coefficient",
                         "auxiliary ring-character L-values", "Lean kernel proof"],
        "discriminant": D,
        "reduced_forms": forms,
        "class_number": len(forms),
        "ordered_class_group": cycle,
        "alpha_coordinates": [10, 1],
        "alpha_multiplication_matrix": multiplication_matrix,
        "alpha_norm": 128,
        "ratio_28th_power_mod_841": residue,
        "unit_lift_first_digit": 21,
        "all_levels_claim": "Pic(Z+29^m O_K) is cyclic of order 196*29^(m-1), generated by the contracted ideal (2,omega), for every m>=1; proof in README.md",
        "finite_level_checks": rows,
        "synthetic_cancellation_fixture": {
            "conductor_exponent_m": m,
            "nonzero_input_coefficients": {str(k): v for k, v in sparse.items()},
            "full_projection_is_zero": True,
            "principal_class_only_projection_constant": principal_only[0],
            "incorrect_stream_lengths_rejected": length_errors_detected,
        },
        "precision_checks": [first_attempt, unsafe, safe],
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = json.dumps(verify(), indent=2) + "\n"
    if args.output:
        args.output.write_text(result)
    print(result, end="")
