#!/usr/bin/env python3
"""Exact elementary screen for a second p=5, K=Q(sqrt(-71)) pilot.

Catalog ranks select test cases only. The eligibility arithmetic and proposed
analytic proof route do not infer L-value assertions from rational points.
Standard library only. Infinite Galois-image conclusions also use the written
Tate-uniformization and closed-subgroup arguments in README.md.
"""
from __future__ import annotations

import argparse
from collections import deque
from fractions import Fraction
from hashlib import sha256
from itertools import product
import json
from math import gcd, isqrt
from pathlib import Path

ROOT = Path(__file__).resolve().parent
P = 5
D = -71
I = (1, 0, 0, 1)
U = (1, 1, 0, 1)
SOURCE = ROOT / "sources" / "cremona-through-1000.txt"


def prime(n):
    return n >= 2 and all(n % d for d in range(2, isqrt(n) + 1))


def valuation(n, p):
    assert n != 0
    n = abs(n)
    k = 0
    while n % p == 0:
        n //= p
        k += 1
    return k


def legendre(n, p):
    assert prime(p) and p > 2
    r = pow(n % p, (p - 1) // 2, p)
    return -1 if r == p - 1 else r


def invariants(a):
    a1, a2, a3, a4, a6 = a
    b2 = a1*a1 + 4*a2
    b4 = 2*a4 + a1*a3
    b6 = a3*a3 + 4*a6
    b8 = a1*a1*a6 + 4*a2*a6 - a1*a3*a4 + a2*a3*a3 - a4*a4
    c4 = b2*b2 - 24*b4
    c6 = -b2**3 + 36*b2*b4 - 216*b6
    delta = -b2*b2*b8 - 8*b4**3 - 27*b6*b6 + 9*b2*b4*b6
    assert c4**3-c6**2 == 1728*delta
    return {"c4": c4, "c6": c6, "discriminant": delta,
            "j": str(Fraction(c4**3, delta))}


def point_count(a, q):
    assert prime(q)
    a1, a2, a3, a4, a6 = a
    count = 1 + sum((y*y+a1*x*y+a3*y-x**3-a2*x*x-a4*x-a6) % q == 0
                    for x in range(q) for y in range(q))
    return {"prime": q, "points_including_infinity": count, "a_q": q+1-count}


def reduced_forms(discriminant):
    forms = []
    for a in range(1, isqrt((-discriminant)//3)+1):
        for b in range(-a, a+1):
            if (b*b-discriminant) % (4*a):
                continue
            c = (b*b-discriminant)//(4*a)
            if a > c or gcd(gcd(a, b), c) != 1:
                continue
            if (abs(b) == a or a == c) and b < 0:
                continue
            forms.append([a, b, c])
    return forms


def mul(a, b):
    return ((a[0]*b[0]+a[1]*b[2]) % P,
            (a[0]*b[1]+a[1]*b[3]) % P,
            (a[2]*b[0]+a[3]*b[2]) % P,
            (a[2]*b[1]+a[3]*b[3]) % P)


def det(a):
    return (a[0]*a[3]-a[1]*a[2]) % P


def generated(generators):
    seen = {I}
    queue = deque([I])
    while queue:
        a = queue.popleft()
        for b in generators:
            c = mul(a, b)
            if c not in seen:
                seen.add(c)
                queue.append(c)
    return seen


def big_image_finite_certificate():
    gl = {a for a in product(range(P), repeat=4) if det(a)}
    sl = {a for a in gl if det(a) == 1}
    candidates = sorted(a for a in gl if (a[0]+a[3]) % P == 3 and det(a) == 3)
    assert len(gl) == 480 and len(sl) == 120 and len(candidates) == 20
    cases = []
    for a in candidates:
        group = generated((U, a))
        assert group == gl
        cases.append({"frobenius_matrix": list(a), "generated_order": len(group)})
    assert generated((U, (1, 0, 1, 1))) == sl
    return {"inertia_transvection": list(U), "frobenius_prime": 3,
            "trace_mod5": 3, "determinant_mod5": 3,
            "polynomial_coefficients_ascending": [3, 2, 1],
            "polynomial_discriminant_mod5": 2,
            "polynomial_roots_mod5": [], "all_possible_cases": cases,
            "all_cases_generate_GL2_F5": True, "GL2_order": 480,
            "SL2_order": 120,
            "infinite_interpretation": "Tate inertia plus these cases give residual GL2(F5); the closed-subgroup lifting theorem stated in README.md gives SL2(Z5) inside the five-adic image."}


def ordinary_root(ap, digits=8):
    assert ap % P
    modulus = P
    root = ap % P
    while modulus < P**digits:
        hits = [root+k*modulus for k in range(P)
                if ((root+k*modulus)**2-ap*(root+k*modulus)+P) % (P*modulus) == 0]
        assert len(hits) == 1
        root = hits[0]
        modulus *= P
    return root, modulus


def algebra_mul(a, b, ap=-4, p=5):
    # Q[F]/(F^2-ap*F+p).
    return (a[0]*b[0]-p*a[1]*b[1],
            a[0]*b[1]+a[1]*b[0]+ap*a[1]*b[1])


def anomaly_certificate():
    root, modulus = ordinary_root(-4)
    assert root % 25 == 16 and root % 125 == 66
    assert valuation(root-1, 5) == 1
    F = (Fraction(0), Fraction(1))
    one = (Fraction(1), Fraction(0))
    finv = (Fraction(-4, 5), Fraction(-1, 5))
    A = (Fraction(38, 25), Fraction(7, 25))
    Ainv = (Fraction(2, 5), Fraction(-7, 25))
    assert algebra_mul(F, finv) == one
    assert algebra_mul(A, Ainv) == one
    assert algebra_mul(A, (Fraction(1), Fraction(-1, 5))) == (one[0]-finv[0], -finv[1])
    determinant_A = A[0]**2 - 4*A[0]*A[1] + 5*A[1]**2
    assert determinant_A == 1
    return {"ordinary_root_modulus": modulus, "ordinary_root_residue": root,
            "ordinary_root_mod25": root % 25, "ordinary_root_mod125": root % 125,
            "alpha_minus_one_valuation": 1,
            "one_minus_alpha_inverse_valuation": 1,
            "one_minus_alpha_over5_valuation": -1,
            "CH_height_prefactor_valuation": -2,
            "frobenius_polynomial": "F^2+4F+5",
            "polynomial_at_one": 10, "polynomial_at_five": 50,
            "base_test_operator_I_F": [str(x) for x in A],
            "base_image_operator_I_F": [str(x) for x in Ainv],
            "base_test_operator_determinant": str(determinant_A),
            "anomalous_prime_excluded_by_CH_hypotheses": False,
            "scope": "These denominators are nonzero but not units. This is not a unit-precision certificate for a future geometric projection."}


def source_rows():
    rows = []
    for line in SOURCE.read_text().splitlines():
        conductor, iso, number, ainvs, rank, torsion = line.split()
        rows.append({"conductor": int(conductor), "cremona_iso": conductor+iso,
                     "cremona_label": conductor+iso+number, "number": int(number),
                     "ainvs": json.loads(ainvs), "catalog_rank": int(rank),
                     "catalog_torsion": int(torsion)})
    assert len(rows) == 5113 and max(r["conductor"] for r in rows) == 999
    return rows


def screen_row(row):
    n = row["conductor"]
    inv = invariants(row["ainvs"])
    counts = [point_count(row["ainvs"], q) for q in [2, 3, 5, 7, 11, 13]]
    ap = next(v["a_q"] for v in counts if v["prime"] == 5)
    inert = legendre(D, n) == -1
    ordinary = ap % 5 != 0
    bad_valuation = valuation(inv["discriminant"], n)
    mult = inv["c4"] % n != 0
    split = legendre(-inv["c6"], n) == 1 if mult else None
    ss_count = n//12 + {1: 0, 5: 1, 7: 1, 11: 2}[n % 12]
    return {**row, "invariants": inv, "point_counts": counts,
            "a5": ap, "ordinary_at5": ordinary, "anomalous_at5": ap % 5 == 1,
            "K_splitting_symbol": legendre(D, n), "N_inert_in_K": inert,
            "N_mod12": n % 12, "multiplicative_at_N": mult,
            "split_multiplicative_at_N": split,
            "discriminant_valuation_at_N": bad_valuation,
            "residual_inertia_transvection_at5": mult and bad_valuation % 5 != 0,
            "eligible_elementary_definite_ordinary_screen": inert and ordinary and mult and bad_valuation % 5 != 0,
            "supersingular_j_count": ss_count,
            "tame_common_level": 71*n,
            "Gamma0_common_level_index": 72*(n+1),
            "X0_common_level_genus": 6*n+5,
            "geometry_dimension_ratio_to389": str(Fraction(n+1, 390)),
            "cost_scope": "Exact dimensions/counts, not wall-time predictions. The common level has four cusps and no elliptic points since71 is 3mod4 and2mod3."}


def certificate():
    provenance = json.loads((ROOT / "sources" / "provenance.json").read_text())
    assert sha256(SOURCE.read_bytes()).hexdigest() == provenance["cremona_complete_prefix"]["local_sha256"]
    rows = source_rows()
    catalog = sorted((r for r in rows if prime(r["conductor"]) and r["catalog_rank"] == 2 and r["number"] == 1),
                     key=lambda r: (r["conductor"], r["cremona_label"]))
    assert [r["cremona_label"] for r in catalog] == ["389a1", "433a1", "563a1", "571b1", "643a1", "709a1", "997b1", "997c1"]
    screened = [screen_row(r) for r in catalog]
    selected = next(r for r in screened if r["conductor"] != 389 and r["eligible_elementary_definite_ordinary_screen"])
    assert selected["cremona_label"] == "433a1" and selected["ainvs"] == [1, 0, 0, 0, 1]
    assert selected["invariants"] == {"c4": 1, "c6": -865, "discriminant": -433, "j": "-1/433"}
    assert selected["a5"] == -4 and selected["split_multiplicative_at_N"]
    counts = {q: point_count(selected["ainvs"], q) for q in [2,3,5,7,11,13,17,19,23,29,31,37,41,43]}
    assert counts[2]["a_q"] == -1 and counts[3]["a_q"] == -2
    roots_frob = [x for x in range(5) if (x*x+2*x+3) % 5 == 0]
    assert roots_frob == []
    forms = {str(c): reduced_forms(D*c*c) for c in [1, 5, 25]}
    assert [len(forms[str(c)]) for c in [1,5,25]] == [7,28,140]
    assert [4,-3,5] in forms["1"]
    # The norm-five ideal has reduced form [4,-3,5], not the identity;
    # a group of prime order7 makes it a generator.
    assert (-3)**2-4*4*5 == D
    omega_roots5 = [x for x in range(5) if (x*x-x+18) % 5 == 0]
    omega_roots433 = [x for x in range(433) if (x*x-x+18) % 433 == 0]
    assert omega_roots5 == [2,4] and omega_roots433 == []
    sqrt_minus_c6 = next(x for x in range(433) if x*x % 433 == 865 % 433)
    assert legendre(-433, 71) == 1
    twist = invariants([1,-18,0,0,-357911])
    assert twist["c4"] == D**2 and twist["c6"] == -865*D**3 and twist["discriminant"] == -433*D**6
    return {
        "schema": "bsd-second-pilot-screen-v1", "status": "PASS",
        "chosen_curve": selected, "selected_point_counts": list(counts.values()),
        "selection_scope": "Smallest distinct prime-conductor catalog-rank2 class passing this elementary p5,K−71 screen in the complete Cremona prefix through1000. Catalog rank selects an example only; it is not a premise of the point-free arithmetic route.",
        "comparative_screen": screened,
        "field_inputs": {"discriminant": D, "omega_polynomial": [18,-1,1],
                         "omega_roots_mod5": omega_roots5, "omega_roots_mod433": omega_roots433,
                         "reduced_forms_minus71": forms["1"], "class_number": 7,
                         "ring_class_numbers_conductors_1_5_25": [7,28,140],
                         "reduced_forms_minus44375_sha256": sha256(json.dumps(forms["25"],separators=(",",":")).encode()).hexdigest(),
                         "prime5_reduced_form": [4,-3,5], "prime5_class_order": 7,
                         "gcd_5N_D": gcd(5*433,71), "coefficient_field_degree_Q5_zeta7": 6,
                         "order5_mod7": next(k for k in range(1,7) if pow(5,k,7)==1)},
        "conductor_and_sign_certificate": {
            "minimality_reason": "The discriminant has valuation1 at433 and is a unit elsewhere; c4 is a unit. The curve has multiplicative I1 reduction at433 and conductor433.",
            "sqrt_minus_c6_mod433": sqrt_minus_c6, "local_root_at433": -1,
            "archimedean_root": -1, "global_root_number": 1,
            "residual_ramification_reason": "The Tate parameter has valuation1, so adjoining a fifth root gives an inertia transvection.",
            "non_CM_reason": "The rational j-invariant −1/433 is not integral."},
        "finite_galois_image": big_image_finite_certificate(),
        "anomalous_prime_audit": anomaly_certificate(),
        "twist_inputs": {"ainvs": [1,-18,0,0,-357911], "invariants": twist,
                         "conductor": 433*71**2, "root_number": 1,
                         "twist_character_at_minus_conductor": legendre(-433,71)},
        "cost_comparison": {"pilot389_supersingular_count": 33,
                            "chosen433_supersingular_count": 36,
                            "same_conductor25_CM_classes": 140,
                            "geometry_dimension_ratio": str(Fraction(434,390)),
                            "quadratic_dimension_proxy_ratio": str(Fraction(434,390)**2),
                            "cubic_dimension_proxy_ratio": str(Fraction(434,390)**3),
                            "extra_base_operator_denominator_digit_relative389": 1},
        "pending_arithmetic_certificates": [
            "Root's separate second_theta calculation: conductor-one trivial toric sum exactly0, with identified E433 Brandt eigenfunction.",
            "Nonconstant conductor-one seven CM values to establish nontrivial order7 auxiliary period nonvanishing.",
            "Exact theta quadratic coefficient and ordinary normalization at conductor25.",
            "Full geometric leading vector, anomalous-prime precision budget, and separation from the new base line."],
        "does_not_use": ["Rational points", "Catalog rank as an arithmetic implication", "Finite Tate–Shafarevich group", "A unit assumption on alpha−1"],
        "source_sha256": sha256(SOURCE.read_bytes()).hexdigest(),
        "source_blob_sha": provenance["cremona_complete_prefix"]["full_file_git_blob_sha"],
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = certificate()
    if args.check:
        assert json.loads((ROOT / "result.json").read_text()) == result
        print("PASS: 433a1 elementary eligibility; all20 residual Frobenius cases; exact anomaly audit; complete-prefix selection")
    elif args.output:
        args.output.write_text(json.dumps(result, indent=2, sort_keys=True)+"\n")
        print(f"Wrote {args.output}")
    else:
        print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
