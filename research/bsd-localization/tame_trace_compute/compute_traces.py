#!/usr/bin/env python3
"""Exact tame traces of the stored E389/K(-71) CM weight jets.

The finite arithmetic is checked here.  The analytic Fricke/Bol theorem
identifying these coefficient calculations with tame traces is explained in
the accompanying README and the separate tame-trace theory note.

Only Python's standard library and the existing CM arithmetic module are used.
No global class, elliptic projection, or finite logarithm is computed.
"""

from __future__ import annotations

import argparse
from fractions import Fraction
import gzip
import hashlib
import importlib.util
import json
from math import gcd
from pathlib import Path
import sys
import time


HERE = Path(__file__).resolve().parent
PILOT = HERE.parent / "reflected_pilot"
SOURCE = PILOT / "cm-weight-jets.json.gz"
SOURCE_SHA256 = "80b2b0f5ba32d6a3d45ebb828c21e5bf043226cfd4290b72dd9d81ed8ae830ba"
ELL = 71
TARGET_LEVEL = 389
ZERO = (0,) * 6

# Import the arithmetic helpers without regenerating the old data or creating
# bytecode files in the other workstream's directory.
sys.dont_write_bytecode = True
spec = importlib.util.spec_from_file_location("cm_weight_jets", PILOT / "cm_weight_jets.py")
cm = importlib.util.module_from_spec(spec)
assert spec.loader is not None
spec.loader.exec_module(cm)


def canonical_bytes(value):
    return (json.dumps(value, sort_keys=True, separators=(",", ":")) + "\n").encode()


def matrix_mul(a, b):
    return [[sum(a[i][r] * b[r][j] for r in range(2))
             for j in range(2)] for i in range(2)]


def determinant(a):
    return a[0][0] * a[1][1] - a[0][1] * a[1][0]


def projective_row(c, d, ell):
    c, d = c % ell, d % ell
    assert c or d
    if c:
        return (1, d * pow(c, -1, ell) % ell)
    return (0, 1)


def coset_certificate(target_level, ell=ELL):
    """Verify the explicit ell+1 trace cosets and normalized-slash matrices."""
    assert gcd(target_level, ell) == 1
    b = -pow(target_level, -1, ell)
    assert (1 + target_level * b) % ell == 0
    d = (1 + target_level * b) // ell
    W = [[ell, b], [target_level * ell, ell * d]]
    assert determinant(W) == ell
    representatives = [[[1, 0], [0, 1]]]
    for j in range(ell):
        numerator = matrix_mul(W, [[1, j], [0, ell]])
        assert all(c % ell == 0 for row in numerator for c in row)
        gamma = [[c // ell for c in row] for row in numerator]
        assert gamma == [[1, j+b], [target_level, target_level*(j+b)+1]]
        assert determinant(gamma) == 1
        assert gamma[1][0] % target_level == 0
        representatives.append(gamma)
    classes = {projective_row(*a[1], ell) for a in representatives}
    expected = {(0, 1)} | {(1, r) for r in range(ell)}
    assert classes == expected
    return {
        "target_level": target_level,
        "source_level": target_level * ell,
        "W_matrix": W,
        "number_of_cosets": len(representatives),
        "all_projective_bottom_rows_distinct_and_complete": True,
        "all_matrix_factorizations_and_determinants_checked": True,
    }


def elliptic_oldform_regression(source, modulus):
    """Use actual q-series, not only the two by two Gram matrix."""
    f = source["f_q_coefficients_exact"]
    bound = (len(f)-1) // ELL
    # Independent finite-field count for the single prime used by the trace.
    points = 1
    for x in range(ELL):
        for y in range(ELL):
            points += (y*y+y-x*x*x-x*x+2*x) % ELL == 0
    aell = ELL + 1 - points
    assert points == 82 and aell == -10 and f[ELL] == aell
    d1 = f
    d2 = [ELL*f[n//ELL] if n % ELL == 0 else 0 for n in range(len(f))]
    # W interchanges the two differential-pullback oldforms.
    t11 = [d1[n] + d2[ELL*n] for n in range(bound+1)]
    t12 = [d2[n] + d1[ELL*n] for n in range(bound+1)]
    assert t11 == [72*a for a in f[:bound+1]]
    assert t12 == [aell*a for a in f[:bound+1]]
    combo = [3*a + 5*b for a, b in zip(d1, d2)]
    reflected = [5*a + 3*b for a, b in zip(d1, d2)]
    t1 = [combo[n] + reflected[ELL*n] for n in range(bound+1)]
    t2 = [reflected[n] + combo[ELL*n] for n in range(bound+1)]
    gram = [[72, aell], [aell, 72]]
    det = 72*72-aell*aell
    assert det == 5084 and det % 5 == 4
    for n in range(bound+1):
        assert Fraction(72*t1[n]-aell*t2[n], det) == 3*f[n]
        assert Fraction(-aell*t1[n]+72*t2[n], det) == 5*f[n]
    inv_det = pow(det, -1, modulus)
    inverse = [[72*inv_det % modulus, -aell*inv_det % modulus],
               [-aell*inv_det % modulus, 72*inv_det % modulus]]
    for i in range(2):
        for j in range(2):
            assert sum(gram[i][r]*inverse[r][j] for r in range(2)) % modulus == int(i == j)
    assert 72+aell == 62 and 62 % 5
    return {
        "curve": [0, 1, 1, -2, 0],
        "point_count_mod71": points,
        "a71": aell,
        "q_bound": bound,
        "oldbasis": ["f(q)", "71*f(q^71)"],
        "tested_oldform_coordinates": [3, 5],
        "trace_gram_matrix": gram,
        "determinant": det,
        "inverse_matrix_modulus": inverse,
        "exact_q_series_trace_and_recovery_identities_checked": 4*(bound+1),
        "fricke_plus_recovery_denominator": 62,
        "fricke_plus_recovery_inverse_modulus": pow(62, -1, modulus),
        "five_adic_digits_lost_by_trace_or_gram_inversion": 0,
    }


def delta_coefficients(bound):
    """Compute Delta=q prod(1-q^n)^24 via its exact logarithmic derivative."""
    sigma = [0]*bound
    for d in range(1, bound):
        for n in range(d, bound, d):
            sigma[n] += d
    product = [1]
    for n in range(1, bound):
        numerator = -24*sum(sigma[j]*product[n-j] for j in range(1, n+1))
        assert numerator % n == 0
        product.append(numerator//n)
    return [0] + product


def weight_twelve_regression():
    """Detect a missing ell^(1-k/2) factor in a different genuine weight."""
    bound = 5
    delta = delta_coefficients(ELL*bound)
    assert delta[:6] == [0, 1, -24, 252, -1472, 4830]
    d1 = delta
    d2 = [ELL**6*delta[n//ELL] if n % ELL == 0 else 0
          for n in range(len(delta))]
    factor = Fraction(1, ELL**5)
    for n in range(bound+1):
        assert d1[n]+factor*d2[ELL*n] == 72*delta[n]
        assert d2[n]+factor*d1[ELL*n] == factor*delta[ELL]*delta[n]
    assert delta[ELL] == 9791485272
    return {
        "form": "Delta=q*product_(n>=1)(1-q^n)^24",
        "weight": 12,
        "q_bound": bound,
        "a71": delta[ELL],
        "normalized_oldbasis": ["Delta(q)", "71^6*Delta(q^71)"],
        "trace_U71_factor": [factor.numerator, factor.denominator],
        "exact_rational_q_series_identities_checked": 2*(bound+1),
    }


def extend_cm_inputs(raw_bound, digits):
    """Extend only the CM jet layer; omit unrelated prime tables and tests.

    This uses the published ideal enumeration and arithmetic helpers.  The
    complete overlap with the older 12-digit artifact is checked separately.
    """
    modulus, logmod = 5**digits, 5**(digits+1)
    log6 = cm.log5_unit(6, digits+1)
    assert log6 % 5 == 0 and log6 % 25 != 0
    inverse_log6_over5 = pow(log6//5, -1, modulus)
    inverse7 = pow(7, -1, logmod)
    logs = {}

    def normalized_log(u):
        u %= logmod
        if u not in logs:
            value = cm.log5_unit(u, digits+1)
            assert value % 5 == 0
            logs[u] = value//5*inverse_log6_over5 % modulus
        return logs[u]

    branches = {}
    for residue in (2, 4):
        root = cm.lift_root(residue, 5, digits+1)
        log_eta_seventh = cm.log5_unit(10+root, digits+1)*inverse7 % logmod
        branches[residue] = [root, log_eta_seventh, [[ZERO]*(raw_bound+1) for _ in range(3)]]
    ideal_count = 0
    for n, k, u, v in cm.ideal_elements(raw_bound):
        ideal_count += 1
        character = cm.zeta(-k, modulus)
        for root, log_eta_seventh, jet in branches.values():
            image = (u+v*root) % logmod
            if image % 5 == 0:
                continue
            value = (cm.log5_unit(image, digits+1)-k*log_eta_seventh) % logmod
            assert value % 5 == 0
            lam = value//5*inverse_log6_over5 % modulus
            jet[0][n] = cm.add(jet[0][n], character, modulus)
            jet[1][n] = cm.add(jet[1][n], cm.scale(character, lam, modulus), modulus)
            jet[2][n] = cm.add(jet[2][n], cm.scale(character, cm.choose2(lam, modulus), modulus), modulus)
    inputs = {}
    for residue, (_, _, g) in branches.items():
        h = [[cm.conjugate(c, modulus) for c in j] for j in g]
        inputs[str(residue)] = {}
        for shifts, name in (((1, 389), "g_depleted_times_V389_h"),
                             ((389, 1), "V389_g_depleted_times_h")):
            inputs[str(residue)][name] = cm.de_rham_input_jets(
                g, h, shifts, modulus, normalized_log)
            both_name = ("both_depleted_g_times_V389_h" if shifts[0] == 1
                         else "both_depleted_V389_g_times_h")
            inputs[str(residue)][both_name] = cm.de_rham_input_jets(
                g, h, shifts, modulus, normalized_log, deplete_h=True)
    return inputs, ideal_count


def trace_vector_series(F, FW, modulus, bound):
    assert ELL*bound < len(F) and ELL*bound < len(FW)
    return [cm.add(F[n], FW[ELL*n], modulus) for n in range(bound+1)]


def direct_weight_five_inputs(raw_bound, residue):
    """Algebraic specialization, independent of p-adic logarithms/jets."""
    modulus = 125
    root = cm.lift_root(residue, 5, 3)
    seventh = cm.seventh_root_unit(10+root, modulus)
    g = [ZERO]*(raw_bound+1)
    for n, k, u, v in cm.ideal_elements(raw_bound):
        image = (u+v*root) % modulus
        if image % 5 == 0:
            continue
        scalar = pow(image, 4, modulus)*pow(seventh, -4*k, modulus) % modulus
        g[n] = cm.add(g[n], cm.scale(cm.zeta(-k), scalar, modulus), modulus)
    h = [cm.conjugate(c, modulus) for c in g]
    output = {}
    for shifts, name in (((1, 389), "g_depleted_times_V389_h"),
                         ((389, 1), "V389_g_depleted_times_h")):
        gg = cm.shift_series(g, shifts[0])
        hh = cm.shift_series(h, shifts[1])
        gg = [cm.scale(c, pow(n, -4, modulus), modulus) if n % 5 else ZERO
              for n, c in enumerate(gg)]
        output[name] = cm.multiply_series(gg, hh, modulus)
        hh = [c if n % 5 else ZERO for n, c in enumerate(hh)]
        both_name = ("both_depleted_g_times_V389_h" if shifts[0] == 1
                     else "both_depleted_V389_g_times_h")
        output[both_name] = cm.multiply_series(gg, hh, modulus)
    return output


def evaluate_weight_five(jet, n, modulus=125):
    W = (6**4-1) % modulus
    return cm.add(cm.add(jet[0][n], cm.scale(jet[1][n], W, modulus), modulus),
                  cm.scale(jet[2][n], W*W, modulus), modulus)


def build(bound=128, digits=5):
    assert bound >= 10 and 3 <= digits <= 12
    encoded_source = gzip.decompress(SOURCE.read_bytes())
    source_hash = hashlib.sha256(encoded_source).hexdigest()
    assert source_hash == SOURCE_SHA256, "pinned source archive differs"
    source = json.loads(encoded_source)
    assert source["schema"] == "E389-Kminus71-CM-weight-jet-v2"
    modulus, raw_bound = 5**digits, ELL*bound
    raw, ideals = extend_cm_inputs(raw_bound, digits)
    overlap = min(raw_bound, source["q_precision"]["largest_coefficient"])
    comparisons = 0
    for residue, cases in raw.items():
        prior = source["branches"][residue]["raw_de_rham_input_cross_oldforms"]
        for name, jet in cases.items():
            for order in range(3):
                for n in range(overlap+1):
                    assert tuple(c % modulus for c in prior[name][order][n]) == jet[order][n], (
                        "raw overlap", residue, name, order, n)
                    comparisons += 1
    traces, first_nonzero = {}, {}
    trace_overlap_checks = 0
    for residue, cases in raw.items():
        traces[residue], first_nonzero[residue] = {}, {}
        for name, jet in cases.items():
            # The theorem supplies F|W=F for each of these three coefficients.
            # This equality is not inferred from their finite q-expansions.
            common = [trace_vector_series(j, j, modulus, bound) for j in jet]
            traces[residue][name] = common
            n0 = next(n for n, c in enumerate(common[0]) if any(c))
            first_nonzero[residue][name] = {"q_exponent": n0,
                                           "jet_coefficients": [j[n0] for j in common]}
            for order in range(3):
                old = source["branches"][residue]["raw_de_rham_input_cross_oldforms"][name][order]
                for n in range(overlap//ELL+1):
                    assert common[order][n] == cm.add(old[n], old[ELL*n], modulus)
                    trace_overlap_checks += 1
    # Validate the fixed-weight specialization without logarithms, including
    # the inverse-Bol multiplier and both tame oldform placements.
    classical_trace_bound = 10
    classical_raw_bound = ELL*classical_trace_bound
    classical_traces = {}
    specialization_checks = 0
    for residue in (2, 4):
        algebraic = direct_weight_five_inputs(classical_raw_bound, residue)
        classical_traces[str(residue)] = {}
        for name, series in algebraic.items():
            jet = raw[str(residue)][name]
            for n in range(classical_raw_bound+1):
                assert evaluate_weight_five(jet, n) == series[n], (
                    "algebraic weight-five input", residue, name, n)
                specialization_checks += 1
            trace = trace_vector_series(series, series, 125, classical_trace_bound)
            for n, c in enumerate(trace):
                assert evaluate_weight_five(traces[str(residue)][name], n) == c
                specialization_checks += 1
            classical_traces[str(residue)][name] = trace
    return {
        "schema": "E389-Kminus71-two-tame-traces-v1",
        "scope": "actual traced overconvergent input jets; no elliptic cohomology projection or finite logarithm",
        "source": {
            "file": "../reflected_pilot/cm-weight-jets.json.gz",
            "uncompressed_sha256": source_hash,
            "arithmetic_module": "../reflected_pilot/cm_weight_jets.py",
            "arithmetic_module_sha256": hashlib.sha256((PILOT / "cm_weight_jets.py").read_bytes()).hexdigest(),
            "regenerated_raw_inputs_sha256": hashlib.sha256(canonical_bytes(raw)).hexdigest(),
            "regenerated_raw_bound": raw_bound,
            "regenerated_raw_ideal_count": ideals,
            "raw_overlap_bound": overlap,
            "raw_overlap_vector_coefficients_checked": comparisons,
            "trace_overlap_vector_coefficients_checked": trace_overlap_checks,
        },
        "coefficient_ring": {"p": 5, "digits": digits, "modulus": modulus,
                             "polynomial": [1]*7,
                             "basis": ["1", "zeta", "zeta^2", "zeta^3", "zeta^4", "zeta^5"]},
        "q_precision": {"largest_coefficient": bound, "remainder": f"O(q^{bound+1})",
                        "raw_coefficients_required_through": raw_bound},
        "weight_coordinate": "W=6^(kappa-1)-1",
        "orders": ["constant", "coefficient of W", "coefficient of W^2 (half of second derivative)"],
        "character_convention": source["character_convention"],
        "inverse_family": "h_W is obtained by zeta -> zeta^-1, with the same CM-type weight exponent",
        "coset_certificates": [coset_certificate(389), coset_certificate(389*25)],
        "trace_theorem": {"normalized_slash": "det(A)^(k/2)*(c*tau+d)^(-k)*F(A*tau)",
                          "general": "Tr1(F)=F+ell^(1-k/2)*Uell(F|W_ell)",
                          "actual_input_Fricke_eigenvalue": 1,
                          "weight_two": "Tr1(Xi)=Tr2(Xi)=Xi+U71(Xi)",
                          "scope": "Fricke/Bol theorem applies to these CM families; arbitrary inputs require their W transform"},
        "elliptic_oldform_regression": elliptic_oldform_regression(source, modulus),
        "weight_twelve_regression": weight_twelve_regression(),
        "common_traces_orders_0_1_2": traces,
        "first_nonzero_traced_coefficient": first_nonzero,
        "algebraic_weight_five_check": {
            "weight": 5, "W_exact": 6**4-1, "modulus": 125,
            "raw_bound": classical_raw_bound, "trace_bound": classical_trace_bound,
            "vector_coefficients_checked": specialization_checks,
            "method": "algebraic seventh roots, fourth powers and n^-4; no logarithms or weight-jet formula",
            "traces": classical_traces,
        },
        "precision_ledger": {
            "tame_trace_digits_lost": 0,
            "E_oldspace_Gram_inversion_digits_lost": 0,
            "separate_integral_Hecke_E_projection_worst_case_digits_lost": 1,
            "q_series_to_proper_de_Rham_cohomology": "not implemented here; separate precision analysis needed",
            "CH_complementary_regulator_comparison": "not established by this computation",
        },
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--bound", type=int, default=128)
    parser.add_argument("--digits", type=int, default=5)
    parser.add_argument("--output", type=Path, default=HERE / "traces.json")
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    started = time.perf_counter()
    result = build(args.bound, args.digits)
    encoded = canonical_bytes(result)
    if args.check:
        assert args.output.read_bytes() == encoded, "saved trace artifact differs"
    else:
        args.output.write_bytes(encoded)
    print(json.dumps({
        "file": str(args.output), "sha256": hashlib.sha256(encoded).hexdigest(),
        "file_bytes": len(encoded), "seconds": round(time.perf_counter()-started, 3),
        "bound": args.bound, "digits": args.digits,
        "raw_bound": result["source"]["regenerated_raw_bound"],
        "raw_overlap_vectors_checked": result["source"]["raw_overlap_vector_coefficients_checked"],
        "classical_specialization_vectors_checked": result["algebraic_weight_five_check"]["vector_coefficients_checked"],
        "scope": result["scope"],
    }, indent=2))


if __name__ == "__main__":
    main()
