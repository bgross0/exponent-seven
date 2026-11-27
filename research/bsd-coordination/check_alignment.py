#!/usr/bin/env python3
"""Align the certified CM orbit with the unchanged C7 period checker.

Only the adapter's finite consistency checks and cyclotomic algebra run here.
CM reduction, Jacquet--Langlands, and Gross's theorem remain cited mathematical
dependencies; the imported package's complete verification is not replayed.
"""

import argparse
from fractions import Fraction
import hashlib
import importlib.util
import json
from math import gcd
from pathlib import Path
import sys


ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
THETA = ROOT / "research/bsd-theta"
CHECKER = ROOT / "research/bsd-localization/logic/c7_period.py"
SUPER = THETA / "data/supersingular-389.json"
RECEIPT = THETA / "evidence/certificate-verification.json"
PINNED_SHA256 = {
    "research/bsd-localization/logic/c7_period.py":
        "64cc142763b4922abf6d613046efd58633ca5debf1628d0d6072ec7adc09f24f",
    "research/bsd-theta/data/supersingular-389.json":
        "cb60ce7574e6a4a0e8cc9d4f108fec26547131ff7c38c2c682d2f1f1316f1998",
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def integers(values, length):
    return (isinstance(values, list) and len(values) == length
            and all(type(value) is int for value in values))


def derive_cycle(indices, adjacency):
    """Return local indices in a deterministic orientation of one seven-cycle."""
    require(integers(indices, 7) and len(set(indices)) == 7,
            "CM indices must be seven distinct integers")
    require(isinstance(adjacency, list) and len(adjacency) == 7
            and all(integers(row, 7) for row in adjacency),
            "CM adjacency must be a 7 by 7 integer matrix")
    require(all(adjacency[i][i] == 0 and sum(adjacency[i]) == 2
                and all(value in (0, 1) for value in adjacency[i])
                for i in range(7)), "CM graph must be simple with degree two")
    require(all(adjacency[i][j] == adjacency[j][i]
                for i in range(7) for j in range(7)), "CM graph is asymmetric")
    start = min(range(7), key=lambda i: indices[i])
    cycle, previous, current = [], None, start
    while True:
        require(current not in cycle, "CM walk repeated a noninitial vertex")
        cycle.append(current)
        candidates = [j for j in range(7) if adjacency[current][j] and j != previous]
        require(len(candidates) == (2 if previous is None else 1),
                "CM walk has ambiguous continuation")
        following = min(candidates, key=lambda j: indices[j])
        if following == start:
            break
        previous, current = current, following
    require(len(cycle) == 7, "CM graph has disconnected cycles")
    return cycle


def prepare_cm_data(data):
    """Check the stored matrix/function interface; do not redo CM construction."""
    require(data["field"] == {"p": 389, "basis": "1,u", "u_squared": 2},
            "Unexpected finite-field convention")
    vertices = data["supersingular_j"]
    require(isinstance(vertices, list) and len(vertices) == 33
            and all(integers(pair, 2) and all(0 <= x < 389 for x in pair)
                    for pair in vertices), "Invalid supersingular coordinates")
    require(len({tuple(pair) for pair in vertices}) == 33, "Duplicate j coordinates")
    matrix = data["brandt_T2_function_matrix"]
    require(isinstance(matrix, list) and len(matrix) == 33
            and all(integers(row, 33) and min(row) >= 0 and sum(row) == 3
                    for row in matrix), "Invalid outgoing Brandt T2 matrix")
    require(data["T2_eigenvalue"] == -2 and data["eigenspace_dimension"] == 1,
            "Unexpected recorded eigenpacket")
    eigenvectors = data["primitive_eigenvectors"]
    require(isinstance(eigenvectors, list) and len(eigenvectors) == 1
            and integers(eigenvectors[0], 33), "Expected one integral eigenvector")
    phi = eigenvectors[0]
    require(gcd(*phi) == 1, "Eigenfunction is not primitive")
    require(all(sum(matrix[i][j] * phi[j] for j in range(33)) == -2 * phi[i]
                for i in range(33)), "Eigenfunction does not satisfy T2 phi = -2 phi")
    weights = [3 if pair == [0, 0] else 2 if pair == [1728 % 389, 0] else 1
               for pair in vertices]
    require(all(weights[j] * matrix[i][j] == weights[i] * matrix[j][i]
                for i in range(33) for j in range(33)), "Weighted adjoint convention fails")
    require(sum(Fraction(phi[i], weights[i]) for i in range(33)) == 0,
            "Eigenfunction fails the weighted cuspidality check")
    indices = data["CM_indices"]
    require(integers(indices, 7) and len(set(indices)) == 7
            and all(0 <= i < 33 for i in indices), "Invalid CM index set")
    adjacency = [[matrix[i][j] for j in indices] for i in indices]
    require(adjacency == data["CM_induced_T2"], "Stored CM adjacency/order mismatch")
    require(data["CM_values"] == [[phi[i] for i in indices]],
            "Stored CM values/order mismatch")
    local_cycle = derive_cycle(indices, adjacency)
    cycle = [indices[i] for i in local_cycle]
    require(all(weights[i] == 1 for i in cycle), "Unexpected CM stabilizer weight")
    return {
        "source_CM_indices": indices,
        "source_values_in_vertex_order": [phi[i] for i in indices],
        "local_cycle": local_cycle,
        "supersingular_indices_in_cycle_order": cycle,
        "j_coordinates_in_cycle_order": [vertices[i] for i in cycle],
        "values_in_cycle_order": [phi[i] for i in cycle],
        "CM_stabilizer_weights": [weights[i] for i in cycle],
    }


def load_checker():
    spec = importlib.util.spec_from_file_location("bsd_alignment_c7_period", CHECKER)
    require(spec is not None and spec.loader is not None, "Cannot load C7 checker")
    module = importlib.util.module_from_spec(spec)
    old_flag = sys.dont_write_bytecode
    try:
        sys.dont_write_bytecode = True
        spec.loader.exec_module(module)
    finally:
        sys.dont_write_bytecode = old_flag
    return module


def build_report():
    for name, expected in PINNED_SHA256.items():
        require(sha256(ROOT / name) == expected, "Pinned source changed: " + name)
    data = json.loads(SUPER.read_text())
    receipt = json.loads(RECEIPT.read_text())
    require(receipt["result"] == "PASS", "Imported verification receipt did not pass")
    require(receipt["input_sha256"]["data/supersingular-389.json"] == sha256(SUPER),
            "CM payload is not the one named by the verification receipt")
    require(receipt["supersingular"]["rational_eigenline_dimension"] == 1,
            "Verification receipt has a different eigenline dimension")
    orbit = prepare_cm_data(data)
    checker = load_checker()
    analysis = checker.analyze(orbit["values_in_cycle_order"])
    require(analysis["cyclotomic_norm"] == 49, "Expected cyclic CM period norm 49")
    require(analysis["all_nontrivial_periods_nonzero_over_Q_zeta7"], "Zero C7 period")
    require(analysis["geometric_validation_performed"] is False
            and analysis["L_value_nonvanishing_certified"] is False,
            "Unexpected change in the checker proof boundary")
    values = orbit["values_in_cycle_order"]
    reversed_values = [values[0], *reversed(values[1:])]
    reverse_norm = checker.analyze(reversed_values)["cyclotomic_norm"]
    shifted_norm = checker.analyze(values[1:] + values[:1])["cyclotomic_norm"]
    require(reverse_norm == shifted_norm == 49, "Orientation/origin changed the norm")
    sources = [Path(__file__).resolve(), CHECKER, SUPER, RECEIPT,
               THETA / "data/arithmetic-audit.json", THETA / "research/arithmetic-audit.md",
               ROOT / "research/bsd-localization/logic/C7_AUXILIARY_PERIOD.md",
               ROOT / "research/bsd-localization/projection/README.md"]
    return {
        "schema_version": 1,
        "result": "BSD_ALIGNMENT_C7_PASS",
        "external_base_commit": "12c58ddf46ebd89141d4392b519ca7ae533e67ea",
        "source_sha256": {str(path.relative_to(ROOT)): sha256(path) for path in sources},
        "curve": {"label": "389.a1", "ainvs": [0, 1, 1, -2, 0], "conductor": 389},
        "quadratic_field": {"discriminant": -71, "omega_polynomial": "x^2-x+18"},
        "finite_field": data["field"],
        "adapter_checks": {
            "pinned_checker_and_CM_payload": True,
            "payload_hash_matches_imported_PASS_receipt": True,
            "matrix_function_and_weight_consistency": True,
            "CM_adjacency_rederived_from_full_matrix": True,
            "one_simple_seven_cycle": True,
            "cyclotomic_norm": 49,
            "reverse_orientation_norm": reverse_norm,
            "one_step_translation_norm": shifted_norm,
            "full_source_verification_replayed": False,
            "mathematical_Gross_theorem_proved_by_adapter": False,
        },
        "class_conventions": {
            "generator": "a=(2,omega), represented by (2,-1,9)",
            "prime29_class": "c=(29,omega-13)=a^4; a=c^2",
            "class_mapping_reference": "research/bsd-localization/projection/README.md",
            "class_mapping_recomputed_by_adapter": False,
            "basepoint_choice": "smallest global CM vertex index; no identity class is asserted",
            "orientation_choice": "smaller-index first neighbor in the undirected norm-two graph",
            "orbit_interpretation": "a^i or a^(-i) acting on an arbitrary base Gross point",
            "exact_orientation_resolved": False,
            "prime29_generator_values_same_orientation": [values[4*i % 7] for i in range(7)],
        },
        "CM_orbit": orbit,
        "cyclotomic_analysis": analysis,
        "mathematical_bridge": {
            "status": "Cited mathematical interpretation of imported geometric evidence; not a new program proof",
            "CM_model": "The seven roots of H_-71 reduced at 389 give the complete conductor-one CM orbit",
            "Brandt_model": "Supersingular Brandt module for the definite algebra ramified at 389 and infinity",
            "eigenline": "The recorded one-dimensional T2=-2 eigenline is identified with E by Jacquet-Langlands",
            "normalization": "One common primitive integral eigenfunction; no independent entry rescalings",
            "weighted_pairing": "If <e_i,e_j>=w_i delta_ij, take g=sum_i(phi_i/w_i)e_i; then <e_j,g>=phi_j",
            "period_formula": "Gross's theorem identifies nonzero projection onto this line with nonzero class-character central L-value",
            "character_convention": "Gross's inverse character exchanges j with -j; all six nontrivial periods are covered",
            "references": [
                "research/bsd-theta/research/arithmetic-audit.md, sections 3 and 5",
                "research/bsd-localization/logic/C7_AUXILIARY_PERIOD.md",
                "https://wstein.org/papers/bib/Gross-Heights_and_the_Special_Values_of_L-series.pdf, section 11, Theorem 11.5",
                "https://sites.math.rutgers.edu/~mpy4/ReductionFinalVersion.pdf, section 2, equations (2.1)-(2.2)",
            ],
        },
        "prime_scope": {
            "conductor_one_auxiliary_period": "Independent of the Iwasawa prime; usable for the p=29 auxiliary hypothesis",
            "imported_theta_certificate_prime": 5,
            "theta_coefficient_computed_by_adapter": False,
            "p29_theta_coefficient_certified_here": False,
        },
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--check", type=Path, help="Compare the deterministic report with saved JSON")
    mode.add_argument("--write", nargs="?", type=Path, const=HERE / "cm-periods.json",
                      help="Write the report, defaulting to this directory's cm-periods.json")
    args = parser.parse_args()
    try:
        report = build_report()
        rendered = json.dumps(report, indent=2, sort_keys=True) + "\n"
        if args.check:
            require(json.loads(args.check.read_text()) == report, "Saved report differs from recomputation")
        if args.write:
            args.write.write_text(rendered)
        print(rendered, end="")
    except (OSError, ValueError, KeyError, TypeError, AssertionError) as error:
        parser.exit(1, "Alignment check failed: " + str(error) + "\n")


if __name__ == "__main__":
    main()
