#!/usr/bin/env python3
"""Recompute the BSD localization package's exact arithmetic certificates."""

import argparse
from concurrent.futures import ThreadPoolExecutor
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import time


ROOT = Path(__file__).resolve().parent
JOBS = [
    ("eligibility", "eligibility/arithmetic/check_eligibility.py",
     ["--check", "eligibility/arithmetic/eligibility.json"], None),
    ("twist_interval", "eligibility/arithmetic/check_twist_lvalue.py",
     ["--check", "eligibility/arithmetic/twist-lvalue.json"], None),
    ("localization_and_logic", "logic/verify_logic.py", [], "logic/result.json"),
    ("cyclotomic_fixtures", "logic/c7_period.py", [], "logic/c7-fixtures.json"),
    ("ring_class_projection", "projection/ring_class_projection.py", [], "projection/result.json"),
    ("p5_refinements", "p5/check_refinements.py", ["--check", "p5/result.json"], None),
    ("local_logarithms_30_digits", "local_model/formal_log.py",
     ["--check", "local_model/result.json"], None),
    ("exterior_descent", "rationality/check_exterior_descent.py", [], "rationality/result.json"),
    ("finite_lifts_and_reflection", "derived_global/bockstein_lifts.py", [],
     "derived_global/bockstein-results.json"),
    ("finite_coordinate_algebra", "finite_log_reciprocity/check_finite_coordinate.py", [],
     "finite_log_reciprocity/finite-coordinate-results.json"),
    ("crystalline_frobenius_and_annihilator", "local_crystalline/frobenius.py",
     ["--check", "local_crystalline/result.json"], None),
    ("published_frobenius_calibration", "local_crystalline/calibration.py", [],
     "local_crystalline/calibration-result.json"),
    ("cyclotomic_strict_height", "local_crystalline/height_leading.py",
     ["--check", "local_crystalline/height-result.json"], None),
    ("ambient_bockstein_algebra", "ambient_arithmetic/check_ambient_jet.py",
     ["--check", "ambient_arithmetic/result.json"], None),
    ("cm_weight_second_jets", "reflected_pilot/cm_weight_jets.py", ["--check"], None),
    ("actual_tame_trace_jets", "tame_trace_compute/compute_traces.py", ["--check"], None),
    ("tame_trace_and_interpolation_audit", "tame_trace_audit/check_trace_audit.py",
     ["--check", "tame_trace_audit/result.json"], None),
    ("exact_elliptic_hecke_projector", "elliptic_projection/check_projector.py", ["--check"], None),
    ("analytic_target_algebra", "analytic_target_audit/check_target.py",
     ["--check", "analytic_target_audit/result.json"], None),
    ("weight_reflection_and_cubic_descent", "weight_reflection/check_reflection.py", ["--check"], None),
    ("proper_cohomology_residue_filter", "residue_filter/check_filter.py", ["--check"], None),
    ("two_slope_calibration_and_geometry_dimensions", "de_rham_strategy/check_strategy.py", ["--check"], None),
    ("selected_trace_2048_12", "trace_scaling/selected_trace.py",
     ["--bound", "2048", "--digits", "12", "--output", "trace_scaling/traces-2048-12.json.gz", "--check"], None),
    ("cubic_trace_6825_12", "trace_scaling/cubic_trace.py", ["--check"], None),
    ("independent_cubic_trace_overlap", "trace_scaling/check_cubic_overlap.py", ["--check"], None),
    ("leading_coordinate_and_projective_target", "leading_comparison/check_leading.py", ["--check"], None),
    ("conditional_cm_tail_arithmetic", "cm_tail_bound/check_bound.py", ["--check"], None),
    ("cubic_undepleted_euler_transfer", "cm_product_transfer/check_transfer.py", ["--check"], None),
    ("cubic_undepleted_product_6825_12", "cm_product_transfer/product_trace.py", ["--check"], None),
    ("finite_two_slope_projection_certificates", "projection_backend/check_projection.py", ["--check"], None),
    ("certified_katz_matrix_fit", "projection_backend/check_katz_matrix_fit.py",
     ["--check", "projection_backend/matrix-fit-regression.json"], None),
    ("fixed_weight_full_frobenius_algebra", "fixed_weight_syntomic/check_identity.py", [],
     "fixed_weight_syntomic/check_result.json"),
    ("actual_finite_cubic_ratio", "projection_backend/check_cubic_ratio.py", ["--check"], None),
    ("perrin_riou_syntomic_operator_comparison", "pr_syntomic_comparison/check_comparison.py", [],
     "pr_syntomic_comparison/check_result.json"),
    ("infinite_katz_bound_arithmetic", "projection_backend/check_infinite_bounds.py", ["--check"], None),
    ("pilot_residual_and_big_image_inputs", "galois_image/check_image.py", ["--check"], None),
    ("full_normalized_local_algebra", "normalized_local_comparison/check_linear_algebra.py", [],
     "normalized_local_comparison/check_result.json"),
    ("projective_nonvanishing_and_corrected_ratio", "comparison_logic_audit/check_logic.py", ["--check"], None),
    ("second_curve_eligibility", "second_pilot/screen.py", ["--check"], None),
    ("second_curve_twist_interval", "second_pilot/check_twist_lvalue.py",
     ["--check", "second_pilot/twist-lvalue.json"], None),
    ("second_curve_rigorous_CM_theta", "second_theta/verify_theta.py",
     ["--check", "second_theta/verification.json"], None),
    ("second_curve_corrupt_witness_rejection", "second_theta/test_rejection.py",
     ["--check", "second_theta/rejection.json"], None),
    ("second_curve_independent_toric_consequences", "second_pilot/check_toric_consequences.py",
     ["--check"], None),
    ("general_projective_certificate_example", "general_criterion/certificate_checker.py",
     ["general_criterion/certificate-example.json"], "general_criterion/certificate-example-result.json"),
    ("general_projective_certificate_E389", "general_criterion/certificate_checker.py",
     ["general_criterion/pilot-line-certificate.json"], "general_criterion/pilot-line-result.json"),
    ("general_projective_certificate_precision_and_corruption", "general_criterion/test_certificate.py",
     [], None),
]


def run_job(job):
    name, script, arguments, expected_path = job
    command = [sys.executable, script, *arguments]
    start = time.perf_counter()
    process = subprocess.run(command, cwd=ROOT, text=True, capture_output=True)
    elapsed = time.perf_counter() - start
    if process.returncode:
        raise RuntimeError(f"{name} failed:\n{process.stdout}\n{process.stderr}")
    if expected_path:
        expected = json.loads((ROOT / expected_path).read_text())
        actual = json.loads(process.stdout)
        if actual != expected:
            raise RuntimeError(f"{name}: fresh output differs from {expected_path}")
    return {"check": name, "command": ["python", script, *arguments],
            "exit_code": process.returncode,
            "matches_saved_certificate": expected_path is not None or "--check" in arguments,
            "elapsed_seconds": round(elapsed, 6)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--receipt", type=Path)
    args = parser.parse_args()
    with ThreadPoolExecutor(max_workers=5) as pool:
        checks = list(pool.map(run_job, JOBS))
    hashes = {}
    for path in sorted(ROOT.rglob("*")):
        if path.is_file() and path.suffix in (".py", ".md", ".json", ".gz", ".txt"):
            if path.name == "verification.json":
                continue
            hashes[str(path.relative_to(ROOT))] = hashlib.sha256(path.read_bytes()).hexdigest()
    receipt = {"status": "PASS", "python": sys.version.split()[0], "checks": checks,
               "sha256": hashes,
               "scope": "The compact suite verifies the retained E389 exact arithmetic, CM jets and traces, crystalline and regulator algebra, finite Katz/projection witnesses, bound arithmetic, residual image, and corrected projective ratio. New checks reconstruct E433 class polynomials with rigorous FLINT/Arb balls, verify its full finite CM/theta witness, reject eleven corrupt witnesses, recompute its exact eligibility and twist interval, and independently check the toric moments/norm. A generic projective certificate checker is exercised on a generic fixture and the E389 data, with precision and corruption tests. Source-based global division and Selmer conditions, the BSV normalized specialization and explicitly proved finite/geometric edge extensions, syntomic/etale and full local comparisons, and the infinite Katz interpretation are written mathematical arguments, not verified by this runner. The former raw DR22 moment argument is withdrawn and is not used. Large Sage geometry has separate replay receipts. This suite adds no Lean verification and does not prove a Selmer-to-point comparison or a second-curve localization theorem."}
    if args.receipt:
        args.receipt.write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n")
    print(json.dumps(receipt, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
