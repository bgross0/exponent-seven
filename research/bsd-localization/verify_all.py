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
            "exit_code": process.returncode, "matches_saved_certificate": True,
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
               "scope": "Exact arithmetic, CM periods, local logs and crystalline Frobenius, cyclotomic height, CM second jets, tame traces, elliptic Hecke projection, reflection/cubic identities, both q6825 cubic inputs at twelve digits, two-slope calibration, residue/Euler filters, tail-bound arithmetic, leading-coordinate/projective identities, finite inverse-minor projection certificates, certified finite Katz matrix fitting, the actual cubic ratio, fixed-weight Frobenius and Perrin--Riou adjoint identities, and algebraic lift/descent/Bockstein fixtures. This runner also checks the integer inequalities and precision table in the infinite Katz bridge. The source-based geometric provenance, analytic tail theorem, Banach and cohomological comparison, and rational projected specialization are written mathematical arguments, not consequences of this finite runner. Actual large Sage geometry and CM projection witnesses have separate replay receipts. The conditional arithmetic comparison still requires a consistently identified global class and normalized full local regulator. No new Lean verification, upstream CM reconstruction, arithmetic global Bockstein, or nonzero reflected logarithm is certified by this runner."}
    if args.receipt:
        args.receipt.write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n")
    print(json.dumps(receipt, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
