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
               "scope": "Exact arithmetic, p5 CM-period refinements, 30-digit local logs, local crystalline Frobenius, leading cyclotomic heights, CM second weight jets, actual tame-trace jets, exact elliptic Hecke projection, low-weight interpolation, and algebraic lift/reflection/descent/finite-coordinate/Bockstein fixtures. Mathematical arguments and conditional comparisons are in the notes. No new Lean verification, upstream CM reconstruction, arithmetic global Bockstein, projected vector L-value, or nonzero reflected logarithm is certified by this runner."}
    if args.receipt:
        args.receipt.write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n")
    print(json.dumps(receipt, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
