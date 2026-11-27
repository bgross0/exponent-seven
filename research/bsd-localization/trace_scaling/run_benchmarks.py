#!/usr/bin/env python3
"""Reproduce the bounded trace-scaling benchmarks and independent comparisons.

Every timed case runs in a fresh process.  Peak RSS is measured in KiB on
Linux.  Timings include its verification, serialization, and gzip encoding.
The final q2048, twelve-digit trace artifact is retained; smaller temporary
artifacts are removed only after all cross-checks succeed.
"""

from __future__ import annotations

import gzip
import hashlib
import json
from pathlib import Path
import subprocess
import sys


HERE = Path(__file__).resolve().parent
BASE = HERE.parent
SCRIPT = HERE / "selected_trace.py"
SOURCE_HASH = "80b2b0f5ba32d6a3d45ebb828c21e5bf043226cfd4290b72dd9d81ed8ae830ba"


def compare_series(a, b, bound, modulus):
    count = 0
    for embedding, branch in a.items():
        for name, jet in branch.items():
            other = b[embedding][name]
            for order in range(3):
                for n in range(bound+1):
                    assert tuple(x % modulus for x in jet[order][n]) == tuple(
                        x % modulus for x in other[order][n]), (embedding, name, order, n)
                    count += 1
    return count


def main():
    baseline_code = '''
import contextlib,hashlib,io,json,pathlib,resource,runpy,sys,time
sys.dont_write_bytecode=True
p=pathlib.Path(sys.argv[1])
s=time.perf_counter()
ns=runpy.run_path(str(p))
j=ns["build"](128,5)
b=ns["canonical_bytes"](j)
assert b==(p.parent/"traces.json").read_bytes()
print(json.dumps({"status":"all checks passed","bound":128,"digits":5,
 "wall_seconds":time.perf_counter()-s,
 "process_peak_RSS_KiB":resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
 "artifact_sha256":hashlib.sha256(b).hexdigest(),
 "scope":"original full-product workflow, including its original verification"}))
'''
    baseline = subprocess.run(
        [sys.executable, "-c", baseline_code, str(BASE / "tame_trace_compute" / "compute_traces.py")],
        check=True, capture_output=True, text=True, timeout=60)
    baseline = json.loads(baseline.stdout)
    (HERE / "benchmark-baseline-128-5.json").write_text(json.dumps(baseline, indent=2, sort_keys=True)+"\n")
    print(json.dumps({"baseline": baseline}), flush=True)

    jobs = [(128, 5, 1), (512, 5, 1), (2048, 5, 1),
            (512, 12, 1), (2048, 12, 1), (2048, 5, 2)]
    results = []
    data = {}
    temporaries = []
    for bound, digits, workers in jobs:
        suffix = f"{bound}-{digits}" + (f"-workers{workers}" if workers > 1 else "")
        receipt_path = HERE / f"benchmark-{suffix}.json"
        keep = (bound, digits, workers) == (2048, 12, 1)
        artifact = HERE / ("traces-2048-12.json.gz" if keep else f"temporary-{suffix}.json.gz")
        command = [sys.executable, str(SCRIPT), "--bound", str(bound), "--digits", str(digits),
                   "--workers", str(workers), "--receipt", str(receipt_path), "--output", str(artifact)]
        proc = subprocess.run(command, check=True, capture_output=True, text=True, timeout=120)
        result = json.loads(proc.stdout)
        results.append(result)
        payload = artifact.read_bytes()
        assert hashlib.sha256(payload).hexdigest() == result["gzip_sha256"]
        uncompressed = gzip.decompress(payload)
        assert hashlib.sha256(uncompressed).hexdigest() == result["uncompressed_sha256"]
        data[(bound, digits, workers)] = json.loads(uncompressed)
        if not keep:
            temporaries.append(artifact)
        print(json.dumps({"bound": bound, "digits": digits, "workers": workers,
                          "seconds": result["wall_seconds"],
                          "parent_peak_RSS_KiB": result["parent_process_peak_RSS_KiB"]}), flush=True)

    high = data[(2048, 12, 1)]["common_traces_orders_0_1_2"]
    low = data[(2048, 5, 1)]["common_traces_orders_0_1_2"]
    verification = {
        "precision_12_to_5_vector_coefficients": compare_series(high, low, 2048, 3125),
        "bound_2048_to_512_at_12_digits_vector_coefficients": compare_series(
            high, data[(512, 12, 1)]["common_traces_orders_0_1_2"], 512, 5**12),
        "bound_2048_to_512_at_5_digits_vector_coefficients": compare_series(
            low, data[(512, 5, 1)]["common_traces_orders_0_1_2"], 512, 3125),
        "bound_2048_to_128_at_5_digits_vector_coefficients": compare_series(
            low, data[(128, 5, 1)]["common_traces_orders_0_1_2"], 128, 3125),
    }
    assert data[(2048, 5, 1)] == data[(2048, 5, 2)]
    verification["two_workers_match_single_worker_entire_artifact"] = True

    # The old archive supplies an independent twelve-digit reference through
    # q57.  Load it after all timed runs, so its larger JSON representation
    # does not contaminate the reported generator memory measurements.
    old_bytes = gzip.decompress((BASE / "reflected_pilot" / "cm-weight-jets.json.gz").read_bytes())
    assert hashlib.sha256(old_bytes).hexdigest() == SOURCE_HASH
    old = json.loads(old_bytes)
    prior = {}
    for embedding, branch in old["branches"].items():
        prior[embedding] = {}
        for name, jet in branch["raw_de_rham_input_cross_oldforms"].items():
            prior[embedding][name] = [
                [[(order[n][r]+order[71*n][r]) % (5**12) for r in range(6)]
                 for n in range(58)] for order in jet]
    verification["pinned_12_digit_archive_vector_coefficients"] = compare_series(high, prior, 57, 5**12)
    verification["pinned_12_digit_archive_uncompressed_sha256"] = SOURCE_HASH

    summary = {
        "status": "all checks passed",
        "baseline": baseline,
        "runs": [{
            "bound": r["bound"], "digits": r["digits"], "workers": r["workers"],
            "wall_seconds": r["wall_seconds"],
            "parent_process_peak_RSS_KiB": r["parent_process_peak_RSS_KiB"],
            "worker_process_peak_RSS_KiB": {
                k: v["process_peak_RSS_KiB"] for k, v in r["performance_by_embedding"].items()},
            "uncompressed_sha256": r["uncompressed_sha256"], "gzip_sha256": r["gzip_sha256"],
            "gzip_bytes": r["gzip_bytes"],
        } for r in results],
        "cross_checks": verification,
        "retained_artifact": "traces-2048-12.json.gz",
        "scope": "scalable arithmetic input generation; no claim of analytic or global nonvanishing",
    }
    (HERE / "result.json").write_text(json.dumps(summary, indent=2, sort_keys=True)+"\n")
    for path in temporaries:
        path.unlink()
    # Remove the exploratory lower-precision artifact only after its contents
    # have been reproduced and checked against the retained higher precision.
    exploratory = HERE / "traces-2048-5.json.gz"
    if exploratory.exists():
        exploratory.unlink()
    print(json.dumps({"cross_checks": verification, "status": "all checks passed"}), flush=True)


if __name__ == "__main__":
    main()
