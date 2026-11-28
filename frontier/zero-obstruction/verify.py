#!/usr/bin/env python3
"""Reproduce the frontier milestone without rebuilding class-group searches."""

import hashlib
import json
import re
import shutil
import subprocess
import sys
import time
from datetime import datetime, timezone
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
PROJECT = ROOT / "Exp7Lean"
HERE = Path(__file__).resolve().parent
OUT = HERE / "verification"
MODULES = [
    "Pointwise", "DampedFormula", "ZeroMass", "ZeroLoss", "Obstruction", "Rows",
    "ComplexTransform", "SmoothedKernel", "SmoothedCorrelation", "SmoothedDecay",
    "SmoothedSum", "All", "Checks"
]
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def without_timings(value):
    if isinstance(value, dict):
        return {k: without_timings(v) for k, v in value.items()
                if k not in {"elapsed_seconds", "total_elapsed_seconds"}}
    if isinstance(value, list):
        return [without_timings(v) for v in value]
    return value


def main():
    lake = shutil.which("lake") or str(Path.home() / ".elan/bin/lake")
    OUT.mkdir(exist_ok=True)
    paths = [PROJECT / "Exp7Lean/Frontier" / f"{m}.lean" for m in MODULES]
    paths += [PROJECT / "Exp7Lean.lean", PROJECT / "lean-toolchain",
              PROJECT / "lake-manifest.json", Path(__file__),
              ROOT / "frontier/zero-integer/verify.py",
              ROOT / "frontier/zero-integer/test_verify.py",
              ROOT / "frontier/zero-integer/result.json",
              ROOT / "frontier/zero-audit/AUDIT.md"]
    source_hashes = {str(p.relative_to(ROOT)): digest(p) for p in paths}
    receipt = {
        "status": "running",
        "started_utc": datetime.now(timezone.utc).isoformat(),
        "head_before_verification": subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip(),
        "toolchain": (PROJECT / "lean-toolchain").read_text().strip(),
        "historical_frontier_commit": "462b231fb1fdd3133de798e2d89501434a86e1a3",
        "scope": "Focused build and new-module kernel replay against compiled imports; "
                 "no fresh class-group search rebuild; no full height-60 formalization",
        "source_sha256": source_hashes,
        "commands": [],
    }

    def run(label, command, cwd):
        print(label, flush=True)
        start = time.monotonic()
        log = OUT / f"{label}.log"
        with log.open("w") as stream:
            result = subprocess.run(command, cwd=cwd, stdout=stream, stderr=subprocess.STDOUT)
        receipt["commands"].append({
            "label": label, "command": command, "cwd": str(cwd.relative_to(ROOT)) or ".",
            "exit_code": result.returncode, "seconds": round(time.monotonic() - start, 3),
            "log": str(log.relative_to(HERE)),
        })
        if result.returncode:
            raise RuntimeError(f"{label} failed; see {log}")
        return log.read_text()

    try:
        run("build", [lake, "build", "Exp7Lean.Frontier.Checks"], PROJECT)
        run("root-import", [lake, "env", "lean", "Exp7Lean.lean"], PROJECT)
        axioms = run("axioms", [lake, "env", "lean", "Exp7Lean/Frontier/Checks.lean"], PROJECT)
        expected = set(re.findall(r"^#print axioms (\w+)$",
                                  (PROJECT / "Exp7Lean/Frontier/Checks.lean").read_text(), re.M))
        found = {}
        for name, entries in re.findall(
            r"'Exp7\.Frontier\.(\w+)' (?:does not depend on any axioms|depends on axioms:\s*\[([^]]*)\])",
            axioms,
        ):
            dependencies = {s.strip() for s in entries.split(",") if s.strip()}
            if not dependencies <= ALLOWED_AXIOMS:
                raise RuntimeError(f"Unexpected axiom dependencies for {name}: {dependencies}")
            found[name] = sorted(dependencies)
        if set(found) != expected:
            raise RuntimeError(f"Axiom inventory mismatch: expected {expected}, found {set(found)}")
        declarations = set()
        for path in paths[:len(MODULES)]:
            declarations.update(re.findall(r"^theorem (\w+)", path.read_text(), re.M))
        if declarations != expected:
            raise RuntimeError("Not every declared frontier theorem has an axiom check")
        receipt["theorem_axioms"] = found
        for module in MODULES:
            run(f"kernel-{module}", [lake, "env", "leanchecker", "-v",
                                     f"Exp7Lean.Frontier.{module}"], PROJECT)
        run("integer-tests", [sys.executable, "frontier/zero-integer/test_verify.py"], ROOT)
        numeric_text = run("integer-replay", [sys.executable, "frontier/zero-integer/verify.py"], ROOT)
        numeric = json.loads(numeric_text)
        prior = json.loads((ROOT / "frontier/zero-integer/result.json").read_text())
        if without_timings(numeric) != without_timings(prior):
            raise RuntimeError("Integer replay differs from the historical result")
        (HERE / "integer-replay.json").write_text(numeric_text)
        receipt["integer_replay_matches_historical_result_except_timings"] = True
        receipt["height_60_residual_enclosures_scale_1000000"] = {
            str(row["X"]): row["profiles"][-1]["residual"] for row in numeric["rows"]
        }
        if {str(p.relative_to(ROOT)): digest(p) for p in paths} != source_hashes:
            raise RuntimeError("A source file changed during verification")
        receipt["module_olean_sha256"] = {
            m: digest(PROJECT / ".lake/build/lib/lean/Exp7Lean/Frontier" / f"{m}.olean")
            for m in MODULES
        }
        receipt["status"] = "passed"
    except Exception as error:
        receipt["status"] = "failed"
        receipt["error"] = str(error)
        raise
    finally:
        receipt["finished_utc"] = datetime.now(timezone.utc).isoformat()
        (OUT / "receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print(f"Passed: {len(found)} theorem dependency checks, "
          f"{len(MODULES)} module replays, and four integer rows.")


if __name__ == "__main__":
    main()
