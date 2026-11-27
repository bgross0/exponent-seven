#!/usr/bin/env python3
"""Replay arithmetic, adversarial checks, and optionally the Lean kernel check.

Dependencies are deliberately explicit. This does not install software, rent
compute, or submit remote jobs. See README.md for the pinned environment.
"""

import argparse
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]


def run(command, log_name):
    result = subprocess.run(command, cwd=ROOT, text=True, capture_output=True)
    target = ROOT / "evidence" / log_name
    target.parent.mkdir(exist_ok=True)
    target.write_text(result.stdout + result.stderr)
    if result.returncode:
        raise RuntimeError(f"Replay failed; inspect {target}\n{result.stderr}")
    return {"command": command, "exit_code": result.returncode, "log": str(target.relative_to(ROOT))}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--gp", default=None, help="PARI/GP executable for independent arithmetic replay")
    parser.add_argument("--formal", action="store_true", help="Requires pinned Lean/lake on PATH and Mathlib fetched")
    args = parser.parse_args()
    command = [sys.executable, "verify_certificate.py"]
    if args.gp:
        command += ["--gp", args.gp]
    results = [run(command, "certificate-replay.log"),
               run([sys.executable, "-m", "unittest", "discover", "-s", "tests", "-v"], "rejection-tests.log")]
    if args.gp:
        result = run([args.gp, "-fq", "-s", "256M", "scripts/cm_independent_audit.gp"], "cm-independent-replay.log")
        text = (ROOT / result["log"]).read_text()
        if "***" in text or "CM_INDEPENDENT_AUDIT_PASS" not in text:
            raise RuntimeError("Independent GP audit did not return its verified pass marker")
        results.append(result)
    if args.formal:
        results.append(run([sys.executable, "formal/verify.py"], "formal-replay-summary.log"))
    (ROOT / "evidence/reproduction.json").write_text(json.dumps({"result": "PASS", "checks": results}, indent=2) + "\n")
    print(json.dumps({"result": "PASS", "checks_completed": len(results), "formal_replayed": args.formal,
                      "independent_PARI_replayed": bool(args.gp)}))


if __name__ == "__main__":
    main()
