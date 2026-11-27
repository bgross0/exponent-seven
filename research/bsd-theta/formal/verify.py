#!/usr/bin/env python3
"""Build the pinned formal project and record its declarations and kernel replay."""

from __future__ import annotations

import datetime as dt
import hashlib
import json
import re
import subprocess
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent
OUT = ROOT / "verification"
MATHLIB_REV = "fc4f59e577feb1a4956671bc04ac18aaaf8cd842"
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def run(command: list[str], log_name: str) -> dict:
    started = time.monotonic()
    result = subprocess.run(command, cwd=ROOT, text=True, capture_output=True)
    log = OUT / log_name
    log.write_text(result.stdout + result.stderr)
    item = {
        "command": command,
        "exit_code": result.returncode,
        "seconds": round(time.monotonic() - started, 3),
        "log": log_name,
        "log_sha256": sha256(log),
    }
    if result.returncode:
        raise RuntimeError(f"Command failed: {command}\n{log.read_text()}")
    return item


def main() -> None:
    OUT.mkdir(exist_ok=True)
    source = (ROOT / "BSDRankTwo.lean").read_text()
    forbidden = re.search(
        r"(?m)^\s*(?:axiom|constant)\b|\b(?:sorry|admit|native_decide)\b", source
    )
    if forbidden:
        raise RuntimeError(f"Forbidden proof construct: {forbidden.group(0)}")
    version = subprocess.check_output(["lean", "--version"], cwd=ROOT, text=True).strip()
    mathlib = subprocess.check_output(
        ["git", "-C", str(ROOT / ".lake/packages/mathlib"), "rev-parse", "HEAD"],
        text=True,
    ).strip()
    if mathlib != MATHLIB_REV:
        raise RuntimeError(f"Wrong Mathlib revision: {mathlib}")
    commands = [
        run(["lake", "build", "BSDRankTwo"], "build.log"),
        run(["lake", "env", "lean", "Check.lean"], "declarations.log"),
        run(["lake", "env", "leanchecker", "-v", "BSDRankTwo"], "kernel-replay.log"),
    ]
    declarations = (OUT / "declarations.log").read_text()
    axioms = {
        name: [a.strip() for a in names.split(",") if a.strip()]
        for name, names in re.findall(
            r"'([^']+)' depends on axioms: \[([^\]]*)\]", declarations
        )
    }
    if len(axioms) != 15:
        raise RuntimeError(f"Expected fifteen axiom reports, found {len(axioms)}")
    for name, dependencies in axioms.items():
        if not set(dependencies) <= ALLOWED_AXIOMS:
            raise RuntimeError(f"Unapproved axiom in {name}: {dependencies}")
    receipt = {
        "recorded_utc": dt.datetime.now(dt.timezone.utc).isoformat(),
        "lean": version,
        "mathlib_revision": mathlib,
        "scope": "Algebraic finite-level coefficient, exact-order certificate, and exact inversion-symmetry soundness.",
        "kernel_replay_scope": "BSDRankTwo declarations replayed against compiled imports.",
        "source_sha256": {
            name: sha256(ROOT / name)
            for name in [
                "BSDRankTwo.lean", "Check.lean", "lean-toolchain", "lakefile.toml",
                "lake-manifest.json", "verify.py",
            ]
        },
        "object_sha256": sha256(ROOT / ".lake/build/lib/lean/BSDRankTwo.olean"),
        "commands": commands,
        "axioms": axioms,
        "forbidden_construct_scan_passed": True,
    }
    target = OUT / "receipt.json"
    target.write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps({"result": "PASS", "theorems": len(axioms), "receipt": str(target)}))


if __name__ == "__main__":
    main()
