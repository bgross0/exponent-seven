#!/usr/bin/env python3
"""Build and kernel-replay the pinned certificate project; audit every theorem.

Run with the pinned Lean/lake toolchain on PATH and Mathlib fetched. No proof
depends on Python or on this receipt: the .lean sources contain the witnesses
and all proofs. This script records what was checked and rejects unexpected
axioms, modified dependency sources, or source changes during verification.
"""
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
LEAN_COMMIT = "611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9"
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def strip_comments(source: str) -> str:
    result, depth, i = [], 0, 0
    while i < len(source):
        if source.startswith("/-", i):
            depth += 1; result.append("  "); i += 2
        elif depth and source.startswith("-/", i):
            depth -= 1; result.append("  "); i += 2
        elif not depth and source.startswith("--", i):
            end = source.find("\n", i)
            end = len(source) if end < 0 else end
            result.append(" " * (end-i)); i = end
        else:
            result.append(source[i] if not depth or source[i] == "\n" else " ")
            i += 1
    if depth:
        raise RuntimeError("Unclosed Lean comment")
    return "".join(result)


def run(command: list[str], log_name: str) -> dict:
    print("Checking " + log_name, flush=True)
    started = time.monotonic()
    result = subprocess.run(command, cwd=ROOT, text=True, capture_output=True)
    log = OUT / log_name
    log.write_text(result.stdout + result.stderr)
    item = {"command": command, "exit_code": result.returncode,
            "seconds": round(time.monotonic()-started, 3), "log": log_name,
            "log_sha256": digest(log)}
    if result.returncode:
        raise RuntimeError(f"Failed {log_name}:\n{log.read_text()[:8000]}")
    return item


def main():
    OUT.mkdir(exist_ok=True)
    modules = sorted(p.stem for p in ROOT.glob("BSD*.lean"))
    names, counts = [], {}
    for module in modules:
        source = strip_comments((ROOT / (module + ".lean")).read_text())
        forbidden = re.search(
            r"(?m)^\s*(?:(?:private|public)\s+)?(?:axiom|constant)\b|"
            r"\b(?:sorry|admit|native_decide|unsafe|implemented_by|partial)\b", source)
        if forbidden:
            raise RuntimeError(f"Forbidden construct in {module}: {forbidden.group(0)}")
        # Attributes can share the declaration line, as in `@[simp] theorem`.
        # Reject an unrecognized theorem form instead of silently skipping it.
        found = re.findall(
            r"(?m)^\s*(?:@\[[\s\S]*?\]\s*)*"
            r"(?:(?:private|public|protected|nonrec)\s+)*"
            r"(?:theorem|lemma)\s+([^\s:(\[{]+)", source)
        declared = re.findall(r"\b(?:theorem|lemma)\s+([^\s:(\[{]+)", source)
        if sorted(found) != sorted(declared):
            raise RuntimeError(f"Unrecognized theorem declaration form in {module}")
        counts[module] = len(found)
        names.extend(module + "." + name for name in found)
    check = "import BSDCertificates\n\n" + "\n".join("#print axioms " + n for n in names) + "\n"
    (ROOT / "Check.lean").write_text(check)
    inputs = sorted([*ROOT.glob("*.lean"), *ROOT.glob("*.toml"),
                     ROOT / "lake-manifest.json", ROOT / "lean-toolchain",
                     ROOT / "verify.py", *ROOT.glob("scripts/*.py")])
    source_hashes = {str(p.relative_to(ROOT)): digest(p) for p in inputs}
    version = subprocess.check_output(["lean", "--version"], cwd=ROOT, text=True).strip()
    if "version 4.36.0," not in version or LEAN_COMMIT not in version:
        raise RuntimeError("Wrong Lean toolchain: " + version)
    dep = ROOT / ".lake/packages/mathlib"
    mathlib = subprocess.check_output(["git", "-C", str(dep), "rev-parse", "HEAD"], text=True).strip()
    if mathlib != MATHLIB_REV:
        raise RuntimeError("Wrong Mathlib revision: " + mathlib)
    if subprocess.run(["git", "-C", str(dep), "diff", "--quiet", "HEAD", "--"],
                      capture_output=True).returncode:
        raise RuntimeError("Tracked Mathlib sources differ from the pinned revision")
    commands = [run(["lake", "build", "BSDCertificates"], "build.log"),
                run(["lake", "env", "lean", "Check.lean"], "axioms.log")]
    reports = (OUT / "axioms.log").read_text()
    axioms = {name: [a.strip() for a in deps.split(",") if a.strip()]
              for name, deps in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", reports)}
    for name in re.findall(r"'([^']+)' does not depend on any axioms", reports):
        axioms[name] = []
    if set(axioms) != set(names):
        raise RuntimeError("Missing or extra axiom reports: " + str(set(names) ^ set(axioms)))
    for name, deps in axioms.items():
        if not set(deps) <= ALLOWED_AXIOMS:
            raise RuntimeError(f"Unexpected axiom in {name}: {deps}")
    def replay(module):
        return run(["lake", "env", "leanchecker", "-v", module], "kernel-" + module + ".log")
    # A single replay avoids loading several large imported environments at once.
    commands.extend(replay(module) for module in modules)
    for rel, expected in source_hashes.items():
        if digest(ROOT / rel) != expected:
            raise RuntimeError("Source changed during verification: " + rel)
    receipt = {
        "result": "PASS", "recorded_utc": dt.datetime.now(dt.timezone.utc).isoformat(),
        "lean": version, "mathlib_revision": mathlib,
        "mathlib_tracked_sources_clean": True,
        "theorem_count": len(names), "prior_theorem_count": counts.get("BSDRankTwo", 0),
        "new_theorem_count": len(names)-counts.get("BSDRankTwo", 0),
        "previous_milestone_theorem_count": 266,
        "theorems_added_since_previous_milestone": len(names)-266,
        "previous_milestone_proof_commit": "c7cd5ffdd05d20e75b1f5f9c80e0e1131c473d2c",
        "theorems_per_module": counts,
        "source_sha256": source_hashes,
        "object_sha256": {m: digest(ROOT / (".lake/build/lib/lean/" + m + ".olean")) for m in modules},
        "commands": commands, "axioms": axioms,
        "axiom_union": sorted({a for deps in axioms.values() for a in deps}),
        "kernel_replay_scope": "All project modules replayed separately against their compiled imports; this is not a fresh replay of every Mathlib declaration.",
        "scope": "Exact finite certificates; full candidate-polynomial semantics; actual distinct roots in a concrete nontrivial completed quadratic order and their exact degree-seven Phi2 graph; actual point counts and ordinary unit roots; two independent actual rational points on the E389 curve with cardinal rank at least two; separate E389 and E433 order certificates from explicitly assumed compatible symmetric finite towers; conditional localization and dimension theorems. No CM polynomial identification, arithmetic tower identification, elliptic Selmer bound, rank upper bound, Sha finiteness, or universal BSD proof is asserted.",
        "forbidden_construct_scan_passed": True,
    }
    (OUT / "receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps({"result": "PASS", "theorems": len(names),
                      "new_theorems": receipt["new_theorem_count"],
                      "receipt": "verification/receipt.json"}), flush=True)


if __name__ == "__main__":
    main()
