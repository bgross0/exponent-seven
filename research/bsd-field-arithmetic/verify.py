#!/usr/bin/env python3
"""Build and replay the actual discriminant -71 field-arithmetic development."""

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import time
from datetime import datetime, timezone


ROOT = Path(__file__).resolve().parents[2]
PROJECT = ROOT / "Exp7Lean"
HERE = Path(__file__).resolve().parent
OUT = HERE / "verification"
TARGET = "Exp7Lean.ClassGroup.SeventyOneChecks"
CHECKS = PROJECT / "Exp7Lean/ClassGroup/SeventyOneChecks.lean"
SOURCES = {
    "Exp7Lean.ClassGroup.SeventyOneLocal": "Exp7.SeventyOneLocal",
    "Exp7Lean.ClassGroup.SeventyOne": "Exp7.K71",
}
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def source_path(module):
    return PROJECT / (module.replace(".", "/") + ".lean")


def declarations():
    result = []
    for module, namespace in SOURCES.items():
        names = re.findall(
            r"^(?:@\[[^\n]*\]\s*)?(?:theorem|lemma)\s+(\w+)",
            source_path(module).read_text(),
            re.M,
        )
        result.extend(f"{namespace}.{name}" for name in names)
    return result


def check_source(names):
    return (
        "import Exp7Lean.ClassGroup.SeventyOne\n\n"
        "/-! Axiom and signature inventory for the discriminant -71 arithmetic. -/\n\n"
        + "\n".join(f"#print axioms {name}" for name in names)
        + "\n\n"
        + "\n".join(f"#check {name}" for name in names)
        + "\n"
    )


def import_closure(module, visited=None, result=None):
    if visited is None:
        visited, result = set(), []
    if module in visited:
        return result
    visited.add(module)
    path = source_path(module)
    if not path.is_file():
        raise RuntimeError(f"Missing project import: {module}")
    for imported in re.findall(r"^import\s+(Exp7Lean[.\w]*)\s*$", path.read_text(), re.M):
        import_closure(imported, visited, result)
    result.append(module)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lake", default=shutil.which("lake"), help="Pinned Lake executable")
    parser.add_argument("--write-checks", action="store_true", help="Regenerate the public theorem inventory")
    args = parser.parse_args()
    names = declarations()
    if not names or len(set(names)) != len(names):
        raise RuntimeError("Empty or duplicate theorem inventory")
    expected = check_source(names)
    if args.write_checks:
        CHECKS.write_text(expected)
        print(f"Wrote {CHECKS.relative_to(ROOT)} with {len(names)} public theorem checks")
        return
    if not args.lake:
        parser.error("lake is not on PATH; supply --lake /absolute/path/to/lake")
    if not CHECKS.is_file() or CHECKS.read_text() != expected:
        raise RuntimeError("Stale axiom inventory; run with --write-checks and review the change")

    modules = import_closure(TARGET)
    paths = [source_path(module) for module in modules]
    paths += [PROJECT / "lean-toolchain", PROJECT / "lake-manifest.json",
              PROJECT / "lakefile.toml", Path(__file__)]
    source_hashes = {str(path.relative_to(ROOT)): sha256(path) for path in paths}
    OUT.mkdir(exist_ok=True)
    receipt = {
        "status": "running",
        "started_utc": datetime.now(timezone.utc).isoformat(),
        "base_head_before_verification": subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip(),
        "scope": "Native Exp7 Lean 4.37.0-rc1: build and kernel replay of the complete "
                 "project import closure for the new field-arithmetic modules, against "
                 "compiled pinned Mathlib imports. No fresh replay of all Mathlib; no "
                 "BSD theta/CM/Picard/Selmer identification or terminal BSD theorem.",
        "toolchain": (PROJECT / "lean-toolchain").read_text().strip(),
        "source_sha256": source_hashes,
        "public_theorems": names,
        "project_modules_replayed": modules,
        "commands": [],
    }
    environment = os.environ.copy()
    environment["PATH"] = str(Path(args.lake).resolve().parent) + os.pathsep + environment["PATH"]

    def save():
        (OUT / "receipt.json").write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n")

    def run(label, command, cwd=PROJECT):
        print(label, flush=True)
        start = time.monotonic()
        log = OUT / f"{label}.log"
        with log.open("w") as stream:
            proc = subprocess.run(command, cwd=cwd, env=environment, stdout=stream,
                                  stderr=subprocess.STDOUT)
        receipt["commands"].append({
            "label": label, "command": [str(x) for x in command],
            "cwd": str(cwd.relative_to(ROOT)) or ".", "exit_code": proc.returncode,
            "elapsed_seconds": round(time.monotonic() - start, 3),
            "log": str(log.relative_to(HERE)), "log_sha256": sha256(log),
        })
        save()
        if proc.returncode:
            raise RuntimeError(f"{label} failed; see {log}")
        return log.read_text()

    try:
        receipt["lean_version"] = run("lean-version", [args.lake, "env", "lean", "--version"]).strip()
        if not receipt["lean_version"].startswith("Lean (version 4.37.0-rc1,"):
            raise RuntimeError("Wrong Lean version")
        manifest = json.loads((PROJECT / "lake-manifest.json").read_text())
        mathlib = next(package for package in manifest["packages"] if package["name"] == "mathlib")
        actual_pin = subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=PROJECT / ".lake/packages/mathlib", text=True).strip()
        if actual_pin != mathlib["rev"]:
            raise RuntimeError("Mathlib checkout differs from the pinned manifest")
        receipt["mathlib_revision"] = actual_pin
        run("build", [args.lake, "--rehash", "build", TARGET])
        output = run("axioms-and-signatures", [args.lake, "env", "lean", str(CHECKS.relative_to(PROJECT))])
        found = {}
        for name, entries in re.findall(
            r"'([^']+)' (?:does not depend on any axioms|depends on axioms:\s*\[([^]]*)\])", output
        ):
            dependencies = {value.strip() for value in entries.split(",") if value.strip()}
            if not dependencies <= ALLOWED_AXIOMS:
                raise RuntimeError(f"Unexpected axioms for {name}: {dependencies}")
            found[name] = sorted(dependencies)
        if set(found) != set(names):
            raise RuntimeError(f"Axiom inventory mismatch: expected {names}; found {list(found)}")
        receipt["theorem_axioms"] = found
        for module in modules:
            run("kernel-" + module, [args.lake, "env", "leanchecker", "-v", module])
        if {str(path.relative_to(ROOT)): sha256(path) for path in paths} != source_hashes:
            raise RuntimeError("A source file changed during verification")
        receipt["module_olean_sha256"] = {
            module: sha256(PROJECT / ".lake/build/lib/lean" / (module.replace(".", "/") + ".olean"))
            for module in modules
        }
        receipt["status"] = "passed"
        receipt["finished_utc"] = datetime.now(timezone.utc).isoformat()
        save()
        print(f"Passed: {len(names)} public theorems; {len(modules)} project modules replayed")
    except Exception as error:
        receipt["status"] = "failed"
        receipt["error"] = str(error)
        receipt["finished_utc"] = datetime.now(timezone.utc).isoformat()
        save()
        raise


if __name__ == "__main__":
    main()
