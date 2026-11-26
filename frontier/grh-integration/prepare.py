#!/usr/bin/env python3
"""Prepare an isolated, single-toolchain GRH integration workspace.

No builds or downloads occur here. Both input repositories must be clean checkouts
at the commits in pins.json. The output directory must not already exist.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import shutil
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
PINS = json.loads((HERE / "pins.json").read_text())

def git(root: Path, *args: str) -> str:
    return subprocess.check_output(["git", "-C", str(root), *args], text=True).strip()

def check_checkout(root: Path, expected: str) -> None:
    actual = git(root, "rev-parse", "HEAD")
    if actual != expected:
        raise SystemExit(f"Wrong source commit at {root}: {actual}; expected {expected}")
    status = git(root, "status", "--porcelain=v1", "--untracked-files=normal")
    if status:
        raise SystemExit(f"Input checkout must be clean: {root}\n{status}")

def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()

def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--exponent-seven", type=Path, required=True)
    parser.add_argument("--grh", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--environment", choices=("external435", "project437"), default="external435")
    parser.add_argument("--compat435", action=argparse.BooleanOptionalAction, default=True,
                        help="Apply the checked Step1 backport in external435 (default on); ignored in project437")
    args = parser.parse_args()
    exp = args.exponent_seven.resolve()
    grh = args.grh.resolve()
    out = args.output.resolve()
    if out.exists():
        raise SystemExit(f"Refusing to overwrite existing output: {out}")
    if out.is_relative_to(exp) or out.is_relative_to(grh):
        raise SystemExit("Output must be outside both input repositories.")
    check_checkout(exp, PINS["project"]["commit"])
    check_checkout(grh, PINS["external"]["commit"])
    compact = grh / PINS["external"]["root"]
    exp_root = exp / PINS["project"]["root"]
    chosen = PINS["external" if args.environment == "external435" else "project"]
    out.parent.mkdir(parents=True, exist_ok=True)
    shutil.copytree(compact, out, ignore=shutil.ignore_patterns(".lake"))
    shutil.copytree(exp_root / "Exp7Lean", out / "src" / "Exp7Lean")
    shutil.copy2(exp_root / "Exp7Lean.lean", out / "src" / "Exp7Lean.lean")
    bridge = out / "src" / "Exp7GRHBridge"
    shutil.copytree(HERE / "bridge", bridge)
    lake_path = out / "lakefile.toml"
    lake = lake_path.read_text()
    old = PINS["external"]["mathlib"]
    if lake.count(old) != 1:
        raise SystemExit("Unexpected external lakefile: cannot identify its single Mathlib pin.")
    lake = lake.replace(old, chosen["mathlib"])
    lake += """
# Added only in this isolated integration workspace.
[[lean_lib]]
name = "Exp7Lean"

[lean_lib.leanOptions]
# Exp7Lean's package defaults, overriding the compact project's autoImplicit=false.
autoImplicit = true
pp.unicode.fun = true
relaxedAutoImplicit = false
weak.linter.mathlibStandardSet = true
maxSynthPendingDepth = 3

[[lean_lib]]
name = "Exp7GRHBridge"
globs = ["Exp7GRHBridge.+"]
"""
    lake_path.write_text(lake)
    (out / "lean-toolchain").write_text(chosen["lean"] + "\n")
    if args.environment != "external435":
        # Never reuse a manifest/cache for the other Mathlib/Lean environment.
        (out / "lake-manifest.json").unlink()
    compat_receipt = None
    if args.environment == "external435" and args.compat435:
        compat_dir = HERE / "compat435"
        verification = json.loads((compat_dir / "verification.json").read_text())
        step1 = out / "src" / "Exp7Lean" / "Step1.lean"
        expected_before = verification["original_step1_sha256"]
        expected_after = verification["patched_step1_sha256"]
        before = digest(step1)
        if before not in (expected_before, expected_after):
            raise SystemExit("Step1 compatibility patch input hash does not match its audited source.")
        if before == expected_before:
            subprocess.run(["git", "apply", "--directory=src", "-p2",
                            str(compat_dir / "Step1.patch")], cwd=out, check=True)
        if digest(step1) != expected_after:
            raise SystemExit("Step1 compatibility patch output hash does not match its audited result.")
        compat_receipt = {
            "patch_sha256": digest(compat_dir / "Step1.patch"),
            "original_step1_sha256": expected_before,
            "patched_step1_sha256": expected_after,
            "foundation_status": verification["status"],
            "note": "Explicit proof backport only; project definitions and theorem statements unchanged.",
        }
    receipt = {
        "status": "PREPARED_NOT_COMPILED",
        "environment": args.environment,
        "lean": chosen["lean"],
        "mathlib": chosen["mathlib"],
        "source_pins": PINS,
        "compat435": compat_receipt,
        "copied_sha256": {},
    }
    for rel in ("Analytic/Statement.lean", "Final4.lean", "Above.lean"):
        src = exp_root / "Exp7Lean" / rel
        dst = out / "src" / "Exp7Lean" / rel
        assert src.read_bytes() == dst.read_bytes()
        receipt["copied_sha256"]["Exp7Lean/" + rel] = digest(dst)
    for rel in ("Statements.lean", "Main.lean"):
        src = compact / "src" / rel
        dst = out / "src" / rel
        assert src.read_bytes() == dst.read_bytes()
        receipt["copied_sha256"]["external/" + rel] = digest(dst)
    for rel in ("Smoke.lean", "Imported.lean", "Final.lean"):
        receipt["copied_sha256"]["Exp7GRHBridge/" + rel] = digest(bridge / rel)
    all_inputs = sorted((out / "src").rglob("*.lean"))
    all_inputs += [out / "lakefile.toml", out / "lean-toolchain"]
    if (out / "lake-manifest.json").is_file():
        all_inputs.append(out / "lake-manifest.json")
    receipt["prepared_inputs_sha256"] = {
        str(path.relative_to(out)): digest(path) for path in all_inputs
    }
    (out / "INTEGRATION-PROVENANCE.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps({"workspace": str(out), "environment": args.environment,
                      "status": receipt["status"]}, indent=2))

if __name__ == "__main__":
    main()

