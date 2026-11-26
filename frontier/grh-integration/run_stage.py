#!/usr/bin/env python3
"""Run one integration build gate and save its observed exit status and log.

This runner never declares a failed or unfinished command to be a proof.
Supply an existing isolated workspace produced by prepare.py and a matching Lake.
"""
from __future__ import annotations
import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import resource
import subprocess
import time

TARGETS = {"smoke": "Exp7GRHBridge.Smoke", "external": "Main",
           "imported": "Exp7GRHBridge.Imported", "final": "Exp7GRHBridge.Final"}

FINAL_DECLARATIONS = (
    "LFunction_eq_zero_re", "Exp7.GRHIntegration.primeConductor",
    "Exp7.searchHigh", "Exp7.searchLow",
    "Exp7.GRHIntegration.theoremA", "Exp7.GRHIntegration.theoremD",
    "Exp7.GRHIntegration.theoremA_fundamental", "Exp7.GRHIntegration.theoremD_fundamental",
)

def main() -> int:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("stage", choices=TARGETS)
    p.add_argument("--workspace", type=Path, required=True)
    p.add_argument("--lake", type=Path, required=True)
    p.add_argument("--threads", type=int, default=2)
    a = p.parse_args()
    if a.threads < 1:
        p.error("threads must be positive")
    root = a.workspace.resolve()
    lake = a.lake.resolve()
    provenance = root / "INTEGRATION-PROVENANCE.json"
    if not provenance.is_file() or not lake.is_file():
        p.error("prepared workspace and installed Lake are required")
    receipt_dir = root / "integration-receipts"
    receipt_dir.mkdir(exist_ok=True)
    log_path = receipt_dir / (a.stage + ".log")
    receipt_path = receipt_dir / (a.stage + ".json")
    # Repeated stages preserve earlier attempts, including failed ones.
    attempt = 1
    while log_path.exists() or receipt_path.exists():
        attempt += 1
        log_path = receipt_dir / f"{a.stage}-{attempt}.log"
        receipt_path = receipt_dir / f"{a.stage}-{attempt}.json"
    env = os.environ.copy()
    env["PATH"] = str(lake.parent) + os.pathsep + env.get("PATH", "")
    env["LEAN_NUM_THREADS"] = str(a.threads)
    command = [str(lake), "build", TARGETS[a.stage]]
    if a.stage == "final":
        # The upstream generators compile their modules directly. Load these checked
        # objects in the same Lake environment without replaying every prime.
        output = root / ".lake/build/lib/lean/Exp7GRHBridge/Final.olean"
        output.parent.mkdir(parents=True, exist_ok=True)
        pending = output.with_name("Final.pending.olean")
        command = [str(lake), "env", "lean", "-R", "src", "src/Exp7GRHBridge/Final.lean", "-o", str(pending)]
    receipt = {"stage": a.stage, "target": TARGETS[a.stage], "command": command,
               "workspace": str(root), "threads": a.threads,
               "started_utc": datetime.now(timezone.utc).isoformat(),
               "status": "RUNNING", "exit_code": None,
               "provenance_sha256": hashlib.sha256(provenance.read_bytes()).hexdigest()}
    receipt_path.write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps({"receipt": str(receipt_path), "log": str(log_path),
                      "status": "RUNNING"}), flush=True)
    started = time.monotonic()
    usage_before = resource.getrusage(resource.RUSAGE_CHILDREN)
    with log_path.open("wb") as log:
        try:
            result = subprocess.run(command, cwd=root, env=env,
                                    stdout=log, stderr=subprocess.STDOUT)
            returncode = result.returncode
        except KeyboardInterrupt:
            returncode = 130
    if a.stage == "final" and returncode == 0:
        pending.replace(output)
        query = log_path.with_suffix(".declarations.lean")
        declarations = log_path.with_suffix(".declarations.log")
        query.write_text("import Exp7GRHBridge.Final\n\n" +
                         "".join(f"#check @{name}\n#print axioms {name}\n" for name in FINAL_DECLARATIONS))
        with declarations.open("wb") as log:
            returncode = subprocess.run([str(lake), "env", "lean", str(query)], cwd=root,
                                        env=env, stdout=log, stderr=subprocess.STDOUT).returncode
        observed = {name: values.split(", ") for name, values in re.findall(
            r"'([^']+)' depends on axioms: \[([^\]]*)\]", " ".join(declarations.read_text().split()))}
        expected = ["propext", "Classical.choice", "Quot.sound"]
        if returncode == 0 and any(observed.get(name) != expected for name in FINAL_DECLARATIONS):
            returncode = 1
        receipt.update(declarations_log=declarations.name, declaration_axioms=observed,
                       declarations_sha256=hashlib.sha256(declarations.read_bytes()).hexdigest(),
                       olean_sha256=hashlib.sha256(output.read_bytes()).hexdigest())
    status = ("COMMAND_SUCCEEDED" if returncode == 0 else
              "INTERRUPTED" if returncode == 130 else "COMMAND_FAILED")
    usage_after = resource.getrusage(resource.RUSAGE_CHILDREN)
    receipt.update(status=status,
                   exit_code=returncode,
                   completed_utc=datetime.now(timezone.utc).isoformat(),
                   elapsed_seconds=round(time.monotonic() - started, 3),
                   child_user_cpu_seconds=round(usage_after.ru_utime - usage_before.ru_utime, 3),
                   child_system_cpu_seconds=round(usage_after.ru_stime - usage_before.ru_stime, 3),
                   largest_child_max_rss_kib=usage_after.ru_maxrss,
                   log_sha256=hashlib.sha256(log_path.read_bytes()).hexdigest())
    receipt_path.write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps(receipt, indent=2), flush=True)
    return returncode

if __name__ == "__main__":
    raise SystemExit(main())
