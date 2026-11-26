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
import resource
import subprocess
import time

TARGETS = {"smoke": "Exp7GRHBridge.Smoke", "external": "Main",
           "imported": "Exp7GRHBridge.Imported", "final": "Exp7GRHBridge.Final"}

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
    receipt = {"stage": a.stage, "target": TARGETS[a.stage], "command": command,
               "workspace": str(root), "threads": a.threads,
               "started_utc": datetime.now(timezone.utc).isoformat(),
               "status": "RUNNING", "exit_code": None,
               "provenance_sha256": hashlib.sha256(provenance.read_bytes()).hexdigest()}
    receipt_path.write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps({"receipt": str(receipt_path), "log": str(log_path),
                      "status": "RUNNING"}), flush=True)
    started = time.monotonic()
    with log_path.open("wb") as log:
        result = subprocess.run(command, cwd=root, env=env,
                                stdout=log, stderr=subprocess.STDOUT)
    receipt.update(status="COMMAND_SUCCEEDED" if result.returncode == 0 else "COMMAND_FAILED",
                   exit_code=result.returncode,
                   completed_utc=datetime.now(timezone.utc).isoformat(),
                   elapsed_seconds=round(time.monotonic() - started, 3),
                   largest_child_max_rss_kib=resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss,
                   log_sha256=hashlib.sha256(log_path.read_bytes()).hexdigest())
    receipt_path.write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps(receipt, indent=2), flush=True)
    return result.returncode

if __name__ == "__main__":
    raise SystemExit(main())
