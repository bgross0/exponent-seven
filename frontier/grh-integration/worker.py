#!/usr/bin/env python3
"""Run the pinned GRH integration on an x86-64 Linux worker, with resumable logs.

Requires Python 3.10+, git, tar, zstd, and HTTPS access to GitHub/Mathlib caches.
Installs the verified Lean release only inside --work-root; never requires sudo.
The default gates prove the interface and then import the actual GRH proof.
The optional final gate attempts the bounded classification wrapper as well.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import fcntl
import hashlib
import json
import os
from pathlib import Path
import platform
import shutil
import subprocess
import sys
import urllib.request

HERE = Path(__file__).resolve().parent
PINS = json.loads((HERE / "pins.json").read_text())
ARCHIVE = "lean-4.35.0-linux.tar.zst"
ARCHIVE_SHA256 = "7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d"
URL = "https://github.com/leanprover/lean4/releases/download/v4.35.0/" + ARCHIVE
STAGES = ("smoke", "external", "imported", "final")
WORK_LOCK = None


def digest(path: Path) -> str:
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest() if hasattr(hashlib, "file_digest") else digest_stream(stream)


def digest_stream(stream) -> str:
    h = hashlib.sha256()
    for block in iter(lambda: stream.read(1024 * 1024), b""):
        h.update(block)
    return h.hexdigest()


def memory_gib() -> float:
    try:
        values = dict(line.split(":", 1) for line in Path("/proc/meminfo").read_text().splitlines())
        return int(values["MemAvailable"].split()[0]) / 1024**2
    except (OSError, KeyError, ValueError):
        return 8.0


def call(command: list[str], *, cwd: Path | None = None, env=None) -> None:
    print("RUN", json.dumps(command), flush=True)
    subprocess.run(command, cwd=cwd, env=env, check=True)


def checkout(root: Path, spec: dict) -> None:
    if not root.exists():
        partial = root.with_name(root.name + ".partial")
        if partial.exists():
            shutil.rmtree(partial)
        partial.mkdir()
        call(["git", "init", str(partial)])
        call(["git", "-C", str(partial), "remote", "add", "origin", spec["repository"] + ".git"])
        call(["git", "-C", str(partial), "fetch", "--depth", "1", "origin", spec["commit"]])
        call(["git", "-C", str(partial), "checkout", "--detach", "FETCH_HEAD"])
        partial.rename(root)
    actual = subprocess.check_output(["git", "-C", str(root), "rev-parse", "HEAD"], text=True).strip()
    dirty = subprocess.check_output(["git", "-C", str(root), "status", "--porcelain=v1"], text=True).strip()
    if actual != spec["commit"] or dirty:
        raise RuntimeError(f"Refusing a modified or incorrectly pinned input checkout: {root}")


def install_lean(root: Path) -> Path:
    target = root / "lean-4.35.0-linux"
    archive = root / ARCHIVE
    marker = target / "verified-toolchain.json"
    if not target.exists():
        if not archive.exists():
            partial = root / (ARCHIVE + ".partial")
            print("Downloading the official Lean release (about 595 MB).", flush=True)
            with urllib.request.urlopen(URL, timeout=180) as src, partial.open("wb") as dst:
                shutil.copyfileobj(src, dst, 1024 * 1024)
            partial.rename(archive)
        if digest(archive) != ARCHIVE_SHA256:
            raise RuntimeError("Lean archive SHA-256 mismatch; no archive has been extracted.")
        staging = root / "toolchain-extract.partial"
        if staging.exists():
            shutil.rmtree(staging)
        staging.mkdir()
        call(["tar", "--zstd", "-xf", str(archive), "-C", str(staging)])
        staged_target = staging / target.name
        (staged_target / marker.name).write_text(json.dumps({"url": URL, "sha256": ARCHIVE_SHA256}, indent=2) + "\n")
        staged_target.rename(target)
        staging.rmdir()
        archive.unlink()  # The checked extracted toolchain is retained; save 595 MB.
    if not marker.is_file() or json.loads(marker.read_text()).get("sha256") != ARCHIVE_SHA256:
        raise RuntimeError("Existing toolchain lacks this worker's verified-download receipt.")
    shutil.copy2(marker, root / marker.name)
    lean = target / "bin" / "lean"
    version = subprocess.check_output([str(lean), "--version"], text=True).strip()
    if "version 4.35.0," not in version:
        raise RuntimeError(f"Unexpected Lean version: {version}")
    print(version, flush=True)
    return target / "bin" / "lake"


def source_identity() -> dict[str, str]:
    paths = [HERE / "pins.json", HERE / "prepare.py", HERE / "worker.py", HERE / "run_stage.py"]
    paths += sorted((HERE / "bridge").glob("*.lean"))
    paths += [HERE / "compat435" / "Step1.patch", HERE / "compat435" / "verification.json"]
    return {str(p.relative_to(HERE)): digest(p) for p in paths}


def validate_workspace(workspace: Path) -> None:
    receipt = json.loads((workspace / "INTEGRATION-PROVENANCE.json").read_text())
    if receipt["source_pins"] != PINS or receipt["environment"] != "external435":
        raise RuntimeError("Existing workspace has different source pins or environment.")
    for name, expected in receipt["copied_sha256"].items():
        relative = name.removeprefix("external/")
        if digest(workspace / "src" / relative) != expected:
            raise RuntimeError(f"Prepared source has changed: {name}")
    if digest(workspace / "src/Exp7Lean/Step1.lean") != receipt["compat435"]["patched_step1_sha256"]:
        raise RuntimeError("Prepared Step1 differs from its proved compatibility patch.")
    inputs = sorted((workspace / "src").rglob("*.lean"))
    inputs += [workspace / "lakefile.toml", workspace / "lean-toolchain", workspace / "lake-manifest.json"]
    actual = {str(path.relative_to(workspace)): digest(path) for path in inputs}
    if actual != receipt.get("prepared_inputs_sha256"):
        raise RuntimeError("Prepared source, Lake configuration, or dependency manifest has changed.")


def main() -> int:
    global WORK_LOCK
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--work-root", type=Path, required=True, help="A new dedicated directory, or this worker's existing directory to resume")
    p.add_argument("--threads", type=int, help="Default: at most 8, at most half the logical CPUs, and about one per 3 GiB available RAM")
    p.add_argument("--stages", nargs="+", choices=STAGES, default=list(STAGES[:3]))
    p.add_argument("--preflight-only", action="store_true", help="Print machine requirements without downloading or creating the work root")
    args = p.parse_args()
    if sys.version_info < (3, 10) or platform.system() != "Linux" or platform.machine() not in ("x86_64", "AMD64"):
        p.error("This pinned worker requires Python 3.10+ on x86-64 Linux.")
    missing = [name for name in ("git", "tar", "zstd") if shutil.which(name) is None]
    cpus = os.cpu_count() or 2
    available = memory_gib()
    threads = args.threads if args.threads is not None else max(1, min(8, cpus // 2, int(available // 3)))
    if threads < 1:
        p.error("--threads must be positive")
    root = args.work_root.expanduser().resolve()
    parent = root
    while not parent.exists():
        parent = parent.parent
    free = shutil.disk_usage(parent).free / 1024**3
    machine = {"logical_cpus": cpus, "available_memory_gib": round(available, 2),
               "free_disk_gib": round(free, 2), "threads": threads, "missing_commands": missing,
               "work_root": str(root), "stages": args.stages}
    print(json.dumps(machine, indent=2), flush=True)
    if args.preflight_only:
        return 0 if not missing else 2
    if missing:
        p.error("Install these packages first: " + " ".join(missing) + ". On Kubuntu: sudo apt install git zstd")
    if not root.exists() and free < 16:
        p.error("The initial build needs at least 16 GiB free; 30 GiB is recommended.")
    identity = source_identity()
    state = root / "WORKER-SOURCES.json"
    if not root.exists():
        root.mkdir(parents=True)
    WORK_LOCK = (root / "WORKER.lock").open("a+")
    try:
        fcntl.flock(WORK_LOCK, fcntl.LOCK_EX | fcntl.LOCK_NB)
    except BlockingIOError:
        p.error("Another worker is already using this work root.")
    if state.is_file():
        if json.loads(state.read_text()) != identity:
            p.error("Existing directory is not a matching worker checkpoint; use a new dedicated directory.")
    else:
        if any(path.name != "WORKER.lock" for path in root.iterdir()):
            p.error("Existing directory is not an empty worker root; use a new dedicated directory.")
        pending_state = root / "WORKER-SOURCES.json.partial"
        pending_state.write_text(json.dumps(identity, indent=2) + "\n")
        pending_state.rename(state)
    (root / "machine.json").write_text(json.dumps(machine, indent=2) + "\n")
    lake = install_lean(root)
    checkout(root / "exponent-seven-pinned", PINS["project"])
    checkout(root / "grh-pinned", PINS["external"])
    workspace = root / "combined"
    if not workspace.exists():
        staging = root / "combined.partial"
        if staging.exists():
            shutil.rmtree(staging)
        call([sys.executable, str(HERE / "prepare.py"), "--exponent-seven", str(root / "exponent-seven-pinned"),
              "--grh", str(root / "grh-pinned"), "--output", str(staging), "--environment", "external435"])
        staging.rename(workspace)
    validate_workspace(workspace)
    env = os.environ.copy()
    env["PATH"] = str(lake.parent) + os.pathsep + env.get("PATH", "")
    env["LEAN_NUM_THREADS"] = str(threads)
    cache_marker = root / "mathlib-cache-completed.json"
    if not cache_marker.exists():
        call([str(lake), "exe", "cache", "get"], cwd=workspace, env=env)
        cache_marker.write_text(json.dumps({"completed_utc": datetime.now(timezone.utc).isoformat(),
                                            "mathlib": PINS["external"]["mathlib"]}, indent=2) + "\n")
    validate_workspace(workspace)
    for stage in args.stages:
        # Lake reuses successful modules. Each invocation retains a fresh stage receipt.
        call([sys.executable, str(HERE / "run_stage.py"), stage, "--workspace", str(workspace),
              "--lake", str(lake), "--threads", str(threads)], env=env)
    print("REQUESTED BUILD GATES COMPLETED. Inspect printed axioms in the saved logs.", flush=True)
    print("Receipts: " + str(workspace / "integration-receipts"), flush=True)
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except KeyboardInterrupt:
        print("Interrupted. Rerun the same command to reuse completed modules.", file=sys.stderr)
        raise SystemExit(130)
    except (RuntimeError, subprocess.CalledProcessError, OSError) as error:
        print(f"WORKER STOPPED: {error}", file=sys.stderr)
        raise SystemExit(1)
