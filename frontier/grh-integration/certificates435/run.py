#!/usr/bin/env python3
"""Build the two pinned per-prime searches and their assembly modules in external435."""
import argparse
import hashlib
import json
import math
import os
from pathlib import Path
import re
import shutil
import subprocess
import time

HERE = Path(__file__).resolve().parent
FAMILIES = {
    "Sieve": (701, 4297, "run_all.sh", "gen_all.py", "search", "searchHigh"),
    "SieveLow": (3, 2759, "run_low.sh", "gen_low_all.py", "searchLow", "searchLow"),
}
AXIOMS = "[propext, Classical.choice, Quot.sound]"


def digest(path):
    with path.open("rb") as handle:
        h = hashlib.sha256()
        for part in iter(lambda: handle.read(1024 * 1024), b""):
            h.update(part)
    return h.hexdigest()


def save(path, value):
    pending = path.with_suffix(".json.tmp")
    pending.write_text(json.dumps(value, indent=2) + "\n")
    pending.replace(path)


def prime_range(lower, upper):
    return [p for p in range(lower, upper + 1) if all(p % i for i in range(2, math.isqrt(p) + 1))]


def build_family(family, work, project, logs, jobs, env):
    lo, hi, runner, generator, prefix, theorem = FAMILIES[family]
    expected = prime_range(lo, hi)
    sources = work / "Exp7Lean" / family
    objects = work / ".lake/build/lib/lean/Exp7Lean" / family
    command = ["bash", str(sources / runner), str(jobs), "0"]
    if family == "SieveLow":
        command += ["--survivors", str(project / "lowrange/low_survivors.txt")]
    with (logs / (family + "-batch.log")).open("a") as log:
        subprocess.run(command, cwd=work, env=env, stdout=log, stderr=subprocess.STDOUT, check=True)

    # The upstream runner can return zero if an individual prime failed. Require
    # its accepted timing record, exact Lean axiom line and artifact for every p.
    timings = {}
    for line in (sources / "logs/times.txt").read_text().splitlines():
        match = re.match(r"^(\d+) OK user_s elapsed_s maxrss_kb: ([\d.]+) ([\d.]+) (\d+)", line)
        if match:
            p, cpu, wall, rss = match.groups()
            timings[int(p)] = dict(user_seconds=float(cpu), elapsed_seconds=float(wall), maxrss_kib=int(rss))
    records = []
    for p in expected:
        source, obj = sources / f"P{p}.lean", objects / f"P{p}.olean"
        axiom = f"'Exp7.{prefix}_{p}' depends on axioms: {AXIOMS}"
        raw = sorted((logs / "primes" / family).glob(f"P{p}.*.log"), key=lambda x: x.stat().st_mtime_ns)
        if p not in timings or not obj.is_file() or not source.is_file() or not raw:
            raise RuntimeError(f"{family}: incomplete certificate for {p}")
        output = raw[-1].read_text()
        if axiom not in output.splitlines() or "error" in output or "sorry" in output:
            raise RuntimeError(f"{family}: inspect {raw[-1]}")
        records.append(dict(prime=p, source_sha256=digest(source), olean_sha256=digest(obj),
                            log_sha256=digest(raw[-1]), **timings[p]))
    save(logs / (family + "-coverage.json"), records)
    subprocess.run(["python3", str(sources / generator)], cwd=work, env=env, check=True)
    source = sources / "All.lean"
    output = logs / (family + "-All.log")
    cmd = ["lake", "env", "lean", str(source.relative_to(work)), "-o", str(objects / "All.pending.olean")]
    started = time.monotonic()
    with output.open("w") as log:
        subprocess.run(cmd, cwd=work, env=env, stdout=log, stderr=subprocess.STDOUT, check=True)
    if f"'Exp7.{theorem}' depends on axioms: {AXIOMS}" not in output.read_text().splitlines():
        raise RuntimeError(f"{family}: inspect assembly axiom output")
    (objects / "All.pending.olean").replace(objects / "All.olean")
    save(logs / (family + "-assembly.json"), dict(command=cmd, exit_code=0, primes=len(records),
         elapsed_seconds=round(time.monotonic()-started,3), source_sha256=digest(source),
         log_sha256=digest(output), olean_sha256=digest(objects / "All.olean")))
    print(f"{theorem}: {len(records)} certificates accepted and assembly checked", flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--workspace", type=Path, required=True)
    parser.add_argument("--project", type=Path, required=True)
    parser.add_argument("--logs", type=Path, required=True)
    parser.add_argument("--jobs", type=int, default=4)
    parser.add_argument("--families", nargs="+", choices=list(FAMILIES), default=list(FAMILIES))
    args = parser.parse_args()
    work, project, logs = (p.resolve() for p in (args.workspace, args.project, args.logs))
    if args.jobs < 1: parser.error("--jobs must be positive")
    pins = json.loads((HERE.parent / "pins.json").read_text())
    pin = subprocess.check_output(["git", "-C", project, "rev-parse", "HEAD"], text=True).strip()
    if pin != pins["project"]["commit"]: raise ValueError("Wrong project checkout")
    env = dict(os.environ, LEANQ=str(HERE / "leanq"), KEEP="1", LEAN_NUM_THREADS="1",
               PYTHONDONTWRITEBYTECODE="1", EXP7_CERT_LOG_DIR=str(logs / "primes"))
    env.pop("PRIMES", None)
    logs.mkdir(parents=True, exist_ok=True)
    # Work outside src so generated certificates never change the pinned source tree.
    for name in ("Basic.lean", "Low.lean", "Witness/SurvivorData.lean",
                 "Sieve/gen.py", "Sieve/estimate.py", "Sieve/run_all.sh", "Sieve/gen_all.py",
                 "Sieve/RootsCertGen.py", "SieveLow/run_low.sh", "SieveLow/gen_low.py", "SieveLow/gen_low_all.py"):
        original = project / "Exp7Lean/Exp7Lean" / name
        target = work / "Exp7Lean" / name
        if not target.exists():
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(original, target)
        if digest(target) != digest(original): raise ValueError(f"Changed generator input: {target}")
    for family in args.families:
        build_family(family, work, project, logs, args.jobs, env)


if __name__ == "__main__":
    main()
