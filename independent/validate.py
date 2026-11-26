#!/usr/bin/env python3
"""Compare search7i (four enumeration modes) with the brute-force ref7.py on
many small truncated configurations. Writes validate.log next to this file."""
import os
import subprocess
import sys
from multiprocessing import Pool

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from ref7 import survivors  # noqa: E402

HERE = os.path.dirname(os.path.abspath(__file__))
BIN = os.path.join(HERE, "search7i")

YSETS = [
    [1, 2, 3, 6, 9, 15, 35],
    [4, 5, 7, 8, 10, 12, 14, 21, 25, 27, 30, 45, 49, 63, 105],
]
MODES = [
    [],                                  # default (auto)
    ["--no-wheel"],                      # every k tested directly
    ["--force-wheel"],                   # CRT range enumeration everywhere
    ["--force-wheel", "--wmax-log2", "9"],  # W small: full-product mode
]


def configs():
    out = []
    for p in [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43]:
        N4 = 4 * p ** 7
        qlos = [1, 1000003, N4 // 50]
        lmaxes = [0, 12, 30] if p <= 31 else [0, 20]
        for ys in YSETS:
            for qlo in qlos:
                for lmax in lmaxes:
                    out.append((p, qlo, lmax, ys))
    # larger p: the default (auto) mode uses multi-modulus CRT enumeration here
    for p in [53, 61, 71, 79]:
        N4 = 4 * p ** 7
        for lmax in [0, 24, 40]:
            for qlo in [1, N4 // 30]:
                out.append((p, qlo, lmax, YSETS[0]))
    return out


def run_c(p, qlo, lmax, ys, mode):
    cmd = [BIN, "--p", str(p), "--qlo", str(qlo), "--lmax", str(lmax),
           "--ylist", ",".join(map(str, ys)), "--threads", "1", "--quiet"] + mode
    r = subprocess.run(cmd, capture_output=True, text=True, check=True)
    if "INTERNAL ERROR" in r.stderr:
        raise RuntimeError(r.stderr)
    return [tuple(map(int, l.split()[1:])) for l in r.stdout.splitlines() if l.startswith("S ")]


def job(cfg):
    p, qlo, lmax, ys = cfg
    ref = survivors(p, qlo, lmax, ys)
    res = []
    for mode in MODES:
        c = run_c(p, qlo, lmax, ys, mode)
        res.append(c == ref)
    yset = sorted({t[2] for t in ref})
    return (p, qlo, lmax, ",".join(map(str, ys)), len(ref), yset, res)


def main():
    cfgs = configs()
    with Pool(20) as pool:
        results = pool.map(job, cfgs, chunksize=1)
    nok = sum(all(r[-1]) for r in results)
    tot_surv = sum(r[4] for r in results)
    with open(os.path.join(HERE, "validate.log"), "w") as f:
        f.write("# p qlo lmax ylist n_ref_survivors y_values_with_survivors "
                "match[auto,no-wheel,force-wheel,force-wheel+smallW]\n")
        for r in results:
            f.write("%d %d %d %s %d %s %s\n" % (r[0], r[1], r[2], r[3], r[4],
                                                ",".join(map(str, r[5])) or "-", r[6]))
        f.write("# configurations: %d, all four C modes match reference: %d, "
                "total reference survivors: %d\n" % (len(results), nok, tot_surv))
    print("configurations:", len(results), "all-match:", nok, "total ref survivors:", tot_surv)
    bad = [r for r in results if not all(r[-1])]
    for r in bad:
        print("MISMATCH", r)
    ys_hit = set()
    for r in results:
        ys_hit.update(r[5])
    print("y values with at least one survivor somewhere:", sorted(ys_hit))


if __name__ == "__main__":
    main()
