#!/usr/bin/env python3
"""Regenerate exact class-polynomial coefficients and 389-adic CM lifts."""

import argparse
import json
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[1]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--gp", default="gp")
    args = parser.parse_args()
    program = r'''
h=polclass(-44375);
if(poldegree(h)!=140,error("Incorrect class polynomial degree"));
rr=polrootspadic(h,[y^2-2,389],32);
if(#rr!=140,error("Incorrect root count"));
print(Str(vector(141,k,polcoef(h,k-1))));
print(Str(vector(#rr,i,[lift(polcoef(lift(rr[i]),0)),lift(polcoef(lift(rr[i]),1))])));
quit
'''
    result = subprocess.run([args.gp, "-fq", "-s", "256M"], input=program,
                            text=True, capture_output=True, cwd=ROOT)
    if result.returncode or "***" in result.stderr:
        raise RuntimeError(result.stderr)
    lines = result.stdout.strip().splitlines()
    if len(lines) != 2:
        raise RuntimeError("Unexpected PARI output")
    coeffs, lifts = map(json.loads, lines)
    if len(coeffs) != 141 or len(lifts) != 140:
        raise RuntimeError("Incomplete data")
    for filename, data in [("H-minus44375-coeffs.json", coeffs), ("CM-minus44375-lifts32.json", lifts)]:
        (ROOT / "data" / filename).write_text(json.dumps(data) + "\n")
    print("Generated degree-140 class polynomial and 140 roots at precision 389^32.")


if __name__ == "__main__":
    main()
