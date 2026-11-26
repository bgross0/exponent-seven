"""Compare lowsearch with a brute-force reference on small configurations with survivors.

The reference loops over every (x, y), tests divisibility, the bounds, q mod 8 and the Legendre
symbols (Euler's criterion) directly from the definition.

Usage:  python3 lowrange/test_lowsearch.py      (after building lowrange/lowsearch)
"""
import math, os, subprocess, sys, tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
BIN = os.path.join(HERE, "lowsearch")


def odd_primes_below(n):
    return [l for l in range(3, n) if all(l % d for d in range(2, math.isqrt(l) + 1))]


def reference(p, qlo, qhi, lcap):
    S = 4*p**7
    ls = odd_primes_below(min(p, lcap))
    out = set()
    for y in range(1, math.isqrt(S//qlo) + 1):
        if y % p == 0:
            continue
        yy = y*y
        for x in range(0, math.isqrt(S - qlo*yy) + 1):
            n = S - x*x
            if n % yy:
                continue
            q = n//yy
            if q < qlo or q >= qhi or q % 8 != 3:
                continue
            if all(pow((-q) % l, (l - 1)//2, l) == l - 1 for l in ls):
                out.add((p, x, y, q))
    return out


def run(p, qlo, qhi, lcap):
    with tempfile.NamedTemporaryFile("w", suffix=".txt", delete=False) as f:
        f.write("1\n")
        name = f.name
    try:
        r = subprocess.run([BIN, name, str(p), str(p), "qlo=%d" % qlo, "qhi=%d" % qhi, "lcap=%d" % lcap],
                           capture_output=True, text=True, check=True)
    finally:
        os.unlink(name)
    return {tuple(int(t) for t in line.split()[1:]) for line in r.stdout.splitlines() if line.startswith("S ")}


def main():
    cases = []
    for p in (3, 5, 7, 11, 13):
        S = 4*p**7
        for qlo in (1, 3, 50, 1000):
            if qlo < S:
                cases.append((p, qlo, S + 1, 10**9))
                cases.append((p, qlo, max(qlo + 1, S//3), 10**9))
    for p in (17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101):
        S = 4*p**7
        for div, lcap in ((40, 10**9), (4000, 10**9), (400, 12), (90000, 20)):
            qlo = S//div
            cases.append((p, qlo, S + 1, lcap))
            cases.append((p, qlo, S//(div//7 + 1) + 5, lcap))
    total = 0; bad = 0; nonempty = 0
    ys = set()
    for p, qlo, qhi, lcap in cases:
        S = 4*p**7
        if math.isqrt(S//qlo) * math.isqrt(S) > 6*10**7:
            continue
        ref = reference(p, qlo, qhi, lcap)
        got = run(p, qlo, qhi, lcap)
        total += 1
        nonempty += bool(ref)
        ys |= {t[2] for t in ref}
        if ref != got:
            bad += 1
            print("MISMATCH p=%d qlo=%d qhi=%d lcap=%d: ref %d, got %d; ref-got %s got-ref %s"
                  % (p, qlo, qhi, lcap, len(ref), len(got), sorted(ref - got)[:3], sorted(got - ref)[:3]))
        else:
            print("ok p=%d qlo=%d qhi=%d lcap=%d: %d survivors" % (p, qlo, qhi, lcap, len(ref)), flush=True)
    print("configurations %d, non-empty %d, mismatches %d, distinct y among survivors %d (max %d)"
          % (total, nonempty, bad, len(ys), max(ys) if ys else 0))
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
