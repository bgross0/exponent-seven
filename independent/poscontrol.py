#!/usr/bin/env python3
"""Positive controls for search7i.

1. For each q in the (corrected) list, count reduced forms of discriminant -q
   to get the class number h(-q). For h = 49, also check that the class group
   has exponent 7: the classes of split primes l <= sqrt(q/3) generate the
   group, and the class of a prime ideal P over l has order dividing 7 iff
   4 l^7 = x^2 + q y^2 has an integer solution (every ideal of norm l^7 is
   P^i P'^(7-i), in the class of P^(2i-7), and 49 never divides 2i-7).
2. For each q = 3 (mod 8): find the least prime p that splits in Q(sqrt(-q)),
   solve 4 p^7 = x^2 + q y^2, run search7i on that p with Qlo = q and the
   default l-condition (odd primes l < p), and check (x, y, q) is reported.
Writes poscontrol.log next to this file.
"""
import os
import subprocess
from math import gcd, isqrt

HERE = os.path.dirname(os.path.abspath(__file__))
BIN = os.path.join(HERE, "search7i")

QS = [71, 151, 223, 251, 463, 467, 487, 587, 811, 827, 859, 1163, 1171, 1483, 1523,
      1627, 1787, 1987, 2011, 2083, 2179, 2251, 2467, 2707, 3019, 3067, 3187, 3907,
      4603, 5107, 5923, 63499, 118843]


def is_prime(n):
    return n >= 2 and all(n % d for d in range(2, isqrt(n) + 1))


def legendre(a, l):
    a %= l
    if a == 0:
        return 0
    return 1 if pow(a, (l - 1) // 2, l) == 1 else -1


def class_number(q):
    """Number of reduced primitive forms (a,b,c), b^2 - 4ac = -q."""
    D = -q
    h = 0
    a = 1
    while 3 * a * a <= q:
        for b in range(-a + 1, a + 1):
            if (b * b - D) % (4 * a):
                continue
            c = (b * b - D) // (4 * a)
            if c < a or (c == a and b < 0):
                continue
            if gcd(gcd(a, abs(b)), c) != 1:
                continue
            h += 1
        a += 1
    return h


def solve_4p7(p, q):
    """All (x, y), x >= 0, y >= 1 with x^2 + q y^2 = 4 p^7."""
    N = 4 * p ** 7
    sols = []
    y = 1
    while q * y * y <= N:
        r = N - q * y * y
        x = isqrt(r)
        if x * x == r:
            sols.append((x, y))
        y += 1
    return sols


def exponent_divides_7(q):
    for l in range(3, isqrt(q // 3) + 1):
        if is_prime(l) and legendre(-q, l) == 1:
            if not solve_4p7(l, q):
                return False, l
    return True, None


def main():
    lines = []
    lines.append("# part 1: class numbers")
    for q in QS:
        h = class_number(q)
        extra = ""
        if h == 49:
            ok, bad = exponent_divides_7(q)
            extra = " exponent_divides_7=%s%s" % (ok, "" if ok else " (fails at l=%d)" % bad)
        lines.append("q=%d prime=%s q%%8=%d h=%d%s" % (q, is_prime(q), q % 8, h, extra))
        print(lines[-1], flush=True)

    lines.append("# part 2: q = 3 mod 8, least split prime p, search7i --p p --qlo q")
    nfound = ntested = 0
    for q in QS:
        if q % 8 != 3:
            continue
        p = 3
        while not (is_prime(p) and legendre(-q, p) == 1):
            p += 2
        sols = solve_4p7(p, q)
        bad_l = [l for l in range(3, p) if is_prime(l) and legendre(-q, l) != -1]
        r = subprocess.run([BIN, "--p", str(p), "--qlo", str(q), "--threads", "4", "--quiet"],
                           capture_output=True, text=True, check=True)
        rep = {tuple(map(int, s.split()[1:])) for s in r.stdout.splitlines() if s.startswith("S ")}
        hits = [(x, y) for (x, y) in sols if (p, x, y, q) in rep]
        ntested += 1
        nfound += bool(hits)
        lines.append("q=%d p=%d solutions(x,y)=%s odd_l<p_not_inert=%s reported_by_C=%s "
                     "total_C_survivors=%d" % (q, p, sols, bad_l or "none", hits, len(rep)))
        print(lines[-1], flush=True)
    lines.append("# q = 3 mod 8 tested: %d, control (x,y,q) reported: %d" % (ntested, nfound))
    print(lines[-1])
    with open(os.path.join(HERE, "poscontrol.log"), "w") as f:
        f.write("\n".join(lines) + "\n")


if __name__ == "__main__":
    main()
