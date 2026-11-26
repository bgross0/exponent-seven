#!/usr/bin/env python3
"""Brute-force reference for the survivor search (independent of search7i.c).

For prime p, a lower bound qlo, an optional bound lmax and a list of y values,
print every (p, x, y, q) with
    N = 4 p^7 - x^2 > 0,  y^2 | N,  q = N / y^2,  q >= qlo,  q = 3 (mod 8),
    (-q / l) = -1 for every odd prime l < p (and l < lmax if lmax > 0).
Plain loops over every x, exact integers, Legendre symbol by Euler's criterion.
Output lines: "S p x y q", sorted by (p, y, x).
"""
import argparse
from math import isqrt


def odd_primes_below(n):
    return [l for l in range(3, n) if all(l % d for d in range(2, isqrt(l) + 1))]


def legendre(a, l):
    a %= l
    if a == 0:
        return 0
    return 1 if pow(a, (l - 1) // 2, l) == 1 else -1


def survivors(p, qlo, lmax, ys):
    bound = p if lmax <= 0 else min(p, lmax)
    ls = odd_primes_below(bound)
    N4 = 4 * p ** 7
    out = []
    for y in ys:
        y2 = y * y
        x = 0
        while x * x < N4:
            N = N4 - x * x
            if N % y2 == 0:
                q = N // y2
                if q >= qlo and q % 8 == 3 and all(legendre(-q, l) == -1 for l in ls):
                    out.append((p, x, y, q))
            x += 1
    out.sort(key=lambda t: (t[0], t[2], t[1]))
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--p", type=int, required=True)
    ap.add_argument("--qlo", type=int, required=True)
    ap.add_argument("--lmax", type=int, default=0)
    ap.add_argument("--ylist", required=True)
    a = ap.parse_args()
    ys = [int(t) for t in a.ylist.split(",")]
    for s in survivors(a.p, a.qlo, a.lmax, ys):
        print("S %d %d %d %d" % s)


if __name__ == "__main__":
    main()
