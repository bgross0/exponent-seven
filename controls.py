"""Positive controls and independent checks for sieve7.

1. For each of the 33 known fields Q(sqrt(-q)) of class group exponent 7 (EKN Table 1, ARSX
   Table A.7): recompute the class group from scratch by listing reduced forms, confirm the
   exponent is 7, find the least split prime p and a solution of 4p^7 = x^2 + q y^2, and check
   that the production code path of sieve7 (wheel + bit sieve forced on) reports exactly that
   (p, y, x, q).
2. Window test: on small windows, recompute the survivor list in pure Python straight from the
   definition (Kronecker symbols of -q) and compare with sieve7's output.
"""
import subprocess, sys, math
from math import gcd, isqrt
from sympy import isprime, primerange
from sympy.functions.combinatorial.numbers import jacobi_symbol as jacobi

KNOWN = [71, 151, 223, 251, 463, 467, 487, 587, 811, 827, 859, 1163, 1171, 1483, 1523, 1627, 1787,
         1987, 2011, 2083, 2179, 2251, 2467, 2707, 3019, 3067, 3187, 3907, 4603, 5107, 5923, 63499,
         118843]


# ---------- binary quadratic forms of discriminant D < 0 ----------
def reduce_form(a, b, c):
    while True:
        if c < a:
            a, b, c = c, -b, a
        if b > a or b <= -a:
            k = (b + a)//(2*a) if b > a else -((a - b)//(2*a))
            # choose k with -a < b - 2ak <= a
            k = (b + a - 1)//(2*a) if (b + a - 1) >= 0 else -((-(b + a - 1) + 2*a - 1)//(2*a))
            b2 = b - 2*a*k
            c = a*k*k - b*k + c
            b = b2
            continue
        if a == c and b < 0:
            b = -b
        if c >= a and -a < b <= a:
            return a, b, c


def ext_gcd(a, b):
    if b == 0:
        return (abs(a), (1 if a >= 0 else -1), 0)
    g, x, y = ext_gcd(b, a % b)
    return g, y, x - (a//b)*y


def compose(f1, f2, D):
    a1, b1, c1 = f1; a2, b2, c2 = f2
    s = (b1 + b2)//2
    g, u, v = ext_gcd(a1, a2)          # u a1 + v a2 = g
    g2, u2, w = ext_gcd(g, s)          # u2 g + w s = g2
    u, v = u*u2, v*u2                  # u a1 + v a2 + w s = g2
    a3 = a1*a2//(g2*g2)
    b3 = b2 + 2*(a2//g2)*((v*(b1 - b2)//2 - w*c2) % (a1//g2))
    c3 = (b3*b3 - D)//(4*a3)
    return reduce_form(a3, b3, c3)


def reduced_forms(D):
    forms = []
    b = D % 2
    while 3*b*b <= -D:
        n = (b*b - D)//4
        a = max(b, 1)
        while a*a <= n:
            if n % a == 0:
                c = n//a
                if gcd(gcd(a, b), c) == 1:
                    forms.append((a, b, c))
                    if 0 < b < a < c:
                        forms.append((a, -b, c))
            a += 1
        b += 2
    return forms


def class_group_exponent(D):
    forms = reduced_forms(D)
    one = reduce_form(1, D % 2, ((D % 2) - D)//4)
    e = 1
    for f in forms:
        k = 1; g = f
        while g != one:
            g = compose(g, f, D); k += 1
        e = e*k//gcd(e, k)
    return len(forms), e


def kron_minus_q(q, l):
    """Kronecker symbol (-q / l) for a prime l"""
    if l == 2:
        r = (-q) % 8
        return 0 if q % 2 == 0 else (1 if r in (1, 7) else -1)
    return jacobi((-q) % l, l)


def least_split(q):
    for l in primerange(2, 10**6):
        if kron_minus_q(q, l) == 1:
            return l


def run(args):
    out = subprocess.run(["./sieve7"] + args, capture_output=True, text=True).stdout
    return [tuple(map(int, ln.split()[1:])) for ln in out.splitlines() if ln.startswith("SURVIVOR")]


def control_known():
    open("ctl_ladder.txt", "w").write("0\n")
    ok = True
    for q in KNOWN:
        h, e = class_group_exponent(-q)
        p = least_split(q)
        S = 4*p**7
        sol = None
        y = 1
        while q*y*y < S:
            r = S - q*y*y
            x = isqrt(r)
            if x*x == r:
                sol = (x, y); break
            y += 1
        assert sol, q
        x, y = sol
        got = run(["ctl_ladder.txt", str(p), str(p), "yonly=%d" % y, "tsmall=0"])
        hit = (p, y, x, q) in got
        got_naive = run(["ctl_ladder.txt", str(p), str(p), "yonly=%d" % y, "naive=1"])
        ok &= (e == 7 and hit and sorted(got) == sorted(got_naive))
        print("q=%6d  h=%4d exponent=%d  least split p=%3d  4p^7 = %d^2 + q*%d^2  sieve7 %s (%d survivors, naive %d)"
              % (q, h, e, p, x, y, "FOUND" if hit else "MISSED", len(got), len(got_naive)))
    print("control_known:", "PASS" if ok else "FAIL")
    return ok


def window(p, y, xcap, lcap):
    """survivors straight from the definition, for the test mode lcap (sieve primes l < lcap only)"""
    S = 4*p**7
    res = []
    ls = [l for l in primerange(3, min(lcap, p)) if y % l != 0]
    for x in range(0, xcap + 1):
        N = S - x*x
        if N <= 0 or N % (y*y):
            continue
        q = N//(y*y)
        if q < 31*10**19:
            continue
        if q % 8 != 3:
            continue
        if all(jacobi((-q) % l, l) == -1 for l in ls):
            res.append((p, y, x, q))
    return res


def control_windows():
    ok = True
    for (p, y, xcap, lcap) in [(2011, 1, 3*10**6, 30), (2011, 3, 6*10**6, 30), (2011, 15, 4*10**7, 30),
                               (3001, 1, 2*10**6, 24), (1009, 1, 3*10**6, 32), (2011, 2, 4*10**6, 30),
                               (2011, 9, 3*10**7, 30), (4201, 1, 2*10**6, 24)]:
        ref = window(p, y, xcap, lcap)
        got = run(["ladder.txt", str(p), str(p), "yonly=%d" % y, "xcap=%d" % xcap, "lcap=%d" % lcap, "tsmall=0"])
        same = sorted(ref) == sorted(got)
        ok &= same
        print("window p=%d y=%d x<=%d l<%d : python %d, sieve7 %d  %s" % (p, y, xcap, lcap, len(ref), len(got), "OK" if same else "MISMATCH"))
    print("control_windows:", "PASS" if ok else "FAIL")
    return ok


if __name__ == "__main__":
    a = control_known()
    b = control_windows()
    sys.exit(0 if (a and b) else 1)
