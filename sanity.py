"""Full-range sanity checks for sieve7 in its test mode (sieve primes l < lcap only, y = 1).

1. Soundness: every reported survivor satisfies the conditions, recomputed from the definition.
2. Counts: the number of survivors over the whole x-range is compared with the product of local
   densities.  A sieve that silently dropped candidates would fall short of the expected count.
Independent of sieve7's tables: uses only Jacobi symbols from sympy.
"""
import subprocess, math
from sympy import primerange
from sympy.functions.combinatorial.numbers import jacobi_symbol as jacobi


def qlo(p):
    rows = open("ladder.txt").read().split("\n")
    q = int(rows[0])
    for r in rows[1:]:
        if r.strip():
            x, Q = map(int, r.split())
            if x <= p and Q > q:
                q = Q
    return q


def run(args):
    out = subprocess.run(["./sieve7", "ladder.txt"] + args, capture_output=True, text=True).stdout
    return [tuple(map(int, l.split()[1:])) for l in out.splitlines() if l.startswith("SURVIVOR")]


def expected(p, lcap):
    S = 4*p**7
    Lmax = math.isqrt(S - qlo(p))
    dens = 0.5                                      # x odd  <=>  q = 3 mod 8  (y = 1, p odd)
    for l in primerange(3, lcap):
        s = S % l
        dens *= sum(1 for r in range(l) if jacobi((r*r - s) % l, l) == -1)/l
    return (Lmax + 1)*dens


tot_found = tot_exp = 0
for p, lcap in [(2003, 140), (3001, 150), (2503, 145), (2003, 100), (3001, 104), (3511, 104)]:
    S = 4*p**7
    got = run([str(p), str(p), "yonly=1", "lcap=%d" % lcap])
    ls = list(primerange(3, lcap))
    Q = qlo(p)
    for (pp, y, x, q) in got:
        assert pp == p and y == 1 and S == x*x + q and q % 8 == 3 and q >= Q
        assert all(jacobi((-q) % l, l) == -1 for l in ls)
    e = expected(p, lcap)
    tot_found += len(got); tot_exp += e
    print("p=%d  l<%d : found %d (all sound), expected %.1f, deviation %+.2f sigma"
          % (p, lcap, len(got), e, (len(got) - e)/math.sqrt(e)))
print("total: found %d, expected %.0f, deviation %+.2f sigma" % (tot_found, tot_exp, (tot_found - tot_exp)/math.sqrt(tot_exp)))
