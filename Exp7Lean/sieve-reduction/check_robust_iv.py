"""Independent interval-arithmetic check (mpmath iv) of the robust rows:
   rowMargin(Q, X, v) - sum_{T <= l < X} max(0, d_l) > 0,
   d_l = -4 log l * sum_{odd k, l^k < X} f(log l^k) / sqrt(l^k).
Uses kernel_verify.rigorous_margin for the base margin and its own f for the penalty."""
import sys, math
from fractions import Fraction
sys.path.insert(0, "/home/zlab/GitHub/exponent-seven")
from mpmath import iv, mp
import kernel_verify as kv
iv.dps = 40

def f_table(X, v):
    m = len(v); sq = sum(t*t for t in v)
    corr = [kv.frac(Fraction(sum(v[k]*v[k+j] for k in range(m - j)), sq)) for j in range(m + 1)]
    width = iv.log(iv.mpf(X)) / m
    Xpow = [X**k for k in range(m + 1)]
    def f_at(n):
        nm = n**m; k = 0
        while k + 1 < m and Xpow[k + 1] <= nm: k += 1
        assert Xpow[k] <= nm < Xpow[k + 1]
        h = iv.log(iv.mpf(n)) / width - k
        h = iv.mpf([max(h.a, 0), min(h.b, 1)])
        return corr[k] + h*(corr[k+1] - corr[k])
    return f_at

ok = 0; worst = None
for line in open(sys.argv[1]):
    t = line.split()
    if not t: continue
    T, X, Q = int(t[0]), int(t[1]), int(t[2])
    half = [int(z) for z in t[3:35]]
    v = half + [-z for z in reversed(half)]
    assert len(v) == 64
    lo, _, _ = kv.rigorous_margin(Q, X, v)
    f_at = f_table(X, v)
    pen = iv.mpf(0)
    for l in kv.primes_below(X):
        if l < T: continue
        d = iv.mpf(0); n = l
        while n < X:
            d += f_at(n) / iv.sqrt(iv.mpf(n))
            n *= l*l
        d = -4*iv.log(iv.mpf(l))*d
        if d.b > 0:
            pen += iv.mpf([max(d.a, 0), d.b])
    margin = iv.mpf(lo) - pen
    good = margin.a > 0
    ok += good
    if worst is None or margin.a < worst[0]: worst = (margin.a, T, X, Q)
    print(f"T={T:5d} X={X:5d} Q={Q:.4e}  margin > {mp.nstr(mp.mpf(margin.a), 8)}  {'OK' if good else 'FAIL'}", flush=True)
print(f"robust rows verified: {ok}/26 ; smallest margin {mp.nstr(mp.mpf(worst[0]), 8)} at T={worst[1]}")
