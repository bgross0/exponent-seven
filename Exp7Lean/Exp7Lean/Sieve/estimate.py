#!/usr/bin/env python3
"""Estimated kernel time of the certificates for all primes 701 <= p <= 4297 (cost model of
gen.py), for the bound Qlo p (default) or QloR p (--robust).  Output: one line per prime, totals."""
import sys
import gen

robust = '--robust' in sys.argv
tot = 0.0
n = 0
rows = []
for p in range(701, 4298):
    if not gen.is_prime(p):
        continue
    Q = gen.qlo_robust(p) if robust else gen.qlo(p)
    Y, plans = gen.plan(p, Q)
    t = sum(pl.time for pl in plans)
    sh = sum(pl.m for pl in plans)
    lv = sum(pl.leaves for pl in plans)
    bits = sum(pl.leaves * pl.nmax for pl in plans)
    rows.append((p, Y, sh, lv, bits, t))
    print('%d Ymax %d shards %d leaves %.4g bits %.4g est_s %.1f' % (p, Y, sh, lv, bits, t), flush=True)
    tot += t
    n += 1
act = [r for r in rows if r[1] > 0]
print('TOTAL primes %d active %d shards %d leaves %.4g bits %.4g est_hours %.2f max_s %.0f' % (
    n, len(act), sum(r[2] for r in rows), sum(r[3] for r in rows), sum(r[4] for r in rows),
    tot / 3600, max(r[5] for r in rows)))
