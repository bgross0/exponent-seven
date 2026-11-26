#!/usr/bin/env python3
"""Generator of the kernel-checked sieve certificates (Exp7Lean/Sieve/Bridge.lean).

Nothing produced here is trusted by Lean: the certificate is a small list of numbers (levels of
the residue tree, groups of sieving primes with the inverse of the step, tiling depths), and the
Lean checker verifies every property it relies on (`YCert.header`) and does the whole search
itself (`YCert.shardOk`), in the kernel.

Usage:
  gen.py P [--robust | --q Q] [--budget BYTES] [--out DIR] [--stats]
writes DIR/P<p>.lean (or P<p>R.lean with --robust, P<p>Q.lean with --q), containing

  theorem Exp7.Sieve.P<p>.prime : PrimeStatement <p> <Q>

and, for the default bound Q = Qlo p, `theorem Exp7.search_<p>` in the form of `SearchHigh`.
--robust uses QloR(p) = max(Qlo p, max {Q : T <= p}) over the rows of
sieve-reduction/robust26.txt.  One file per prime; inside a file the work is cut into shard
declarations whose kernel caches are freed one after the other (`Elab.async false`), so the
memory of the process is bounded by --budget (plus the imports).
"""
import argparse
import os
import re
from math import isqrt

HERE = os.path.dirname(os.path.abspath(__file__))
QLOW = 310000000000000000000


def rows():
    txt = open(os.path.join(HERE, '..', 'Basic.lean')).read()
    a = txt.index('def bootstrapRows')
    b = txt.index('def allRows')
    return [(int(q), int(x)) for q, x in re.findall(r'⟨(\d+), (\d+)⟩', txt[a:b])]


def qlo(p):
    return max([QLOW] + [q for q, x in rows() if x <= p])


def qlo_robust(p):
    q = qlo(p)
    for line in open(os.path.join(HERE, '..', '..', 'sieve-reduction', 'robust26.txt')):
        f = line.split()
        if len(f) >= 3 and int(f[0]) <= p:
            q = max(q, int(f[2]))
    return q


def is_prime(n):
    return n > 1 and all(n % d for d in range(2, isqrt(n) + 1))


SMALL = [l for l in range(3, 400) if is_prime(l)]


def factor(n):
    f = {}
    d = 2
    while d * d <= n:
        while n % d == 0:
            f[d] = f.get(d, 0) + 1
            n //= d
        d += 1
    if n > 1:
        f[n] = f.get(n, 0) + 1
    return f


def cond_a(S, y, m, r):
    return (r * r + 3 * y * y) % m == S % m


def cond_b(S, l, r):
    return pow((r * r - S) % l, l // 2, l) == l - 1


def test(S, y, lev, r):
    ell, m, kind = lev
    return cond_b(S, m, r) if kind else cond_a(S, y, m, r)


def frontier(S, y, levels):
    nodes, step = [0], 1
    for lev in levels:
        ell, m, kind = lev
        new = []
        for b in nodes:
            # same order as the Lean `flatBelow` (c descending)
            for c in range(ell - 1, -1, -1):
                x = b + step * c
                if test(S, y, lev, x % m):
                    new.append(x)
        nodes, step = new, step * ell
    return nodes, step


def density(S, lev, y):
    ell, m, kind = lev
    if not kind:
        return None
    return sum(cond_b(S, m, r) for r in range(m)) / m


# Cost model, calibrated on kernel runs (see the notes): time per leaf = TA + TB * bits,
# kernel cache per leaf = C0 + C1 * bits.
# (the cost per bit grows with the leaf length when the bitsets leave the CPU caches).
TA, TB, TN0 = 1.2e-3, 0.7e-9, 2e6
C0, C1 = 65e3, 2.2
TSHARD = 0.15      # per shard declaration: the patterns are recomputed


def leaf_time(n):
    return TA + TB * n * (1 + n / TN0)


class YPlan:
    """Certificate for one y."""

    def __init__(self, p, S, Q, y, budget, lmax, maxbits, wheel=None, gmin=400):
        self.y = y
        B = S - Q * y * y
        self.Xb = isqrt(B) + 1
        assert B < self.Xb ** 2
        # levels A: lifting of the roots of x^2 + 3 y^2 = S modulo the prime powers dividing
        # 8 y^2; for each prime the chain is cut after the last level that rejects something
        # (a level that rejects nothing only splits classes: x = r + 2 y^2 t is enough).
        la = []
        nodes, step = [0], 1
        f = factor(8 * y * y)
        for l in sorted(f):
            chain = []
            keep = 0
            nd, st = nodes, step
            for i in range(1, f[l] + 1):
                lev = (l, l ** i, False)
                new = []
                for b in nd:
                    for c in range(l - 1, -1, -1):
                        x = b + st * c
                        if cond_a(S, y, lev[1], x % lev[1]):
                            new.append(x)
                chain.append((lev, new, st * l))
                if len(new) < l * len(nd):
                    keep = i
                nd, st = new, st * l
            for lev, new, st2 in chain[:keep]:
                la.append(lev)
                nodes, step = new, st2
        self.nroots = len(nodes)
        self.stepA = step
        # wheel: levels B; the number of wheel primes minimises the estimated time
        avail = [l for l in SMALL if l < p and y % l != 0 and l <= lmax]
        dens = [sum(cond_b(S, l, r) for r in range(l)) for l in avail]
        best = None
        leaves = float(self.nroots)
        st = step
        for i in range(0, 12):
            n = (self.Xb + st - 1) // st
            est = leaves * leaf_time(n)
            if n <= maxbits and (best is None or est < best[0]):
                best = (est, i)
            if wheel is not None and i == wheel:
                best = (est, i)
                break
            leaves *= dens[i]
            st *= avail[i]
        self.time, nw = best
        lb = [(l, l, True) for l in avail[:nw]]
        for l in avail[:nw]:
            step *= l
        sieve_primes = avail[nw:]
        self.stepF = step
        self.nmax = (self.Xb + step - 1) // step
        # groups of sieving primes: product at most about the leaf length
        pmax = max(self.nmax, gmin)
        groups = []
        cur = []
        prod = 1
        for l in sieve_primes:
            if cur and prod * l > pmax:
                groups.append(cur)
                cur, prod = [], 1
            cur.append(l)
            prod *= l
        if cur:
            groups.append(cur)
        self.groups = []
        for g in groups:
            P = 1
            for l in g:
                P *= l
            inv = pow(step, -1, P)
            comps = []
            for l in g:
                d = 0
                while l * 2 ** d < P + self.nmax:
                    d += 1
                comps.append((l, d))
            self.groups.append((P, inv, comps))
        # cut between top and rest: the kernel cache of the subtree below a frontier node
        # should be well below the budget
        levels = la + lb
        mult = [1.0] * len(la) + [float(d) for d in dens[:nw]]
        leafmem = C0 + C1 * self.nmax

        def below(c):
            r = 1.0
            for d in mult[c:]:
                r *= d
            return r
        cut = len(la)
        while cut < len(levels) and below(cut) * leafmem > budget / 2:
            cut += 1
        self.top, self.rest = levels[:cut], levels[cut:]
        nodes, st = frontier(S, y, self.top)
        self.fr = nodes
        self.F = len(nodes)
        self.chunk = max(1, int(budget / (below(cut) * leafmem)))
        self.m = (self.F + self.chunk - 1) // self.chunk
        self.leaves = self.F * below(cut)
        self.time = self.leaves * leaf_time(self.nmax) + TSHARD * self.m + 0.2

    def lean_cert(self):
        ls = lambda L: '[' + ', '.join('⟨%d, %d, %s⟩' % (e, m, 'true' if k else 'false')
                                       for e, m, k in L) + ']'
        gs = '[' + ',\n    '.join(
            '⟨%d, %d, [%s]⟩' % (P, inv, ', '.join('(%d, %d)' % c for c in comps))
            for P, inv, comps in self.groups) + ']'
        return ('⟨%d, %d,\n  %s,\n  %s,\n  %s⟩' % (self.y, self.Xb, ls(self.top), ls(self.rest), gs))


def plan(p, Q, budget=1e9, lmax=251, maxbits=6000000, wheel=None, ymax=None, gmin=400):
    S = 4 * p ** 7
    Y = isqrt(S // Q)
    assert S < Q * (Y + 1) ** 2 and Q * Y * Y <= S
    ys = range(1, (Y if ymax is None else min(Y, ymax)) + 1)
    return Y, [YPlan(p, S, Q, y, budget, lmax, maxbits, wheel, gmin) for y in ys]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('p', type=int)
    ap.add_argument('--out', default=HERE)
    ap.add_argument('--robust', action='store_true', help='use the bound QloR(p)')
    ap.add_argument('--q', type=int, default=None, help='use this lower bound for q')
    ap.add_argument('--budget', type=float, default=1e9,
                    help='estimated bytes of kernel cache per shard declaration')
    ap.add_argument('--lmax', type=int, default=251, help='largest sieving prime')
    ap.add_argument('--maxbits', type=int, default=6000000, help='largest leaf length')
    ap.add_argument('--wheel', type=int, default=None, help='(testing) number of wheel primes')
    ap.add_argument('--gmin', type=int, default=400, help='groups of sieving primes have product <= max(leaf length, GMIN)')
    ap.add_argument('--name', default=None)
    ap.add_argument('--ymax', type=int, default=None, help='(testing) only y <= YMAX')
    ap.add_argument('--stats', action='store_true', help='print the plan only')
    a = ap.parse_args()
    p = a.p
    assert is_prime(p)
    Q0 = qlo(p)
    Q = a.q if a.q is not None else (qlo_robust(p) if a.robust else Q0)
    Y, plans = plan(p, Q, a.budget, a.lmax, a.maxbits, a.wheel, a.ymax, a.gmin)
    name = a.name or ('P%d%s' % (p, 'Q' if a.q is not None else 'R' if a.robust else ''))
    print('p=%d Q=%d Ymax=%d shards=%d leaves~%.4g bits~%.4g est_time~%.1fs' % (
        p, Q, Y, sum(pl.m for pl in plans), sum(pl.leaves for pl in plans),
        sum(pl.leaves * pl.nmax for pl in plans), sum(pl.time for pl in plans)))
    if a.stats:
        for pl in plans:
            print('  y=%d roots=%d stepA=%d F=%d chunk=%d m=%d nmax=%d leaves~%.3g top=%d rest=%d '
                  'groups=%d t~%.1fs' % (pl.y, pl.nroots, pl.stepA, pl.F, pl.chunk, pl.m, pl.nmax,
                                        pl.leaves, len(pl.top), len(pl.rest), len(pl.groups),
                                        pl.time))
        return
    Sx = '(4 * %d ^ 7)' % p
    out = ['/- Generated by Exp7Lean/Sieve/gen.py (p = %d, Q = %d, budget %g). -/' % (p, Q, a.budget),
           'import Exp7Lean.Sieve.Bridge', 'import Exp7Lean.Basic', '',
           '/- One declaration at a time: the kernel caches of a shard are freed before the next. -/',
           'set_option Elab.async false', '',
           'namespace Exp7.Sieve.%s' % name, '']
    for pl in plans:
        out.append('noncomputable def c%d : YCert :=\n  %s\n' % (pl.y, pl.lean_cert()))
        fr = ['  [']
        for i, b in enumerate(pl.fr):
            s = str(b) + (', ' if i < len(pl.fr) - 1 else '')
            if len(fr[-1]) + len(s) > 99:
                fr[-1] = fr[-1].rstrip()
                fr.append('   ')
            fr[-1] += s
        fr[-1] += ']'
        out.append('noncomputable def f%d : List ℕ :=\n%s\n' % (pl.y, '\n'.join(fr)))
        out.append('theorem c%d_header : c%d.header %s %d %d f%d %d %d = true := by decide +kernel\n'
                   % (pl.y, pl.y, Sx, Q, p, pl.y, pl.chunk, pl.m))
        for i in range(pl.m):
            out.append('theorem c%d_s%d : c%d.shardOk %s f%d %d %d = true := by decide +kernel'
                       % (pl.y, i, pl.y, Sx, pl.y, pl.chunk, i))
        lines = ['\ntheorem c%d_ok : YOk %s %d %d %d :=\n  c%d.yOk rfl c%d_header ((YCert.shardsUpTo_zero _ _ _ _)'
                 % (pl.y, Sx, Q, p, pl.y, pl.y, pl.y)]
        for i in range(pl.m):
            lines.append('    |>.succ c%d_s%d' % (pl.y, i))
        out.append('\n'.join(lines) + ')\n')
    assert len(plans) == Y or a.ymax is not None
    out += ['/-- No solution for `p = %d` and `q ≥ %d`. -/' % (p, Q),
            'theorem prime : PrimeStatement %d %d :=' % (p, Q),
            '  prime_of_yOk (Y := %d) (by norm_num) ((yOkUpTo_zero _ _ _)' % len(plans)]
    for pl in plans:
        out.append('    |>.succ c%d_ok' % pl.y)
    out[-1] += ')'
    out += ['', 'end Exp7.Sieve.%s' % name, '']
    if Q == Q0:
        out += ['/-- The instance `p = %d` of `Exp7.SearchHigh`. -/' % p,
                'theorem Exp7.search_%d : ∀ x y q : ℕ, 1 ≤ y → 4 * %d ^ 7 = x ^ 2 + q * y ^ 2 →' % (p, p),
                '    Exp7.Qlo %d ≤ q → q %% 8 = 3 →' % p,
                '    (∀ l, l.Prime → 3 ≤ l → l < %d → jacobiSym (-(q : ℤ)) l = -1) → False := by' % p,
                '  intro x y q hy hS hq h8 hj',
                '  have hQ : (%d : ℕ) ≤ Exp7.Qlo %d := by decide +kernel' % (Q, p),
                '  exact Exp7.Sieve.%s.prime x y q hy hS (hQ.trans hq) h8 hj' % name,
                '', '#print axioms Exp7.search_%d' % p, '']
    else:
        out += ['#print axioms Exp7.Sieve.%s.prime' % name, '']
    os.makedirs(a.out, exist_ok=True)
    open(os.path.join(a.out, name + '.lean'), 'w').write('\n'.join(out))


if __name__ == '__main__':
    main()
