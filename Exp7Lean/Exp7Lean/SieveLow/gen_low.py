#!/usr/bin/env python3
"""Generator of the kernel-checked certificates of the low-range search (Exp7Lean/SieveLow).

Nothing produced here is trusted by Lean.  A certificate is a list of numbers (windows, wheels,
groups of sieving primes with the inverse of the step, square roots modulo prime powers, the
positions of the survivors); the Lean checkers verify every property they rely on and do the whole
search themselves, in the kernel.  This script does the same search with Python integers (class
`Plan` mirrors the Lean `Task` block for block and bit for bit), in order to know the survivors
that have to be listed, and it checks them against Witness/SurvivorData.lean and, if the file is
there, against lowrange/low_survivors.txt of the C search.

Usage:
  gen_low.py P [--ycut Y] [--budget BYTES] [--out DIR] [--stats] [--verbose] ...
writes DIR/P<p>.lean, containing

  theorem Exp7.SieveLow.P<p>.main :
      LowStatement <p> <QloFull p> 310000000000000000000 (survSlice a n)
  theorem Exp7.searchLow_<p> : LowStatement <p> (QloFull <p>) QLOW survivorQs

The range of q is cut at Qm (see DESIGN.md):
  part B, Qa <= q < Qm : the sieve over q (`QStmt`); each exception is then listed, or has no
                         solution (`NoSol`, a sieve over y);
  part A, Qm <= q < Qb : then y <= Y0, and for each y the sieve over x (`YC`, `rangeOk`), in
                         table mode when the blocks are short.
Qm = floor(S / (Y0 + 1)^2) + 1; --ycut Y0 fixes the cut (default: chosen by the cost model).
--stats prints the plan and the estimated cost without writing the file; the line `STAT` is
  STAT p Y0 ymax sieves sieves_in_table_mode leaves bits exceptions_of_part_B survivors
       est_kernel_s est_elaboration_s generator_s
One file per prime; inside a file the work is cut into declarations whose kernel caches are freed
one after the other (`Elab.async false`), --budget being the estimated size of these caches.
"""
import argparse
import os
import re
import sys
import time
from math import isqrt, log2

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'Sieve'))
from RootsCertGen import make_cert, roots_of, roots_of8  # noqa: E402

QLOW = 310000000000000000000
B = 10 ** 5
SURV_DEFAULT = '/home/zlab/GitHub/exponent-seven/lowrange/low_survivors.txt'

# ---------------------------------------------------------------- cost model (kernel, seconds)
# calibrated on kernel runs, see DESIGN.md
T_LEAF = 0.35e-3     # per leaf: window, mask, exit
T_LEAFT = 0.35e-3    # the same in table mode
T_GRP = 60e-6        # per group and leaf
T_BIT = 0.7e-9       # per bit, group and leaf (a shift and an `and` of kernel literals)
T_BITBIG = 0.7e-9
T_CACHE = 4e5
T_NODE = 30e-6       # per child tested in the wheel
T_TAB = 30e-6        # per unit of modulus, for the dilated pattern of one modulus (per task)
T_Y = 1.5e-3         # per y with a sieve: fixed cost (roots, checks, task)
T_ROOT8 = 0.35e-3    # per root modulo y^2: the lifts modulo 8 y^2
T_YTAB = 2e-3        # per y in table mode: fixed cost
T_YNONE = 0.06e-3    # per y without roots
T_ELAB = 8e-3        # elaboration of one full certificate (about 2 ms per list literal)
T_ELABT = 3e-3       # elaboration of one certificate in table mode
T_TABY = 0.3e-3      # table mode: per y and sieving prime actually used
T_DIL = 58e-6        # table mode: per entry of the dilation tables (once per declaration)
T_ELEM = 23e-6       # one step of the scan of the list of survivors
T_EXC = 70e-3        # one exception of the sieve over q (elaboration and check of `nosolOk`)
C_A = 5e-3           # part A, per y (average over all y), used to choose the cut
C_LEAF = 30e3        # bytes of kernel cache per leaf
C_LEAFT = 60e3       # the same in table mode (all the group steps included)
C_GRP = 2e3          # bytes per group and leaf
C_BIT = 0.26         # bytes per bit, group and leaf


def t_bit(n):
    return T_BITBIG if n > T_CACHE else T_BIT


def is_prime(n):
    return n > 1 and all(n % d for d in range(2, isqrt(n) + 1))


SMALL = [l for l in range(3, 400) if is_prime(l)]


def rows_full():
    out = []
    for name, a, b in (('Basic.lean', 'def bootstrapRows', 'def allRows'),
                       ('Low.lean', 'def lowRows', 'def fullRows')):
        txt = open(os.path.join(HERE, '..', name)).read()
        out += [(int(q), int(x)) for q, x in
                re.findall(r'⟨(\d+), (\d+)⟩', txt[txt.index(a):txt.index(b)])]
    return out


def qlo_full(p):
    return max([B] + [q for q, x in rows_full() if x <= p])


def survivor_qs():
    txt = open(os.path.join(HERE, '..', 'Witness', 'SurvivorData.lean')).read()
    a = txt.index('def survivorQs')
    b = txt.index(']', a)
    return [int(t) for t in re.findall(r'\d+', txt[txt.index('[', a):b])]


def factor(n):
    f = {}
    d = 2
    while d * d <= n:
        while n % d == 0:
            f[d] = f.get(d, 0) + 1
            n //= d
        d += 1 if d == 2 else 2
    if n > 1:
        f[n] = f.get(n, 0) + 1
    return f


def jacobi_neg_is_minus_one(q, l):
    """(-q / l) = -1 for the odd prime l."""
    return pow((-q) % l, (l - 1) // 2, l) == l - 1


# ---------------------------------------------------------------- the three families (Lean: Fam)
class FamX:
    """Lean `famX S L y`: condB modulo the primes 3 <= l < min(L, 400), l not dividing y."""

    def __init__(self, S, L, y):
        self.S, self.L, self.y = S, L, y
        self.name = 'famX'

    def avail(self):
        return [l for l in SMALL if l < self.L and self.y % l != 0]

    def cond(self, l, r):
        return pow((r * r + (l - self.S % l)) % l, l // 2, l) == l - 1


class FamQ:
    """Lean `famQ L`: Euler's criterion for -q."""

    def __init__(self, L):
        self.L = L
        self.name = 'famQ'

    def avail(self):
        return [l for l in SMALL if l < self.L]

    def cond(self, l, r):
        return pow((l - r) % l, l // 2, l) == l - 1


class FamY:
    """Lean `famY p S q`: y not 0 mod p; S - q y^2 not a non-residue modulo the primes m."""

    def __init__(self, p, S, q):
        self.p, self.S, self.q = p, S, q
        self.name = 'famY'

    def avail(self):
        return [self.p] + [m for m in SMALL if m != self.p]

    def cond(self, m, r):
        if m == self.p:
            return r != 0
        return pow((self.S % m + (m - self.q % m) * (r * r)) % m, m // 2, m) != m - 1


_tab_cache = {}


def table(F, key, l):
    """Residues r mod l with cond l r (key identifies the family)."""
    k = (key, l)
    if k not in _tab_cache:
        if len(_tab_cache) > 4000:
            _tab_cache.clear()
        _tab_cache[k] = [F.cond(l, r) for r in range(l)]
    return _tab_cache[k]


def tile(w, mask, depth):
    b = mask
    for d in range(depth):
        b |= b << (w * 2 ** d)
    return b


class Plan:
    """A Lean `Task` together with its bases, and the simulation of the kernel computation."""

    def __init__(self, F, key, bases, step0, Xa, Xb, top, rest, sieve, gmin=400, single=False,
                 depth=None):
        self.F, self.key, self.bases, self.step0 = F, key, bases, step0
        self.Xa, self.Xb, self.top, self.rest = Xa, Xb, top, rest
        self.stepTop = step0
        for m in top:
            self.stepTop *= m
        self.stepF = self.stepTop
        for m in rest:
            self.stepF *= m
        step = self.stepF
        self.nmax = (max(Xb - Xa, 0) + step - 1) // step
        pmax = max(self.nmax, gmin)
        groups, cur, prod = [], [], 1
        for l in sieve:
            if cur and (single or prod * l > pmax):
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
                comps.append(l)
            d = 1
            while min(g) * 2 ** d < P + self.nmax:
                d += 1
            if depth is not None:
                assert single and d <= depth
                d = depth
            self.groups.append((P, inv, d, comps))
        self.exc = []
        self.nleaves = 0
        self.bits = 0
        self.grpsteps = 0
        self.frontier_len = None

    # -- simulation ------------------------------------------------------------------------
    def pats(self):
        out = []
        full = None
        for P, inv, d, comps in self.groups:
            acc = (1 << (P + self.nmax)) - 1
            for l in comps:
                t = table(self.F, self.key, l)
                bits = 0
                for j in range(l):
                    if t[self.stepF * j % l]:
                        bits |= 1 << j
                acc &= tile(l, bits, d)
            out.append((P, inv, acc))
        return out

    def run(self):
        """Simulate the task; fills exc (sorted), nleaves, bits, frontier_len."""
        pats = self.pats()
        Xa, Xb, stepF = self.Xa, self.Xb, self.stepF
        exc = []
        nleaves = bits = grpsteps = 0
        # frontier
        nodes, step = list(self.bases), self.step0
        for m in self.top:
            t = table(self.F, self.key, m)
            nodes = [b + step * c for b in nodes for c in range(m) if t[(b + step * c) % m]]
            step *= m
        self.frontier_len = len(nodes)
        rest = self.rest
        tabs = [table(self.F, self.key, m) for m in rest]

        def walk(b, step, i):
            nonlocal nleaves, bits, grpsteps
            if i == len(rest):
                b1 = b + step * ((max(Xa - b, 0) + step - 1) // step)
                n = (max(Xb - b1, 0) + step - 1) // step
                nleaves += 1
                bits += n
                acc = (1 << n) - 1
                for P, inv, tl in pats:
                    if acc == 0:
                        break
                    grpsteps += 1
                    acc &= tl >> (b1 * inv % P)
                while acc:
                    low = acc & -acc
                    exc.append(b1 + step * (low.bit_length() - 1))
                    acc ^= low
                return
            m, t = rest[i], tabs[i]
            for c in range(m):
                x = b + step * c
                if t[x % m]:
                    walk(x, step * m, i + 1)

        for b in nodes:
            walk(b, step, 0)
        self.exc = sorted(exc)
        self.nleaves, self.bits, self.grpsteps = nleaves, bits, grpsteps
        return self.exc

    # -- cost ------------------------------------------------------------------------------
    def setup_time(self):
        t = sum(l for P, inv, d, comps in self.groups for l in comps) * T_TAB
        t += sum(self.top + self.rest) * T_TAB
        return t

    def est_time(self):
        """Kernel time, from the counts of the simulation."""
        n = self.bits / max(self.nleaves, 1)
        tb = t_bit(n)
        gsteps = self.grpsteps
        return (self.setup_time() + self.nleaves * T_LEAF + gsteps * T_GRP
                + tb * n * gsteps
                + T_NODE * self.nleaves * (2 if self.rest or self.top else 0)
                + len(self.exc) * self.nleaves * 3e-6)

    def est_mem(self):
        n = self.bits / max(self.nleaves, 1)
        return (self.nleaves * C_LEAF + self.grpsteps * (C_GRP + C_BIT * n)
                + sum(P + self.nmax for P, inv, d, comps in self.groups) / 8 * 6)

    # -- Lean ------------------------------------------------------------------------------
    def lean_task(self, exc_name=None):
        flat = []
        for P, inv, d, comps in self.groups:
            assert P >= 1 and inv >= 1 and d >= 1 and min(comps) >= 1
            flat += [0, P, inv, d] + comps
        gs = str(flat)
        ex = exc_name if exc_name else '[' + ', '.join(map(str, self.exc)) + ']'
        return 'Task.mk %d %d %d %s %s %s %s' % (
            self.step0, self.Xa, self.Xb, str(self.top), str(self.rest), gs, ex)


def lean_cert(cert):
    e2, s0, odd = cert
    ents = ', '.join('OddEntry.mk %d %d %s %d' % (l, e, 'none' if r is None else '(some %d)' % r,
                                                  inv) for (l, e, r, inv) in odd)
    return 'Cert.mk %d %d [%s]' % (e2, s0, ents)


def choose_wheel(F, key, avail, nbases, step0, Xa, Xb, maxbits, margin, force=None):
    """Number of wheel primes (minimising the estimated time) and the sieving primes."""
    counts = [sum(table(F, key, l)) for l in avail[:14]]
    best = None
    leaves, step, walk = float(nbases), step0, 0.0
    for k in range(0, len(counts) + 1):
        n = (max(Xb - Xa, 0) + step - 1) // step
        K = min(len(avail) - k, int(log2(leaves * n + 2)) + margin)
        g = min(K, log2(n + 2) + 2)
        est = leaves * (T_LEAF + g * (T_GRP + t_bit(n) * n)) + walk \
            + T_TAB * sum(avail[k:k + K])
        if n <= maxbits and (best is None or est < best[0]):
            best = (est, k, K)
        if force is not None and k == force:
            best = (est, k, K)
            break
        if k == len(counts) or n <= 1:
            break
        walk += leaves * avail[k] * T_NODE + avail[k] * T_TAB
        leaves *= counts[k]
        step *= avail[k]
    if best is None:
        raise RuntimeError('no wheel gives blocks of at most %d bits' % maxbits)
    est, k, K = best
    return avail[:k], avail[k:k + K], est


def cut_frontier(F, key, wheel, nbases, leafmem, budget):
    """Split the wheel into top and rest so that the leaves below one class of the frontier fit
    in the budget; returns (top, rest, chunk estimate of classes per shard)."""
    counts = [sum(table(F, key, l)) for l in wheel]

    def below(c):
        r = 1.0
        for d in counts[c:]:
            r *= d
        return r
    cut = 0
    while cut < len(wheel) and below(cut) * leafmem > budget / 2:
        cut += 1
    chunk = max(1, int(budget / (below(cut) * leafmem)))
    return wheel[:cut], wheel[cut:], chunk


# ---------------------------------------------------------------- part A: one y
def depth_for(nmax, depths):
    """Tiling depth of table mode (among the allowed ones): l + nmax <= l * 2^d for l >= 3."""
    for d in depths:
        if 3 * 2 ** d >= 3 + nmax:
            return d
    raise RuntimeError('no depth for blocks of %d bits' % nmax)


class YPlan:
    """Certificate for one y of part A.  `prep` classifies y and computes the roots; the sieve is
    planned later (`finish_full`, or `finish_tab` with the sieving primes of the range)."""

    def __init__(self, p, S, Qa, Qb, y, a):
        self.p, self.S, self.Qa, self.Qb, self.y, self.a = p, S, Qa, Qb, y, a
        self.kind = None
        self.depth = None
        self.shards = None
        self.surv = []
        self.time = T_YNONE
        self.mem = 2e3
        self.elab = 0.2e-3
        if y % p == 0:
            self.kind = 'skip'
            return
        f = factor(y)
        for l in sorted(f):
            if l != 2 and pow(S % l, (l - 1) // 2, l) == l - 1:
                self.kind = 'nonres'
                self.l = l
                return
        u = S // 4
        if (y % 4 == 0 and u % 4 != 1) or (y % 8 == 0 and u % 8 != 1):
            self.kind = 'two'
            return
        self.cert = make_cert(S, y)
        yy = y * y
        self.Xb = isqrt(S - Qa * yy) + 1
        self.Xa = isqrt(S - Qb * yy) + 1 if S >= Qb * yy else 0
        assert S - Qa * yy < self.Xb ** 2 and (self.Xa == 0 or (self.Xa - 1) ** 2 + Qb * yy <= S)
        self.F = FamX(S, p, y)
        self.key = ('X', S)
        # table mode: classes modulo y^2 (the sieve does not use q = 3 mod 8)
        self.n = (max(self.Xb - self.Xa, 0) + yy - 1) // yy
        self.kind = 'tab' if self.n <= a.tabmax else 'full'
        if self.kind == 'tab':
            self.bases = roots_of(S, self.cert)
            self.depth = depth_for(self.n, a.depths)
            self.mem = len(self.bases) * C_LEAFT + 20e3
        else:
            self.bases = roots_of8(S, y, self.cert)
        self.cand = len(self.bases) * self.n

    def finish_tab(self, tp):
        a, y = self.a, self.y
        self.plan = Plan(self.F, self.key, self.bases, y * y, self.Xa, self.Xb, [], [],
                         [l for l in tp if y % l != 0], a.gmin, single=True, depth=self.depth)
        self.plan.run()
        self.survivors()
        gmax = 0
        if self.plan.nleaves:
            gmax = min(len(tp), 2 * self.plan.grpsteps // self.plan.nleaves + 2)
        self.time = (T_YTAB + gmax * T_TABY + self.plan.nleaves * T_LEAFT
                     + self.plan.grpsteps * T_GRP + len(self.plan.exc) * 0.1e-3)
        self.elab = T_ELABT

    def finish_full(self):
        a, y, yy = self.a, self.y, self.y * self.y
        F, key, bases, Xa, Xb = self.F, self.key, self.bases, self.Xa, self.Xb
        if Xa >= Xb or not bases:
            wheel, sieve = [], []
        else:
            wheel, sieve, _ = choose_wheel(F, key, F.avail(), len(bases), 8 * yy, Xa, Xb,
                                           a.maxbits, a.margin, a.wheel)
        self.plan = Plan(F, key, bases, 8 * yy, Xa, Xb, [], wheel, sieve, a.gmin)
        self.plan.run()
        self.survivors()
        self.time = T_Y + T_ROOT8 * len(bases) + self.plan.est_time() + len(self.plan.exc) * 0.1e-3
        self.mem = self.plan.est_mem() + 20e3
        self.elab = T_ELAB
        if self.mem > a.budget / 2:
            leafmem = self.mem / max(self.plan.nleaves, 1)
            top, rest, chunk = cut_frontier(F, key, wheel, 1, leafmem, a.budget)
            pl = Plan(F, key, bases, 8 * yy, Xa, Xb, top, rest, sieve, a.gmin)
            pl.exc = self.plan.exc
            nodes, step = list(bases), 8 * yy
            for m in top:
                t = table(F, key, m)
                nodes = [b + step * c for b in nodes for c in range(m) if t[(b + step * c) % m]]
                step *= m
            pl.frontier_len = len(nodes)
            pl.nleaves, pl.bits, pl.grpsteps = self.plan.nleaves, self.plan.bits, self.plan.grpsteps
            per_class = self.mem / max(pl.frontier_len, 1)
            self.chunk = max(1, int(a.budget / per_class))
            self.m = (pl.frontier_len + self.chunk - 1) // self.chunk
            self.plan = pl
            self.shards = self.m
            self.time += self.m * (self.plan.setup_time() + T_Y)

    def survivors(self):
        """The x left by the sieve: listed (true survivors of the search) or with a witness."""
        S, p, y = self.S, self.p, self.y
        self.wits = []
        self.surv = []
        for x in self.plan.exc:
            q, rem = divmod(S - x * x, y * y)
            assert rem == 0 and self.Qa <= q < self.Qb, (y, x)
            if q % 8 != 3:
                assert self.kind == 'tab'
                continue
            bad = [l for l in range(3, p, 2) if is_prime(l) and not jacobi_neg_is_minus_one(q, l)]
            if not bad:
                self.surv.append((x, q))
            else:
                assert bad[0] < 400, 'no witness below 400 for y=%d x=%d' % (y, x)
                if bad[0] not in self.wits:
                    self.wits.append(bad[0])

    def lean_xc(self):
        return 'XC.mk (%s) (%s) %s' % (lean_cert(self.cert), self.plan.lean_task(),
                                       str(self.wits))

    def lean_yc(self):
        if self.kind == 'skip':
            return 'YC.skip'
        if self.kind == 'nonres':
            return 'YC.nonres %d' % self.l
        if self.kind == 'two':
            return 'YC.two'
        if self.kind == 'tab':
            e2, s0, odd = self.cert
            flat = []
            for (l, e, r, inv) in odd:
                assert l >= 1 and e >= 1 and r >= 1 and inv >= 1
                flat += [0, l, e, r, inv]
            return 'YC.tab (XT.mk %d %d %s %d %d %s %s)' % (
                e2, s0, str(flat), self.Xa, self.Xb, str(self.plan.exc), str(self.wits))
        return 'YC.full (' + self.lean_xc() + ')'


# ---------------------------------------------------------------- part B
def plan_q(p, Qa, Qm, a, top_force=None):
    """The sieve over q in [Qa, Qm): list of Plans (the range may be cut in several windows)."""
    F = FamQ(p)
    key = ('Q', p)
    avail = F.avail()
    wheel, sieve, est = choose_wheel(F, key, avail, 1, 8, Qa, Qm, a.maxbits, a.margin + 4, a.qwheel)
    return F, key, wheel, sieve, est


def est_q(p, Qa, Qm, a):
    """Estimated time of part B, with the expected number of exceptions."""
    if Qm <= Qa:
        return 0.0
    dens = 1.0
    for l in range(3, p, 2):
        if is_prime(l):
            dens *= (l - 1) / (2 * l)
    try:
        return plan_q(p, Qa, Qm, a)[4] + (Qm - Qa) / 8 * dens * T_EXC
    except RuntimeError:
        return float('inf')


def nosol_plan(p, S, q, a):
    """Sieve over y showing that S - q y^2 is never a square for y prime to p; returns the Plan,
    or the list of solutions y if there are some."""
    Xb = isqrt(S // q) + 1
    assert S < q * Xb * Xb
    F = FamY(p, S, q)
    key = ('Y', p, q)
    avail = F.avail()
    K = min(len(avail), int(log2(Xb + 2)) + a.margin + 6)
    while True:
        pl = Plan(F, key, [0], 1, 0, Xb, [], [], avail[:K], a.gmin)
        ex = pl.run()
        if not ex:
            return pl, []
        sols = [y for y in ex if y % p != 0 and isqrt(S - q * y * y) ** 2 == S - q * y * y]
        if sols:
            return None, sols
        if K == len(avail):
            raise RuntimeError('NoSol sieve does not terminate for q = %d' % q)
        K = min(len(avail), K + 8)


# ---------------------------------------------------------------- output helpers
def wrap(items, indent='  ', width=99):
    lines = [indent + '[']
    for i, s in enumerate(items):
        s = s + (', ' if i < len(items) - 1 else '')
        if len(lines[-1]) + len(s) > width and len(lines[-1]) > len(indent) + 1:
            lines[-1] = lines[-1].rstrip()
            lines.append(indent + ' ')
        lines[-1] += s
    lines[-1] = lines[-1].rstrip() + ']'
    return '\n'.join(lines)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('p', type=int)
    ap.add_argument('--out', default=HERE)
    ap.add_argument('--ycut', type=int, default=None, help='Y0: part A does y <= Y0')
    ap.add_argument('--budget', type=float, default=6e8,
                    help='estimated bytes of kernel cache per declaration')
    ap.add_argument('--maxbits', type=int, default=3000000, help='largest block length')
    ap.add_argument('--margin', type=int, default=5,
                    help='sieving primes beyond log2(number of candidates)')
    ap.add_argument('--gmin', type=int, default=400,
                    help='groups of sieving primes have product <= max(block length, GMIN)')
    ap.add_argument('--wheel', type=int, default=None, help='(testing) wheel primes in part A')
    ap.add_argument('--qwheel', type=int, default=None, help='(testing) wheel primes in part B')
    ap.add_argument('--ymax', type=int, default=None,
                    help='(testing) part A only for y <= YMAX: the file proves `UpTo` only')
    ap.add_argument('--ymin', type=int, default=None,
                    help='(testing) with --ymax: only the y in [YMIN, YMAX], as `rangeOk` theorems')
    ap.add_argument('--rangelen', type=int, default=1500, help='largest number of y per range')
    ap.add_argument('--tabmax', type=int, default=3000,
                    help='table mode for the y whose blocks have at most TABMAX bits')
    ap.add_argument('--tabk', type=int, default=24,
                    help='largest number of sieving primes in table mode')
    ap.add_argument('--depths', default='3,6', help='tiling depths allowed in table mode')
    ap.add_argument('--tmargin', type=int, default=2,
                    help='table mode: sieving primes beyond log2(number of candidates)')
    ap.add_argument('--survivors', default=SURV_DEFAULT,
                    help='low_survivors.txt of the C search, for the cross-check (if present)')
    ap.add_argument('--name', default=None)
    ap.add_argument('--stats', action='store_true', help='print the plan only')
    ap.add_argument('--verbose', action='store_true')
    ap.add_argument('--profile', action='store_true', help='(testing) Lean profiler output')
    a = ap.parse_args()
    p = a.p
    assert is_prime(p) and 3 <= p < 2760
    t0 = time.time()
    S = 4 * p ** 7
    Qa, Qb = qlo_full(p), QLOW
    name = a.name or 'P%d' % p
    ymax = isqrt(S // Qa) if Qa <= S else 0
    # ---- the cut
    if a.ycut is not None:
        Y0 = min(a.ycut, ymax)
    else:
        Y0, best = ymax, None
        cands = sorted(set([ymax] + [y for y in (int(40 * 1.25 ** i) for i in range(40))
                                     if y < ymax]))
        for y in cands:
            qm = max(Qa, S // (y + 1) ** 2 + 1) if y < ymax else Qa
            est = y * C_A + est_q(p, Qa, qm, a)
            if best is None or est < best:
                best, Y0 = est, y
    Qm = max(Qa, S // (Y0 + 1) ** 2 + 1) if Y0 < ymax else Qa
    if Qm == Qa:
        Y0 = ymax
    assert S < Qm * (Y0 + 1) ** 2
    print('p=%d S=%d Qa=%d ymax=%d  cut: Y0=%d Qm=%d' % (p, S, Qa, ymax, Y0, Qm), flush=True)

    out = ['/- Generated by Exp7Lean/SieveLow/gen_low.py (p = %d, Y0 = %d, budget %g). -/'
           % (p, Y0, a.budget),
           'import Exp7Lean.SieveLow.Assembly', '',
           '/- One declaration at a time: the kernel caches are freed before the next. -/',
           'set_option Elab.async false', 'set_option maxRecDepth 100000',
           'set_option linter.all false', ''] + (
               ['set_option profiler true', 'set_option profiler.threshold 20', '']
               if a.profile else []) + [
           'namespace Exp7.SieveLow.%s' % name, '',
           'open Exp7.Sieve Exp7.Roots', '']
    surv_found = set()
    est_time = est_elab = 0.0

    # ---- part B
    qexc = []
    if Qm > Qa:
        F, key, wheel, sieve, est = plan_q(p, Qa, Qm, a)
        pl0 = Plan(F, key, [3], 8, Qa, Qm, [], wheel, sieve, a.gmin)
        pl0.run()
        leafmem = pl0.est_mem() / max(pl0.nleaves, 1)
        top, rest, chunk = cut_frontier(F, key, wheel, 1, leafmem, a.budget)
        pl = Plan(F, key, [3], 8, Qa, Qm, top, rest, sieve, a.gmin)
        nodes, step = [3], 8
        for m in top:
            t = table(F, key, m)
            nodes = [b + step * c for b in nodes for c in range(m) if t[(b + step * c) % m]]
            step *= m
        pl.exc = pl0.exc
        qexc = pl0.exc
        nfr = len(nodes)
        m = (nfr + chunk - 1) // chunk
        tq = pl0.est_time() + m * (pl0.setup_time() + 0.02)
        est_time += tq
        print('part B: q in [%d, %d): wheel %s, %d sieving primes, %d leaves of <= %d bits, '
              '%.3g bits, frontier %d, %d shards, %d exceptions, est %.1f s' % (
                  Qa, Qm, wheel, len(sieve), pl0.nleaves, pl0.nmax, pl0.bits, nfr, m, len(qexc),
                  tq), flush=True)
        out.append('/-! ## Part B: the sieve over `q`, `%d ≤ q < %d` -/\n' % (Qa, Qm))
        out.append('noncomputable def qexc : List ℕ :=\n%s\n' % wrap(list(map(str, qexc))))
        out.append('noncomputable def qt : Task :=\n  %s\n' % pl.lean_task('qexc'))
        out.append('theorem qt_header : qHeader %d %d %d qt %d %d = true := by decide +kernel\n'
                   % (p, Qa, Qm, chunk, m))
        for i in range(m):
            out.append('theorem qt_s%d : qt.shardOk (famQ %d) [] [3] %d %d = true := by decide +kernel'
                       % (i, p, chunk, i))
        lines = ['\ntheorem qstmt : QStmt %d %d %d qexc :=' % (p, Qa, Qm),
                 '  q_sound qt_header ((Task.shardsUpTo_zero _ _ _ _ _)']
        for i in range(m):
            lines.append('    |>.succ qt_s%d' % i)
        out.append('\n'.join(lines) + ')\n')
    # exceptions of part B
    exc_steps = []
    for i, e in enumerate(qexc):
        pl, sols = nosol_plan(p, S, e, a)
        if sols:
            surv_found.add(e)
            exc_steps.append((e, None))
            if a.verbose:
                print('  exception q=%d: solutions y=%s (survivor)' % (e, sols))
        else:
            est_time += pl.est_time()
            out.append('noncomputable def n%d : Task :=\n  %s\n' % (i, pl.lean_task()))
            out.append('theorem n%d_ok : nosolOk %d %d %d n%d = true := by decide +kernel\n'
                       % (i, p, S, e, i))
            exc_steps.append((e, 'n%d_ok' % i))
            if a.verbose:
                print('  exception q=%d: no solution (%d sieving moduli)' % (
                    e, sum(len(g[3]) for g in pl.groups)))

    # ---- part A
    ylast = Y0 if a.ymax is None else min(Y0, a.ymax)
    yfirst = 1 if a.ymin is None else a.ymin
    a.depths = [int(d) for d in a.depths.split(',')]
    a.tabmax = min(a.tabmax, 3 * 2 ** a.depths[-1] - 3)
    availp = [l for l in SMALL if l < p]
    plans = []          # the y in order
    ranges = []         # ('y', YPlan) for a sharded y, or ('r', [YPlan], tp, d)
    cur, cur_mem, cur_d = [], 0.0, None

    def close():
        nonlocal cur, cur_mem, cur_d
        if not cur:
            return
        tabs = [yp for yp in cur if yp.kind == 'tab']
        K = 0
        if tabs:
            K = min(len(availp), a.tabk,
                    max(int(log2(yp.cand + 2)) for yp in tabs) + a.tmargin + 1)
        tp = availp[:K]
        for yp in tabs:
            yp.finish_tab(tp)
        ranges.append(('r', cur, tp, cur_d or 1))
        cur, cur_mem, cur_d = [], 0.0, None

    for y in range(yfirst, ylast + 1):
        yp = YPlan(p, S, Qm, Qb, y, a)
        plans.append(yp)
        if yp.kind == 'full':
            yp.finish_full()
        if yp.shards is not None:
            close()
            ranges.append(('y', yp))
            continue
        if cur and (cur_mem + yp.mem > a.budget or len(cur) >= a.rangelen or
                    (yp.depth is not None and cur_d is not None and yp.depth != cur_d)):
            close()
        cur.append(yp)
        cur_mem += yp.mem
        if yp.depth is not None:
            cur_d = yp.depth
    close()
    sieves = [yp for yp in plans if yp.kind in ('full', 'tab')]
    tA = sum(yp.time for yp in plans)
    est_elab = sum(yp.elab for yp in plans)
    tdil = sum(sum(l * l for l in r[2]) * T_DIL for r in ranges if r[0] == 'r')
    for yp in sieves:
        for x, q in yp.surv:
            surv_found.add(q)
    est_time += tA + tdil
    print('part A: y in [%d, %d], q in [%d, %d): %d sieves (%d in table mode), %d leaves, '
          '%.3g bits, %d listed, %d other exceptions; %d ranges; est %.1f s + tables %.1f s '
          '+ elab %.1f s' % (
              yfirst, ylast, Qm, Qb, len(sieves), sum(yp.kind == 'tab' for yp in sieves),
              sum(yp.plan.nleaves for yp in sieves), sum(yp.plan.bits for yp in sieves),
              sum(len(yp.surv) for yp in sieves),
              sum(len(yp.plan.exc) - len(yp.surv) for yp in sieves),
              len(ranges), tA, tdil, est_elab), flush=True)
    if a.verbose:
        for r in ranges:
            if r[0] == 'r':
                ys = r[1]
                print('  range y in [%d, %d]: %d sieves, %d leaves, %d group steps, tp %d primes, '
                      'depth %d, est %.2f s' % (
                          ys[0].y, ys[-1].y, sum(yp.kind in ('full', 'tab') for yp in ys),
                          sum(yp.plan.nleaves for yp in ys if yp.kind in ('full', 'tab')),
                          sum(yp.plan.grpsteps for yp in ys if yp.kind in ('full', 'tab')),
                          len(r[2]), r[3], sum(yp.time for yp in ys)
                          + sum(l * l for l in r[2]) * T_DIL))
            else:
                yp = r[1]
                print('  y = %d: %d shards, %d leaves, %.3g bits, est %.2f s' % (
                    yp.y, yp.m, yp.plan.nleaves, yp.plan.bits, yp.time))

    # ---- the survivors of this prime
    allq = survivor_qs()
    pos = {q: i for i, q in enumerate(allq)}
    assert len(pos) == len(allq)
    partial = a.ymax is not None or a.ymin is not None
    missing = [q for q in surv_found if q not in pos]
    assert not missing, 'survivors not in survivorQs: %s' % missing[:5]
    if surv_found:
        idx = sorted(pos[q] for q in surv_found)
        sa, sn = idx[0], idx[-1] - idx[0] + 1
        if not partial:
            assert sn == len(idx), 'the survivors of p are not a contiguous part of survivorQs'
    else:
        sa, sn = 0, 0
    if os.path.exists(a.survivors) and not partial:
        ref = set()
        for line in open(a.survivors):
            f = line.split()
            if f and f[0] == 'S' and int(f[1]) == p:
                ref.add(int(f[4]))
        assert ref == surv_found, 'survivors differ from %s: %d vs %d' % (
            a.survivors, len(ref), len(surv_found))
        print('cross-check: the %d survivors found are those of %s' % (len(ref), a.survivors))
    listed = 'survSlice %d %d' % (sa, sn)
    est_time += len(surv_found) ** 2 / 2 * T_ELEM   # scans of the list of survivors
    print('survivors: %d (slice %d %d); estimated kernel time %.1f s; generator %.1f s' % (
        len(surv_found), sa, sn, est_time, time.time() - t0), flush=True)
    # one line for the projections: p Y0 ymax sieves tab leaves bits exceptions survivors
    # est_kernel est_elab generator
    print('STAT %d %d %d %d %d %d %d %d %d %.1f %.1f %.1f' % (
        p, Y0, ymax, len(sieves), sum(yp.kind == 'tab' for yp in sieves),
        sum(yp.plan.nleaves for yp in sieves), sum(yp.plan.bits for yp in sieves),
        len(qexc), len(surv_found), est_time, est_elab, time.time() - t0), flush=True)
    if a.stats:
        return

    out.append('/-! ## The survivors of `p = %d` -/\n' % p)
    out.append('noncomputable def listed : List ℕ := %s\n' % listed)
    if Qm > Qa:
        lines = ['theorem exc_done : ExcDone %d listed qexc :=' % p, '  (excDone_nil _ _)']
        for e, th in reversed(exc_steps):
            if th is None:
                lines.append('    |>.listed %d (by decide +kernel)' % e)
            else:
                lines.append('    |>.nosol %d (nosolOk_sound\' (by norm_num) %s)' % (e, th))
        out.append('\n'.join(lines) + '\n')
        out.append('theorem partB : LowStatement %d %d %d listed := low_of_q qstmt exc_done\n'
                   % (p, Qa, Qm))

    out.append('/-! ## Part A: the sieve over `x` for `y ≤ %d`, `%d ≤ q < %d` -/\n' % (Y0, Qm, Qb))
    args = '%d %d %d %d %d listed' % (p, S, Qm, Qb, p)
    chain = []
    nr = 0
    for r in ranges:
        if r[0] == 'y':
            yp = r[1]
            y = yp.y
            out.append('noncomputable def x%d : XC :=\n  %s\n' % (y, yp.lean_xc()))
            out.append('theorem x%d_header : x%d.header %d %d %d %d listed %d %d %d = true := by\n'
                       '  decide +kernel\n' % (y, y, S, Qm, Qb, p, y, yp.chunk, yp.m))
            for i in range(yp.m):
                out.append('theorem x%d_s%d : x%d.shardOk %d %d %d %d %d = true := by decide +kernel'
                           % (y, i, y, S, p, y, yp.chunk, i))
            lines = ['\ntheorem y%d : YStmt %s %d :=' % (y, args, y),
                     '  XC.sound (by norm_num) x%d_header ((XC.shardsUpTo_zero _ _ _ _ _)' % y]
            for i in range(yp.m):
                lines.append('    |>.succ x%d_s%d' % (y, i))
            out.append('\n'.join(lines) + ')\n')
            chain.append('    |>.succ y%d' % y)
        else:
            ys, tp, d = r[1], r[2], r[3]
            out.append('noncomputable def r%d : List YC :=\n%s\n' % (
                nr, wrap([yp.lean_yc() for yp in ys])))
            out.append('theorem r%d_ok :\n    rangeOk %s %s %d %d %d r%d = true := by\n'
                       '  decide +kernel\n' % (nr, args, str(tp), d, ys[0].y - 1, ys[-1].y, nr))
            chain.append('    |>.range r%d_ok' % nr)
            nr += 1
    if a.ymin is not None:
        out += ['end Exp7.SieveLow.%s' % name, '']
        out += ['#print axioms Exp7.SieveLow.%s.r%d_ok' % (name, i) for i in range(nr)]
    else:
        out.append('theorem upTo : UpTo %s %d :=\n  (upTo_zero _ _ _ _ _ _)\n%s\n' % (
            args, ylast, '\n'.join(chain)))
        if a.ymax is not None and ylast < Y0:
            out += ['end Exp7.SieveLow.%s' % name, '',
                    '#print axioms Exp7.SieveLow.%s.upTo' % name, '']
        else:
            out.append('theorem partA : LowStatement %d %d %d listed :=\n'
                       '  low_of_upTo\' (Y := %d) (by norm_num) (by norm_num) upTo\n'
                       % (p, Qm, Qb, Y0))
            out.append('/-- The low-range search for `p = %d`. -/' % p)
            if Qm > Qa:
                out.append('theorem main : LowStatement %d %d %d listed := partB.glue partA\n'
                           % (p, Qa, Qb))
            else:
                out.append('theorem main : LowStatement %d %d %d listed := partA\n' % (p, Qa, Qb))
            out += ['end Exp7.SieveLow.%s' % name, '',
                    '/-- The instance `p = %d` of `Exp7.SearchLow`. -/' % p,
                    'theorem Exp7.searchLow_%d :' % p,
                    '    Exp7.SieveLow.LowStatement %d (Exp7.QloFull %d) Exp7.QLOW Exp7.survivorQs :='
                    % (p, p),
                    '  Exp7.SieveLow.lowStatement_of_cert (by decide +kernel) Exp7.SieveLow.%s.main'
                    % name,
                    '', '#print axioms Exp7.searchLow_%d' % p, '']
    os.makedirs(a.out, exist_ok=True)
    path = os.path.join(a.out, name + '.lean')
    open(path, 'w').write('\n'.join(out))
    print('wrote %s (%d bytes)' % (path, os.path.getsize(path)))


if __name__ == '__main__':
    main()
