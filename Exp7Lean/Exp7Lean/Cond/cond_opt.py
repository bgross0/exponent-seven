"""Floating-point search for conditional kernels (the least split prime p is known).

For a prime p, a cut-off X > p and m = 64 equal cells on [0, log X], g is a step function with
values v_0..v_{m-1} and f its normalised autocorrelation.  With chi(l) = -1 for the primes l < p,
chi(p) = +1 and chi(l) = +-1 unknown for the primes p < l < X, GRH and the explicit formula give

    condSum_p(f) - J_f  <=  log(q/pi) + psi(3/4),
    condSum_p(f) = sum_{l<p} T_l(-1) + T_p(+1) + sum_{l>p} min(T_l(+1), T_l(-1)).

This file only *finds* v (floats: smoothed L-BFGS with an exact gradient, several starts) and
rounds it to integers.  The inequality is proved in Lean (Exp7Lean/Cond/Eval.lean); the integer
mirror of that evaluator is cond_mirror.py.

Usage:  python3 cond_opt.py scan p [X ...]     (float values of log Q for several X)
"""
import sys, math, warnings
warnings.simplefilter("ignore")
import numpy as np
from scipy.optimize import minimize

sys.path.insert(0, "/home/zlab/GitHub/exponent-seven")
import kernel_opt

CONST = kernel_opt.CONST
M = 64
_cache = {}


def setup(X, m=M):
    """E, O: per prime l < X the even / odd exponent parts of T_l as linear forms in the
    autocorrelation values c_0..c_m (T_l(s) = (E_l + s O_l) . c);  Gw, Jc: J_f = Jc - Gw . c."""
    if (X, m) in _cache:
        return _cache[(X, m)]
    L = math.log(X); d = L/m
    P = [int(l) for l in kernel_opt.primes_below(X)]
    E = np.zeros((len(P), m + 2)); O = np.zeros((len(P), m + 2))
    for i, l in enumerate(P):
        n = l; k = 1
        while n < X:
            u = math.log(n)/d; j = int(u); th = u - j
            co = 2*math.log(l)/math.sqrt(n)
            T = E if k % 2 == 0 else O
            T[i, j] += co*(1 - th); T[i, j+1] += co*th
            n *= l; k += 1
    _, Gw, Jc = kernel_opt.weights(X, m)
    r = (np.array(P), E[:, :m+1], O[:, :m+1], Gw, Jc)
    _cache[(X, m)] = r
    return r


def corr_of(v):
    m = len(v)
    n = np.array([v[:m-j] @ v[j:] for j in range(m)] + [0.0])
    return n/n[0], n[0]


class Problem:
    def __init__(self, p, X, m=M):
        P, E, O, Gw, Jc = setup(X, m)
        self.m = m; self.Jc = Jc
        lo = P < p; at = P == p; hi = P > p
        assert at.sum() == 1
        self.wfix = (E[lo] - O[lo]).sum(0) + (E[at] + O[at]).sum(0) + E[hi].sum(0) + Gw
        self.Oh = O[hi]

    def value(self, v, eps=0.0):
        c, _ = corr_of(v)
        y = self.Oh @ c
        return float(self.wfix @ c - np.sqrt(y*y + eps*eps).sum() - self.Jc)

    def fg(self, v, eps):
        m = self.m
        c, n0 = corr_of(v)
        y = self.Oh @ c
        r = np.sqrt(y*y + eps*eps)
        val = float(self.wfix @ c - r.sum() - self.Jc)
        gc = self.wfix - (y/r) @ self.Oh
        Mv = gc[0]*v
        for j in range(1, m):
            Mv[j:] += gc[j]/2*v[:m-j]
            Mv[:m-j] += gc[j]/2*v[j:]
        g = 2*(Mv - (gc @ c)*v)/n0
        return -val, -g

    def eig_start(self, signs=None):
        """Top eigenvector for a fixed sign pattern of the unknown primes."""
        w = self.wfix.copy()
        if signs is not None:
            w = w + signs @ self.Oh
        m = self.m
        Mx = np.zeros((m, m))
        for r in range(m):
            for s in range(m):
                j = abs(r - s)
                Mx[r, s] = w[0] if j == 0 else w[j]/2
        vals, vecs = np.linalg.eigh(Mx)
        return vecs[:, -1]

    def optimise(self, starts, iters=3000):
        best_v, best_val = None, -1e99
        for v0 in starts:
            v = np.array(v0, dtype=float)
            v = v/np.linalg.norm(v)
            for eps in (3e-2, 1e-2, 3e-3, 1e-3, 3e-4, 1e-4, 3e-5, 1e-5, 1e-6):
                r = minimize(self.fg, v, args=(eps,), jac=True, method="L-BFGS-B",
                             options={"maxiter": iters, "maxfun": 4*iters, "ftol": 1e-15,
                                      "gtol": 1e-10})
                v = r.x/np.linalg.norm(r.x)
            val = self.value(v)
            if val > best_val:
                best_val, best_v = val, v
        return best_val, best_v


def resample(vp, Lp, X, m=M):
    """The step function with values vp on [0, Lp), sampled at the cell midpoints of [0, log X)."""
    d = math.log(X)/m; dp = Lp/len(vp)
    out = np.zeros(m)
    for j in range(m):
        t = (j + 0.5)*d
        i = int(t/dp)
        out[j] = vp[i] if i < len(vp) else 0.0
    return out


def starts_for(p, X, pr, m=M):
    st = []
    st.append(pr.eig_start())                              # ignore the penalty
    st.append(pr.eig_start(-np.ones(pr.Oh.shape[0])))      # all unknown primes inert
    _, vp = kernel_opt.best(p, m)
    st.append(resample(vp, math.log(p), X, m))             # the unconditional kernel for X = p
    _, vp2 = kernel_opt.best(p + 1, m)
    st.append(resample(vp2, math.log(p + 1), X, m))
    return st


def best(p, X, m=M, extra=()):
    pr = Problem(p, X, m)
    st = starts_for(p, X, pr, m) + [np.array(e, dtype=float) for e in extra]
    # sign-iterated eigenvectors from the best start
    val, v = pr.optimise(st)
    for _ in range(3):
        c, _n = corr_of(v)
        s = -np.sign(pr.Oh @ c)
        v2 = pr.eig_start(s)
        val2, v2 = pr.optimise([v2])
        if val2 > val + 1e-9:
            val, v = val2, v2
        else:
            break
    return val, v


def round_vec(v, scale=10**6):
    v = np.array(v, dtype=float)
    v = v/np.max(np.abs(v))
    if v[0] < 0:
        v = -v
    return [int(round(t*scale)) for t in v]


if __name__ == "__main__":
    if sys.argv[1] == "scan":
        p = int(sys.argv[2])
        need = math.log(4*p**7)
        base = kernel_opt.best(p, M)[0] + CONST
        print("p=%d  log(4p^7)=%.4f  row-type bound (X=p): %.4f" % (p, need, base))
        for X in map(int, sys.argv[3:]):
            val, v = best(p, X)
            vi = np.array(round_vec(v), dtype=float)
            vr = Problem(p, X).value(vi)
            print("  X=%5d  logQ=%.4f  rounded=%.4f  gain=%+.4f  excl=%s" %
                  (X, val + CONST, vr + CONST, val + CONST - base, val + CONST > need), flush=True)
