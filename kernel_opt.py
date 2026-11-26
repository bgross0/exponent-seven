"""Floating-point search for a good positive-definite test function.

For a cut-off X and m equal steps on [0, log X], g is a step function with values v_0..v_{m-1},
f = (g * g~) / |g|^2 is its normalised autocorrelation (piecewise linear, f(0)=1, f=0 beyond log X,
Fourier transform >= 0).  If every prime below X is inert for the odd real primitive character
chi of prime conductor q, the Guinand-Weil explicit formula and GRH give

    sum_{p<X} A_p(f)  <=  log(q/pi) + psi(3/4) + J_f ,
    A_p = 2 log p sum_{k>=1, p^k<X} (-1)^k f(k log p) p^{-k/2},
    J_f = int_0^oo a(u) (1 - f(u)) du,   a(u) = 2 e^{-3u/2} / (1 - e^{-2u}).

The left side minus J_f is linear in f, so it is a Rayleigh quotient in v; the best v is the top
eigenvector.  This file only *finds* v (floats).  kernel_verify.py proves the inequality.
"""
import sys, json, math
import numpy as np


def primes_below(n):
    s = np.ones(n, dtype=bool); s[:2] = False
    for i in range(2, int(n**0.5) + 1):
        if s[i]:
            s[i*i::i] = False
    return np.nonzero(s)[0]


def a_fun(u):
    return 2*np.exp(-1.5*u)/(1 - np.exp(-2*u))


def weights(X, m):
    L = math.log(X); d = L/m
    W = np.zeros(m + 2)
    for p in primes_below(X):
        p = int(p); lp = math.log(p); n = p; sgn = -1
        while n < X:
            kap = 2*sgn*lp/math.sqrt(n)
            u = math.log(n)/d; j = int(u); th = u - j
            W[j] += kap*(1 - th); W[j+1] += kap*th
            n *= p; sgn = -sgn
    # gamma side, Simpson on each cell
    G = np.zeros(m + 2); Jconst = 0.0
    K = 2000
    th = np.linspace(0, 1, K + 1)
    sw = np.ones(K + 1); sw[1:-1:2] = 4; sw[2:-1:2] = 2; sw *= 1.0/(3*K)
    # first cell: (1-c1) * (1/d) int_0^d u a(u) du
    u = th*d
    ua = np.where(u > 0, u*a_fun(np.maximum(u, 1e-300)), 1.0)
    I0 = float(np.sum(sw*ua))  # = (1/d) * int_0^d u a(u) du
    Jconst += I0; G[1] += I0
    for j in range(1, m):
        u = (j + th)*d
        av = a_fun(u)
        A = float(np.sum(sw*av))*d
        A1 = float(np.sum(sw*av*th))*d
        Jconst += A
        G[j] += A - A1; G[j+1] += A1
    Jconst += 4.0/(3*X**1.5*(1 - X**-2.0))
    return W[:m+1], G[:m+1], Jconst


def best(X, m):
    W, G, Jc = weights(X, m)
    w = W + G
    M = np.zeros((m, m))
    for r in range(m):
        for s in range(m):
            j = abs(r - s)
            M[r, s] = w[0] if j == 0 else w[j]/2
    # c_0 = 1 contributes W[0] (G[0] is 0); keep it on the diagonal
    vals, vecs = np.linalg.eigh(M)
    v = vecs[:, -1]
    F = vals[-1] - Jc
    return F, v


CONST = math.log(math.pi) + 0.5772156649015329 - math.pi/2 + 3*math.log(2)  # log(pi) - psi(3/4)


def margin(X, m, Q):
    F, v = best(X, m)
    return F - math.log(Q) + CONST, v


if __name__ == "__main__":
    m = int(sys.argv[1]); Q = float(sys.argv[2])
    for X in map(int, sys.argv[3:]):
        mg, v = margin(X, m, Q)
        print(X, round(mg, 4))
