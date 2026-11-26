# Numerical sanity check of the Guinand-Weil identity in the normalisation of Statement.lean:
#   sum_gamma h(gamma) = log(q/pi) + psi(3/4) + J_f - 2 sum_{n<X} Lambda(n) chi(n) f(log n)/sqrt(n)
# for chi = Legendre symbol mod q (q prime, q = 3 mod 4), f = normalised autocorrelation of g,
# h(t) = |int g(x) e^{itx} dx|^2 / int g^2.
import sys
from mpmath import mp, mpf, mpc, quad, exp, log, pi, sqrt, digamma, euler, gamma, arg, findroot, dirichlet, cos, sin, inf, loggamma, im, re
mp.dps = 20
q = int(sys.argv[1]); X = int(sys.argv[2]); mode = sys.argv[3]; T = float(sys.argv[4])
L = log(X)
def leg(n):
    n %= q
    if n == 0: return 0
    return 1 if pow(n, (q-1)//2, q) == 1 else -1
chi = [leg(n) for n in range(q)]
def vonM(n):
    if n < 2: return mpf(0)
    m = n; p = None
    for d in range(2, n+1):
        if m % d == 0:
            p = d; break
    while m % p == 0: m //= p
    return log(p) if m == 1 else mpf(0)
if mode == 'step':      # v = [1]
    f = lambda u: max(mpf(0), 1 - abs(u)/L)
    h = lambda t: L if t == 0 else 4*sin(t*L/2)**2/(L*t**2)
else:                   # smooth g(x) = sin(pi x/L)^2 on [0,L]: fast decay of h
    g = lambda x: sin(pi*x/L)**2 if 0 <= x <= L else mpf(0)
    n2 = quad(lambda x: g(x)**2, [0, L])
    f = lambda u: quad(lambda x: g(x)*g(x+abs(u)), [0, max(mpf(0), L-abs(u))])/n2 if abs(u) < L else mpf(0)
    def h(t):
        G = quad(lambda x: g(x)*exp(1j*t*x), [0, L/2, L])
        return abs(G)**2/n2
primeSum = 2*sum(vonM(n)*leg(n)*f(log(n))/sqrt(n) for n in range(1, X))
J = quad(lambda u: 2*exp(-mpf(3)/2*u)/(1-exp(-2*u))*(1-f(u)), [0, L/2, L, 2*L, inf])
psi34 = -euler + pi/2 - 3*log(2)
assert abs(psi34 - digamma(mpf(3)/4)) < mpf(10)**(-15)
rhs = log(q/pi) + psi34 + J - primeSum
print("q,X,mode", q, X, mode, " primeSum", primeSum, " J", J, " log(q/pi)+psi34+J", log(q/pi)+psi34+J)
# zeros of L(1/2+it, chi): Z(t) real
def Z(t):
    s = mpc(0.5, t)
    th = im(loggamma((s+1)/2)) + t/2*log(q/pi)
    return re(exp(1j*th)*dirichlet(s, chi))
zs = []; step = 0.05; t = 0.0; prev = Z(mpf(0)+1e-9)
import math
N = int(T/step)
for k in range(1, N+1):
    t1 = k*step; cur = Z(t1)
    if prev == 0 or cur*prev < 0:
        zs.append(findroot(Z, (t1-step, t1), solver='anderson'))
    prev = cur
NT = T/math.pi*math.log(q*T/(2*math.pi*math.e))
print("zeros found in (0,T]:", len(zs), " main term of N(T)/2:", NT, " first:", [float(z) for z in zs[:3]])
zsum = 2*sum(h(z) for z in zs)   # zeros come in pairs +-gamma (real chi); gamma=0 not a zero here
tail = (2/(math.pi*float(L)))*(math.log(q*T/(2*math.pi))+1)/T if mode == 'step' else 0.0
print("zero sum (|gamma|<=T):", zsum, " + mean tail estimate:", tail, " =", zsum+tail)
print("arithmetic side  log(q/pi)+psi(3/4)+J-primeSum:", rhs)
print("difference:", rhs-(zsum+tail))
