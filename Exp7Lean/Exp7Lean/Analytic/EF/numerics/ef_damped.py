# Check the damped identity  Z(delta) = R(delta)  used in the blueprint (delta >= 0):
#  Z(delta) = sum_gamma (1/pi) int h(t) delta/(delta^2+(t-gamma)^2) dt = sum_gamma 2 int_0^L f(u) e^{-delta u} cos(gamma u) du
#  R(delta) = log(q/pi) + psi(3/4+delta/2) + int_0^oo 2 e^{-(3/2+delta)u}(1-f(u))/(1-e^{-2u}) du
#             - 2 sum_{n<X} Lambda(n) chi(n) f(log n) n^{-1/2-delta}
import sys, math
from mpmath import mp, mpf, mpc, quad, exp, log, pi, sqrt, digamma, findroot, dirichlet, cos, sin, inf, loggamma, im, re
mp.dps = 18
q = int(sys.argv[1]); X = int(sys.argv[2]); delta = mpf(sys.argv[3]); T = float(sys.argv[4])
L = log(X)
def leg(n):
    n %= q
    return 0 if n == 0 else (1 if pow(n, (q-1)//2, q) == 1 else -1)
chi = [leg(n) for n in range(q)]
def vonM(n):
    if n < 2: return mpf(0)
    p = next(d for d in range(2, n+1) if n % d == 0); m = n
    while m % p == 0: m //= p
    return log(p) if m == 1 else mpf(0)
f = lambda u: max(mpf(0), 1 - abs(u)/L)          # v = [1]
R = (log(q/pi) + digamma(mpf(3)/4 + delta/2)
     + quad(lambda u: 2*exp(-(mpf(3)/2+delta)*u)/(1-exp(-2*u))*(1-f(u)), [0, L/2, L, 2*L, inf])
     - 2*sum(vonM(n)*leg(n)*f(log(n))*mpf(n)**(-mpf(1)/2-delta) for n in range(1, X)))
def H(g):  # closed form of 2 int_0^L (1-u/L) e^{-delta u} cos(g u) du = 2 Re int_0^L (1-u/L) e^{-(delta - i g)u} du
    z = mpc(delta, -g)
    return 2*re(1/z - (1-exp(-z*L))/(L*z*z))
def Zf(t):
    s = mpc(0.5, t); th = im(loggamma((s+1)/2)) + t/2*log(q/pi)
    return re(exp(1j*th)*dirichlet(s, chi))
zs = []; step = 0.05; prev = Zf(mpf(1e-9))
for k in range(1, int(T/step)+1):
    t1 = k*step; cur = Zf(t1)
    if cur*prev < 0: zs.append(findroot(Zf, (t1-step, t1), solver='anderson'))
    prev = cur
Zsum = 2*sum(H(g) for g in zs)
# mean tail: H(delta,gamma) ~ 2*(delta + 1/L)/gamma^2 on average (kink of f e^{-delta|u|} at 0 has slope jump 2(delta+1/L))
tail = (2*(float(delta)+1/float(L))/math.pi)*(math.log(q*T/(2*math.pi))+1)/T
print("q,X,delta", q, X, delta, " zeros:", len(zs), " Z(|gamma|<=T) =", Zsum, " tail ~", tail, " Z ~", Zsum+tail, "  R =", R, " diff", R-Zsum-tail)
