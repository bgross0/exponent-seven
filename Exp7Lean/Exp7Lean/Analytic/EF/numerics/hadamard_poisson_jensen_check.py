"""Numerical sanity checks for HadamardHF1Poisson.lean / HadamardHF1Boundary.lean.

1. P1 (logDeriv_eq_circleAverage_add_sum): for F = exp(az) * prod (z - a_k)^{m_k},
     F'/F(w) = mean_theta[ 2 zeta/(zeta - w)^2 * log|F(zeta)| ] + sum_{|rho|<R} m_rho (1/(w-rho) + conj(rho)/(R^2 - conj(rho) w)),
   zeta = R e^{i theta}, checked at an interior point w and at w = 0.
2. B2 (norm_kernel_sub_le) and B3 (norm_reflected_sub_le): the worst observed ratio lhs/rhs over
   random samples must be <= 1.

Expected output: the two "lhs"/"rhs" pairs agree to ~1e-14; the last line shows two ratios < 1.
"""
import numpy as np
zeros=[(0.3+0.4j,1),(-0.5+0.2j,2),(1.7-0.3j,1),(0.1-0.9j,3)]
def F(z):
    v=np.exp(0.7*z+0.2j*z)*(1.3-0.4j)
    for a,m in zeros: v=v*(z-a)**m
    return v
def logderiv(z):
    v=0.7+0.2j
    for a,m in zeros: v+=m/(z-a)
    return v
R=1.2
w=0.2-0.3j
n=200000
th=(np.arange(n)+0.5)*2*np.pi/n
zeta=R*np.exp(1j*th)
I=np.mean(2*zeta/(zeta-w)**2*np.log(abs(F(zeta))))
S=sum(m*(1/(w-a)+np.conj(a)/(R**2-np.conj(a)*w)) for a,m in zeros if abs(a)<R)
print("lhs",logderiv(w),"rhs",I+S)
# w=0
w=0
I0=np.mean(2*zeta/(zeta-w)**2*np.log(abs(F(zeta))))
S0=sum(m*(1/(w-a)+np.conj(a)/(R**2-np.conj(a)*w)) for a,m in zeros if abs(a)<R)
print("lhs0",logderiv(0),"rhs0",I0+S0)
# kernel bound check
rng=np.random.default_rng(0)
worst=0;worst2=0
for _ in range(200000):
    R=rng.uniform(0.1,10); z=R*np.exp(1j*rng.uniform(0,2*np.pi)); w=rng.uniform(0,R/2)*np.exp(1j*rng.uniform(0,2*np.pi))
    lhs=abs(2*z/(z-w)**2-2*z/z**2); worst=max(worst,lhs/(20*abs(w)/R**2) if abs(w)>0 else 0)
    rho=rng.uniform(0,R)*np.exp(1j*rng.uniform(0,2*np.pi))
    l2=abs(np.conj(rho)/(R**2-np.conj(rho)*w)-np.conj(rho)/R**2); worst2=max(worst2,l2/(2*abs(w)/R**2) if abs(w)>0 else 0)
print(worst,worst2)
