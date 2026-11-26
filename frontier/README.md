# Frontier: an unconditional necessary zero condition for a large exponent-seven field

26 November 2026. Research draft. The following argument uses classical analytic number theory and a finite interval computation. It does NOT assume GRH, but its conclusion is a necessary condition on a counterexample, not a proof that no counterexample exists. No novelty or peer-review claim is made. The analytic derivation and interval implementation require independent review; no Lean proof of this extension has yet been compiled.

## Candidate theorem

Let D be a negative fundamental discriminant with class group of exponent 7. If
3.9*10^30 <= |D| <= 10^162, then D=-q with q prime, q=3 mod 4, and L(s,chi_q) has a zero rho=beta+i*t with beta>51/100 and |t|<=1000.

Equivalently, the entire interval is excluded if the relevant characters satisfy beta<=51/100 for nontrivial zeros of height at most 1000. No hypothesis on high zeros is required. By functional-equation symmetry this low-height hypothesis implies |beta-1/2|<=1/100. It is a much weaker hypothesis than full GRH, but still far from a verified unconditional exclusion for all such conductors.

## Derivation

Use Step 0 and Step 1 of exponent-seven, which are unconditional. For any split prime p, q<=4*p^7. For each row (X,Qmin,Qmax), 4*X^7<Qmin<=q<=Qmax. Also X<q. Thus every prime p<X is inert; chi_q(p)=-1.

Put L=log X, a=99*L/200, b=L/200. Let g0 be +1 on [-a,0), -1 on [0,a), and zero elsewhere. Let w_b be the probability density 1/(2b) on [-b,b]. Let g=g0*w_b, N=integral g^2, and f(u)=integral g(t)g(t+u)dt/N.

The support of g is [-L/2,L/2]. The support of f is [-L,L]. The unsmoothed autocorrelation R0(u) for u>=0 is 2a-3u for u<=a, u-2a for a<=u<=2a, and 0 beyond. Convolution by w_b twice gives R. Since 2b<a and the triangular distribution w_b*w_b has mean absolute value 2b/3, N=R(0)=2a-2b. Equivalently
R(u)= sum_{(c,k)} c*((u-k+2b)_+^3-2*(u-k)_+^3+(u-k-2b)_+^3)/(24*b^2),
where (c,k)=(-1,-2a),(4,-a),(-6,0),(4,a),(-1,2a). Thus f=R/N is piecewise cubic with exact rational coefficients in u/L. The verifier evaluates those polynomials with interval arithmetic.

Let G(z)=integral g(t) exp(izt)dt, H(z)=G(z)G(-z)/N=integral f(u) exp(izu)du. In particular H is entire, nonnegative on the real axis, and
H(z)=4*(1-cos(a*z))^2*sin(b*z)^2/(N*b^2*z^4)
with a removable singularity at zero. It decays as O(|Re z|^-4) on every fixed horizontal strip.

The classical Guinand-Weil explicit formula (same normalization as Exp7Lean/Exp7Lean/Analytic/Statement.lean, but retaining the zero sum rather than replacing it by positivity under GRH) gives
sum_rho H((rho-1/2)/i) = log(q/pi) + psi(3/4) + J_f - P,
where nontrivial zeros are counted with multiplicities,
P=2*sum_{p^k<X} (-1)^k*log(p)*f(log(p^k))/sqrt(p^k),
J_f=integral_0^infty 2*exp(-3u/2)/(1-exp(-2u))*(1-f(u))du,
psi(3/4)=-gamma+pi/2-3log2.
The expression is real by symmetry; take real parts term by term. This identity is unconditional. The test function meets the usual analyticity and decay conditions. The existing formalization of the GRH inequality does not itself establish this general identity for this smoothed test function; extracting/formalizing it is a separate obligation.

Since R0 is 3-Lipschitz and convolution by a probability density preserves this bound, 1-f(u)<=3u/N. The integrand is nonnegative by Cauchy-Schwarz. Expanding the positive geometric series and integrating yields
J_f <= (3/N)*sum_{k>=0} 2/(3/2+2k)^2 <= 14/(3N).
The last inequality uses the first term 8/9 and the integral from zero to infinity, 2/3.

### Unconditional weighted zero-mass bound

Write rho=beta+i*t. The completed nonprincipal primitive L-function has all its zeros in 0<beta<1. The real logarithmic derivative identity at s=2 gives
sum_rho (2-beta)/((2-beta)^2+t^2) = (log q)/2 + Re(gammaFactor'/gammaFactor)(2) + Re(L'/L)(2).
For the odd character the gamma-factor term equals (psi(3/2)-log pi)/2<0, from psi(3/2)=2-gamma-2log2. The Euler-product estimate
|L'/L(2)| <= sum_{n>=2} Lambda(n)/n^2 <= sum_{n>=2} log(n)/n^2 < 2
follows by bounding the decreasing summand by the first term plus its integral. If A0=2-beta in [1,2], then A0/(A0^2+t^2)>=1/(2*(1+t^2)). Hence
Z:=sum_rho 1/(1+t^2) <= log q+4 <= log Qmax+4.
The repo's analytic Hadamard partial-fraction work should be reusable for this bound.

### Low-zero contribution without positivity on the critical line

Suppose all zeros with |t|<=T satisfy |beta-1/2|<=d. For z=t+i*eta with |eta|<=d, write
C0=Fourier(g*cosh(eta*u))(t), S0=Fourier(g*sinh(eta*u))(t).
Because g is real, G(z)=C0-S0, G(-z)=conj(C0+S0).
Thus Re H(z)=(|C0|^2-|S0|^2)/N >= -|S0|^2/N.
We have ||g||_1<=2a and ||g'||_1<=4 by convolution and the total variation of g0. Use the direct L1 bound and integration by parts:
A=(2a*sinh(d*L/2))^2/N,
B=(4*sinh(d*L/2)+2a*d*cosh(d*L/2))^2/N.
Consequently Re H(t+i*eta)>=-min(A,B/t^2)>=-(A+B)/(1+t^2), with the first expression interpreted using A at t=0. Summing gives low-zero loss <=(A+B)*Z.

### High-zero contribution without ANY GRH or quasi-GRH assumption

For any nontrivial zero |eta|<1/2. The explicit H formula and |cos(a*z)|<=cosh(a/2), |sin(b*z)|<=cosh(b/2), |z|>=|t| imply
|H(z)| <= C/|t|^4,
C=4*(1+cosh(a/2))^2*cosh(b/2)^2/(N*b^2).
For |t|>T, (1+t^2)/t^4 <= (1+T^2)/T^4. Summing gives high-zero loss <=C*(1+T^2)/T^4*Z. No zeros are computed, and no zero-free hypothesis is used here.

### Certificate inequality

Combining both sides, the absence of a zero with beta>1/2+d and |t|<=T is impossible if
P-14/(3N)+log(pi)-psi(3/4)-log Qmax
  -[(A+B)+C*(1+T^2)/T^4]*(log Qmax+4)>0.
This is precisely what the verifier checks. The low-zero assumption beta<=1/2+d also gives beta>=1/2-d by the functional equation and conjugation.

## Executed interval checks

All rows have d=1/100, T=1000. Endpoints are exact integers; four cutoffs are small compared with the conductors. Residuals below are rounded DOWN.

| X | Qmin | Qmax | prime-power terms | residual > |
|---:|---:|---:|---:|---:|
| 19000 | 3.9e30 | 1e32 | 2222 | 1.548594 |
| 30000 | 1e32 | 1e40 | 3320 | 0.754336 |
| 100000 | 1e40 | 1e60 | 9700 | 23.506603 |
| 1000000 | 1e60 | 1e162 | 78734 | 77.515170 |

Run python frontier/zero_rectangle.py (mpmath, sympy). The four rows were executed independently using the same interval evaluation with exact rational coefficients. The result JSON contains outward-rounded endpoints in units of 10^-6. The numerical part uses mpmath.iv at 45 decimal digits; it is not yet a kernel-verified computation. The hardcoded gamma enclosure is the one already independently certified by independent/verify_constants.py. The prime enumeration and interval library remain part of the trust base.

## Why this is strategically relevant

A recent preprint, Bhattacharjee, "Split Primes and the Exponent of Imaginary Quadratic Class Groups" (11 Nov 2026), Theorem 2/Table 1, claims the exponent-seven ceiling 10^161.39 under H(7/8), i.e. all Dirichlet L-functions zero-free to the right of 7/8. OpenAI's 30 Sep 2026 quasi-RH preprint and companion Lean development claim this hypothesis. Both source results require their own review. If those claims are accepted, the four rows cover the entire gap from the old ERH ceiling to the weaker proposed ceiling, subject only to the local low-zero condition on the relevant characters. This does not eliminate that condition.

The practical obstacle is not numerical precision or zero summation at high height. It is proving a uniform exclusion of the low, off-line zeros in this enormous conductor family, or exploiting the exponent-seven condition itself to rule them out. Checking individual conductors is infeasible. No quantum speedup has been demonstrated for that uniform analytic problem.

Parallel unconditional route: revisit Heath-Brown, Forum Math. 20 (2008), 275-283, whose square-sieve argument establishes finiteness for exponent 5/<=6. Combine its two-split-prime norm equations with modern pointwise 7-torsion methods and explicit zero-density estimates. A bound h_7(q) << q^(1/2-epsilon) for every q (as opposed to almost every q), combined with Siegel's class-number lower bound, would already prove unconditional finiteness; effectivity and an explicit usable ceiling are further separate challenges.

Sources:
- EKN, arXiv:1803.02056 (2020), norm equation / existing classification bounds.
- Carneiro et al., arXiv:2404.08380, Lemma 9 (explicit formula).
- Bhattacharjee, https://www.preprints.org/manuscript/202611.1131 (weaker-hypothesis ceiling).
- OpenAI, https://github.com/openai/math/tree/main/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026 (proposed H(7/8)).
- Heath-Brown, https://doi.org/10.1515/FORUM.2008.014 (unconditional finiteness for exponents 5 and 6).
