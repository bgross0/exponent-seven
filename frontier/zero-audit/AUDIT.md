# Independent audit of the local zero obstruction

Date: 26 November 2026. This audit concerns the research draft at
`a4e01114ef231c168e8da06501c3aa3c72284e52`, `frontier/README.md` and
`frontier/zero_rectangle.py`. It does not claim a compiled Lean theorem,
unconditional classification, or mathematical novelty.

## Result and limits

I found no fatal mathematical error in the draft's explicit formula,
smoothed-Haar kernel, or low/high-zero estimates. The factor of 2 in the prime
sum, gamma term, and Fourier normalization agree with the classical formula.
The proposed conclusion is a necessary condition on a hypothetical large
exponent-seven field; it does not exclude that field unconditionally.

There is a simple useful improvement. Evaluate the logarithmic derivative at
`s=T+1` to control zeros above height `T`. This improves the bound on their
total possible negative contribution from order `T^-2` to order `T^-3`.
With every other estimate unchanged, the same four rows pass at `T=100`
instead of `T=1000`. An elementary improvement in the total weighted zero
mass gives `T=80`. Using the actual sign and variation of the Haar kernel
improves the low-zero estimate further, and all four rows pass at `T=60`.

Subject to the analytic lemmas below and the numerical certificates, the
resulting mathematical statement is:

> If a negative fundamental discriminant D has class group of exponent 7 and
> `3.9*10^30 <= |D| <= 10^162`, then `D=-q` for a prime q and the associated
> quadratic Dirichlet L-function has a nontrivial zero `beta+i*t` with
> `beta > 51/100` and `|t| <= 60`.

This is an audited research argument. The analytic lemmas and arithmetic
certificates still need to be connected and checked in Lean before presenting
it as a machine-checked theorem. No result concerning an alleged proof of
GRH, quasi-GRH, or a new conductor ceiling is used in this implication. The
upper endpoint `10^162` is simply the endpoint of the finite interval covered.

## 1. Arithmetic reduction and exact quantifiers

Use the project's unconditional genus-theory and norm-equation theorems.
Exponent exactly 7 implies `D=-q`, where q is prime and q is 3 modulo 4.
A split prime p satisfies

`4*p^7 = x^2 + q*y^2`, with `y>=1`,

and consequently `q<=4*p^7`. For a row `(X,Qmin,Qmax)` with
`4*X^7 < Qmin <= q <= Qmax`, every prime p below X is therefore inert.
Since X<q, no such prime is ramified. This includes p=2. Thus the character
value is `chi(p)=-1` for every p<X and `chi(p^k)=(-1)^k`.

All four original integer endpoint tests pass. Adjacent intervals meet, so
there is no uncovered gap. The zero conclusion is strict in beta and
nonstrict in height. If no zero has `beta>1/2+d` and `|t|<=T`, reflection
under the functional equation also excludes `beta<1/2-d` at those heights.
Thus every low zero lies in `|beta-1/2|<=d`, including boundary zeros.

## 2. Kernel identities

Let `L=log X`, `a=99*L/200`, `b=L/200`, and `N=2a-2b=49L/50`.
Let g0 equal +1 on [-a,0), -1 on [0,a), and zero elsewhere, and let
`w_b=(1/(2b))*1_[-b,b]`. Put `g=g0*w_b`.

The support of g is [-L/2,L/2]. The autocorrelation R0 of g0 is even, and
for u>=0 is `2a-3u` on [0,a], `u-2a` on [a,2a], and zero afterward.
Convolving R0 with `w_b*w_b` gives R. Because `2b<a`, its value at zero is
`2a-3 E|V|=2a-2b=N`, where V has the triangular density `w_b*w_b` and
`E|V|=2b/3`. Therefore `f=R/N` is an even normalized autocorrelation, has
support [-L,L], and satisfies f(0)=1 and |f(u)|<=1.

The second derivative of R0 in the sense of distributions has coefficients
`(-1,4,-6,4,-1)` at `(-2a,-a,0,a,2a)`. Integrating twice against the triangular
kernel gives exactly the truncated-cubic formula in the draft and code.
There is no missing sign or scale factor.

With `G(z)=integral g(t)*exp(i*z*t) dt`, direct integration gives

`G(z) = -2i*(1-cos(a*z))*sin(b*z)/(b*z^2)`.

Thus the Fourier transform of f is

`H(z)=G(z)G(-z)/N = 4*(1-cos(a*z))^2*sin(b*z)^2/(N*b^2*z^4)`.

The apparent singularity at zero is removable. H is entire, nonnegative on
the real axis, and decays as `O(|Re z|^-4)` in every fixed horizontal strip.
These are stronger than the explicit formula's required decay assumptions.

## 3. Explicit formula and convergence

Primary source: Carneiro, Milinovich, Quesada-Herrera, and Ramos,
*Fourier optimization, the least quadratic non-residue, and the least prime
in an arithmetic progression*, arXiv:2404.08380v2, Lemma 9, equation (3.1):
<https://arxiv.org/html/2404.08380v2#S3>.

Their Fourier transform is `hhat(v)=integral h(t)*exp(-2*pi*i*t*v)dt`.
For h=H, Fourier inversion gives `Hhat(v)=2*pi*f(2*pi*v)`. Consequently
their conductor term becomes `log(q/pi)` and their prime term becomes

`P = 2*sum_{p^k<X} (-1)^k*log(p)*f(log(p^k))/sqrt(p^k)`.

The gamma-factor integral equals `psi(3/4)+J_f`, with

`J_f = integral_0^infty 2*exp(-3u/2)/(1-exp(-2u))*(1-f(u)) du`.

To see the gamma term's sign directly, use the integral representation of
`Re psi(3/4+i*t/2)-psi(3/4)`, substitute v=2u, and use Fourier inversion.
The integrand before interchanging integrals is nonnegative because H(t)>=0
for real t and `1-cos(tu)>=0`, so Tonelli applies. The displayed positive
J term is correct.

Thus, unconditionally,

`sum_rho H((rho-1/2)/i) = log(q/pi)+psi(3/4)+J_f-P`.

All zeros are counted with multiplicity. The character is primitive and
nonprincipal, so no principal-character pole terms occur. The completed
L-function has no trivial zeros; its zeros lie in the open critical strip.
The `O(t^-4)` decay and the usual zero count imply absolute convergence of
this zero sum. The weighted sums used below also converge absolutely.

The draft's existing formalized GRH inequality is not automatically a
formalized version of this unconditional identity for g. That bridge remains
a proof obligation, rather than something established by running Python.

## 4. Archimedean error

R0 is 3-Lipschitz; convolution with a probability density preserves this.
Since R(0)=N, `1-f(u)<=3u/N` for u>=0. Expanding the positive geometric
series in J and using Tonelli yields

`J_f <= (3/N)*sum_{k>=0} 2/(3/2+2k)^2 <= 14/(3N)`.

The last series bound is its first term 8/9 plus the integral 2/3. This is
loose but valid. In particular it applies beyond the support of f as well.

## 5. Real logarithmic derivative and the improved global zero mass

For real sigma>1 the Hadamard partial-fraction identity is

`sum_rho (sigma-beta)/((sigma-beta)^2+t^2)`
`= (log q-log pi+psi((sigma+1)/2))/2 + Re L'/L(sigma)`.

One way to justify the absence of an unknown Hadamard constant is to pair
zeros under the functional equation about s=1/2. The paired logarithmic
derivative has no linear exponential term; central zeros, if present, are
included with their multiplicity. The real-part sum is absolutely convergent.
The project's in-house partial-fraction development is the intended formal
source for this identity.

At sigma=2, put A0=2-beta in (1,2). The inequality

`A0/(A0^2+t^2) >= 1/(2*(1+t^2))`

is immediate after multiplication by positive denominators. The Euler
product and `Lambda(n)<=log n` give

`|L'/L(2)| <= sum_{n>=2} log(n)/n^2`
`<= log(2)/4 + integral_2^infty log(x)/x^2 dx`
`= 1/2 + 3*log(2)/4`.

The summand is decreasing for x>=2. Combining this with
`psi(3/2)=2-gamma-2log2` proves

`Z := sum_rho 1/(1+t^2) <= log q + kappa`,
`kappa := 3-gamma-(log2)/2-log pi < 1`.

The interval verifier encloses kappa in `[0.931480,0.931481]`. We use the
simpler bound `Z<=log Qmax+1` for the height-80 and height-60 profiles.
The original bound `Z<=log Qmax+4` is valid and also retained as a baseline.

An optional, unused refinement is available from reflection symmetry.
Pair A0 and 3-A0. If v=A0*(3-A0) is in [2,9/4] and s=t^2, then

`9*(v+s)*(1+s)-4*(v^2+(9-2v)*s+s^2)`
`=v*(9-4v)+(17v-27)*s+5*s^2 >=0`.

This gives `Z<=(3/4)*(log q+kappa)<(3/4)*(log q+1)`. No reported numerical
profile uses this refinement; it is recorded for a later optimization pass.

## 6. Original low-zero estimate

Write `z=t+i*eta`, with |eta|<=d. Set C0 to the real-frequency Fourier
transform of `g(u)*cosh(eta*u)` and S0 to that of `g(u)*sinh(eta*u)`.
Since g is real,

`G(z)=C0-S0`, `G(-z)=conjugate(C0+S0)`,
`Re H(z)=(|C0|^2-|S0|^2)/N >= -|S0|^2/N`.

The draft's bounds `||g||_1<=2a` and `||g'||_1<=4` are valid. They give

`A=(2a*sinh(dL/2))^2/N`,
`B=(4*sinh(dL/2)+2ad*cosh(dL/2))^2/N`,
`Re H(z)>=-min(A,B/t^2)>=-(A+B)/(1+t^2)`.

The first expression uses A at t=0. The final inequality follows by splitting
at `t^2=B/A`; it is valid also if A or B vanishes. Summing the low zeros
therefore costs at most `(A+B)*Z`.

## 7. Sharper low-zero estimate from this particular kernel

For t>=0, g has the following exact shape:

| interval | -g(t) |
| --- | --- |
| [0,b] | t/b |
| [b,a-b] | 1 |
| [a-b,a+b] | (a+b-t)/(2b) |
| [a+b,infinity) | 0 |

In particular g is odd and is nonpositive on the positive half-line. For
eta>=0, the function `g(t)*sinh(eta*t)` is even and nonpositive. Its L1 norm
is consequently the absolute value of its Fourier transform at zero,
and grows monotonically with eta. Evaluating G at i*d gives the improved
bound

`A_exact = 4*(cosh(ad)-1)^2*sinh(bd)^2/(N*b^2*d^4)`.

For the derivative bound, suppose

`sinh(d*(a-b)) >= 2*b*d*cosh(d*(a-b))`.

This sufficient condition is checked with positive interval margin for every
row. Since tanh(x)/x decreases on x>0, it implies
`tanh(eta*(a-b))>=2*b*eta` for every 0<eta<=d.
For t in [a-b,a+b], it follows that
`tanh(eta*t)>=eta*(a+b-t)`. Hence
`(a+b-t)*sinh(eta*t)` is nonincreasing on the tapered interval.

The magnitude of `g(t)*sinh(eta*t)` increases from zero to
`sinh(eta*(a-b))` and then decreases to zero on each half-line. Its total
variation is exactly `4*sinh(eta*(a-b))`, giving

`B_exact = 16*sinh(d*(a-b))^2/N`.

Use the same integration-by-parts and min inequality as above. The improved
low-zero loss is at most `(A_exact+B_exact)*Z`. This estimate requires the
extra shape and monotonicity lemmas in this section; a verifier must not use
it without proving those lemmas. The height-60 profile uses this improvement.

## 8. Improved high-zero estimate

For any nontrivial zero, `|eta|<1/2`. The exact H formula gives

`|H(t+i*eta)| <= C/t^4`,
`C=4*(1+cosh(a/2))^2*cosh(b/2)^2/(N*b^2)`.

This follows from `|cos(a*z)|<=cosh(a/2)`,
`|sin(b*z)|<=cosh(b/2)`, and |z|>=|t|. There is no hypothesis on high zeros.

Let T>=2 be an even integer and set sigma=T+1. The gamma argument is the
integer `1+T/2`, so no new gamma-function evaluator is needed:

`psi((sigma+1)/2)=H_(T/2)-gamma`,

where H_n is the nth harmonic number, an exact rational. For every zero,

`(sigma-beta)/((sigma-beta)^2+t^2) >= T/((T+1)^2+t^2)`.

Also, since sigma>=2,

`|L'/L(sigma)| <= sum log(n)/n^2 <2`.

It follows that

`W_T := sum_rho 1/((T+1)^2+t^2)`
`<= [log Qmax-log pi+H_(T/2)-gamma+4]/(2T)`.

For |t|>T, the function `((T+1)^2+t^2)/t^4` decreases with |t|, so

`sum_{|t|>T} |H((rho-1/2)/i)|`
`<= C*((T+1)^2+T^2)/T^4`
`   *[log Qmax-log pi+H_(T/2)-gamma+4]/(2T)`.

This is the replacement high-zero loss. It has order
`C*(log Qmax+log T)/T^3`. The original estimate had order
`C*log Qmax/T^2` because it used the total mass measured at s=2 even for
zeros with very large |t|.

## 9. Executed numerical checks

`verify_shifted_tail.py` recomputes the original finite prime sum with
`mpmath.iv` at 45 decimal digits, then applies the new losses. It imports the
original file solely for its finite prime-sum implementation and interval
helpers. It is therefore independent of the original high-tail implementation,
but not an independent prime-sum or arithmetic implementation. A separate
integer-only verifier is the appropriate independent check of that trust base.

The numerical margin used here is deliberately broadened to the original
verifier's outward 10^-6 endpoint enclosure before the new losses are
subtracted. Every endpoint in `shifted-tail-result.json` is an integer in units
of 10^-6. The following residuals are valid rounded-down lower endpoints.

| X | original low loss, T=100 | improved Z, T=80 | exact Haar low loss, T=60 |
| ---: | ---: | ---: | ---: |
| 19000 | 1.520509 | 1.012938 | 1.040802 |
| 30000 | 0.723110 | 0.044905 | 0.253505 |
| 100000 | 23.464230 | 22.211112 | 23.119888 |
| 1000000 | 77.406693 | 71.603861 | 75.929004 |

For the fixed original low-zero inequality with `Z<=log Qmax+1`, the first
passing even heights in the four rows are 66, 80, 40, and 44. These are not
claims of optimal heights over different kernels or bounds. The height-60
profile additionally uses Section 7; its complete intervals are in the JSON.

The finite certificate does not compute any L-function zeros. It proves an
inequality which, combined with the analytic statements, forces the existence
of a zero if an exponent-seven field occurs in the specified conductor range.

## 10. Lean handoff and unresolved tasks

The following are the main proof obligations, in dependency order:

1. Extract an unconditional explicit formula for the smoothed test function,
   or a sufficiently general admissible test-function interface, from the
   analytic development. Include the full zero sum and multiplicities.
2. Extract the real logarithmic-derivative identity for arbitrary real
   sigma>1. The choices 2, 61, 81, and 101 need only elementary gamma
   recurrences at integers or half-integers.
3. Prove the Haar convolution, normalization, support, Fourier transform,
   and Lipschitz identities. Prove the additional shape and total-variation
   lemmas before using the height-60 profile.
4. Formalize the pointwise low/high bounds and summation over the reflected
   zero multiset. Use absolute convergence explicitly.
5. Verify each finite prime-power sum and elementary constant enclosure with
   the existing fixed-point numerical framework, plus a prime table through
   one million. This is considerably larger than the current below-6400 table.
6. Compose the certificate with Step 0/Step 1. Keep the result as a separate
   necessary-condition theorem; it does not discharge SearchHigh, SearchLow,
   or the global GRH hypothesis of the classification theorem.

The main remaining mathematical obstacle is to rule out the forced low,
off-line zero uniformly for this class of conductors. Lowering its possible
height does not by itself solve that obstacle, and checking every conductor
individually is not a feasible substitute.
