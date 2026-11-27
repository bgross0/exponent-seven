# Exact arithmetic eligibility: 389.a1, Q(sqrt(-71)), p = 29

This directory independently checks the elementary arithmetic needed for the
proposed localization experiment. It also gives a rational interval proving
that the quadratic-twist central value is positive, using the standard
modularity and functional-equation theorems spelled out below.

**Status:** both Python checkers executed successfully. They use only the
standard library, exact integers and rational numbers. These are reproducible
arithmetic certificates with mathematical interpretations, **not Lean-checked
proofs**. There is no claim here of a rank upper bound, a new BSD theorem, or nonvanishing
of an auxiliary ring-class-character L-value.

## Reproduce

Run from this directory:

```sh
python3 check_eligibility.py --check eligibility.json
python3 check_twist_lvalue.py --check twist-lvalue.json
```

To regenerate the two data files, replace `--check` with `--output`. The second
checker recomputes 6,000 Fourier coefficients and the rational interval in
about 1.3 seconds in the observed environment. The command receipts and hashes
are in `verification.json`.

The primary model identity is

\[
 E=389.a1:\quad y^2+y=x^3+x^2-2x,
 \qquad [a_1,a_2,a_3,a_4,a_6]=[0,1,1,-2,0].
\]

The [LMFDB curve record](https://www.lmfdb.org/EllipticCurve/Q/389a1/) and
[underlying data](https://www.lmfdb.org/EllipticCurve/Q/data/389.a1) identify
this model and the points `(0,0)` and `(1,0)`. The calculations below do not
assume the database's rank, torsion, regulator or BSD fields.

## Eligibility table

| Quantity or hypothesis | Independently checked value | Mathematical interpretation |
|---|---|---|
| Weierstrass invariants | b2=4, b4=-4, b6=1, b8=-3; c4=112, c6=-856 | Direct substitution |
| Discriminant | Delta=389; c4^3-c6^2=1728*389 | Nonsingular, globally minimal integral model |
| Conductor | 389 | Good away from389; multiplicative at 389 |
| Good reduction at 29 | 389 is nonzero modulo29 | Good |
| Point count at 29 | #E(F29)=36, including infinity | a29=-6 |
| Ordinarity at 29 | 29 does not divide -6 | Ordinary |
| Non-anomalous prime | 29 does not divide36 | E(F29)[29]=0 |
| K | O_K=Z[omega], omega^2-omega+18=0 | Fundamental discriminant -71 |
| 29 in K | omega=13 or17 modulo29 | Split |
| 389 in K | (-71/389)=-1 | Inert |
| Discriminant coprimality | gcd(71,389*29)=1 | K unramified at 29 and389 |
| Definite factor N^- | 389 | One inert prime; squarefree, odd number of factors |
| Class number | Seven reduced primitive forms | h_K=7; class group C7 |
| Residual irreducibility | T^2+2T+3 has no root modulo29 | Irreducible Frobenius at 3 |
| Residual ramification | v389(Delta)=1, not divisible by 29 | Nontrivial unipotent inertia via Tate uniformization |
| Absolute irreducibility | Previous two rows combined | Holds over Q and K, by the argument below |

The assertions identifying reduction types, the Frobenius representation, the
class group, and ordinarity use the usual theorems connecting these notions
to the finite calculations. They are not silently counted as Python proofs
of those theorems.

### Minimality, multiplicative reduction and residual inertia

An integral model with discriminant valuation less than12 at every prime is
minimal: an integral improvement would decrease that valuation by a positive
multiple of 12. Here the sole nonzero valuation is v389(Delta)=1. Since c4 is
a 389-adic unit, the reduction is multiplicative, of type I_1. Moreover,

\[
 95^2\equiv -c_6=856\pmod{389},
\]

so it is split multiplicative. Thus the local Tamagawa number is 1 and its
local root number is -1.

For a split Tate curve over Q_389, write its parameter as q_T. The equality
v389(q_T)=v389(Delta)=1 implies that adjoining a 29th root of q_T is ramified.
The action on E[29] therefore contains a nonidentity unipotent matrix. The
prime-to-389 roots of unity are unramified, so this is a statement about the
actual residual inertia action, not just its semisimplification. The standard
criterion is that this action is unramified precisely when29 divides
v389(Delta). See the Tate-curve proof of Proposition 3.4 in
[Ribet, *From the Taniyama-Shimura Conjecture to Fermat's Last Theorem*](https://math.berkeley.edu/~ribet/Articles/toulousela.pdf).
Ribet states that proposition in his semistable example; the Tate-uniformization
argument just given is the general multiplicative-reduction argument used here.

### Irreducibility, including after extension to K

Exact enumeration gives #E(F3)=6, hence a3=-2. The characteristic polynomial
of a good Frobenius on E[29] is

\[
 T^2-a_3T+3=T^2+2T+3.
\]

Its discriminant is -8=21 modulo29, which is not a square; the checker also
exhaustively verifies that the polynomial has no root in F29. A Galois-stable
F29-line would give a Frobenius eigenvalue in F29, a contradiction.

This alone proves irreducibility over F29. To get **absolute** irreducibility,
use the nonidentity unipotent inertia element at 389. Its unique invariant
line over the algebraic closure is its 1-eigenspace, already defined over F29.
Any line invariant under the full representation would have to be this line,
contradicting the preceding F29-irreducibility. This argument needs no database
isogeny computation or classification of subgroups of GL2(F29).

The same proof works on restriction to G_K. The prime3 splits in K, so its
Frobenius polynomial is unchanged at either prime above 3. The extension at 389
is unramified, so the nontrivial inertia element remains available.

### The seven ordinary ideal classes

The complete list of reduced primitive positive definite forms of
discriminant-71 is

\[
 (1,1,18),\quad(2,\pm1,9),\quad(3,\pm1,6),\quad(4,\pm3,5).
\]

The enumeration is exhaustive because a reduced form has
`|b| <= a <= c`, hence `3*a^2 <= 71` and `a <= 4`; the standard boundary
convention removes duplicate reduced forms. The classical form-class
bijection gives h_K=7, and a group of prime order 7 is cyclic. This agrees
with the independently retrieved
[LMFDB number-field record](https://www.lmfdb.org/NumberField/2.0.71.1).

This class number is important for the theta implementation: a formula that
assumes h_K=1 cannot simply be reused. The ring-class decomposition and its
cyclic generator are developed in the parent artifact, not duplicated here.

## Explicit rational points: torsion and independence

Let P=(0,0) and Q=(1,0). Both lie on the curve, and P+Q=(-2,-1).
The certificate gives full point lists at 3,7 and11.

First, E(Q) has no nonidentity torsion. At any good prime ell, reduction is
injective on torsion of order prime to ell. Here the reduction orders are

\[
 \#E(\mathbf F_3)=6,\qquad \#E(\mathbf F_7)=13.
\]

If a rational torsion point had prime order r, then for r=3 reduction at 7
would force3 to divide 13; for r=7 reduction at 3 would force7 to divide 6.
Every other r would have to divide both 6 and 13. All cases are impossible.
Any nonidentity torsion point has a multiple of prime order, so there is no
torsion. In particular P and Q have infinite order.

Second, P and Q are Z-independent. At11 there are 16 points, and the complete
doubling table shows that `2E(F11)` has 4 elements. The reductions of P, Q and
P+Q are all outside this doubling image. Thus P and Q have independent images
in E(F11)/2E(F11).

If a nonzero integer relation aP+bQ=O existed, torsion-freeness would permit
dividing out a common factor until at least one of a,b was odd. Reduction
modulo11 and then modulo the doubling image would contradict the independence
just established. This proves a rank **lower** bound of 2 without any height
approximation. It proves neither a rank upper bound nor saturation of the
subgroup generated by these points.

The same points remain independent after extension to K: a relation among
rational points over K is the same equality of curve points over Q.

As a separate cross-check of the localization agent, exact rational group-law
arithmetic gives

\[
 z([36]P)=-x([36]P)/y([36]P)\equiv203=7\cdot29\pmod{29^2}.
\]

The exact rational coordinates and parameter are in `eligibility.json`.
The formal-log inference is owned by the neighboring `logic/` artifact.

## A certified nonzero quadratic-twist L-value

The second checker proves the following interval, conditional only on the
standard mathematical interpretation of the elliptic-curve L-series described
in this section:

\[
\begin{split}
0.9360088537803042525901954783264223920549
&\le L(E^{(-71)},1)\\
&\le0.9360088573972690020870684844656754102100.
\end{split}
\]

In particular the quadratic-twist central value is nonzero. Every endpoint
and numerical error bound was calculated with integers and fractions; no
floating-point approximations enter this result.

### Model, conductor, character and sign

An integral model for the quadratic twist is

\[
 [0,-71,1,-10082,-89478].
\]

The checker verifies exactly that its invariants are

\[
 c_4'=(-71)^2c_4,\quad c_6'=(-71)^3c_6,\quad
 \Delta'=71^6\cdot389.
\]

It is minimal for the same discriminant-valuation reason as above. At71 it
is a ramified quadratic twist of good reduction; at this residue characteristic
greater than 3 the type is I_0* with conductor exponent 2. At389 it is
multiplicative with conductor exponent 1. All other primes are good. Thus

\[
 N'=389\cdot71^2=1,960,949.
\]

The primitive quadratic character is
`chi_-71(n)=Legendre(n,71)`, with value0 at multiples of 71. The base curve has
global sign +1: its archimedean and sole finite bad local signs are both -1.
The standard coprime quadratic-twist sign formula gives

\[
 w(E^{(-71)})=w(E)\chi_{-71}(-389)=+1.
\]

These conductor and sign facts use the standard local classification and
quadratic-twist functional-equation formula. They are explicit analytic inputs,
not consequences of a positive numerical sum alone.

### Why this finite sum encloses the L-value

By modularity, let `f(z)=sum a_n exp(2*pi*i*n*z)` be the normalized weight 2
newform of the twist. The Mellin formula at the arithmetic center 1 is

\[
 L(E^{(-71)},1)=2\pi\int_0^\infty f(it)\,dt.
\]

Split the integral at `1/sqrt(N')`. The Fricke functional equation with
global sign +1 makes the two pieces equal. Integrating the Fourier expansion
on the upper half therefore gives

\[
 L(E^{(-71)},1)=2\sum_{n\ge1}\frac{a_n}{n}r^n,
 \qquad r=\exp(-2\pi/\sqrt{N'}).
\]

The checker calculates each prime trace of the base curve by finite-field
point counting, except that the split multiplicative trace at 389 is+1. Euler
factor recurrences calculate all coefficients up to6,000, and multiplication
by `chi_-71(n)` gives the twist coefficients. All6,001 entries including a0
and the prime traces are included in `twist-lvalue.json`.

Hasse's bound and the Euler factors give
`|a_n| <= d(n)*sqrt(n) <= 2*n`. Hence the uncomputed tail satisfies

\[
 \left|2\sum_{n>6000}\frac{a_n}{n}r^n\right|
 \le\frac{4r^{6001}}{1-r}<1.809\cdot10^{-9}.
\]

The certificate bounds pi by Machin's exact arctangent identity with
alternating-series remainders, bounds sqrt(N') with integer square roots,
then bounds r by the alternating exponential series. Powers, the finite
sum and the tail are rounded outwards at integer scale 10^40. The resulting
interval is separated from zero by more than 0.93.

Thus the interval is an elementary rational numerical proof once modularity,
the stated conductor/sign, the Mellin/Fricke identity and the Hasse bound are
accepted. A Lean translation must import or prove those statements as well
as checking the finite arithmetic; it cannot replace them with new axioms and
call the result a formal proof.

## What remains outside this certificate

The [Castella-Hsieh paper](https://web.math.ucsb.edu/~castella/Kato-print.pdf)
requires further global and auxiliary-character conditions in addition to
the local eligibility checks. In particular positivity of `L(E^(-71),1)`
does not establish `L(E/K,chi,1) != 0` for a chosen ring-class character.
The theta calculation and a correct account of all ideal classes remain
separate tasks. Nor does the point-independence proof establish the necessary
Selmer upper bound or localization injectivity. The neighboring logic audit
tracks those distinctions.

The numerical and finite certificates here use no ERH/GRH assumption and no
conjectural BSD formula. Their standard algebraic and analytic interpretation
theorems are stated explicitly so a future formal proof can target the real
interfaces.
