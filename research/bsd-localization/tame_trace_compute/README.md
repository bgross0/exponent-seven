# Two tame traces, computed

`compute_traces.py` computes the actual two tame traces of the eight CM input
families already specified in `../reflected_pilot/`, through **q^128 modulo
5^5**. The result is `traces.json`. Its three entries for each input are the
constant, linear, and quadratic Taylor coefficients in the weight coordinate
W. The calculation extends the CM arithmetic to q^9088 and then applies an
exact trace formula. It does not build 72 separate cusp expansions.

This is a calculation of overconvergent modular-form inputs. It does not yet
produce a class in the elliptic curve's proper de Rham cohomology, a value of
the complementary Perrin–Riou regulator, or the finite logarithm of the
reflected global class. Nonzero coefficients of a traced input do not imply
that its projection to the elliptic curve is nonzero.

## Reproduce

From the repository root:

```sh
python research/bsd-localization/tame_trace_compute/compute_traces.py --check
```

Without `--check`, the program writes the deterministic artifact. The default
parameters are `--bound 128 --digits 5`. The finite computation uses only
Python's standard library and the existing CM arithmetic helpers. A default
run took about 6.4 seconds in this environment. No Lean build, CM-point
enumeration, or external algebra system is required.

The full regenerated raw input is hashed and discarded. The saved artifact
contains only the traces, finite verification results, small specialization
fixtures, and provenance. The checker regenerates the input and the result.
The older compressed source is pinned by its uncompressed SHA256:

```text
80b2b0f5ba32d6a3d45ebb828c21e5bf043226cfd4290b72dd9d81ed8ae830ba
```

## What is being traced

Put K=Q(sqrt(-71)), omega^2-omega+18=0, and
`a=(2,omega)`, so `a^7=(10+omega)`. The coefficient ring is

```text
(Z/3125 Z)[zeta] / (1+zeta+...+zeta^6),
basis 1,zeta,zeta^2,zeta^3,zeta^4,zeta^5.
```

The finite class character satisfies psi(a)=zeta. In the earlier theta
certificate the generator was c=a^4; converting to that convention requires
zeta=zeta_upstream^2. The two embeddings are distinguished by omega=2 or 4
modulo 5.

Write s=kappa-1 and W=6^s-1. The two CM families are g_W for the character
psi and h_W for its **finite class-character inverse**, with the same CM-type
weight exponent. Thus h_W is obtained by zeta -> zeta^-1; it is not the
inverse of the entire varying Hecke character. The cross-oldform inputs are

\[
\Xi_{a,b}(W)=d^{-s}\big((V_a g_W)^{[5]}\big)\,V_bh_W,
\qquad (a,b)=(1,389),(389,1),
\]

where d=q d/dq and V_m acts by q -> q^m. The superscript [5] deletes all
coefficients whose q-exponent is divisible by 5. On the remaining terms,
d^-s multiplies the q^n coefficient by

\[
(1+W)^{-\log_5(n)/\log_5(6)}.
\]

For each cross placement, the artifact also keeps the separately named
variant in which h is 5-depleted. These are genuinely different inputs: for
the V389-g placement their traces already differ at q^9, and for the
V389-h placement they differ at q^28. No Euler-factor equality between the
variants is asserted.

The stored order-two entry is [W^2]Xi, which is one half of its second W
derivative. Multiplication by 2 converts it to that derivative without any
5-adic loss. Conversion to derivatives in kappa requires the chain rule for
W=6^(kappa-1)-1 and is not silently performed.

## Trace normalization and the symmetry that makes this small

Use the normalized slash operator

\[
(F|_k A)(\tau)=\det(A)^{k/2}(c\tau+d)^{-k}F(A\tau).
\]

Let ell=71, M=389, b=-23, and d=-126. Then

\[
W_{71}=\begin{pmatrix}71&-23\\27619&-8946\end{pmatrix},
\quad\det W_{71}=71.
\]

For 0<=j<71, the matrices

\[
\gamma_j=71^{-1}W_{71}\begin{pmatrix}1&j\\0&71\end{pmatrix}
=\begin{pmatrix}1&j-23\\389&389(j-23)+1\end{pmatrix}
\]

together with the identity are complete trace coset representatives. The
program checks every determinant, matrix factorization, and projective
bottom row in P^1(F71). It also checks the analogous representatives at
M=389*25, covering the classical p-depleted level convention.

Summing these cosets gives

\[
\operatorname{Tr}_1(F)
=F+71^{1-k/2}U_{71}(F|_kW_{71}).
\]

At weight two, with trivial product character,

\[
\operatorname{Tr}_1(F)=F+U_{71}(F|W_{71}),\qquad
\operatorname{Tr}_2(F)=F|W_{71}+U_{71}F.
\]

The special CM inputs above satisfy **Xi|W71=Xi**. The reasoning uses three
ingredients: harmonic theta-series Poisson summation gives the Fricke scalar
i^-kappa=-i at classical weights kappa=1 mod4; the two cross-oldform
placements supply a further character factor chi_-71(389)=-1; and the
normalized inverse Bol operator transports the same scalar to the
5-depleted primitive. The two scalar factors in the product therefore
multiply to +1. The inverse-Bol step needs the overconvergent argument:
the quotient in Coleman's Theorem 5.4 is a cohomology space on which U is
invertible, so a U-killed form has a primitive. Bol covariance makes the
difference of the desired transforms have zero d^(kappa-1); its constant
q-expansion is also U-killed and hence zero. Here chi_-71(5)=1 makes the
tame Atkin–Lehner operator commute with the relevant U5 operation.

The analytic family and q-expansion principle extend this identity from the
dense classical weights to all three stored W coefficients. The detailed
theta/Fricke, inverse-Bol, and analytic-family arguments are in
[`../tame_trace_theory/TAME_TRACE.md`](../tame_trace_theory/TAME_TRACE.md).
The Python program does not purport to prove those analytic theorems by
finite q-expansion comparison.

Consequently the **two actual traces coincide**, and each coefficient is
computed by

\[
\boxed{[q^n]\operatorname{Tr}_1\Xi
=[q^n]\operatorname{Tr}_2\Xi
=[q^n]\Xi+[q^{71n}]\Xi.}
\]

This simplification applies to these CM families. For an arbitrary input,
the transformed q-expansion F|W71 is still required.

## Exact regressions and checks

The verification covers the following distinct issues:

| Check | Result |
|---|---:|
| Coset certificates | 72 representatives each at M=389 and M=9725 |
| Regenerated raw input | q^9088, 23,696 ideal representatives |
| Raw overlap against the earlier 12-digit artifact | 98,328 six-coordinate coefficients |
| Trace overlap through q^57 | 1,392 six-coordinate coefficients |
| Log-free algebraic weight-five input and trace specialization | 5,776 six-coordinate coefficients |
| Elliptic oldform trace/recovery identities | 232 exact rational identities |
| Weight-12 Delta trace identities | 12 exact rational identities |

The algebraic weight-five check calculates coefficients with fourth powers
and a Hensel-lifted seventh root of 10+omega. It applies the n^-4 multiplier
and the two oldform placements directly, without logarithms or the jet
formula. Since W=6^4-1 has 5-adic valuation one, the integral W^3 tail
vanishes modulo 125. The check compares the resulting raw inputs through
q^710 and their traces through q^10. Here the theta specialization is
classical; its inverse-Bol primitive is overconvergent.

The weight-12 regression uses
Delta=q product(1-q^n)^24 and the oldbasis
Delta(q), 71^6 Delta(q^71). It verifies the factor 71^-5 in the trace,
using tau(71)=9,791,485,272. This catches a weight-normalization error that
a weight-two-only check would miss.

Every one of the eight traced inputs first becomes nonzero at q^6. Its
constant W coefficient there is zeta+zeta^-1. For example, on the omega=2
branch of `V389_g_depleted_times_h`, the three vectors at q^6 modulo 3125
are

```text
W^0: [3124,    0, 3124, 3124, 3124, 3124]
W^1: [1031,   66, 1031, 1031, 1031, 1031]
W^2: [2379, 2849, 2379, 2379, 2379, 2379]
```

## Oldspace recovery and precision

For E389's normalized form f, an independent count gives #E(F71)=82 and
a71=-10. In the differential-pullback oldbasis

\[
\delta_1f=f(q),\qquad\delta_2f=71f(q^{71}),
\]

the two traces have Gram matrix

\[
G=\begin{pmatrix}72&-10\\-10&72\end{pmatrix},\qquad
\det G=5084\equiv4\pmod5.
\]

The checker takes the genuine q-series 3 delta1 f + 5 delta2 f, computes
both traces, and recovers 3f and 5f coefficientwise through q^57 with exact
rational arithmetic. Modulo 3125,

\[
G^{-1}=\begin{pmatrix}1608&1265\\1265&1608\end{pmatrix}.
\]

Fricke-plus inputs have equal oldspace coordinates after elliptic
projection. Their common coordinate is their common projected trace divided
by 72+a71=62; 62^-1=2873 modulo 3125. This division is a 5-adic unit
operation. **The unprojected trace divided by 62 is not thereby the
elliptic coordinate.**

There is no loss of 5-adic precision in the trace or this Gram inversion.
The separate Hecke-polynomial elliptic projector in `../elliptic_projection/`
has a denominator of 5-adic valuation one on a Hecke-stable integral lattice.
Therefore five input digits leave at most four digits after that step,
before any separately quantified loss in overconvergent-to-proper-de-Rham
reduction. This file does not identify a q-expansion lattice with that
cohomological lattice without performing the conversion.

The output bound q^128 exceeds the classical weight-two level-389 Sturm
bound 65. That is a useful regression and input size, **not a certificate
that an overconvergent q^128 jet determines its proper de Rham projection**.
The tame trace itself still needs raw coefficients through 71 times the
desired output bound: q^9088 for q^128. The roughly 72-fold reduction in
level-dependent workspace concerns the subsequent projection/reduction
stage. It is not a 72-fold reduction in the raw q-expansion length.

## Sources and next interface

- R. Coleman, [Classical and overconvergent modular forms](https://www.wstein.org/people/coleman/papers/classical_and_overconvergent_forms.pdf), Inventiones 124 (1996), Theorems 5.1 and 5.4: invertible cohomological U and the Bol quotient.
- N. Mascot, [Companion forms and explicit computation of PGL2 number fields with very little ramification](https://warwick.ac.uk/fac/sci/maths/people/staff/mascot/companion.pdf), Theorem 2.4.1: Atkin–Lehner action on oldforms.
- H. Darmon and A. Lauder, [Stark points on elliptic curves via Perrin-Riou's philosophy](https://people.maths.ox.ac.uk/lauder/papers/DL.pdf), Section 1: the g-depleted family input and the distinction between a base de Rham comparison and a family derivative comparison.

The next executable interface is a bounded-precision overconvergent
cohomology reduction at tame level 389, retaining both elliptic Frobenius
directions, followed by the separately certified E projector. A comparison
of the resulting analytic second jet with the complementary regulator of
the same global class remains a further mathematical obligation.
