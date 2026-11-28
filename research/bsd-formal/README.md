# Lean proofs for the BSD certificate project

This directory formalizes finite arithmetic and algebra from the BSD research
streams. It contains **266 proved theorems: 251 new theorems and 15 preserved
theorems from the original theta package**. The project is pinned to Lean
4.36.0 and Mathlib commit `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`.

The latest extension adds **113 theorems** to the previous 153-theorem
milestone. It constructs actual roots of the two full candidate polynomials,
constructs ordinary unit roots from the two curves' point counts, and
constructs a power series from a compatible finite tower. See
[`ARITHMETIC_BRIDGES.md`](ARITHMETIC_BRIDGES.md) for the completed bridges and
the exact arithmetic inputs still required.

The verification result and exact source hashes are recorded in
[`verification/receipt.json`](verification/receipt.json). The verifier builds
the project, prints every theorem's axiom dependencies, and separately replays
each project module with `leanchecker` against its compiled imports. The
permitted axiom set is `propext`, `Classical.choice`, and `Quot.sound`.

The key remaining arithmetic task is to identify the finite data and the
power series in these proofs with the specified curve's arithmetic CM objects
and infinite theta series. The conditional theorem states those obligations
explicitly. This directory does not prove the universal BSD conjecture.

## 1. What Lean now proves

| Module | Theorems | Content |
| --- | ---: | --- |
| `BSDRankTwo` | 15 existing | Prime-power coefficient precision, exact inversion-symmetry vanishing, and general order certificates |
| `BSDFiniteWitness` | 26 new | Exact E433 coordinate data, Deuring coefficients and roots, cubic factorizations, eigenvector, both congruence cycles, and value extraction |
| `BSDCoordinateRing` | 16 new | Soundness of the coordinate operations and Horner evaluation in actual Mathlib rings and polynomials |
| `BSDEigenline` | 12 new | The exact one-dimensional rational minus-one eigenspace of the displayed matrix |
| `BSDHenselWitness` | 10 new | All 147 exact numerical strong-Hensel premises for the full integer candidate polynomials |
| `BSDCMPeriods` | 24 new | Corrected cyclic sums, explicit Bezout identities, nonvanishing, units, and conjugate product 49 |
| `BSDThetaCertificate` | 21 new | All 140 quotient-fiber sums, ordinary regularization, the concrete conditional certificate over the 5-adic integers, and a proved nonvacuity example |
| `BSDLocalization` | 25 new | Finite determinant soundness, full-regulator transversality, and Kummer-subspace dimension implications |
| `BSDCertificates` | 4 new | Connections from the canonical finite tables to the period and theta-polynomial results |
| `BSDHenselSemantics` | 28 new | Full polynomial/derivative semantics, monicity and degrees, actual residual divisibility, and normalized derivative units |
| `BSDHenselLift` | 12 new | Actual root existence in the explicitly constructed nontrivial completed quadratic order |
| `BSDHenselDistinct` | 16 new | Injective seven- and 140-root families and exact canonical-residue labels |
| `BSDOrdinary` | 22 new | Actual Mathlib curve point counts at five and the unique ordinary unit root of each point-count Euler polynomial |
| `BSDThetaLimit` | 31 new | Construction from a compatible finite tower, exact low-order vanishing, first-level approximation, and a complete conditional order certificate |
| `BSDArithmeticCertificate` | 4 new | The assembled E433 finite-tower implication with the actual ordinary normalization `alpha^(-2)` |

The theorem inventory is generated from declarations rather than comments.
The source and verification receipt distinguish the 15 reused theorems from
the new contribution.

### Exact finite arithmetic

For the E433 data, Lean checks the following explicit computations:

- The prime 433 and the fact that 5 has no square root modulo 433.
- All 216 distinct roots of the degree-216 Deuring polynomial, whose literal
  coefficients are proved equal to the defining squared binomial coefficients.
- The displayed j-relations and coverage of all 36 listed vertices.
- All 36 full cubic factorizations of the displayed Phi_2 expression and the
  complete integral eigenvector identity.
- All congruence edges among the 7 and 140 displayed canonical residue pairs
  modulo `433^4`, their degree-two graphs, and the complete cycle permutations.
- Extraction of the seven and 140 values from the same vertex/eigenfunction
  table, avoiding a disconnected copy of the claimed values.

`BSDCoordinateRing` proves that the coordinate implementation really computes
in any ring satisfying `m = 0` and `u^2 = 5`. It also constructs the concrete
Mathlib quotient

\[
 (\mathbb Z/m\mathbb Z)[u]/(u^2-5)
\]

using `AdjoinRoot`, and transfers finite zero witnesses to genuine polynomial
zeros there. These results do not yet prove that the quotient is a field or
identify its elements with arithmetic CM invariants.

### Exact eigenspace, including uniqueness

For the displayed 36-by-36 matrix A and vector v, Lean proves

\[
\ker(A+I)=\mathbb Qv,
\qquad \dim_{\mathbb Q}\ker(A+I)=1.
\]

An explicit integer correction matrix B supplies the certificate

\[
B(A+I)=32(I-ve_0^{\mathsf T}).
\]

Every entry is checked by kernel reduction. A generic proved lemma then shows
that any null vector x equals `x 0 * v`. This proves uniqueness directly over
the rationals; it does not rely on the earlier Python rank computation.

### Full integer polynomial and Hensel numerical premises

The two candidate polynomials have degrees seven and 140. Every full integer
coefficient is retained, including coefficients with 2,054 decimal digits.
Lean checks the compact residues and formal-derivative coefficient lists
against those full integers.

For every one of the 147 supplied high-precision approximations, the coordinate
calculation has residual divisibility exponent exactly 24, recorded derivative
exponent s, and

\[
24>2s,\qquad 24-s\ge4.
\]

The same approximations reduce to the canonical residue tables modulo
`433^4`. The new semantic bridge interprets every full coefficient and the
formal derivative as actual Mathlib polynomials. It proves that these
polynomials are monic of degrees seven and 140 over every nontrivial
commutative coefficient ring.

`BSDHenselLift` constructs the concrete ring

\[
C=\widehat{\mathbb Z[\sqrt5]}^{\,(433^4)},
\]

proves that it is nontrivial and complete, and applies a proved scaled
Hensel theorem. `BSDHenselDistinct` then proves actual families of seven
and 140 roots, respectively, injective within each family. Their residues
are exactly the original canonical root-table entries. All numerical
hypotheses are discharged by the existing data and new semantic proofs.

Identifying the candidate polynomials with analytic Hilbert class polynomials
and identifying this completion with the intended unramified quadratic
433-adic integer ring remain separate arithmetic steps. No integral-domain,
exhaustive-root-list, or cross-family distinctness claim is made here.

### Cyclic character periods

The corrected cyclic vectors are

\[
v_{389}=(-1,0,-1,1,0,0,1),\qquad
v_{433}=(1,1,-1,0,0,0,-1).
\]

Let P be the corresponding period polynomial and
`Phi7(z) = 1 + z + ... + z^6`. Explicit integer polynomial identities give

\[
A(z)P(z)+B(z)\Phi_7(z)=7.
\]

Consequently, at a Phi_7-root, the period is a unit whenever 7 is a unit in
the coefficient ring. In an integral domain, the module proves the resulting
nonvanishing for all six powers of a primitive seventh root. It also proves
the exact product

\[
\prod_{j=1}^{6}P(\zeta^j)=49.
\]

This is a formal product identity. Identifying it with a field norm or with
arithmetic toric periods requires the corresponding field or CM identification.

### The actual 5-adic power-series certificate

The 140 values give

\[
(b_0,b_1,b_2,b_3,b_4)=(0,1,-2,1,0),
\quad G(\gamma)=\gamma(\gamma-1)^2,
\quad G(1+T)=T^2+T^3.
\]

For ordinary unit scale u and arbitrary lower-level trace scale c, define

\[
G_{\rm reg}=uG(1+T)-c\sum_{j=0}^{4}(1+T)^j.
\]

Lean proves `[T^2]G_reg = u - 10c`. The principal theorem
`BSDThetaCertificate.five_adic_certificate` works over the actual Mathlib
`PadicInt 5`. Its arithmetic inputs are precisely:

1. `F.constantCoeff = 0` exactly.
2. The actual origin-dependent inversion equation
   `F = W * F.subst(inversionSeries)`.
3. `W.constantCoeff = 1` for that functional-equation multiplier.
4. `IsUnit u` for the ordinary normalization.
5. An integral finite-level identity
   \[
   F-G_{\rm reg}=((1+T)^5-1)H+5J,
   \qquad H,J\in\mathbb Z_5[[T]].
   \]

It concludes both

\[
\operatorname{ord}_T F=2,
\qquad F=T^2V,\quad V(0)\in\mathbb Z_5^\times.
\]

The ring facts about five and two are discharged in Mathlib. The theorem
derives exact linear vanishing from exact symmetry; it never promotes a
finite-precision zero to an exact zero. The same integral ring contains all
approximation errors, so denominators cannot silently erase the residue test.

The multiplier is essential at the displayed cycle origin. Lean proves
`G = (1+T)^4 * G.subst(inversionSeries)` for the raw E433 polynomial and proves
that `F=G`, `W=(1+T)^4`, `u=1`, `c=H=J=0` satisfy all inputs jointly. This
checks nonvacuity of the corrected algebraic interface. It is not an arithmetic
identification of G with the infinite theta series. See
[`ORIGIN_CONVENTIONS.md`](ORIGIN_CONVENTIONS.md) for the review finding and the
corresponding E389 convention.

### Ordinary roots from actual curve point counts

`BSDOrdinary` defines both curve models over a coefficient ring, proves their
integer discriminants, and proves that their reductions modulo five are
elliptic. It counts Mathlib's actual `WeierstrassCurve.Affine.Point` types,
including the point at infinity:

\[
\#E_{433}(\mathbb F_5)=10,\qquad \#E_{389}(\mathbb F_5)=9.
\]

The traces defined from these counts are -4 and -3. Applying Mathlib's
5-adic Hensel theorem constructs the unique unit root of each point-count
Euler polynomial:

\[
\alpha_{433}^2+4\alpha_{433}+5=0,\qquad
\alpha_{389}^2+3\alpha_{389}+5=0.
\]

Their existence and unit properties are proved, not hypotheses.
`BSDArithmeticCertificate` uses the actual unit
`conductor25Scale = alpha433^(-2)`. Identification of this chosen scale with
the arithmetic CM normalization is part of the remaining first-level
identification.

### Constructing the series from a finite tower

`BSDThetaLimit` takes finite polynomials `G n` at quotient order `5^n`.
Successive cyclic compatibility means

\[
\omega_n\mid G_{n+1}-G_n,\qquad \omega_n=(1+T)^{5^n}-1.
\]

The proved prime-power binomial bounds make every coefficient sequence
5-adically Cauchy. Mathlib completeness constructs `thetaLimit G`, with
uniqueness and proved coefficient precision. Finite inversion symmetries
at every level, with origin multipliers of augmentation one, and zero
augmentation at level zero imply exact constant and linear vanishing of
the constructed limit. No infinite functional equation or infinite
vanishing assumption is supplied.

The intended entry point is
`BSDArithmeticCertificate.e433_certificate_of_finite_tower`. It uses the
actual ordinary scale, the successive distribution relation, the finite
symmetries, zero level-zero augmentation, and five first-level coefficient
congruences modulo five. It concludes

\[
\operatorname{ord}_T F=2,\qquad F=T^2V,\qquad V(0)\in\mathbb Z_5^\times
\]

for the constructed series. The integral approximation witnesses are also
constructed. The family consists of finite objects at every level: the
distribution and symmetry inputs are **uniform statements for all levels**,
not consequences of checking one finite table.

Statement review found that exact first-level equality to the regularized
element, together with exact zero augmentation, forces its correction scalar
to be zero. This is now a proved lemma. The intended modulo-five interface
avoids that extra restriction. A constant control tower
`u(T^2+T^3)-cT^4` proves the revised hypotheses jointly consistent for every
correction scalar c, using multiplier `(1+T)^4`. The control tower is not an
arithmetic CM identification.

### Localization and Kummer linear algebra

`BSDLocalization.logarithm_ne_zero_of_theta_and_leading_comparison` formalizes
the local algebraic argument for a full two-coordinate regulator. It combines
an exact theta-order input, an augmentation-unit scalar identity for that same
regulator, a leading-direction comparison, and separation from the exceptional
line. Specialization control and a finite local logarithm then give a nonzero
logarithm.

The global family, local conditions, specialization-division property, and
arithmetic comparison identities are explicit hypotheses. This theorem proves
the implication between them; it does not construct the global arithmetic
class.

The finite direction test is also formal:

\[
5\cdot86-21\cdot5=325\equiv75\pmod{125},
\quad25\mid325,\quad125\nmid325.
\]

The reduction interface allows coefficient quotients of characteristic 125,
including extension quotients; it does not impose residue degree one.

Finally, two independent vectors in a proposed Kummer subspace and an ambient
dimension bound of two force that subspace to be the whole space. A surjective
quotient with that kernel is zero. An alternative theorem uses a nonzero strict
class together with injectivity of localization when the proposed Kummer space
has dimension one. Arithmetic Kummer membership is always explicit.

## 2. Remaining arithmetic proof obligations

| Layer | Remaining obligation |
| --- | --- |
| CM geometry | Prove the Deuring and CM interpretations of the finite data and identify the candidate integer polynomials with the actual Hilbert class polynomials |
| Completed coefficient ring | Identify the concrete completed quadratic order with the intended unramified quadratic 433-adic integer ring; actual root existence and canonical labels are now proved |
| Automorphic identification | Identify the displayed matrix/eigenline with the Brandt/Jacquet-Langlands object for the specified curve |
| Class action | Identify the cycle with the class-group action and prove that index modulo five gives the intended anticyclotomic quotient |
| Arithmetic theta tower | Construct the actual finite CM family, prove its distribution and finite symmetry uniformly over all levels, prove its zero augmentation, and identify its first-level coefficients and normalization; the limit construction and certificate implication are now proved |
| Global classes | Construct the compatible global family, verify the finite local condition, and prove the full arithmetic regulator comparison |
| Rational points and Sha | Identify the actual Kummer/Selmer objects and quotient, then formalize the arithmetic passage from its vanishing to finite primary Sha |
| Universal BSD | Establish the required complex L-function order and rational rank for every curve in the exact target |

The written research arguments supply references and proposed proofs for some
of these rows. They have not been inserted as axioms into this project.

## 3. Relation to the shared handoff and earlier work

This formalization acknowledges and uses the coordinated handoff in
[PR #6](https://github.com/bgross0/exponent-seven/pull/6), commit
`cf84450fb80b673c9b32c5abb71d7e26d4e87957`. In particular, it uses the corrected
cyclic E389 ordering, not the old sorted-j ordering.

`BSDRankTwo.lean` is byte-identical to the file in that handoff's imported theta
package. It is replayed here; its 15 theorems are not counted as newly proved.
The other sources formalize parts of the work at
`f3742fbf6ae1915cc35def76d2bc3937bebfda1e`. The first 153-theorem milestone
is preserved at proof commit `94c4424551e7cb16a72e9ec27546b685576353dc`;
the latest extension adds 113 theorems without replacing the original
numerical certificate.

The shared handoff's E389 rank-two and finite-5-primary-Sha conclusion is a
documented application of arithmetic theorems and the independently supplied
rational points. The present project has not converted that entire arithmetic
application into an end-to-end Lean theorem. The newly proved dimension lemmas
are components of that future formal argument.

The published Castella-Hsieh appendix already treats E433 with p=11 and
K=Q(sqrt(-7)); our computation uses p=5 and K=Q(sqrt(-71)). No priority claim
for this tuple, new rank-two curve, or new general BSD theorem is made. See
[the published paper, Table 1](https://web.math.ucsb.edu/~castella/Kato-print.pdf).

## 4. Reproduction

From this directory, with the pinned Lean toolchain available:

```sh
lake update
lake exe cache get
python verify.py
```

`lake-manifest.json` records all dependency revisions. `lake update` should
preserve the pinned Mathlib revision; the verifier rejects a different one.
The verifier also rejects modified tracked Mathlib sources, unapproved axiom
dependencies, prohibited proof constructs, and source changes during the run.

The optional Python renderers reproduce the finite and Hensel data modules
from the original certificate. The Hensel renderer needs the existing
`python-flint` dependency and rigorous Arb reconstruction. Running those
renderers is not necessary to check the Lean proofs: the full witnesses are
already included in the Lean sources.

Kernel replay checks each project module against compiled imports. It is not
a fresh replay of every theorem in the whole Mathlib dependency graph.

## 5. Left to Solve submission scope

The reviewed target is
[`WeierstrassCurve.Affine.Rat.weakBSD`](https://lefttosolve.com/p/WeierstrassCurve.Affine.Rat.weakBSD).
It quantifies over every rational elliptic curve and equates the complex
L-function's meromorphic order with rational-point rank. None of the theorems
in this directory has that type. A theorem whose remaining hypotheses include
the arithmetic bridge is not a complete proof of that target.

These are complete proofs of their stated finite, constructive, or conditional propositions.
They are appropriate reusable auxiliary results for the problem team's notes.
They must not be submitted as `OMA.solution` for universal BSD. The submission
record is in [`submission/`](submission/). The first research contribution
was acknowledged as note 68678; the 113-theorem arithmetic extension was
acknowledged as note 78488. Neither acknowledgment is checker acceptance of
universal BSD.
