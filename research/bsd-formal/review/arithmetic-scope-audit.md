# Arithmetic and formalization scope audit

Audit date: 2026-11-28. Source snapshot: `bgross0/exponent-seven`,
`bsd-lean-certificate-proofs` at
`72e9f63708fbe3b48342de296a60979e32bb8c31`.

This is a read-only audit of the existing arithmetic argument and its remaining
formalization obligations. It does not claim a new proof of the theta
identification or the Selmer criterion. The rational-point shortcut described
below was independently checked mathematically; its Lean implementation is
being developed separately.

## 1. Fix the endpoint and the curve

The endpoint of the coordinated original pilot is

\[
E_{389}:y^2+y=x^3+x^2-2x,\qquad
\operatorname{rank}E_{389}(\mathbf Q)=2,\qquad
\Sha(E_{389}/\mathbf Q)[5^\infty]\text{ finite}.
\]

This is the conclusion recorded in Section 4 of the
[shared handoff at cf84450](https://github.com/bgross0/exponent-seven/blob/cf84450fb80b673c9b32c5abb71d7e26d4e87957/research/bsd-coordination/README.md).
It is a particular application of published arithmetic results. It does not
assert the complex analytic rank, the leading-coefficient formula, finiteness
of every primary component of Sha, or universal BSD.

The currently assembled Lean theta theorem is instead for

\[
E_{433}:y^2+xy=x^3+1.
\]

The two streams share useful generic algebra, but their finite tables,
ordinary roots, and curve-level conclusions cannot be interchanged. The
current E433 theorem is a secondary certificate-construction milestone, not
the end-to-end E389 pilot theorem.

## 2. What the formal endpoint actually takes as input

Read the declarations, rather than using the total theorem count as a measure
of remaining arithmetic distance. The entry point
`BSDArithmeticCertificate.e433_certificate_of_finite_tower` takes a sequence
`G : ℕ → Polynomial ℤ_[5]` and hypotheses giving:

1. Successive compatibility modulo `(1+T)^(5^n)-1` for every level.
2. Finite inversion symmetry, with augmentation-one origin multipliers, at
   every level.
3. Exact zero augmentation at level zero.
4. Five first-level coefficient congruences with the regularized E433 data.

The actual ordinary normalization is constructed, and the infinite power
series is constructed from the given compatible tower. No actual arithmetic
CM tower `G` is defined in this module. Its constant control tower proves
consistency of the interface, not identification with CM theta elements.

Authoritative source:
[BSDArithmeticCertificate.lean at 72e9f63](https://github.com/bgross0/exponent-seven/blob/72e9f63708fbe3b48342de296a60979e32bb8c31/research/bsd-formal/BSDArithmeticCertificate.lean).
The current
[formal README](https://github.com/bgross0/exponent-seven/blob/72e9f63708fbe3b48342de296a60979e32bb8c31/research/bsd-formal/README.md)
and
[arithmetic bridge ledger](https://github.com/bgross0/exponent-seven/blob/72e9f63708fbe3b48342de296a60979e32bb8c31/research/bsd-formal/ARITHMETIC_BRIDGES.md)
state this boundary accurately.

| Layer | Proved or computed in the cited snapshot | Missing arithmetic identification |
| --- | --- | --- |
| Polynomial roots | Actual distinct roots of the displayed full integer polynomials in a nontrivial completed quadratic order | These polynomials are Hilbert class polynomials; the completion is the intended local coefficient ring |
| Finite graph and eigenline | All displayed coordinate checks and the exact one-dimensional eigenspace of the displayed matrix | Actual supersingular curves, modular isogeny correspondence, Brandt module, and Jacquet–Langlands identification with the specified curve |
| Seven and 140 values | Values extracted from the canonical finite tables; period identities and quotient sums | Actual CM orbit, ideal-class action, coherent class labels and anticyclotomic projection |
| Ordinary root | Actual curve point counts at five, and the unique unit root of their Euler polynomial | Its use in the actual arithmetic theta normalization |
| Infinite series | A limit constructed from a compatible finite tower; exact lower vanishing and order certificate | Construct the arithmetic tower and prove its all-level relations |
| Selmer conclusion | Generic Kummer-subspace and dimension implications | Actual arithmetic cohomology, local conditions, the published theta-to-Selmer theorem, and the arithmetic Kummer exact sequence |

Thus the remaining work includes substantial theory development. It is not
only a few numerical checks or a final invocation of an existing Mathlib
theorem.

## 3. Audit of the written E389 arithmetic argument

The dependency pattern in the shared handoff matches the primary published
criterion. Castella–Hsieh's Theorem B assumes positive rational rank in
addition to the hypotheses of Theorem A. Under those assumptions, theta order
two gives nonvanishing of their generalized Kato class, and Theorem A then
gives Selmer dimension two. The independently supplied two rational points
give the required rank lower bound. The Kummer sequence and finite
cogeneration of the primary Sha group then yield the stated pilot conclusion.

The cited theorem therefore does not remove the positive-rank hypothesis.
Trying to prove a general localization or geometricity statement without
that input is a different research problem. The particular E389 pilot can
use its explicit points and does not need to solve that general problem.

Primary source:
[Castella–Hsieh, published paper, Theorems A and B, pp. 5–6](https://web.math.ucsb.edu/~castella/Kato-print.pdf).
The field extension used for the order-seven auxiliary character is an
extension of coefficients; it does not alter the base number field of the
elliptic curve. The existing audit tracks residual irreducibility,
ramification, the two auxiliary L-values, and the coefficient conventions.

The reviewed documents give a coherent application of these published
theorems. This audit does not replace independent verification of every CM,
modular-symbol, or local-representation implementation by a Lean proof.
Their interpretation remains external to the kernel.

Canonical arithmetic sources:

- [E389 theta certificate at cf84450](https://github.com/bgross0/exponent-seven/blob/cf84450fb80b673c9b32c5abb71d7e26d4e87957/research/bsd-theta/research/theta-certificate.md).
- [E389 arithmetic audit at cf84450](https://github.com/bgross0/exponent-seven/blob/cf84450fb80b673c9b32c5abb71d7e26d4e87957/research/bsd-theta/research/arithmetic-audit.md).
- [Original localization argument at 12c58dd](https://github.com/bgross0/exponent-seven/blob/12c58ddf46ebd89141d4392b519ca7ae533e67ea/research/bsd-localization/logic/AUDIT.md).
- [Exact arithmetic eligibility and point independence at 12c58dd](https://github.com/bgross0/exponent-seven/blob/12c58ddf46ebd89141d4392b519ca7ae533e67ea/research/bsd-localization/eligibility/arithmetic/README.md).

## 4. A shorter exact route to theta augmentation zero

This is a proposed shortening of the arithmetic proof dependency, not a
claim that the CM distribution relation has been formalized.

Let `S_m` be the sum of the primitive quaternionic eigenfunction over the full
CM orbit of conductor `5^m`. In the split setting here, with units `{±1}`,
the ordinary horizontal/vertical Hecke relations give

\[
S_1=(a_5-2)S_0,\qquad
S_2=a_5 S_1-4S_0,\qquad
S_{m+1}=a_5 S_m-5S_{m-1}\quad(m\ge2).
\]

The initial factor four is essential: the first ring-class kernel has order
`5-1`; subsequent kernels have order five. The two horizontal edges at
conductor one account for the `-2` in the first equation.

Both supplied seven-value vectors have sum zero. Once they are identified
with the actual CM evaluations, the recurrence proves every `S_m=0`.
Alternatively, the E389 arithmetic audit already computes the conductor-five
sum exactly as zero, using the degree-28 class polynomial and retaining root
multiplicities.

With `α²-a_5 α+5=0`, the level-one ordinary augmentation is

\[
\alpha^{-1}S_1-4\alpha^{-2}S_0
=\alpha^{-2}\bigl(\alpha(a_5-2)-4\bigr)S_0
=(1-\alpha^{-1})^2 S_0=0.
\]

Compatibility then preserves augmentation exactly in the inverse limit.
This avoids using complex L-value interpolation merely to establish
`Θ(0)=0`. It does not remove the separate `L(E,1)=0` premise of the
Castella–Hsieh application.

The primary construction and distribution proof are
[Chida–Hsieh, Section 4.2, Definition 4.1 and Lemma 4.2](https://www.math.ntu.edu.tw/~mlhsieh/research/central.pdf).
Their relation is an actual Hecke identity for the Gross points. Replacing it
by a relation imposed on an arbitrary sequence would leave the arithmetic
gap unchanged.

## 5. Direct rational-point theorem: an independently checked shortcut

Let `P=(0,0)` and `Q=(1,0)` on E389. Their sum is `(-2,-1)`. For a finite
point `R=(x,y)`, the duplication numerator and denominator are

\[
N=x^4+4x^2-2x+3,\qquad
D=4x^3+4x^2-8x+1=(2y+1)^2.
\]

When `2R` is finite, `x(2R)=N/D`. A half of a point with x-coordinate
`k=0,1,-2` therefore gives a rational root of the monic polynomial `N-kD`.
Every such rational root is integral. The resulting quartics have no roots
modulo eleven:

| k | Monic quartic |
| --- | --- |
| 0 | `x^4+4x^2-2x+3` |
| 1 | `x^4-4x^3+6x+2` |
| -2 | `x^4+8x^3+12x^2-18x+5` |

Their residue lists, for `x=0,...,10`, were independently recomputed as

```
k= 0: 3,6,9,4,7,3,1,1,5,6,10
k= 1: 2,5,9,4,4,3,8,6,8,5,1
k=-2: 5,8,9,4,2,3,9,2,10,8,6
```

For a nonzero point satisfying `2R=0`, the equation `D=0` implies, with
`u=2x`,

\[
u^3+2u^2-8u+2=0.
\]

Again `u` would be integral, but the values modulo four are `2,1,2,3`.
Thus multiplication by two is injective on the actual rational-point group.

An integer relation `mP+nQ=0` with an odd coefficient would make one of
`P,Q,P+Q` a double, contradicting the quartic checks. Both coefficients must
be even. Injectivity of multiplication by two gives the halved relation, and
descent on `|m|+|n|` forces both coefficients to vanish.

This proves actual Z-linear independence without needing Mordell–Weil
finite generation, the general reduction homomorphism, or torsion-freeness
at every prime. The implementation must handle the point at infinity before
using the finite duplication formula. This shortcut supplies a real
curve-level arithmetic statement, not a generic linear-algebra implication.

## 6. What a direct descent can and cannot replace

An explicit 2-descent could give the particular curve's algebraic rank upper
bound and bypass all CM/Jacquet–Langlands machinery for the rank statement.
It would not establish finite 5-primary Sha. A 5-descent with certified
local/global coverage could potentially replace the theta/Selmer route for
that primary component, but it requires an actual elliptic-curve Selmer
calculation and its soundness theorem. Merely replaying a software rank or
Selmer output is insufficient.

Accordingly there are two genuine endpoint routes:

1. Continue the actual CM theta construction and formalize the published
   theta-to-Selmer arithmetic theorem, then combine with the point theorem.
2. Produce and formalize an actual 5-descent certificate that gives the needed
   5-primary Selmer bound, then combine with the point theorem.

Neither is currently a few existing Mathlib imports. The second avoids much
automorphic theory but introduces substantial descent and local-solubility
theory. A direct 2-descent is a valuable separate rank theorem, with a smaller
endpoint.

## 7. Pinned Mathlib evidence

At the project's exact Mathlib commit
`fc4f59e577feb1a4956671bc04ac18aaaf8cd842`:

- [EllipticCurve/LFunction.lean](https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/AlgebraicGeometry/EllipticCurve/LFunction.lean)
  defines local Euler factors, a formal arithmetic-function L-function, and
  its L-series. This file does not supply modularity or the analytic BSD
  conclusions needed here.
- [DedekindDomain/SelmerGroup.lean](https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/RingTheory/DedekindDomain/SelmerGroup.lean)
  concerns the multiplicative group `K(S,n)` of a fraction field. It is not
  the elliptic-curve Selmer space used in the pilot. Its own documentation
  lists the exact-sequence and finiteness proofs as future work.
- [Height/EllipticCurve.lean](https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/NumberTheory/Height/EllipticCurve.lean)
  supplies the naive height and approximate parallelogram law. It should not
  be cited as an already formalized E389 rank or descent theorem.

The complete pinned tree contains no dedicated files named for
Jacquet–Langlands, Heegner points, elliptic Selmer groups, or Tate–Shafarevich
groups. This file-name inventory is supporting evidence about scope, not a
proof that no equivalent lemma exists under a different name.

## 8. Acceptance criterion for closure

A completed end-to-end pilot should have a terminal Lean theorem about the
fixed E389 model and the actual arithmetic objects, with no assumed CM
identification, Selmer-dimension bound, Kummer comparison, or Sha conclusion.
The existing finite tables may appear as data, but their semantic bridges
must be proved. Its complete transitive axiom audit must contain only the
standard accepted axioms. A consistent model of the abstract certificate
interface is useful testing evidence, but cannot be substituted for that
arithmetic identification.
