# Rank-two BSD: the completed pilot and a reflected-class research target

Research branch: `bsd-derived-localization`, continuing
`bsd-localization-audit` commit `12c58ddf46ebd89141d4392b519ca7ae533e67ea`.
The original base in exponent-seven is
`640e6c91b3485e1a55c99476ecb06ebd8379740b`.

Pilot:

\[
E=389.a1:\ y^2+y=x^3+x^2-2x,\qquad
K=\mathbf Q(\sqrt{-71}),\qquad p=5.
\]

The other research thread supplied its completed p=5 theta certificate.
This continuation accepts that arithmetic/theorem bridge as an identified
input, extracts further exact consequences, and develops a specific global
class to investigate next. It does not redo the 140-class CM construction.
The original p=29 arithmetic and projection work remains available below.

## What is completed

**For this pilot, the supplied Selmer-dimension theorem and our two
independent rational points imply rank exactly two and finite 5-primary
Sha.** This is an application of established results to the certificate,
not a new general BSD theorem or a claim that the curve's rank was unknown.

| Addition | Result | Evidence and scope |
|---|---|---|
| Completed pilot corollary | rank E(Q)=2 and Sha(E/Q)[5^infinity] finite | [p5 proof](p5/README.md), using the supplied theta/arithmetic bridges and our point-independence certificate |
| Actual cyclic toric period | Norm 49; all six nontrivial periods are 5-adic units | [Exact p5 checker](p5/check_refinements.py), with provenance in [inputs](p5/inputs.json) |
| Coefficient descent | Selmer dimension descends from Q5(zeta7); the strict line descends | [p5 proof](p5/README.md); arbitrary normalized individual classes need not be Q5-valued |
| Local comparison target | Point logarithms and strict-line coordinate to 30 normalized 5-adic digits | [Formal-log proof and data](local_model/README.md), including a rigorous tail estimate |
| Family obstruction | An everywhere-Selmer family in this definite anticyclotomic tower cannot supply the missing base class | [Derived-class analysis](derived_global/DERIVED_CLASSES.md), applying the published universal-norm theorem |
| Reflected relaxed class | A well-defined, possibly zero Selmer class under the stated CH hypotheses and theta order at least two | [Construction](derived_global/DERIVED_CLASSES.md) and [independent cohomological review](rationality/REFLECTED_REVIEW.md); nonzero localization remains unresolved |
| Geometric realization criterion | A canonical Selmer exterior class and a finite-extension Kummer comparison sufficient for rank two | [Rationality note](rationality/README.md); the comparison itself remains to be constructed |
| Descent failure to avoid | A Galois-invariant wedge of two character components need not descend from rational points | [Exact exterior/descent checker](rationality/check_exterior_descent.py) |

These additions contain mathematical proofs and exact Python calculations.
They are **not additional Lean kernel-checked theorems**. The supplied
package has its own formal layer and verification receipts. The new finite
matrix examples are explicitly abstract algebraic models, not elliptic
curves or counterexamples to BSD.

## Input provenance and the pilot corollary

The supplied archive is `bsd-rank-two-certificate-2026-11-27.zip`, SHA256

```
f4d0332acbe087da2dda53a9a380f41c75d3ec63c5ad59441f2a5785ef21531a
```

Its argument identifies the CM/Brandt computation with the ordinary theta
element and proves exact lower zeros followed by a unit quadratic term:

\[
\Theta_{E/K,5}(T)=T^2U(T),\qquad U(0)\in\mathbf Z_5^\times.
\]

Together with its audited hypotheses and Castella--Hsieh's Theorems A/B,
this gives a two-dimensional rational 5-adic Selmer space. The finite
coefficient-field extension used for the order-seven character does not
change that dimension. The exact logical input is the supplied arithmetic
argument, not just the saved finite vector or its successful Python run.

Our independent certificate proves that P=(0,0) and Q=(1,0) are independent:
reduction at 3 and 7 eliminates rational torsion, and their images modulo
2E(F11) are independent. The Kummer exact sequence

\[
0\longrightarrow E(\mathbf Q)\otimes\mathbf Q_5
\longrightarrow \operatorname{Sel}(\mathbf Q,V_5E)
\longrightarrow V_5\Sha(E/\mathbf Q)\longrightarrow0
\]

then has a subspace of dimension at least two inside a space of dimension
two. Its quotient vanishes. Cofinite generation of the 5-primary Sha group
makes zero divisible corank equivalent to finiteness. No finiteness of Sha
was assumed in making this argument.

This establishes neither triviality of Sha[5^infinity], nor finiteness of
all primary components, nor the full BSD leading-term formula. In this
specific example every rational Selmer class is consequently in the
Kummer image; the general geometric realization problem remains open.

## The next class has a concrete formula

Write gamma=1+T and use the odd parameter

\[
t=\frac{\gamma-\gamma^{-1}}2,
\]

which generates the same augmentation ideal at odd p and changes sign
under anticyclotomic conjugation. Let c denote the semilinear action of
complex conjugation on the appropriate global Iwasawa cohomology module.
The proposed class is

\[
x=\left.\frac{\kappa_\infty-c\kappa_\infty}{t}\right|_{t=0}.
\]

Here kappa_infinity is the specified relaxed diagonal class, with zero full
localization at one p-adic prime and an allowed singular component at the other. Its
conjugate has the opposite local conditions. This distinction is necessary:
the published universal-norm vanishing rules out obtaining the desired
class from a compatible family satisfying both ordinary conditions.

The numerator has zero specialization because the base class belongs to
the plus eigenspace; the quadratic-twist Selmer component is zero. Global
cohomological exactness supplies unique division in the actual bounded
Iwasawa module. The quotient is conjugation invariant. The
order-two Coleman vanishing leaves order at least one after division;
Castella--Hsieh's derived-height theorem supplies the specialized Selmer
condition. The construction and its independent review give the module,
specialization, and rational-descent arguments explicitly. The class takes
values in the finite coefficient extension L used for the auxiliary character;
a nonzero L-valued logarithm would also yield a rational Qp-valued witness
by a suitable coefficient functional.

The remaining arithmetic question is

\[
\log_{\omega_E}(\operatorname{loc}_p x)\ne0.
\]

It is not implied by a nonzero quadratic theta coefficient. The reflected
numerator can have global order one or two. In the second case x=0, while
the second derivative can land in an anti-invariant relaxed component.
Even order one proves a nonzero class, not by itself a nonzero logarithm.
The new explicit countermodel records this distinction. A finite-logarithm
reciprocity law, or another independent arithmetic argument, must resolve it.

A further [ambient-control analysis](derived_global/AMBIENT_CONTROL.md)
shows why the global H2 specialization obstruction also matters. Two
exact algebraic complexes have identical Selmer elementary divisors and
order-two regulator data, but different reflected specializations. These
are insufficiency models, not arithmetic realizations; a stronger global
arithmetic obstruction remains a question to investigate.

Changing the relaxed family by a regular scalar unit changes x by a
nonzero scalar and a multiple of the original strict class. Thus its
nonzero-logarithm question is insensitive to that normalization ambiguity.
The note also retains the involution in the published height formula;
omitting it would produce an incorrect parity argument.

## Numerical target for the next comparison

For omega_E=dx/(2y+1), the new exact calculation gives

\[
\begin{aligned}
\log_5(P)/5&\equiv439539435537114752261,\\
\log_5(Q)/5&\equiv226464719373794906613
\end{aligned}
\pmod{5^{30}}.
\]

The strict line in the P,Q basis is generated by rP-Q, where

\[
r\equiv281099199846294196408\pmod{5^{30}}.
\]

This is a comparison benchmark for a future global-class computation, not
that computation itself. The ratio r is not an algebraic-number recognition
target: the p-adic analytic subgroup theorem makes it transcendental for
these independent points on this non-CM curve. The relevant rationality
question concerns the class or its exterior regulator.

## The second global step: geometric realization

Suppose a nonzero-localization construction and the published rank-two
machinery give a two-dimensional space S, a nonzero functional ell, and
0 != kappa in ker(ell). Then

\[
\eta_\kappa=\frac{\kappa\wedge z}{\ell(z)}\in\bigwedge^2S
\]

is nonzero and independent of the choice of z with ell(z) != 0. A precise
sufficient geometric target is to realize its restriction to a finite
extension F/Q in the exterior square of the Kummer image of E(F).
Applying the exterior square of corestriction then gives
[F:Q]^2 eta_kappa in the rational Kummer exterior square, forcing rank two
and finite p-primary Sha.

This requires a global comparison with actual points or degree-one cycle
classes. Pairing inverse character components and taking a diagonal Galois
norm is insufficient: their wedge may be invariant while the trace of each
point is zero. The two trace operations are different. The exact C7 example
in the rationality note makes this failure explicit.

Under the hypotheses above, Kummer membership of the nonzero strict class,
exterior membership of eta_kappa, equality of Selmer and Kummer spaces,
and finite p-primary Sha are equivalent. The geometric target specifies
what must be constructed; it does not reduce that arithmetic assertion to
linear algebra.

## Earlier independent certificates retained

- [Eligibility and independent points](eligibility/arithmetic/README.md),
  including the original p=29 checks.
- [Certified quadratic-twist central value](eligibility/arithmetic/check_twist_lvalue.py),
  with the infinite tail bounded using rational arithmetic.
- [All-level cyclic ring-class coordinates at p=29](projection/README.md).
- [C7 nonvanishing criterion](logic/C7_AUXILIARY_PERIOD.md).
- [Logical audit](logic/AUDIT.md), [theorem ledger](literature/THEOREM_LEDGER.md),
  and [theta conventions](literature/THETA_CONVENTIONS.md).

The continuation corrects an earlier misattributed published regression
fixture in the theta-conventions note. The actual first table row uses
p=11 and K=Q(sqrt(-2)); none of our executable calculations depended on the
incorrectly quoted coefficient pair. The original p=29 search instructions
are now historical planning: the supplied p=5 result closes that pilot
computation at a smaller level.

## Reproduction

From the repository root:

```sh
python research/bsd-localization/verify_all.py
```

To write a fresh receipt:

```sh
python research/bsd-localization/verify_all.py --receipt research/bsd-localization/verification.json
```

The runner checks the original arithmetic and the new p5, formal-log,
Bockstein, reflection and exterior-algebra certificates against saved JSON.
All scripts use Python's standard library. The receipt records exit status,
timing and file hashes. This command does not rebuild or reverify the other
thread's CM/Lean package; its input provenance and mathematical scope are
stated above.
