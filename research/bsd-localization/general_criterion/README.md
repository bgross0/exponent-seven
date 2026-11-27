# A reusable sufficient criterion for nonzero finite localization

Date: 2026-11-27.

## What this theorem does

An ordinary elliptic curve, an eligible imaginary quadratic field, and
an exact theta coefficient can be combined with a **full geometric
comparison** and a certified two-dimensional direction test to construct
a Selmer class with nonzero finite localization.

The criterion below separates the algebraic implication from the
arithmetic work needed to apply it. It is not a theorem that every
analytic-rank-two curve satisfies the hypotheses. It does not produce
a rational point or eliminate a divisible Tate--Shafarevich contribution.

The source audit identified a gap in the older DR22 raw-moment edge
argument. [BSV_REPAIR.md](BSV_REPAIR.md) supplies a different full
specialization argument, using the BSV family and its published
normalized specialization theorem. An application must use that
argument with its actual hypotheses, or another independently proved
full comparison. Killing extra cohomology or matching one ordinary
scalar is not a substitute.

The machine-readable certificate here checks the **last finite
line-separation step only**. The file does not turn assertions in a
provenance field into verified arithmetic theorems.

## 1. The local theorem with minimal structural assumptions

Let L be a finite extension of Q_p and let Omega be a complete
overfield containing any regulator period coefficients. Let R be
the ring of analytic germs at t=0 over L, or its formal completion
when only the algebraic lemma is used. Let M be an R-module with
a specialization map

\[
                 \mathrm{sp}:M\longrightarrow H,
                 \qquad\ker(\mathrm{sp})=tM.                       \tag{1}
\]

Let `H_f` be a subspace of H with an injective logarithm `ell`.
Let D be a two-dimensional Omega-vector space with a nondegenerate
alternating pairing. Suppose

\[
                 P:M\longrightarrow D[[t]]
\]

is R-linear and regular, its base value factors through sp, and
there is a nonzero `zeta in D` such that

\[
             P_0(H_f)=0,\qquad
             \operatorname{im}P_0\subseteq\Omega\zeta.              \tag{2}
\]

Assume `y=t*x` in M, with `x0=sp(x) in H_f`. Suppose one regular
scalar regulator row satisfies

\[
                  \mu P(y)=u(t)\Theta(t),
                  \quad u(0)\ne0,\quad\operatorname{ord}_t\Theta=2.
                                                                         \tag{3}
\]

Finally let `A(W)` be an analytic vector with known first nonzero
coefficient

\[
                 A(W)=W^m(A_m+O(W)),\quad A_m\ne0,
                 \qquad m\ge0,                                    \tag{4}
\]

and suppose the **full** projective comparison proves

\[
 P(y(t(W)))\wedge K(W)A(W)=0,
 \quad t(W)=aW+O(W^2),\ a\ne0,\quad K(0)\in\mathrm{GL}(D).          \tag{5}
\]

The coefficients of P may lie in Omega even when the class is
defined over the finite field L. No descent of the full regulator
output to L is assumed.

### Theorem: quadratic transversality

Under (1)--(5), the condition

\[
                  \boxed{\det(K(0)A_m,\zeta)\ne0}                 \tag{6}
\]

implies `ell(x0) != 0`. Equivalently, one may certify
`det(A_m,K(0)^(-1)zeta) != 0` in the analytic coordinates.

### Proof

Since x0 is finite, (2) gives `P(x) in tD[[t]]`. Hence
`P(y)=tP(x)` has order at least two. Equation (3) forces its
order to be exactly two. Put `v2=[t^2]P(y)`, so `v2 != 0`.

The coefficient of degree `m+2` in (5) gives

\[
                    a^2v_2\wedge K(0)A_m=0.
\]

Both vectors are nonzero. Thus their lines agree, and (6) implies
`<v2,zeta> != 0`.

If x0 were zero, (1) would give `x=t*w`. Then `y=t^2*w`, and
(2) would force

\[
                 [t^2]\langle P(y),\zeta\rangle
                    =\langle P_0(w_0),\zeta\rangle=0,
\]

because a line in an alternating plane is its own annihilator.
This contradicts the preceding nonzero value. Thus x0 is nonzero;
injectivity of ell on H_f proves the result. QED.

### What is minimal here

* The analytic order m need **not** be two. It need only be known,
  with exact lower zeros and a nonzero leading coefficient.
* Theta is a convenient source of the actual regulator's exact
  order two. An independent proof of `ord P(y)=2` can replace (3).
* No determinant-order theorem for P, no freeness of M, and no
  absolute logarithm calibration are required.
* Only the base image containment in (2) is required; it need not
  be proved surjective onto the line.
* A row `mu(t)` regular at zero suffices in (3). For the arithmetic
  application it is the specified source-defined ordinary row.
* A nonzero leading projective comparison alone does not determine
  the order of P(y). Equation (3) supplies that separate information.

## 2. Arithmetic form of the criterion

Let E/Q have good ordinary reduction at p >= 5. Let K be an
imaginary quadratic field in which `p=mathfrak p*mathfrak pbar`
splits. Let `V=V_pE tensor L`, let K_infinity be its
anticyclotomic Z_p-extension, and choose a topological generator
gamma. Put

\[
 t=(\gamma-\gamma^{-1})/2,
 \qquad M_{\rm glob}=H^1_{\rm Iw}(K_\infty,V).
\]

Complex conjugation c acts semilinearly by `c(gamma)=gamma^-1`
and fixes the external coefficient field. For a family kappa in
M_glob, require the following **explicit arithmetic hypotheses**.

**G1: global reflected construction.** The actual base specialization
`kappa0` is finite Selmer and satisfies `c(kappa0)=kappa0`. The full
localization of kappa at the conjugate prime is zero. The
universal-character specialization exact sequence gives
`ker(sp_glob)=tM_glob`, with no t-torsion ambiguity. For an elliptic
curve the latter follows from `H^0(K,V_pE)=0`.

**G2: the theta identity for this same family.** The actual selected
localization y has the source-defined identity (3), with exact
theta order two. The factor u is an augmentation unit: `u(0)!=0`
over the coefficient field. It need not be an integral p-adic unit.
Exact lower zeros of Theta are required; congruences to zero at
finite precision are insufficient.

**G3: finite local control and the normalized full base map.** The
source theorem places the reflected quotient's specialization in
the finite local condition, and the full normalized regulator
satisfies (1)--(2). For the CH family this uses Theorem 4.5 as in
the pilot. Alternatively, prove `ker(mu P0)=H_f`: then
`mu P(x)=u*Theta/t` vanishes at the base, which itself proves
finiteness. A vanishing scalar without its correct base-kernel
identification does not establish this condition.

**G4: full projective comparison.** The analytic vector is attached
to a geometric family with a proved full classical specialization,
and (5) holds for the actual y. Section 3 below gives a sufficient
rank-one route for proving this, including every comparison layer.

**G5: infinite analytic and finite separation certificates.** The
leading coefficient in (4) belongs to the actual analytic germ,
with a proved tail/error bound and exact lower zeros. The matrix
K(0), exceptional line, and analytic vector use the same elliptic
realization and basis. A certified nonzero determinant proves (6).

### Arithmetic theorem

If G1--G5 hold, the quotient

\[
                   x=\frac{\kappa-c\kappa}{t}                      \tag{7}
\]

exists uniquely in global Iwasawa cohomology, has c-invariant base
specialization, and descends to a class

\[
 z\in\operatorname{Sel}_{\rm BK}(\mathbf Q,V_pE\otimes L),
 \qquad \boxed{\log_{\omega_E}(\operatorname{loc}_p z)\ne0}.         \tag{8}
\]

### Proof of the global assertions

G1 makes the numerator of (7) have zero global specialization,
so the exact sequence gives division by t. Torsion-freeness gives
uniqueness. Since c(t)=-t and the numerator changes sign, c(x)=x.
Strictness at the other prime gives

\[
             \operatorname{loc}_{\mathfrak p}\kappa
                       =t\operatorname{loc}_{\mathfrak p}x.         \tag{9}
\]

G3 makes the specialization finite at the selected prime;
conjugation makes it finite at the other prime. Away from p,
the rational local cohomology of V_pE is zero: local p-power
torsion is finite, hence H0=0; self-duality gives H2=0; the
local Euler characteristic gives H1=0. Thus no additional
rational local condition is missing.

Restriction/corestriction identifies conjugation-invariant Selmer
classes over K with those over Q. Applying the local theorem to
(9) gives (8). The finite elliptic logarithm over Q_p is injective:
under local Kummer it is the ordinary formal logarithm on
`E(Q_p) tensor Q_p`, whose torsion kernel disappears after
rationalization.

One may take a suitable Q_p-linear coefficient functional on L
to obtain a Q_p-valued Selmer witness with nonzero localization.
This descent is not canonical. No argument here identifies z
with a global rational point.

G1's conjugation-invariance can, for example, be supplied by
`Sel_BK(Q,V_p(E^K))=0`. An auxiliary central L-value certificate
must be joined to the exact rank-zero theorem and hypotheses
that prove this Selmer vanishing; a decimal nonzero L-value alone
is not a substitute.

## 3. A sufficient source-based route to G4

The following requirements prove the common full projective
comparison. They are not additional consequences of a theta
coefficient calculation.

### 3.1 The same generic global module

Let S be the compact relaxed/strict anticyclotomic Selmer module
for `V_pE`, with the selected prime relaxed and its conjugate
strict. Require

\[
             \dim_{\operatorname{Frac}\Lambda}
                     (S\otimes_\Lambda\operatorname{Frac}\Lambda)=1.
                                                                         \tag{10}
\]

Both the chosen reflected family kappa and the geometric family
must have nonzero variable components in this same space. Then
their **full global classes** are proportional over its fraction
field. Equal ordinary images alone would not prove this.

A standard sufficient source is Castella--Do Theorem 3.3.3 and
the proof of Theorem 5.6.1, with `r=1,chi=1`. Its hypotheses
include: E non-CM; p good ordinary and prime to 6N; p split in
K and prime to h_K; the inert conductor factor squarefree with
an odd number of prime factors; `gcd(pN,D_K)=1`; residual
absolute irreducibility and distinguishedness; and big image in
the source's sense, namely an image containing SL2(Z_p).
Their exact source conditions, rather than a paraphrase, must
be checked for each application. Its auxiliary Euler-system
witness may use a different character from the one computed.

This source proves the rank of the **entire compact module**.
It is not an inference from the vanishing of a universal-norm
image at the base. A different proof of (10), or a direct full
class comparison, can replace this source.

### 3.2 Full classical specialization

Use a genuine geometric family, for example the BSV family in
[BSV_REPAIR.md](BSV_REPAIR.md). At the required `(2,k,k)`
classical weights, prove its specialization is the projected
etale Abel--Jacobi class used by the full syntomic formula,
up to a nonzero scalar or an explicitly controlled correspondence.

For BSV, the repair uses Theorem 8.1, the audited exponent-zero
extension of Proposition 8.3, and the full cuspidal extension
of Proposition 3.7. It explicitly retains normalized ordinary
duality and the cusp correction. Its classical sequence is
`k_n=1+2(p-1)p^n`. The weight-one hypotheses include p-regularity
and the source's exclusion of certain real quadratic self-twists.

For a proposed alternative construction, the falsifiable target
is the full normalized extension-class diagram: coefficient
specialization, residue/invariant generator, Gysin/trace maps,
and the two dual towers must agree. Merely replacing a raw
dual distribution sheaf by a symmetric power fails this test.

### 3.3 Both local coordinates and analytic continuation

Prove the CM test tensor selects the full rank-two variable
component and eliminates the auxiliary mixed components for
every elliptic test vector. Apply syntomic/etale Abel--Jacobi
compatibility to that same class. Match the **normalized**
regulator with both independent elliptic test vectors and derive
its full adjoint Euler operator.

The resulting fixed-weight identities must imply a genuine
analytic wedge identity of the form (5), after the stated
cancellations. The superflat continuation argument in
`fixed_weight_syntomic/PROJECTIVE_INTERPOLATION.md` is one
such method. It does not analytically interpolate `p^s` or a
factorial. It does not require the pointwise scalar factors to
vary analytically.

Ordinary and tame test-vector choices act through multiplicity
spaces of the full elliptic representation. Prove their maps
are scalar on the elliptic factor, with the chosen factor
nonzero at the base, rather than inferring this from an
ordinary coordinate. A finite extension of coefficients may
be used throughout; external coefficients remain distinct
from the local unramified field acted on by Frobenius.

The generic scalar between the geometric and reflected families
may have a zero or pole. It changes order and absolute scale,
but not the leading projective line. The theta identity for
the actual reflected family supplies its regulator order two
separately. Reflection is not performed on the meromorphically
rescaled geometric representative.

## 4. A general formula for the base exceptional line

In the CH unramified base branch, retain the fixed self-dual
elliptic realization and put

\[
 F^2-a_pF+p=0,\qquad \varphi=F/p,
 \qquad A_\varphi=(1-p^{-1}\varphi^{-1})(1-\varphi)^{-1}.
\]

The normalized base interpolation identifies its image line
with `A_phi^dagger` applied to the Hodge line. A common period
scalar is harmless. In an alternating plane
`A^dagger=det(A)A^-1`. Direct algebra gives

\[
 A_\varphi=
 \frac{(p-a_p)^2-p+(2p-a_p)F}{p(p+1-a_p)},\qquad
 \det A_\varphi=1,
\]

\[
 A_\varphi^{-1}
    =\frac{p(p-1)+(a_p-2p)F}{p(p+1-a_p)}.                          \tag{11}
\]

Thus a reusable projective representative is

\[
              \boxed{\zeta\ \parallel\
                 \bigl[p(p-1)+(a_p-2p)F\bigr]\omega_E.}            \tag{12}
\]

To verify (11), use `F^-1=(a_p-F)/p` and
`(p-F)(p-a_p+F)=p(p+1-a_p)`. The determinants of
`1-F^-1` and `1-F/p` are both `(p+1-a_p)/p`.
These denominators are nonzero. They need not be integral units.

Formula (12) generalizes the pilot numerator `20-13F` when
`p=5,a_p=-3`. The leading comparison matrix `K(0)` is still a
separate arithmetic computation; the pilot's particular matrix
is not universal. A different finite-character branch or
different regulator normalization must first be matched to
the stated base formula, rather than assumed to share it.

## 5. Invariance and meaningful failure modes

The nonzero test is invariant under a common basis change in
GL2, nonzero scalar changes of either line, and a parameter
change with nonzero derivative. Finite coefficient extension
also preserves equality or inequality of the lines. Finite
precision bounds must be transported through those operations;
a nonintegral basis change can lose digits.

An augmentation-unit change of the **actual** global family is
also harmless for localization. If `u(t)=u0+u1*t+...`, then

\[
 x'_0=u_0x_0+2u_1\kappa_0
 \quad\text{for}\quad
 x'=\frac{u\kappa-c(u\kappa)}t.
\]

The base class kappa0 has zero localization, by strictness and
conjugation-invariance. Thus the finite logarithm scales by
the nonzero u0. This statement does not extend to an arbitrary
nonunit: replacing kappa by `t*kappa` gives reflected base
`2*kappa0`, whose localization is zero. Meromorphic factors are
used only to transport projective directions, not to change
the reflected class.

Two local countermodels mark the criterion's limits. Let
`M=R^2`, `H_f=L*e1`, and take the second coordinate as the theta
row.

* If `P=diag(t,1)` and `y=(t^2,t^3)`, then `Theta=t^3`, the
  leading vector `(1,1)` is outside the base image `L*e2`, but
  `sp(y/t)=0`. Exact order two cannot simply be replaced by
  a higher order.
* If `P=diag(t^2,1)` and `y=(t,t^2)`, then `Theta=t^2` and
  `sp(y/t)=e1` is nonzero, but the quadratic leading vector
  lies on the base image line. Failure of the direction test
  does not prove zero localization.

These are algebraic models of the logic, not claimed elliptic
realizations.

## 6. Falsifiable gates for another curve

| Gate | Evidence required | A failure means |
|---|---|---|
| Eligible arithmetic data | Curve, K, p, ordinary roots, CM character, exact source hypotheses | This chosen source package cannot yet be applied |
| Global reflected family | Full strictness, actual base c-invariance, specialization/division | No justified global quotient has been constructed |
| Exact theta order two | Exact constant/linear zeros and nonzero quadratic coefficient, with normalization bridge | The quadratic theorem is unavailable; more finite digits alone do not create exact zeros |
| Correct finite local condition | CH control theorem or an explicit `ker(mu P0)=H_f` identity | Scalar vanishing cannot be called finite localization |
| One full global line | Rank-one theorem with its hypotheses, or direct full class identification | Ordinary scalar agreement leaves the second coordinate undetermined |
| Full projected specialization | BSV repair or another complete normalized extension-class comparison | The analytic vector is not yet attached to the arithmetic family |
| Full local comparison | Same CM block, both elliptic tests, normalized averaging and adjoints | The exceptional direction may be in the wrong coordinates |
| Actual infinite analytic coefficient | Proven exact lower zeros, coefficient/tail bounds, shared basis | A finite truncated fit remains only a finite calculation |
| Finite line separation | Valid primitive ball certificate with nonzero determinant residue | Zero residue is inconclusive; increase precision or change the test case |

The family and local formula arguments may be reused with checked
hypotheses. The theta coefficient, Frobenius matrix, leading
analytic vector, test-vector nonzero factors, and arithmetic
eligibility are specific to each new curve. The order-seven
structure of `Q(sqrt(-71))` simplifies some auxiliary checks;
it is not required by the algebraic criterion.

[criterion-gates-template.json](criterion-gates-template.json)
records these gates without granting a machine-verified status
to mathematical assertions. The finite certificate contract and
checker are documented in [CERTIFICATE.md](CERTIFICATE.md).

## References and proof level

The local implication and formula (11) are proved in this note.
The global module argument uses exact Galois cohomology and the
identified published sources. These arguments are not new Lean
theorems.

* Castella--Hsieh, [primary PDF](https://web.math.ucsb.edu/~castella/Kato-print.pdf):
  Definition 3.3, (3.9), Theorems 3.4, 3.6, 4.5, and Corollary 3.7.
* Castella--Do, [primary PDF](https://kimtuando.github.io/website/Schoen_CM.pdf):
  Notation 3.3.2, Theorem 3.3.3, and the proof of Theorem 5.6.1
  under the hypotheses of Theorem 5.5.1.
* BSV and its official erratum, with exact source locations and
  the two edge extensions: [BSV_REPAIR.md](BSV_REPAIR.md).
* Full local conventions and base-line calculation:
  [normalized_local_comparison](../normalized_local_comparison/README.md).
* Source and finite-computation ledger for the first pilot:
  [PILOT_LOCALIZATION_THEOREM.md](../PILOT_LOCALIZATION_THEOREM.md).

The remaining arithmetic gap after a successful application is
the passage from the constructed Selmer class to rational points,
or control of the relevant Tate--Shafarevich contribution. The
theorem deliberately stops at the nonzero finite localization in (8).
