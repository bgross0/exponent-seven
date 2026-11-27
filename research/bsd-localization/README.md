# Rank-two BSD: projective target and finite projection certificates

Research branch: `bsd-projection-certificates`, continuing
`bsd-de-rham-preparation` commit `704a86d0f48f0f037d327ee9339a7e211e1a2652`.
The latter continued
`bsd-tame-trace-computation` commit `0667f5e23fa33a4cfc09ccd80abaedc94c9d5297`.
The latter continued `bsd-finite-log-coordinate` commit
`29eaf5a02bff8907b9914cdf71221da8bb6e6896`.
That branch continued `bsd-derived-localization` at
`46ca3323b6b8f10f2334925220a5c75a487a2bfb`.
The preceding audit commit is `12c58ddf46ebd89141d4392b519ca7ae533e67ea`.
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

This continuation proves that the ordinary second coefficient is already
nonzero under the supplied theta/arithmetic and analytic inputs. The new
numerical target is the ratio of the critical and ordinary coefficients.
It provides an explicit conditional CM tail inequality, a simpler cubic
product input with a fixed Euler correction, and executable two-slope
projection certificates with measured precision loss. Bounded Sage
geometry jobs run on the research branch. The reflected class's finite
logarithm has not been evaluated; identifying the relevant line under an
arithmetic regulator comparison remains a substantive theorem to prove.

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
| Finite-coordinate extraction | An invariant first coefficient of a regular finite-log lift, or a second coefficient of a calibrated complementary vector regulator | [Proof and exact algebra](finite_log_reciprocity/FINITE_COORDINATE.md); an arithmetic reciprocity comparison is still required |
| Explicit interpolation annihilator | `zeta=(20I-13F)/45 omega`, computed modulo `5^7` | [Local crystalline proof](local_crystalline/README.md), using exact Frobenius modulo `5^8` |
| Cyclotomic strict height | `h_cyc(R,R)/5=1 mod5`, for `R=(log Q/5)P-(log P/5)Q` | [Exact rational height certificate](local_crystalline/height_leading.py); this is a cyclotomic quantity |
| CM analytic input | Weight-one CM forms and their first two normalized weight derivatives, both p-adic embeddings | [Executable input and scope](reflected_pilot/README.md); no projected vector L-value or global class is computed |
| Actual tame traces | Both traces equal `Xi+U71 Xi`; eight inputs through q128 and weight order two modulo 5^5 | [Proof](tame_trace_theory/TAME_TRACE.md), [computation](tame_trace_compute/README.md), and [independent audit](tame_trace_audit/README.md) |
| Exact elliptic projector | Complete rank-two E factor; polynomial in T2 and T3 with at most one 5-adic digit of loss | [Witness and checker](elliptic_projection/README.md); proper de Rham reduction of the input remains separate |
| Low-weight interpolation | Fourteen classical CM weights suffice for a second coefficient modulo 5^12 in an integral fixed module | [Proof and exact weights](tame_trace_audit/README.md); reduction and normalization denominators must be added |
| Global obstruction criterion | The reflected logarithm is nonzero exactly when the augmentation-localized global H2 has length one, under the listed identifications | [Conditional arithmetic reduction](ambient_arithmetic/README.md); the actual first global Bockstein has not been evaluated |
| Analytic target reduction | Second-factor depletion is cohomologically invisible; the normalized elliptic vector is even in weight and fixed by coefficient conjugation | [Proof](analytic_target_audit/README.md) and [finite identities](weight_reflection/README.md); the entire first vector coefficient is zero |
| Larger executable input | One cubic-field representative through q6825 and weight order two modulo 5^12; generated in 16.896 seconds | [Data, algorithms, and measured benchmarks](trace_scaling/README.md); raw series, not yet projected de Rham coordinates |
| Two-slope calibration | Explicit invertible conversion from the two p-stabilizations to omega, eta modulo 5^7 | [Calibration](de_rham_strategy/README.md); the U and F slope labels are interchanged |
| Proper residue filter | U5^2-1 kills the residue quotient; its elliptic inverse is -(F+2I)/9 | [Proof and exact matrix check](residue_filter/README.md); zero correction loss in an F-stable integral lattice |
| Finite geometry handoff | A 1333-dimensional six-digit Katz gate and an exact 195-dimensional pole-order core | [Executable Sage jobs and scope](de_rham_strategy/README.md); cloud-run provenance is recorded separately |
| Ordinary second coefficient | ord_W a_E(W)=2, using the supplied theta input and Castella--Do's conductor-one factorization | [Leading comparison](leading_comparison/README.md); no value or valuation of a2 is claimed |
| Projective numerical target | r_E=b2/a2 is invariant under regular scalar normalization and parameter change | [Line-level comparison target](leading_comparison/README.md); the arithmetic bad line is still unidentified |
| Conditional quantitative tail | Explicit pole-index bound; cutoff17 gives eight digits after saturated pole reduction | [Proof and exact inequalities](cm_tail_bound/README.md), with the fixed-weight Coleman realization (CF) stated explicitly |
| Undepleted cubic representative | Tr71 of (Q+sigma Q)/2 through q6825 modulo5^12; an explicit R(U) recovers the original E projection | [Product and Euler correction](cm_product_transfer/README.md); one-digit worst-case correction loss |
| Finite projection implementation | Both slopes, exact inverse-minor witnesses, and valuation-sensitive normalization | [Executable adapter and proof](projection_backend/README.md); actual infinite input/operator comparison remains separate |

These additions contain mathematical proofs and exact Python calculations.
They are **not additional Lean kernel-checked theorems**. The supplied
package has its own formal layer and verification receipts. The new finite
matrix examples are explicitly abstract algebraic models, not elliptic
curves or counterexamples to BSD.

## Current frontier: compute a direction and identify the exceptional line

Write the analytic vector in its calibrated elliptic stabilization basis:

\[
 L(W)=a_E(W)[f_\alpha]+b_E(W)[f_\beta].
\]

The preceding reflection argument gave L(0)=L'(0)=0. The new
[leading-comparison proof](leading_comparison/README.md) combines this
with Castella--Do Proposition5.2.1 and the actual conductor-one theta
input to prove

\[
 \operatorname{ord}_W a_E(W)=2.
\]

The source permits the conductor-one class characters used here. At the
minimal common tame level, the two diagonal CM placements come from
level71 and vanish in the E-new projection; the two cross placements
have the same output. Thus a good triple-product test vector gives a
regular scalar multiple of a_E. Its exact order two forces the same
order for a_E. The proof checks regularity in the CM weight variables;
it does not infer it merely from nonvanishing of a scalar function.

Consequently the next numerical target can be

\[
 r_E=\frac{[W^2]b_E}{[W^2]a_E}\in\mathbf Q_5(\xi).
\]

This ratio removes common period and coordinate scales. Under the
appropriate arithmetic comparison, the reflected logarithm is nonzero
exactly when the second vector lies outside the image of the rank-one
base regulator. It therefore suffices to identify that one line, rather
than every entry of an absolute comparison matrix. That identification
is still unproved. The note gives a DL Euler-line candidate and an exact
model showing why the known ordinary scalar law does not determine it.

### A quantitative bound for a simpler input

The new [tail theorem](cm_tail_bound/README.md) uses the explicit
fixed-weight Coleman-family realization (CF) and compatible integral
Katz/pole models. The [source review](cm_tail_bound/CF_REVIEW.md) supplies
the qualitative realization for the actual normalized CM family from
published analytic theorems. It assumes no quantitative radius or integral
norm for that family. A unit-eigenvector minimum argument, together
with published radius estimates, then yields the second-coefficient
numerator bound at pole index i:

\[
 v_5(B_{i,2})\ge
 \max\left(0,\left\lceil\frac{20i-58}{25}\right\rceil-4\right).
\]

After saturated pole reduction the loss is at most floor(log_5(i-1)).
Keeping pole indices through10,12,15,17 gives discarded-tail bounds of
2,4,6,8 digits respectively. These numbers precede the actual later
coordinate and normalization losses. The analytic argument is separate
from the finite q-expansion checker; a backend still has to identify its
computed lattice with the model used in this bound.

The bounded input is the ordinary CM product Q=h_-s*V389(h_s). Its cubic
average has been generated through q6825 modulo5^12 in22.160 seconds.
The [new artifact](cm_product_transfer/cubic-product-6825-12.json.gz)
is230499 bytes compressed. With tau=1-xi-xi^2, its proper E projection
is converted to the original depleted input by

\[
 R(U)=\frac{U^2-\tau U+1}{U(U-\tau/2)}.
\]

This operator is constant in W, integral on the ordinary eigenline, and
has valuation -1 on the critical eigenline. The inverse is integral.
The exact field and matrix checks are in
[cm_product_transfer](cm_product_transfer/README.md).

### Executable finite projection, with corrected error accounting

Once a Katz geometry capsule is available, run:

```sh
python research/bsd-localization/projection_backend/project_capsule.py --katz de-rham-katz6/katz-capsule.json.gz --input-kind undepleted-product --output undepleted-projection-output
```

The adapter fits all eleven input/fixture columns, isolates both dual
eigenfunctionals, and normalizes them against the two actual elliptic
p-stabilizations. It retains the Q output separately from the Euler-
corrected depleted output. Certificates contain finite equations and
scaled inverse-minor witnesses that can be verified independently of
the elimination algorithm.

The normalization bound has been corrected. A numerator N and denominator
D known to precisions a,b, with t a lower bound for v(N) and v=v(D)<b,
give quotient precision min(a-v,b+t-2v). The previous unconditional
M-c-v statement was too optimistic for nonintegral outputs. An exact
counterexample and the corrected theorem are included.

The finite certificate still needs the compatible infinite input and
operator comparison before it becomes a theorem about the analytic CM
vector. The conditional tail estimate is stated in a saturated pole
model; it must not be inserted directly as a precision label on an
unrelated finite Katz-fit row.

## Preceding reduction: one cubic input and the finite geometry

The new [analytic audit](analytic_target_audit/README.md) removes redundant
inputs before the expensive geometry. The eight saved raw variants do not
have identical q-series, but have the same proper elliptic output after
the prescribed identifications. The projected output is fixed by
sigma(zeta7)=zeta7^-1. It can therefore be computed from one averaged
representative over

\[
 L^+=\mathbf Q_5(\xi),\qquad
 \xi=\zeta_7+\zeta_7^{-1},\qquad
 \xi^3+\xi^2-2\xi-1=0.
\]

This is a sixteen-fold reduction in scalar input storage: eight inputs
over a degree-six field become one input over a degree-three field. It is
not a measured sixteen-fold speedup for the whole project. Both elliptic
de Rham directions are retained.

If s=k-1 and L(s) is the properly normalized elliptic projection, then

\[
 \langle389\rangle^{s/2}L(s)
 \quad\text{is even in }s,\qquad L(0)=L'(0)=0.
\]

The base zero uses Darmon--Lauder's proved Theorem 3.1 and L(E,1)=0;
the first zero follows from the weight symmetry. No conjectural derivative
identity is used for those zeros. The desired remaining analytic datum is
the vector coefficient L2=[W^2]L(W), with W=6^s-1. The stored second jet is
a Taylor coefficient, not the second derivative (which is twice it).

### The input is ready

[cubic-trace-6825-12.json.gz](trace_scaling/cubic-trace-6825-12.json.gz)
contains all three Taylor orders through q6825 modulo 5^12. Generation
took 16.896 seconds and about 129 MiB peak resident memory in this
environment. The compressed file is 224893 bytes. The generator only
computes the coefficients consumed by the trace, shares the weight-jet
products, and uses exact packed-integer convolution. It avoids generating
all discarded variants. Independent full-precision and lower-precision
overlap checks pass; details and source hashes are in the
[benchmark report](trace_scaling/README.md).

The geometry is independent of the cubic coefficients. Build it once over
the base 5-adic ring and apply it to the three scalar columns. The next
job on a node with Sage is:

```sh
timeout 45m sage -python research/bsd-localization/de_rham_strategy/backend_probe.py --mode katz --digits 6 --output de-rham-katz6
```

This uses Sage's documented higher_level_UpGj implementation. It exports
the finite U5 matrix, its q-expansion basis, both classical elliptic
p-stabilizations, and runtime/source provenance. It checks the finite
matrix identities. The cloud job is tracked on the research branch.
The subsequent dual-eigenvector extraction is now implemented in
[projection_backend](projection_backend/README.md). The analytic tail
argument is a separate theorem and must be connected to the computed
lattice. Six matrix digits do not certify six final
vector digits. The precise precision contract is in the
[backend note](de_rham_strategy/README.md).

A second node can construct the smaller exact algebraic core independently:

```sh
timeout 45m sage -python research/bsd-localization/de_rham_strategy/backend_probe.py --mode pole-core --output de-rham-pole-core
```

This builds the quotient of weight-ten numerators by 98 derivative
relations, leaving dimension 195. Its classical q-expansion bound proves
those finite numerator identities; it does not truncate the analytic
input automatically. A derived cup-product/weight-twelve-trace formula
offers a route to extracting the E component without constructing every
ambient Hecke operator, but its numerical implementation remains pending.

### Two obligations that computation alone will not remove

1. **An integral tail bound.** The CM identity
   d^-s(g_s^[5])=h_-s^[5] rewrites the difficult inverse-Bol expression as a
   product of ordinary CM-family sections. This specializes the remaining
   problem to their norm on a fixed strict neighborhood and the growth of
   their weight jets. Analytic overconvergence and integral q-coefficients
   alone do not supply the advertised Katz-lattice precision. See the
   [radius audit](analytic_target_audit/RADIUS_AND_RESIDUES.md).
2. **A leading-order arithmetic comparison.** The analytic vector must be
   matched to the actual CH localization and its finite-log regulator.
   Because both lower vector coefficients vanish, this stage needs only
   the constant comparison matrix, the linear parameter scale, and the
   finite-log normalization at leading order. A nonzero second analytic
   vector by itself does not prove a nonzero reflected logarithm. The
   [target audit](analytic_target_audit/README.md) proves the simplification
   and retains an exact insufficiency model.

The global Bockstein criterion below is an independent arithmetic route
to the same missing nonvanishing. It remains worth pursuing in parallel;
the completed cyclotomic height concerns a different deformation direction.

## The new finite-coordinate target

Let `y=loc_v(kappa_infinity)` at the prime where the CH scalar Coleman
map is nonzero. The other full localization vanishes, so
`loc_v(x)=y/t`. At the base, `y_0=0`. In a local basis `w,n`, with
`w` generating the finite direction and normalized by `log(w_0)=1`,
and `F(n)=1`, write

\[
y=t\,a(t)w+t^2b(t)n.
\]

The scalar theta identity determines `t^2 b(t)`; the wanted finite
logarithm is `a(0)`. The proof identifies a coordinate-independent
extraction rule. If `G` is any regular lift of the finite logarithm,

\[
\log_\omega(x_0)=[t]G(y).
\]

Changing `G` by another lift does not alter that coefficient. In
particular, more precision in the scalar theta series does not evaluate
this different coordinate without an additional arithmetic relation.

CH's base-character interpolation operator identifies an explicit
complementary pairing. For `phi=F/5` on `H^1_et(E)(1)`, set

\[
\zeta=(1-F/5)(1-F^{-1})^{-1}\omega
       =\frac{20I-13F}{45}\omega.
\]

The pairing `Col_zeta` vanishes at the base on every local class.
If its divided map is calibrated by
`(Col_zeta/t)_0 = c_zeta*log_omega` on the finite line, with
`c_zeta != 0`, the exact desired expression is

\[
\boxed{\log_\omega(x_0)=c_\zeta^{-1}[t^2]\operatorname{Col}_\zeta(y).}
\]

The local simple-determinant and normalization comparison, followed by
an explicit reciprocity law for this complementary component, are
specified in the [finite-coordinate note](finite_log_reciprocity/FINITE_COORDINATE.md).
These are proof obligations, not assumptions silently used to report
nonvanishing.

The exact Frobenius computation gives

\[
F\equiv\begin{pmatrix}285070&163221\\276685&105552\end{pmatrix}
\pmod{390625},\qquad
\zeta\equiv13133\omega+32916\eta\pmod{78125},
\]

where `omega=dx/(2y+1)`, `eta=x omega`, and matrix columns are images.
The implementation includes a rigorous infinite-tail bound and agrees
with an independently published `37a1` unit-root/E2 example.

The three ordinary dominant triple-product quotients all annihilate the
deepest all-plus line containing the missing finite coordinate. Merely
permuting these quotients does not recover it. Darmon--Lauder's full
de Rham-valued analytic construction supplies a concrete second-jet
candidate to investigate. Its comparison with this CH class is an
additional theorem, and the derivative assertion in their paper is
explicitly conjectural. The
[source ledger](finite_log_reciprocity/SOURCE_LEDGER.md) records exact
theorem scopes, including the recent finite-slope and CM results.

## New completed step: actual traces and an exact projector

The two CM cross products at tame level `71*389=27619` have fixed total
weight two. The new [trace proof](tame_trace_theory/TAME_TRACE.md)
tracks the native CM Fricke sign, the oldform character at 389, and the
unique depleted inverse-Bol primitive. It proves that the whole family
is Fricke-71 invariant. Consequently the two geometric degeneracy traces
are equal, including their weight derivatives:

\[
\boxed{\operatorname{Tr}_1\Xi_j=\operatorname{Tr}_2\Xi_j
=\Xi_j+U_{71}\Xi_j,\qquad j=0,1,2.}
\]

This bypasses independent construction of all 72 cusp expansions for
these particular inputs. The proof uses analytic continuation from a
sequence of classical weights accumulating at weight one, not a finite
numerical test of the identity.

The [computed trace artifact](tame_trace_compute/traces.json) contains
all eight inputs (two p-adic embeddings, two cross-oldform placements,
and two depletion variants), each through `q^128` and `W^2`, modulo
`5^5`. Generation requires raw CM input through `q^9088`. It checks all
98,328 overlapping raw vector coefficients against the earlier 12-digit
archive. An independent algebraic weight-five specialization supplies
5,776 further vector-coefficient checks. The oldspace normalization is
tested with the actual elliptic q-series and independently with Delta
at weight twelve. These are finite input checks, not a computation of
the projected arithmetic class.

On the elliptic oldspace the trace/pullback matrix is

\[
\begin{pmatrix}72&-10\\-10&72\end{pmatrix}.
\]

The Fricke-plus symmetry reduces recovery to

\[
\Pi_{E,\mathrm{old}}\Xi_j
=(\pi_1^*+\pi_2^*)\left(\frac1{62}\Pi_E\operatorname{Tr}_1\Xi_j\right).
\]

This is a two-dimensional de Rham vector, not an ordinary-only line.
The factor 62 is a 5-adic unit. The final global test vector still has
to use its prescribed combination of the degeneracy coordinates.

The separate [elliptic projector certificate](elliptic_projection/README.md)
constructs the 65-dimensional relative Manin-symbol space at level 389
and isolates the complete rank-two elliptic factor. With `A=T2+4*T3`,
an explicit monic degree-32 integer polynomial gives

\[
P_E=\frac{q(A)}{q(-10)},\qquad
q(-10)=4991964896182583587087694480,\quad v_5(q(-10))=1.
\]

The identity is checked entry-by-entry over the rationals. It transfers
as an identity of Hecke correspondences to proper de Rham cohomology.
On any Hecke-stable integral lattice the projection loses at most one
5-adic digit. The Manin matrix has an entry `-1/40`, demonstrating why
one cannot assume this projector integral. Its two eigenvector columns
are not silently identified with the crystalline `omega,eta` basis.

### Correct resource accounting

For the stated 12-digit reference Katz setup:

| Quantity | At tame level 27619 | After trace, at tame level 389 |
|---|---:|---:|
| Weight-78 modular-form dimension | 180182 | 2503 |
| q coefficients consumed by the projection stage | 912600 | 12675 |
| Raw CM bound to provide those trace coefficients | 912600 | 899925 |
| One dense matrix, four-byte entries | 129862212496 bytes | 25060036 bytes |
| One dense matrix, eight-byte working entries | 259724424992 bytes | 50120072 bytes |

The matrix-storage estimate improves by about 5182. The factor 72 in
q precision concerns the **projection stage**: obtaining `B` traced
coefficients still needs raw coefficients through `71B`. It is not a
72-fold reduction in raw CM generation, nor a measured runtime gain.
The new trace identity controls the cusp operation, while overconvergent
reduction, its tail bound, extra matrices, and final normalization retain
their own costs.

The q128 pilot exceeds the classical weight-two Sturm bound 65. That
is useful for classical regressions, but it does not certify an arbitrary
overconvergent jet from finitely many q coefficients. The next missing
computational operation is the proper de Rham reduction at level 389
with both slopes and bounded denominators. A full regulator comparison
with the CH class remains a separate mathematical obligation.

## A global test independent of computing the full vector L-function

The [ambient arithmetic note](ambient_arithmetic/README.md) sharpens the
previous abstract obstruction models. With `R` the augmentation discrete
valuation ring, let

\[
M=H^1_{\rm Iw}(K_\infty,V)_R,\quad
B=H^2_{\rm Iw}(K_\infty,V)_R,\quad
N=R\kappa+Rc\kappa.
\]

The note lists and analyzes the exact Poitou--Tate sequence, local
Coleman saturation, and anticyclotomic main-conjecture equality needed
to obtain

\[
\operatorname{length}_R B=\operatorname{length}_R(M/N),\qquad
\ell(x_0)\ne0\Longleftrightarrow\operatorname{length}_R B=1.
\]

Using the pilot's two-dimensional plus Selmer space and nonzero finite
localization further reduces the possibilities to `B=R/(t)` and
`B=R/(t^2)`. The conjugation sign in the specialization sequence is
tracked explicitly. The first alternative gives a transverse reflected
class; the second makes it strict.

A first global Bockstein, equivalently cup product with the linearized
anticyclotomic character, distinguishes the two cases. If an actual
global cohomology complex is represented through first order by
`D(t)=D0+tD1+...`, its rank is

\[
\operatorname{rank}[D_0\mid D_1K_0]-\operatorname{rank}D_0,
\qquad \operatorname{im}K_0=\ker D_0.
\]

This specifies a second arithmetic route to the missing logarithm.
No certified global presentation or arithmetic cup-product value is
provided in this package; the executable matrices are exact algebraic
fixtures. The cyclotomic height computed separately concerns a
different direction and does not select either anticyclotomic case.

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
python -m pip install -r research/bsd-localization/requirements.txt
python research/bsd-localization/verify_all.py
```

To write a fresh receipt:

```sh
python research/bsd-localization/verify_all.py --receipt research/bsd-localization/verification.json
```

The runner performs 30 checks covering the original arithmetic, p5,
formal-log, reflection, exterior-algebra, finite-coordinate, crystalline,
height, ambient-jet, CM-weight-jet, tame-trace, interpolation, exact Hecke
projector, analytic-target identities, cubic descent, residue and Euler
filters, two-slope calibration, both larger trace inputs, the conditional
tail arithmetic, leading-coordinate identities, and finite projection
certificates. Symbolic checks use SymPy1.14.0; the finite projection
adapter uses NumPy2.3.5 with explicit integer overflow guards. The other
scripts use Python's standard library.
The receipt records exit status, timing, and hashes of sources and
compressed data. This command does not rebuild or reverify the other
thread's CM/Lean package; its input provenance and mathematical scope are
stated above.
