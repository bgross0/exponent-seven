# A full weight-two specialization using the BSV family

Date: 2026-11-27. This note supplies a replacement for the disputed
DR22 raw-moment specialization step. It changes the comparison family
to the **Bertolini--Seveso--Venerucci family**. It does not assert an
identity between the historical BSV and DR22 constructions.

## Result and the issue being repaired

The previous rational projected-edge argument correctly kills the
extra cohomology in the weight-two factor, but that fact alone does
not identify the normalized specialization of a family constructed
through dual cohomology. A raw covariant moment of a distribution
sheaf cannot be substituted for that dual ordinary specialization.
The missing compatibility must be proved or bypassed.

BSV provides a bypass. Its **Theorem 8.1 already includes balanced
triples with a weight equal to two**, and states the specialization
of its actual family using its normalized dual ordinary comparison.
The remaining work is finite-dimensional:

1. Extend the explicit tame-level degeneracy calculation in BSV
   Proposition 8.3 to the zero symmetric exponent in the first factor.
2. Extend the geometric comparison in BSV Proposition 3.7 after the
   cuspidal weight-two projection, identifying its invariant-theoretic
   class with the cusp-corrected DR I cycle.

Both steps are proved below. They identify **full Galois classes**,
before taking any ordinary regulator coordinate. Consequently the
full syntomic formula in DR I can be applied to the specialization
of the BSV family. All coefficient comparisons here are rational;
no claim about integral unit normalizations is made.

### Primary version and erratum

Use BSV, *Reciprocity laws for balanced diagonal classes*, Astérisque
434 (2022), 77--174:

* [Author PDF](https://www.esaga.uni-due.de/f/massimo.bertolini/publications/Ast-BSV1.pdf).
  Printed page numbers below refer to the author's 94-page version.
* [Official erratum](https://www.esaga.uni-due.de/f/massimo.bertolini/publications/Errata-AstBSV1.pdf).

The standing condition in Section 1.1, printed page 3, is **p >= 5**.
The inequality was checked visually; text extraction can misread it
as strict. Thus p=5 is permitted.

The erratum corrects an overly general finite-slope perfect-duality
assertion after (82). It explicitly proves the required duality for
ordinary slope zero, and states that the remainder of the paper is
unaffected. Theorem 8.1 uses the maps `s_(U,0)` in (83), as is visible
in (156), (165), and (167)--(168). This replacement stays in that
ordinary case. It uses no uncorrected assertion about arbitrary
positive slopes.

## 1. Precise replacement proposition

Let p >= 5. Let `(f,g,h)` be ordinary cuspidal Hida families satisfying
the setup and self-duality assumptions of BSV, with common tame level
N prime to p. Specialize to a balanced classical triple of weights

\[
                         (2,k,k),\qquad k\ge3,
\]

whose three forms are ordinary p-stabilizations of forms of tame
level dividing N. The first tame form is cuspidal of weight two and
trivial nebentype. Write

\[
 r=k-2,\quad \mathbf r=(0,r,r),\quad
 \alpha_f,\beta_f,\alpha_g,\beta_g,\alpha_h,\beta_h
\]

for the roots, with the alpha roots ordinary. Use BSV's rational
dualities, degeneracy maps, and Hecke normalizations. Project the
first factor to its cuspidal f-component and use a cusp as the
basepoint in DR I Definition 3.2.

**Proposition.** After the ordinary-to-tame degeneracy identification,
the specialized full BSV class is a nonzero scalar multiple of the
full projected etale Abel--Jacobi class of the DR I `(2,k,k)` cycle.
The scalar is allowed to depend on k and to have positive or
negative p-adic valuation. The proposition permits the classes
themselves to be zero.

More precisely, in BSV's classical invariant-theoretic realization,

\[
 \Pi^\alpha\rho_{(2,k,k)}\kappa_{\rm BSV}
       = E_{\rm BSV}(2,k,k)\,\kappa(f,g,h),                         \tag{1}
\]

where

\[
\begin{split}
 E_{\rm BSV}={}&
 \left(1-\frac{\alpha_f\beta_g\beta_h}{p^{r+2}}\right)
 \left(1-\frac{\beta_f\alpha_g\beta_h}{p^{r+2}}\right)\\
 &\cdot\left(1-\frac{\beta_f\beta_g\alpha_h}{p^{r+2}}\right)
 \left(1-\frac{\beta_f\beta_g\beta_h}{p^{r+2}}\right).             \tag{2}
\end{split}
\]

The class `kappa(f,g,h)` on the right is defined by BSV (41)--(48).
Under the stated rational geometric realization it is the projected
DR I Abel--Jacobi class, up to the overall sign and the fixed
duality conventions described in Section 4 below. Those conventions
give a nonzero scalar, not an elliptic matrix.

### Weight-one CM family hypotheses

The setup of BSV includes Assumption 1.1: a weight-one center
must be classical, cuspidal, p-regular, and have no real
multiplication by a real quadratic field in which p splits.
These conditions are retained in the replacement.

For `K=Q(sqrt(-71))` and an order-seven unramified character
`psi`, `psi != psi^c`, so the two theta series are cuspidal.
Their projective Galois image is the dihedral group of order
fourteen. This group has a unique quotient of order two; the
corresponding quadratic self-twist is the character of the
imaginary field K. Hence these forms have no real quadratic
self-twist. At the selected prime above five the two roots are
`zeta7^2` and `zeta7^-2`, distinct even modulo five. The same
checks hold for the inverse character. Thus BSV's weight-one
conditions hold for the CM pair used here. Their truth is
independent of whether the elliptic factor has conductor 389
or another eligible conductor.

For a different CM pair these checks must be repeated. A
dihedral representation with a different projective image need
not have a unique quadratic self-twist. The word "CM" alone
does not verify BSV's stated hypothesis.

## 2. The normalized specialization is already a source theorem

BSV Section 3 begins with a triple of **nonnegative** symmetric
exponents satisfying the triangle inequalities (Assumption 3.1).
Its invariant is

\[
 \operatorname{Det}_{\mathbf r}
  =[x,y]^{r-r_3}[x,z]^{r-r_2}[y,z]^{r-r_1}.
\]

For `(0,r,r)` this is simply `[y,z]^r`. The class

\[
 \widetilde\kappa_{N,\mathbf r}
   =\operatorname{HS}\,d_*(\operatorname{Det}_{\mathbf r})            \tag{3}
\]

is defined in (43) on the affine modular curve. Its definition
does not require the three exponents to be positive. The rational
self-duality maps `s_i` in (44) include `s_0=id`.

The actual BSV family is defined in (155)--(156) using the big
invariant, diagonal pushforward, Hochschild--Serre, ordinary
cohomology, and the normalized duality maps. Theorem 8.1, printed
page 60, applies to **each balanced classical triple** and gives

\[
 (p-1)\alpha_f\,\rho_w(\kappa_{\rm BSV})
   =\left(1-\frac{\alpha_f\beta_g\beta_h}{p^{r+2}}\right)
      \kappa^\dagger(f,g,h).                                    \tag{4}
\]

Its proof (160)--(168) treats the normalized comparison, including
the duality identity (165), for nonnegative exponents. We use (4)
as that source theorem. We do not replace its maps by raw moments,
and do not assert that a rank-one specialized measure sheaf is a
higher-rank symmetric-power sheaf.

For the CM weight-one branches in this project, a suitable classical
sequence is

\[
                  s_n=2(p-1)p^n,\qquad k_n=1+s_n.
\]

This respects BSV's congruence modulo `2(p-1)` around its centers.
At p=5 use `s_n=8*5^n`. It still approaches the same weight-one
germ, and the superflat estimates and first nonzero analytic
coefficient are unchanged. It is unnecessary to continue factors
such as `p^s` or factorials analytically.

## 3. Extending the explicit p-degeneracy calculation

BSV Proposition 8.3 is printed for all three weights at least three.
Here is the extension needed, with the exact point at which the
zero exponent enters.

### 3.1 Coefficient maps at exponent zero

The maps in Section 2.3, (16)--(22), arise from the relative Tate
module of the universal elliptic curve and finite base maps.
For every i >= 0 their i-th symmetric-power maps are defined. At
i=0 the symmetric-power coefficient map of either p-isogeny is
the identity. In particular

\[
            \lambda_p^{0*}\lambda_{p*}^{0}=p^0\,\mathrm{id}
                  =\mathrm{id},\qquad s_0=\mathrm{id}.            \tag{5}
\]

One must not substitute degree-p trace on the fibre's constant
cohomology for this coefficient map. The finite-map degrees are
already recorded separately in the pushforwards by `nu`, `mu`,
and the covers used in the proof.

The declaration `u >= 1` preceding the maps `pi_i^u` in Step 2 of
Proposition 8.3 is extended by these definitions at u=0. The
equations then have the same meaning.

### 3.2 The three steps survive

* **Step 1, (174)--(175):** the invariant transforms by `p^r` under
  simultaneous isogenies. At `(0,r,r)` this follows immediately
  from `[y,z]^r`; the first coefficient map is the identity. The
  degrees `p+1` and `p-1` of the base covers are unchanged.
* **Step 2, (176)--(180):** the finite Galois-cover transfer identity
  and push-pull formulas remain valid for the constant sheaf in
  the first factor. Every occurrence of `p^{r_1}` becomes `1`.
  All other exponents are nonnegative under the triangle
  inequalities. No step divides by `r_1` or by a vanishing
  factorial. The eight simultaneous and mixed pushforward
  identities therefore hold with `r_1=0`.
* **Step 3, (181)--(183):** projection to the cuspidal forms and
  expansion of the p-stabilization operator are finite algebra.
  Its factorization uses only `alpha_x beta_x=chi_x(p)p^{w_x-1}`,
  self-duality of the characters, and `2r=r_1+r_2+r_3`. These
  identities still hold with `r_1=0`.

These checks extend the displayed conclusion of Proposition 8.3:

\[
 \Pi^\alpha\kappa^\dagger
   =(p-1)\alpha_f
      \prod_{\epsilon\in\{(\alpha_g,\beta_h),
                           (\beta_g,\alpha_h),
                           (\beta_g,\beta_h)\}}
       \left(1-\frac{\beta_f\epsilon_1\epsilon_2}{p^{r+2}}\right)
        \kappa(f,g,h).                                          \tag{6}
\]

Combining (4) and (6) and cancelling the nonzero `(p-1)alpha_f`
gives (1). The independent source audit in
[edge_specialization_audit](../edge_specialization_audit/README.md)
checks the map definitions and all three steps separately.

All four factors in (2) are nonzero. Since the forms have good
reduction at p, each numerator has complex absolute value
`p^{(1+2(k-1))/2}`. Dividing by `p^k=p^{r+2}` gives absolute
value `p^(-1/2)`, which differs from one. This argument proves
nonvanishing, not an integral-unit or analytic-interpolation claim.

The map `Pi^alpha` is the same Galois-equivariant ordinary-to-tame
identification on the full p-old representation. It retains a
rank-two elliptic Galois factor. Its comparison with another
nonzero Galois-equivariant identification of that factor is scalar
when the elliptic representation is absolutely irreducible. It is
not the ordinary rank-one projection on elliptic de Rham cohomology.

## 4. The edge invariant is the projected DR I cycle

This is the full geometric part of the replacement.

Let `Y=Y_1(N)`, let `X` be its smooth proper compactification, and
let `E_Y -> Y` be the universal elliptic curve. At `(0,r,r)` take

\[
 A=\varnothing,\qquad B=C=\{1,\ldots,r\}.
\]

The open geometric diagonal is the image of

\[
 E_Y^r\longrightarrow Y\times E_Y^r\times E_Y^r,
 \qquad (x;P_1,\ldots,P_r)
       \longmapsto(x;(x;P_1,\ldots,P_r);(x;P_1,\ldots,P_r)).        \tag{7}
\]

BSV Proposition 3.7 compares this type of cycle with (3) but its
section assumes positive exponents. We now justify the two places
requiring adjustment at the edge.

### 4.1 The relative invariant calculation

The relative diagonal of a single elliptic curve has middle
Kunneth component `x tensor y - y tensor x`, in a fixed symplectic
basis. For r factors it has component

\[
                         (x\otimes y-y\otimes x)^{\otimes r}.
\]

Regroup the factors into the B and C blocks and apply the rational
Scholl symmetrizers. The resulting polynomial is, up to the fixed
Koszul sign,

\[
 \sum_{j=0}^r(-1)^j\binom rj
     x_B^{r-j}y_B^j x_C^j y_C^{r-j}
        =(x_By_C-y_Bx_C)^r.                                    \tag{8}
\]

This is exactly `Det_(0,r,r)` from BSV (41). Its coefficient of
`x_B^r y_C^r` is one, so the comparison factor is nonzero for
every r, including r >= p. Changing consistently between symmetric
powers and divided powers can introduce rational factorial
normalizations; it does not introduce a zero map over `Q_p`.
In BSV's polynomial and Scholl conventions, (8) is its identity
(61)--(63), with the overall sign allowed in Proposition 3.7.

This calculation directly identifies the **residue/invariant**;
it does not infer agreement of extensions from null-homology alone.
Apply the same functorial diagram as BSV (60): relative Gysin for
(7), the Leray maps, and diagonal pushforward commute with the
absolute cycle-class map. Applying Hochschild--Serre afterwards
therefore gives (3) from the projected geometric cycle.

### 4.2 The missing middle-degree concentration

The exponent-zero first factor has extra degree-zero and degree-two
cohomology on `X`. Project to the cuspidal f-component. An explicit
filter which is the identity there and kills these two trivial
components is

\[
                 R_f=\frac{q+1-T_q}{q+1-a_q(f)},\qquad q\nmid Np.  \tag{9}
\]

The denominator is nonzero by the weight-two Weil bound. The other
two positive Scholl components have middle degree `r+1`. After
the cuspidal first-factor projection, the surviving total geometric
cohomology is therefore in degree `2r+3`. The codimension-`r+2`
cycle has zero projected geometric class in degree `2r+4`, and
its projected Abel--Jacobi extension is defined in the desired
tensor of three `H^1` groups.

This restores precisely the concentration used around BSV (59).
The remaining diagrams in the proof of Proposition 3.7 are
functoriality diagrams and still commute after applying this
projector. We use the full cuspidal isotypic projection as well as
the elementary filter (9); (9) alone is not asserted to be an
idempotent cutting out the entire f-motive.

On the affine curve, `H^3(Y^3,S_[r])` is already the tensor of the
three `H^1` groups, since each curve has geometric cohomological
dimension one. The extra first-factor `H^0` can occur in lower
total degree but does not alter this `H^3` identification. The
full `f tensor g tensor h` cuspidal projection makes restriction
from the proper realization to the affine one an isomorphism on
the modular tensor under consideration. Every boundary piece is
Eisenstein in at least one of the three modular factors, and the
cuspidal projection in that factor removes it. The first-factor
projection alone is not being used to remove boundaries in the
other factors. This is the usual parabolic realization of the
modular Galois representation, used in both source constructions.

### 4.3 The cusp correction and full Abel--Jacobi compatibility

DR I Definition 3.2, printed page 27, defines

\[
 \Delta_{2,k,k}
 =(1,\epsilon_r,\epsilon_r)
       \bigl(\varphi_{ABC}(E^r)-\{o\}\times\varphi_{BC}(E^r)\bigr), \tag{10}
\]

where `o` is a cusp. Its restriction to the affine open is exactly
the Scholl projection of (7): the second term restricts to zero.
The restriction of cycle classes and the Hochschild--Serre maps
is functorial. Under the cuspidal cohomology identification in
Section 4.2, the projected etale Abel--Jacobi class of (10)
therefore agrees with the class obtained from (8) and (3).

One can also remove the correction before passing to the open:
`T_q[o]-(q+1)[o]` is a degree-zero cusp divisor, so it is torsion
by Manin--Drinfeld. Thus `R_f[o]=0` in the rational Chow group.
The proper corrected and uncorrected cycles have the same
projected rational Chow class. This argument uses the cusp
basepoint; it is not valid for an arbitrary point.

All these are maps of full Galois representations and extension
classes. The proof has not paired with a single ordinary elliptic
test vector. Applying the syntomic/etale comparison, then testing
against every admissible elliptic `eta` in DR I Theorem 3.8,
retains both elliptic coordinates.

This completes the proof of the replacement proposition.

## 5. Transfer to the actual reflected CH family

Use `kappa_BSV` in place of `kappa_DR22` in the generic comparison
of [global_class_comparison](../global_class_comparison/README.md).
There is an especially direct source match: Castella--Do (4.5)
defines its class as the BSV class, Remark 4.3.1 identifies its
construction, and Theorem 3.2.1 / (3.3)--(3.4) gives the relaxed/
strict condition on its variable CM summand.

At the classical sequence specified above, the replacement
proposition and the full fixed-weight syntomic formula imply
nonzero variable specializations when the analytic germ is
nonzero. The BSV variable class is then nontorsion. Under the
same rank-one Selmer theorem as before,

\[
                     \kappa_{\rm BSV}=f(T)\kappa_{\rm CH},
                     \qquad f(T)\ne0,
\]

in full generic global cohomology. The scalar can be meromorphic.
The proof of full projective leading-direction transfer is unchanged.
The reflected quotient is still formed from the actual CH class.

The local normalized regulator `P`, its interpolation operator
`K_s`, and the full fixed-weight syntomic vector do not change.
They are attached to the same classical projected cycle and
full elliptic realization. Scalar changes from (2) or period
normalizations cancel from the wedge comparison. No assertion
that the old DR22 raw specialization proof was correct is needed.

## Scope and residual obligations

This repair is a written proof using BSV Theorem 8.1 and its valid
ordinary duality, together with explicitly checked extensions of
the finite degeneracy and geometric comparison arguments. It is
not a new Lean verification of those source theorems.

For a second curve, the same proposition applies only after checking
the actual BSV family hypotheses, the same CM component, tame and
p-old test-vector identifications, and the source-compatible
syntomic/etale comparison. A finite theta calculation or finite
line-separation certificate cannot replace these gates.

## Source locations

| Assertion | Primary source |
|---|---|
| p >= 5, Hida setup, weight-one regularity | BSV Section 1.1, printed pages 3--4 |
| Nonnegative exponents, invariant class | BSV Assumption 3.1 and (41)--(48), pages 18--20 |
| Geometric Gysin/Leray identity | BSV Proposition 3.7 and (60)--(63), pages 25--27; extended after the edge projection above |
| Actual normalized family specialization | BSV Theorem 8.1 and (160)--(168), pages 60--65 |
| p-stabilization algebra | BSV (169)--(183), pages 65--70; exponent-zero extension above |
| Ordinary duality is valid | Official BSV erratum, first bullet, case h=0 |
| Corrected `(2,k,k)` cycle and full syntomic pairing | DR I Definition 3.2 and Theorem 3.8, [primary PDF](https://www.math.mcgill.ca/darmon/pub/Articles/Research/62.DR-Diagonal1/paper.pdf) |
| Same BSV family and CM local conditions | Castella--Do (4.5), Remark 4.3.1, Theorem 3.2.1, [primary PDF](https://kimtuando.github.io/website/Schoen_CM.pdf) |
