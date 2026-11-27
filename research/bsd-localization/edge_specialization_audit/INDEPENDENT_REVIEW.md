# Independent review of the BSV replacement

Date: 2026-11-27. Reviewer: the independent comparison-logic workstream.

## Verdict

The replacement in `../general_criterion/BSV_REPAIR.md` supplies a
**full Galois-cohomology comparison** at the classical weights `(2,k,k)`,
with the setup, test vectors, coefficient identifications, and cuspidal
projections specified there. I found no surviving normalized-moment
premise in this route. It does not complete the abandoned raw DR22
moment argument; it obtains the required comparison from the BSV family
and its actual normalized ordinary specialization.

This verdict concerns the written proof of the finite degeneracy and
geometric extensions. BSV Proposition 8.3 and its geometric Proposition
3.7 are printed with positive symmetric exponents; their use at first
exponent zero is justified by the arguments reviewed below, rather than
by pretending that their printed statements already include that case.

## 1. Sources actually checked

The review read the primary texts, not just the repair's descriptions:

* BSV Section 1.1 and Assumptions 1.1--1.2; Assumption 3.1 and
  equations (41)--(48); Proposition 3.7, especially diagrams (60) and
  the invariant calculation (61)--(63); Theorem 8.1 and equations
  (155)--(168); and all three stages (174)--(183) of Proposition 8.3.
* The official BSV erratum's corrected ordinary duality statement.
* DR I Definition 3.2, its Abel--Jacobi construction (65)--(66), and
  the full test space and functional of Theorem 3.8, (73)--(74).
* Castella--Do (4.5), Remark 4.3.1, and Theorem 3.2.1 with (3.3)--(3.4),
  to check that the replacement really is the family named in the
  proposed subsequent Selmer comparison.

The source files used are the saved primary PDFs and text extractions
in `global-class-sources/`. Primary URLs are listed below.

## 2. The full-class chain

Put `r=k-2` and `bold r=(0,r,r)`. Use the ordinary stabilizations of
the specified tame forms and their full Galois representations. The
chain being proved is

\[
\begin{split}
\Pi^\alpha\rho_{(2,k,k)}\kappa_{\rm BSV}
 &=E_{\rm BSV}(2,k,k)\,\kappa(f,g,h),\\
\kappa(f,g,h)
 &=\operatorname{pr}_{fgh}\,s_{\boldsymbol r,*}
       \operatorname{HS}\,d_*(\operatorname{Det}_{(0,r,r)}),
\end{split}
\]

followed by the rational geometric identification of the second line
with the projected **étale Abel--Jacobi class** of the proper
cusp-corrected DR I cycle. The possible sign and consistent
symmetric-power/divided-power normalizations give a nonzero scalar.
The coefficient dualities and twists are those in BSV (44)--(48).

None of these equalities is obtained by pairing against one ordinary
elliptic differential. The comparison holds in full cohomology before
the CM summand is selected or the syntomic functional is evaluated.
The classes themselves are allowed to vanish; nonzero comparison
factors are not a proof that a particular class is nonzero.

### Actual normalized specialization

BSV Theorem 8.1 applies directly to balanced classical triples with a
weight equal to two. Its underlying invariant construction explicitly
allows nonnegative symmetric exponents. At the edge,

\[
                    \operatorname{Det}_{(0,r,r)}=[y,z]^r.
\]

Crucially, the theorem compares the actual BSV family through its
ordinary duality and control maps. Equation (165) supplies the
normalized compatibility; setting the coefficient exponent to zero
does not replace that cohomological map by a raw moment. The
coefficient self-duality `s_0` is the identity, while the normalization
in the cohomological comparison remains the one in the source.

### Tame degeneracy at exponent zero

The p-isogeny maps on the coefficient sheaves are symmetric powers of
degree-one maps. At exponent zero both coefficient maps are identities.
The degrees of the finite maps of modular curves remain separate.
Consequently the step introducing `pi_i^u` for `u>=1` has a literal
extension at `u=0`; it does not turn a coefficient map into a
degree-p trace.

I checked all three parts of the printed proof:

1. The simultaneous pushforwards use the determinant transformation
   `[y,z]^r -> p^r[y,z]^r` and the unchanged base-cover degrees.
2. The six mixed pushforwards use finite Galois-cover transfer,
   functoriality, and `lambda_p^{u*}lambda_{p*}^u=p^u`. These are
   valid at `u=0`. No division by the zero exponent occurs.
3. The p-stabilization expansion and factorization use the Hecke-root
   identities and `2r=r_1+r_2+r_3`, all unchanged at `(0,r,r)`.

This proves the eight identities used in the repair and therefore its
extension of Proposition 8.3. Combining it with Theorem 8.1 produces
the four displayed Euler factors. Each ratio in those factors has
complex absolute value `p^(-1/2)`, by the Weil bounds at the good
prime p. Thus every factor is nonzero. This does not assert p-adic
unit status or uniform valuation bounds as the weight varies.

### Why the geometric comparison is an extension comparison

For `A=empty` and `B=C={1,...,r}`, the relative diagonal has middle
tensor component

\[
                    (x\otimes y-y\otimes x)^{\otimes r}.
\]

Regrouping and applying the rational Scholl symmetrizers gives
`[y,z]^r`, with a nonzero extreme coefficient. This calculation
identifies the invariant but is not, by itself, the argument about
extensions.

The additional required step is present: the relative Gysin maps,
Leray maps, and absolute cycle-class map fit into the functorial
diagram BSV (60), also when the first relative dimension is zero.
The diagram identifies the actual open cycle class with
`d_* Det_(0,r,r)`. Applying Hochschild--Serre therefore identifies
their Galois-cohomology classes. Equality of extensions is obtained
from equality of these functorially related cycle classes, not from
null-homology or residue equality alone.

For the proper realization, **all three cuspidal projections must
be retained**. The elementary first-factor filter

\[
                 R_f=\frac{q+1-T_q}{q+1-a_q(f)}
\]

kills the extra first-factor `H^0` and `H^2` and is identity on the
chosen f-component. It is not a substitute for the full `(f,g,h)`
projection or for the chosen tame multiplicity/test-vector maps.
After those cuspidal projections, proper-to-affine restriction is
an isomorphism on the relevant modular tensor: its omitted boundary
pieces are Eisenstein. This allows recovery of the full proper
Abel--Jacobi class from the open comparison.

DR I's cusp-supported correction restricts to zero on the affine
open. There is also the stronger rational Chow observation used in
the repair: `T_q[o]-(q+1)[o]` is a degree-zero cusp divisor and hence
torsion by Manin--Drinfeld, so `R_f[o]=0`. This uses a cusp basepoint
and is not an argument for an arbitrary basepoint.

These observations prove the edge geometric comparison after the
specified projections. Only afterwards does DR I Theorem 3.8 provide
the syntomic functional, whose first-factor test space at this edge
contains both elliptic coordinates.

## 3. Family and prime qualifications

The standing BSV prime restriction is `p>=5`, so p=5 is allowed.
The official erratum repairs the overly broad finite-slope duality
claim and proves the required case of ordinary slope zero. The
specialization here uses precisely that ordinary case. No
uncorrected positive-slope duality claim is needed.

The arithmetic sequence must respect BSV's stated weight congruence
modulo `2(p-1)`. For the line through `(2,1,1)`, the correct sequence is

\[
               s_n=2(p-1)p^n=8\cdot5^n,\qquad k_n=1+s_n.
\]

These balanced triples tend to the required germ. This replacement
does not change its first nonzero analytic coefficient; it does not
analytically interpolate the factorials or `p^{s_n}`.

The weight-one CM-center hypotheses remain genuine hypotheses. For
the stated order-seven unramified character of `Q(sqrt(-71))`,
cuspidality follows from the distinct conjugate characters, the two
roots at five are distinct, and the dihedral projective image of
order fourteen has a unique quadratic self-twist, namely the
imaginary CM field. Thus the real-multiplication exclusion in BSV
Assumption 1.1 is satisfied here.

The tame and p-old identifications must be the specified compatible
maps. A Galois-equivariant identification of a selected irreducible
elliptic copy is scalar, but two arbitrary linear functionals on an
unselected multiplicity space need not be proportional. The repair
retains the selected copies and test vectors, so it does not use that
invalid stronger assertion.

## 4. Scope of acceptance

This review accepts the replacement proposition as a written
mathematical proof with its displayed setup. The CDo source match is
literal: (4.5) names the BSV family, Remark 4.3.1 identifies its
construction, and the variable summand in (3.4) has zero **full**
localization at the strict prime. This removes a possible mismatch
between the new geometric family and the proposed Selmer comparison.

The review does not independently re-prove the global rank-one
theorem, the infinite Katz/theta inputs, the computed analytic germ,
the full normalized CH regulator comparison, or the final reflected
localization implication. Those remain the separately recorded
inputs of the larger argument. It also adds no Lean formalization.
In particular, acceptance of this full-class repair does not by
itself identify a Selmer class with a rational point.

No edits to the repair file were needed for this verdict. This
independent review is frozen with the component files it inspected.

## Primary references

* [BSV, Reciprocity laws for balanced diagonal classes](https://www.esaga.uni-due.de/f/massimo.bertolini/publications/Ast-BSV1.pdf).
* [Official BSV erratum](https://www.esaga.uni-due.de/f/massimo.bertolini/publications/Errata-AstBSV1.pdf).
* [Darmon--Rotger, Diagonal cycles and Euler systems I](https://www.math.mcgill.ca/darmon/pub/Articles/Research/62.DR-Diagonal1/paper.pdf).
* [Castella--Do, Diagonal cycles and anticyclotomic Iwasawa theory of modular forms](https://kimtuando.github.io/website/Schoen_CM.pdf).
