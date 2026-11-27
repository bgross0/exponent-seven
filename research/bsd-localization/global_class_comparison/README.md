# Full global comparison through a rank-one Selmer module

Date: 2026-11-27. Pilot: `E389.a1`, `K=Q(sqrt(-71))`, `p=5`.

## Result and scope

**Revision:** the comparison family is now BSV. The prior DR22 raw-moment
specialization argument was incomplete; the replacement proof and its
source hypotheses are in [BSV_REPAIR](../general_criterion/BSV_REPAIR.md).
The generic rank-one argument itself and the CH reflected class are
unchanged.

There is a way to compare the **full variable elliptic components** of the
Castella--Hsieh class and the Bertolini--Seveso--Venerucci diagonal family without
identifying their historical cycle constructions, their integral lattices,
or the absolute normalization of their test vectors.

Under the arithmetic and nonzero-theta inputs already used in this package,
the two nonzero classes belong to the same one-dimensional vector space
over the fraction field of the anticyclotomic Iwasawa algebra. Consequently

\[
             \kappa_{\rm BSV}=f(T)\kappa_{\rm CH},\qquad f(T)\ne0.       \tag{1}
\]

This is an equality of full global cohomology classes **after passing to
the fraction field**, in the variable CM summand. It is not inferred from
equality of two ordinary regulator values. The additional arithmetic input
that makes (1) possible is a rank-one theorem of Castella--Do, together with
the pilot's big-image verification in [galois_image](../galois_image/README.md).

Equation (1) is enough to transport a leading **projective** local-regulator
direction. The scalar may have a zero or pole at the base. One need not
prove that it is a unit, provided the order of the particular CH regulator
used in the derived argument is established independently.

The reflected/derived class is therefore still formed from the actual CH
family. Nothing here replaces that class by an arbitrarily rescaled BSV
family. The local comparison with the analytic computation remains a
separate assertion about the full regulator; the new argument supplies its
global-family prerequisite.

These are written mathematical deductions from the indicated sources and
the package's named inputs. They have not been formalized in Lean.

## 1. Coefficients, the deformation, and the exact module

Let `L` be a finite extension of `Q5` containing the values of the order-seven
class-group character `psi`, and let `O` be its valuation ring. We can take
`L=Q5(zeta7)`, an unramified extension of degree six. The computed vector has
coefficients in the unramified degree-three subfield
`L0=Q5(zeta7+zeta7^-1)`.

Let `Gamma=Gal(K_infinity/K)` be the anticyclotomic `Z5`-extension group and
put

\[
 \Lambda=\mathcal O[[\Gamma]],\quad B=\Lambda[1/5],\quad
 A=B_{(T)},\quad Q=\operatorname{Frac}(B),\qquad T=\gamma-1.
\]

Here `A` is the local ring at augmentation, a discrete valuation ring with
residue field `L`; its completion is `L[[T]]`. A rational function in `Q`
has a meromorphic germ at augmentation. This is stronger than just an
unspecified formal proportionality in an unrelated power-series field.

Write `V=V5(E)`. In the same-CM-type diagonal, the finite inducing
characters of the two theta families are `psi` and `psi^-1`. The tensor
induction decomposition, after its central self-dual twist, consists of

\[
 V\otimes\operatorname{Ind}_K^{\mathbf Q}(\Psi^{1-c})
 \quad\oplus\quad
 V\otimes\operatorname{Ind}_K^{\mathbf Q}(\psi/\psi^c).                 \tag{2}
\]

The first summand is the variable anticyclotomic elliptic representation;
the second is the auxiliary finite-character representation. This is CH
(2.4), (3.12)--(3.13). The projectors are the coordinate projectors onto
the diagonal and off-diagonal pairs in the tensor of two induced bases.
They do not divide by a difference of characters, so the collision at
augmentation does not destroy the splitting. Applying the first projector
and Shapiro gives a class in the Iwasawa cohomology of `V` over `K`.

The chosen prime is fixed throughout. If a source's universal character
uses the inverse Artin convention, apply the involution `gamma -> gamma^-1`
to both representation and parameter. It is an isomorphism, not an
identification of the two local primes by a scalar. The coordinate audit in
[leading_comparison](../leading_comparison/README.md), Section 4, gives,
for the norm-two Artin generator's coordinate `T_a`,

\[
                  T_a=(1+W)^\delta-1,\qquad\delta=2\pmod5.           \tag{3}
\]

Thus the CM weight disk and the anticyclotomic disk have isomorphic local
rings and fraction fields. Both classes in (1) are transported using this
same convention before they are compared.

The local Lubin--Tate interpolation uses the negative twist `j=-s`,
where `W=6^s-1`. For a Lubin--Tate-adapted generator with character
value `6`, its coordinate is instead `T_LT=(1+W)^(-1)-1`.
These are coordinates for different generators of the same deformation:

\[
                  T_a=(1+T_{\rm LT})^{-\delta}-1.
\]

The Jacobian is `-delta`, a five-adic unit. This coordinate conversion
does not change the negative twist `j=-s` or the actual character.
The unspecified `T` in the module and leading-order arguments can be
either coordinate, with this conversion applied consistently.

Let `S` denote Castella--Do's compact Iwasawa Selmer module

\[
 S=\operatorname{Sel}_{\rm rel,str}(K_\infty,T_5E\otimes\mathcal O).
                                                                         \tag{4}
\]

The local condition is unrestricted at the selected prime `p` of `K`,
zero at its conjugate `pbar`, and the propagated finite condition away
from five. It is this entire Iwasawa module, not the image of its base
specialization or its space of universal norms, that will have rank one.

## 2. The precise rank-one input and its pilot hypotheses

Use the author version of Castella--Do, *Diagonal cycles and anticyclotomic
Iwasawa theory of modular forms*, dated August 4, 2025:
[primary PDF](https://kimtuando.github.io/website/Schoen_CM.pdf).

Theorem 3.3.3(I), printed page 32, gives rank one for the compact
relaxed/strict Selmer module when its Euler-system bottom class is
nontorsion and the modular representation has big image. The proof of
Theorem 5.6.1, printed page 43, supplies exactly that non-torsion input:
its reciprocity formula (5.17), together with the stated theta
nonvanishing theorem, gives a nontorsion bottom class; immediately before
(5.18) the proof explicitly concludes that the compact relaxed/strict
module has Iwasawa rank one.

Apply that proof with `r=1`, `chi=1`, and therefore `j=0` and `c=1`.
It proves

\[
                            \dim_Q(S\otimes_\Lambda Q)=1.             \tag{5}
\]

The hypotheses of Theorem 5.5.1, which Theorem 5.6.1 invokes, are checked
as follows.

| Source hypothesis | Pilot verification |
|---|---|
| Ordinary weight `2r` newform, `p` prime to its level | `r=1`, level `389`, `a5=-3` |
| Standing prime restriction `p` prime to `6N_f` | `gcd(5,6*389)=1` |
| `p` split in `K` | `X^2-X+18` has roots `2,4` modulo five |
| `p` prime to the class number | `h(-71)=7` |
| `N^-` squarefree with an odd number of prime factors | `389` is prime and inert in `K` |
| `gcd(p*N_f,c*D_K)=1` | `gcd(5*389,71)=1`, `c=1` |
| Prime-to-`p` finite part of `chi` | `chi=1` |
| Residual absolute irreducibility and `p`-distinguishedness | Image contains `SL2(F5)`; ordinary inertia characters are cyclotomic and trivial |
| `p>2r-2` | `5>0` |
| Non-CM | `j(E)=1404928/389` is not an algebraic integer |
| Big image as in Notation 3.3.2 | Image contains `SL2(Z5)` |

The exact residual-image certificate and the passage to five-adic big
image are in [galois_image](../galois_image/README.md). This verifies the
source's stated hypothesis, rather than replacing it by residual
irreducibility alone.

Two distinctions matter.

* The implication `L(f/K,chi,r) != 0 => Sel_BK=0` is the **conclusion** of
  Theorem 5.5.1. Its antecedent is not an extra assumption of Theorem
  5.6.1. In this pilot the central value vanishes. The latter proof uses
  a nonzero Iwasawa theta series, which is compatible with a zero at
  augmentation.
* The proof may choose an auxiliary ray-class character different from
  the order-seven character used in the computation. That character
  constructs a witness proving the rank of (4). The module (4) itself
  only depends on `E`, `K`, and the trivial target twist. After any
  coefficient extension needed for that witness, faithful flatness
  descends the rank statement. The two families being compared need
  not use that auxiliary character.

We use the rank statement directly. We do not infer that the compact
ordinary/ordinary module is zero from a vanishing universal-norm image,
nor confuse the cotorsion conclusion for a discrete dual Selmer group
with an integral vanishing assertion for a compact module.

## 3. Both full classes satisfy the same local condition

### 3.1 The BSV condition is genuinely strict at the other prime

BSV Corollary 8.2 places its full family in the balanced Selmer group.
The kernel of the map to cohomology of the quotient representation is,
by the long exact sequence, the image

\[
 H^1(\mathbf Q_5,F^{\rm bal}\mathbb V)
       \longrightarrow H^1(\mathbf Q_5,\mathbb V).                    \tag{6}
\]

Here `F^bal` is the rank-four balanced representation, denoted `F^2`
in BSV. Castella--Do (4.5) explicitly uses this BSV family, and its
CM decompositions (3.3)--(3.4) and Proposition 5.3.1 verify the same
full relaxed/strict condition. Thus this statement applies to the
family whose normalized specialization is used in the replacement
[edge comparison](../general_criterion/BSV_REPAIR.md).

Choose local splittings of the two CM representations into their plus
and minus characters. They split because they are induced from a field
in which five splits. Ignoring the common central twist in the notation,

\[
 F^{\rm bal}
 =V\otimes g^+\otimes h^+
  \;\oplus\; F^+V\otimes g^-\otimes h^+
  \;\oplus\; F^+V\otimes g^+\otimes h^-.                            \tag{7}
\]

For the same CM type, the variable block is the pair `++` and `--`;
the mixed signs form the auxiliary block. Projecting (7) to the
variable block therefore gives **full `V` at one prime and zero at
the other**. In particular the conjugate-prime localization of the
projected BSV class is zero in full `H^1`, not merely after taking an
ordinary quotient.

This deduction is compatible with specialization: the composite map
from `F^bal` to the conjugate variable block is already the zero map
of representations. Applying cochains, specialization, and the CM
projector keeps it zero. No claim that a kernel commutes with a
nonflat specialization is needed, and no `H^0` connecting class can
restore a discarded component. The stronger image statement (6) is
the reason this is safe.

Castella--Do independently writes this same full/zero local
decomposition in (3.3)--(3.4), printed page 30, and its two-family
version in Proposition 5.3.1. Thus the local condition agrees with
the one in (4), including which prime is relaxed.

### 3.2 CH has the same full strict condition

CH Theorem 3.6 and its proof, printed page 18, give the full strict
vanishing at the conjugate prime for the projected class. Its displayed
decomposition of the balanced submodule is precisely (7) after
projecting (2). The assumptions there are the supplied vanishing of
the triple central value and nonvanishing of the auxiliary central
value. No nonzero finite localization is an assumption of this
statement.

### 3.3 Away from five, the conditions agree at augmentation

Here is a rational local argument that also deals with bad primes.
For any finite place `v` of `K` away from five,

\[
 H^0(K_v,V)=H^2(K_v,V)=0,
 \qquad H^1(K_v,V)=0.                                               \tag{8}
\]

For `H^0`, the group `E(K_v)[5^infinity]` is finite, so its Tate module
vanishes. Weil self-duality and local Tate duality give `H^2=0`.
The local Euler characteristic at residue characteristic different
from five gives `H^1=0`. This includes the multiplicative prime `389`.
It is also the reasoning used in Castella--Do's proof of Theorem
3.2.1, printed page 30.

For precision, apply this to the local Galois cohomology complex of
the finite free Iwasawa representation. The usual finite local
cohomology complex is perfect over the coefficient algebra and
satisfies derived coefficient specialization. Localizing at `(T)`
and reducing modulo `T` therefore gives the acyclic complex in (8).
Derived Nakayama makes the localized complex acyclic. Consequently
the ambient local `H^1` at every such place is zero over `A`; any
propagated finite or unramified condition agrees there. This argument
uses derived specialization, not the invalid implication that
finite-level vanishing alone forces arbitrary inverse-limit vanishing.

In this pilot the perfect-complex input can also be seen directly:
the curve is semistable and the anticyclotomic deformation is
unramified away from five. Wild inertia away from five acts trivially
on the Tate module, and the only relevant tame pro-five inertia is
procyclic. Its cohomology is represented by the two-term complex with
differential `tau-1`. Adding unramified Frobenius gives the usual
finite mapping-cone complex. All its terms are finite free over `A`,
so coefficient specialization is literal derived tensor product.
This supplies the required local perfectness without an assertion
about a general nonsemistable deformation.

Global cohomology and the Selmer kernels are computed with a fixed
finite set of ramified places. Flat localization preserves those
kernels. Thus both projected classes, allowing the finite
denominators of the test-vector maps, belong to

\[
                       S_A=S\otimes_\Lambda A
\]

or, if a chosen meromorphic representative has a pole at the base,
to `S_A tensor_A Q`. Multiplying that representative by a power of
`T` clears the pole. For the generic comparison the latter statement
already suffices; it makes no integral saturation claim.

## 4. Actual family existence and nonzero generic classes

The CM families are residually irreducible: an order-seven character
remains distinct from its conjugate in characteristic five, and its
induction is irreducible. They are also distinguished at five. The
chosen norm-five ideal class is the square of the norm-two generator,
so the two weight-one Frobenius roots are `zeta7^2` and `zeta7^-2`,
which remain distinct modulo five. This verifies the CM-family
conditions in addition to those for `f`.

BSV Section 1.1 and (155)--(156) provide the ordinary family at
`p>=5`, with tame level prime to `p`. The official erratum explicitly
preserves the ordinary duality used in its construction. Its weight-one
hypotheses are checked in [BSV_REPAIR](../general_criterion/BSV_REPAIR.md):
the order-seven CM forms are classical and p-regular, and their dihedral
projective image of order fourteen has only the imaginary quadratic
self-twist, so they have no real quadratic multiplication.

This rational ordinary construction has no `p`-prime-to-`phi(N)`
restriction. The older DR17 integral construction does impose it; it
fails here and is not used. Tame finite-group projectors are taken in
characteristic zero. The former DR22 raw-moment edge proof is withdrawn;
the replacement uses BSV Theorem 8.1 and explicitly proved finite and
geometric extensions, not an asserted identification of BSV with DR22.

Both generic classes are nonzero for allowed nonzero test choices.
For CH, its ordinary Coleman reciprocity law and the supplied theta
series of exact order two give a nonzero regulator image, hence a
nontorsion class.

For BSV, use the **full syntomic specialization** as the primary
argument. Choose the explicit minimal-level test-vector projection
corresponding to the analytic cross-placement vector `A(W)`; Section
6 describes its relation to the common computed vector `L(W)`.
The nonzero analytic quadratic coefficient proves that `A(W)` is not
the zero germ. Along the classical weights `s_n=8*5^n`, the parameters
`W_n=6^(s_n)-1` approach zero and `A(W_n)` is nonzero for every
sufficiently large `n`.

The projected edge proposition identifies the BSV specialization
with the appropriate projected etale diagonal cycle, up to a
nonzero scalar. DR I Theorem 3.8 gives its full syntomic functional
for every elliptic test vector. The CM test tensor extracts precisely
the variable local rank-two block; both mixed auxiliary blocks are
annihilated. The fixed-weight Euler operators are invertible at these
classical weights, and all CM period identifications act by a
nonzero scalar on this block. These full-vector statements are
proved in [normalized_local_comparison](../normalized_local_comparison/README.md),
Sections 2--3, using the fixed-weight argument and the corrected BSV
projected-edge comparison. Consequently the variable class has nonzero local
Bloch--Kato logarithm at every sufficiently large classical weight
in this sequence.

A torsion family would be killed by a nonzero coefficient germ.
That germ has no zeros at sufficiently small nonzero `W_n`, so
the torsion family's specialization there would be zero. This
contradicts the preceding nonzero logarithms. Thus `kappa_BSV` is
nontorsion in the variable block. This argument needs neither
vanishing of the auxiliary BSV class nor the normalized full
Perrin--Riou interpolation formula.

There is also an ordinary-reciprocity cross-check. BSV Theorem A
identifies an ordinary regulator image with the triple-product
function. Its `f` quotient of (7) is
`(V/F^+V) tensor g^+ tensor h^+`: it belongs to the variable block
and kills the two mixed auxiliary terms. Castella--Do Proposition
5.2.1 supplies the conductor-one factorization used in
[leading_comparison](../leading_comparison/README.md), Section 1:

\[
 L_p^f(W)=u(W)\Theta(E/K;W)\Theta(E/K,\psi^2;0)C_f,                 \tag{9}
\]

where the second theta value and `C_f` are nonzero and `u` is regular
and nonzero at the base. This provides another nonzero scalar image
when the triple-product normalizations are identified. No argument
in this note equates full classes merely because their ordinary
images agree.

## 5. The full comparison theorem

**Proposition.** After the representation, prime, and parameter
identifications in Section 1, let `kappa_CH` and `kappa_BSV` be the
variable components with the nonzero test choices of Section 4.
Then (1) holds in full global cohomology over `Q`.

**Proof.** Section 3 places both classes in `S tensor Q`.
Section 2 proves this space is one-dimensional. Section 4 proves
neither class is zero. Either class is therefore a basis and the
other has a unique nonzero scalar multiple in `Q`. This is an
equality in the Selmer subspace of full global cohomology. Applying
any linear localization or full regulator preserves it. No
injectivity of an ordinary scalar regulator is used. QED.

**Projective consequence.** Let `P` be the same full local regulator
applied to both localizations. Suppose `P(kappa_CH)` is nonzero and
write in a local coordinate

\[
 P(\kappa_{\rm CH})=T^m(v+O(T)),\quad v\ne0,
 \qquad f(T)=T^r(a+O(T)),\quad a\ne0.
\]

Then

\[
 P(\kappa_{\rm BSV})=T^{m+r}(av+O(T)).                              \tag{10}
\]

Thus the leading projective directions coincide, even when `r` is
nonzero. The statement also holds after (3), and after applying a
matrix-valued analytic comparison whose constant matrix is invertible.
It does not assert that the orders coincide. If some independent
argument proves both orders equal, (10) additionally proves `r=0`;
that stronger conclusion is not needed here.

## 6. Why the tame test vectors multiply the full vector by one scalar

This section supplies the full-vector version of the ordinary
test-vector reduction in `leading_comparison`, Section 2.

At common tame level `71*389`, put `N=389` and write

\[
 \check g=a g+bV_Ng,\qquad \check h=c h+dV_Nh.
\]

The inverse-Bol product is a linear combination of the two diagonal
placements `D_s,V_ND_s` and the cross placements `A_s,B_s`, with
coefficients `ac,bd<N>^-s,ad,bc`, respectively. Proper `E`-new
projection kills the diagonal placements because they come from
level `71`. The existing trace calculation gives equality of the
two cross outputs in the full two-dimensional elliptic cohomology.
Consequently the output is `(ad+bc)L(s)` before taking an ordinary
coordinate.

The `f` test vector acts in the oldspace at `71`. This action is a
tame algebraic correspondence and is `G_Q`-equivariant on étale
cohomology. Big image gives

\[
                   \operatorname{End}_{G_{\mathbf Q}}(V\otimes L)=L.
\]

The `E`-isotypic oldspace is `V tensor M_old`. Every equivariant
map to `V` is therefore `id_V tensor ell` for a functional `ell`
on the multiplicity space. The Fricke-71-plus condition fixes the
one-dimensional multiplicity line used by the computed trace.
Such a map acts on the entire elliptic factor by one scalar.
Comparison functoriality gives the same conclusion in de Rham
cohomology. There are not two independent scalars on the ordinary
and critical Frobenius lines.

Hence the analytic vector for good minimal-level test vectors has
the form

\[
                       A_{\rm test}(W)=q(W)L(W).                    \tag{11}
\]

Regularity of `q` in the CM weights follows from Castella--Do
Remark 4.1.2 and its fixed-`f` specialization in Section 5.2, as
audited in `leading_comparison`, Section 2. Only the fixed `f`
variable may carry the denominators there. The ordinary coordinate
of `L` has exact order two and (9) also has order two, so `q(0)`
is nonzero. This last use of ordinary order determines whether an
**already proved full-vector scalar** vanishes. It is not a
substitute for proving that the map is scalar.

An ordinary `p`-stabilization likewise acts on the `p`-old
multiplicity factor of a full rank-two Galois representation. It
must not be replaced by a rank-one projection on `D_cris(V)`.
The full local comparison should retain that distinction when
identifying its chosen tame de Rham coordinates.

## 7. Consequence for the reflected class and what remains separate

Retain the actual CH family and define, as in
[DERIVED_CLASSES](../derived_global/DERIVED_CLASSES.md), Section 6,

\[
 t=(\gamma-\gamma^{-1})/2,\qquad
 x=(\kappa_{\rm CH}-c\kappa_{\rm CH})/t.
\]

The existing global division, conjugation invariance, and base finite
Selmer arguments still apply to this exact class. At the selected
prime the strictness of the conjugate family identifies the
localization of the numerator with that of `kappa_CH`. Equation
(10) transports the projective leading direction computed from
the DR family to this numerator's full regulator.

In particular, a zero or pole in `f` does not alter the reflected
class or its symmetry. We do not divide, reflect, or specialize
`f*kappa_CH` and then pretend to recover `x`. Exact regulator order
for the CH numerator must be obtained from its own ordinary theta
identity and the local finite condition; this is independent of
the generic projective comparison.

Finite coefficient extension causes no descent obstruction for the
nonvanishing test. All global and local linear maps commute with
finite scalar extension. If the finite localization map is nonzero
after extension to `L`, it was nonzero before extension. A computed
line defined over `L0` can be compared with a line after extension
to `L`; faithful flatness detects equality and inequality of the
original `L0` lines. No claim that the scalar `f` itself lies in
`L0` is necessary.

### Exact status of the comparison

| Assertion | Status of this note |
|---|---|
| CH and BSV variable classes are proportional in full generic global cohomology | Proved from the cited rank-one theorem and the stated package inputs |
| Their leading full-regulator directions agree projectively | Proved by (10) |
| Good tame test vectors have the same leading analytic vector line | Proved by (11) and its nonzero base factor |
| Literal equality of historical integral families | Not asserted or needed |
| Equality of their base specializations without tracking orders | Does not follow from generic proportionality |
| A unit relating the two generic classes at augmentation | Not asserted or needed |
| Full normalized PR/syntomic operator for the BSV family | Separate local comparison obligation |
| Nonzero finite logarithm of the reflected class | Requires that local operator and the computed separation from its exceptional line |

This note supplies the generic global line. The separate
[normalized local comparison](../normalized_local_comparison/README.md)
identifies its full regulator with the syntomic vector in the same
character and test-vector conventions, and gives the base image line.
Together these arguments remove any need to identify the historical
integral families for the projective nonvanishing test.

## Primary references and dependency boundary

* Castella--Hsieh, *On the nonvanishing of generalised Kato classes
  for elliptic curves of rank 2*, Forum Math. Sigma 10 (2022), e12:
  [author PDF](https://web.math.ucsb.edu/~castella/Kato-print.pdf).
  Equations (3.10)--(3.13), Theorem 3.6, Corollary 3.7, and the
  derived arguments cited in the frozen package.
* Bertolini--Seveso--Venerucci, *Reciprocity laws for balanced diagonal classes*:
  [author PDF](https://www.esaga.uni-due.de/f/massimo.bertolini/publications/Ast-BSV1.pdf)
  and [official erratum](https://www.esaga.uni-due.de/f/massimo.bertolini/publications/Errata-AstBSV1.pdf).
  Theorem 8.1 and Corollary 8.2; finite edge extensions of Propositions
  8.3 and 3.7 are proved in `general_criterion/BSV_REPAIR.md`.
* Darmon--Rotger, *Diagonal cycles and Euler systems II*:
  [author PDF](https://web.mat.upc.edu/victor.rotger/docs/DR2.pdf).
  Its Section 1.5--1.6 integral `p`-prime-to-`phi(N)` restriction
  is explicitly not used for the BSV construction here.
* Castella--Do, *Diagonal cycles and anticyclotomic Iwasawa theory
  of modular forms*, August 4, 2025 author version:
  [primary PDF](https://kimtuando.github.io/website/Schoen_CM.pdf).
  Theorem 3.2.1; Notation 3.3.2; Theorem 3.3.3; Remark 4.1.2;
  Proposition 5.2.1; Theorems 5.5.1 and 5.6.1, especially the
  latter proof's explicit compact rank-one conclusion before (5.18).

The rank-one result is a use of Castella--Do's Euler-system theorem,
including its cited general Euler-system machinery. This note does
not independently reprove that machinery or a main conjecture.
It checks the exact output being used and its pilot hypotheses.
