# Arithmetic specialization at the weight-two edge

Date: 2026-11-27. This is a continuation of the independent source audit.
It does not change the frozen fixed-weight or finite-computation files.

## Status and the precise improvement

The published diagonal families are **full Galois classes**, before any
ordinary regulator pairing. There is therefore no inherent loss of the
second elliptic coordinate at their construction stage. There are, however,
two real checks between that observation and the desired comparison:

1. The crystalline geometric interpolation results inspected below exclude
   the edge with one modular weight equal to two in the paragraphs governing
   their statements. A cuspidal projection repairs the visible cohomological
   obstruction. The repair, and its limits, are made explicit here.
2. A syntomic/Bloch--Kato vector is not the Perrin--Riou vector. The latter
   requires the full adjoint interpolation operator, in the same character,
   period, test-vector, and reciprocity conventions. The local character
   ambiguity can be substantially reduced, but the normalized averaged
   Coleman map must still be matched.

The proposed full arithmetic-family specialization is **not marked proved
for the existing named CH class** by this note. The elementary projected
edge lemma below is proved. Section 3 gives a rational, projective
extension of the DR22 geometric comparison by its actual extension-class
construction. This is a deduction with a proof, rather than a claim that
the printed theorem already includes the edge. Identifying this family
and its de Rham trivialization with the existing named CH class remains
separate.

## 1. What the primary sources actually provide

Use the following author versions; theorem numbering refers to these files.

* **DR14:** Darmon--Rotger, *Diagonal cycles and Euler systems I*,
  [author PDF](https://web.mat.upc.edu/victor.rotger/docs/DR1.pdf).
  Definition 3.2 explicitly treats weights `(2,k,k)`, `k>2`, by subtracting
  a cycle supported at the chosen cusp in the first factor. Theorem 3.8 and
  its proof treat this case as well. Thus the **fixed-weight** syntomic
  calculation does have a geometric cycle at our weights.
* **DR17:** Darmon--Rotger, *Diagonal cycles and Euler systems II*,
  [author PDF](https://web.mat.upc.edu/victor.rotger/docs/DR2.pdf).
  Section 1 constructs an equal-weight family with the first form of weight
  two. Equation (47) uses the explicit first-factor correspondence written
  below. The introduction, around (13), distinguishes construction from
  weight-two cycles from specialization at higher weights. This text does
  not itself establish the needed higher-weight geometric comparison.
  Section 1.6 also assumes `p` does not divide `phi(N)`. That hypothesis
  fails at `p=5`, `N=389*71`; it must not disappear in a citation. The
  rational argument below does not assert an integral extension of DR17.
* **DR22:** Darmon--Rotger, *p-adic families of diagonal cycles*,
  [arXiv:2207.01314](https://arxiv.org/pdf/2207.01314).
  Definition 2.9 and Definition 5.2 give the full family. Theorem 3.1,
  Corollary 3.3, and Theorem 4.1 compare its moments with geometric cycles.
  **Scope correction:** Section 3 assumes all three exponents
  `k°,l°,m°>0` after its opening discussion. The paragraph immediately
  before (4.8), on printed page 33, imposes the same condition for the
  remainder of Section 4. Theorem 4.1 is therefore not a direct citation
  for `(2,k,k)`. The section starts more generally, but that later
  restriction governs the theorem.
* **BSV22:** Bertolini--Seveso--Venerucci, *Reciprocity laws for balanced
  diagonal classes*,
  [author PDF](https://www.esaga.uni-due.de/f/massimo.bertolini/publications/Ast-BSV1.pdf).
  Theorem 8.1 is full Galois-class specialization. The comparison in
  Proposition 8.3 has all three modular weights at least three. The
  inspected author version also has a standing restriction on the prime
  stronger than needed by the present pilot. It cannot silently supply our
  weight-two, prime-five geometric comparison.
* **CDo:** Castella--Do,
  [*Diagonal cycles and anticyclotomic Euler systems*, author PDF](https://kimtuando.github.io/website/Schoen_CM.pdf).
  Equation (4.5) uses the BSV family; Remark 4.3.1 identifies it with their
  distribution construction at `m=1`. Equations (5.5)--(5.9) are actual
  Galois-representation and Selmer decompositions. In contrast, Theorem
  4.3.2 evaluates a rank-one quotient regulator.
* **CH:** Castella--Hsieh, *On the nonvanishing of generalised Kato classes
  for elliptic curves of rank 2*,
  [published author PDF](https://web.math.ucsb.edu/~castella/Kato-print.pdf).
  Equations (3.10)--(3.13) construct/project the full class and its variable
  CM summand. Definition 3.3 constructs a vector Coleman map. Equation
  (3.9) then defines a specifically normalized, Frobenius-averaged scalar
  map for each test eigenvector. Theorem 3.4 applies to both eigenvectors,
  not just the ordinary test vector of Theorem 3.6.

Equality of the ordinary outputs of two classes does not identify their
full classes. One may instead explicitly choose the DR22 family for a new
construction, using its own reciprocity theorem and the CM decomposition.
That avoids an unproved historical-class identification; it does not
automatically transfer every symmetry or derived-class assertion previously
proved for another chosen normalization.

## 2. A proved rational projected-edge lemma

Let `X` be a modular curve with good Hecke operator `T_q`, `q` prime to
its level, and let `f` be a cuspidal weight-two eigenform with trivial
nebentype. Put

\[
 R_f=\frac{q+1-T_q}{q+1-a_q(f)}.                 \tag{1}
\]

Assume `a_q(f) != q+1`. This is automatic for a weight-two cuspidal
eigenform at a good prime, by the Weil bound. Let `r=k-2>0`, and use
the Scholl pieces of the two weight-`k` Kuga--Sato factors. Coefficients
in this section are rational, or in a characteristic-zero coefficient
field.

### Lemma

1. `R_f` is the identity on the `f`-isotypic part of `H^1(X)` and kills
   `H^0(X)` and `H^2(X)` in the trivial-nebentype component.
2. After applying `R_f` in the first factor and the two positive-weight
   Scholl projectors, the surviving cohomology of the triple product is
   concentrated in degree
   \[
      1+(r+1)+(r+1)=2k-1.
   \]
   Consequently the projected class of any codimension-`k` cycle is zero
   in degree `2k`: its projected cycle is null-homologous.
3. If `o` is a cusp, then `R_f[o]=0` in `CH_0(X)_Q`, and
   `R_f[X]=0` in `CH_1(X)_Q`. In particular, the cusp-supported correction
   from DR14 Definition 3.2 is killed after applying `R_f` in the first
   factor. The projected corrected and uncorrected cycles agree in the
   rational Chow group, hence have the same projected Abel--Jacobi image.

### Proof

The action of `T_q` on the degree-zero and degree-two trivial cohomology
is multiplication by `q+1`; on the specified cuspidal eigenspace it is
`a_q(f)`. This proves the first assertion. Positive Scholl pieces have
cohomology only in their middle degrees. The Kunneth formula gives the
second assertion, because the only surviving total degree is odd and
the codimension-`k` cycle class is in degree `2k`.

For the third assertion, `T_q[o]-(q+1)[o]` is a degree-zero divisor
supported at cusps. The Manin--Drinfeld theorem makes its class torsion;
it is therefore zero after tensoring with `Q`. Both projections defining
the Hecke correspondence have degree `q+1`, so its action on the
fundamental class of `X` is also multiplication by `q+1`. External
products preserve these identities. Applying the Abel--Jacobi map to
equal rational Chow classes proves the last assertion. A primary reference
for the cuspidal divisor theorem is Drinfeld, *Two theorems on modular
curves*, Funct. Anal. Appl. 7 (1973), 155--156,
[DOI 10.1007/BF01078890](https://doi.org/10.1007/BF01078890).

This argument for correction cycles is stronger than a cohomology-only
argument and genuinely uses the cusp condition. For an arbitrary point
`o`, the divisor `T_q[o]-(q+1)[o]` can have a nonzero Jacobian class;
killing `H^0` and `H^2` would not by itself kill its Abel--Jacobi
contribution. In a model where the first factor has descended to
`X_0(M)` and the basepoint is infinity, one may also use the literal
cuspidal Hecke identity when applicable.

The exact same correspondence (1) already occurs in DR17 (47). It is a
cohomological filter, not an assertion that this degree-one Hecke
polynomial is an idempotent on the whole motive.

### Pilot specialization

For
\[
 E:y^2+y=x^3+x^2-2x,
\]
the exact count `#E(F_3)=6` gives `a_3=-2`. Thus
\[
                  R_f=(4-T_3)/6.                     \tag{2}
\]
The denominator is a `5`-adic unit. Using `q=2` would unnecessarily
introduce a factor of five in the denominator. Formula (2) is valid in
each required first-factor level because `3` is prime to `389*71*5`.

In fact `q=3` also makes the full DR22 auxiliary factor
`C_q=(a_q(f)-q-1)(a_q(g)-q-1)(a_q(h)-q-1)` a unit near the pilot
basepoint. The prime `3` splits in `Q(sqrt(-71))`. At weight one a
CM coefficient at `3` is either `2` or `zeta_7^j+zeta_7^{-j}` with
`j` nonzero modulo seven. In the second case it satisfies
`X^3+X^2-2X-1`; this polynomial has value `71`, a unit modulo five,
at `X=4`. Hence neither CM coefficient is `4` modulo five. All
three factors of `C_3` are units at the base and on a sufficiently
small weight disk.

## 3. How far the published specialization proof now extends

The following is an audit of the actual uses of a positive first exponent.
It does not collapse them into a single null-homology assertion.

| Step in DR22 | What happens at `(k°,l°,m°)=(0,r,r)` |
|---|---|
| Moment maps (1.20), specialization (3.1)--(3.3) | Degree-zero moment is evaluation on the constant polynomial `1`. The maps were defined for nonnegative exponents. No division by `k°` is introduced. |
| Clebsch--Gordan invariant, Lemma 3.2 | It is `(X_2Y_3-Y_2X_3)^r`. The other two determinant exponents are zero. This is nonzero and has the required Tate weight. |
| Surjectivity in the excision diagram (3.5) | The source uses vanishing of `H^4(X^3,H^{k°,l°,m°})`. At the edge it need not vanish globally. Its cuspidal first-factor projection does vanish: the only obstructing first-factor `H^2` is killed by (1). |
| Identification of the middle cohomology in (4.9) | The same projection kills the extra first-factor `H^0` and `H^2`; the retained piece is precisely the `H^1` tensor product. |
| Raw cycle versus DR14 cycle | DR14 Definition 3.2 supplies the cusp correction. Section 2 proves that it vanishes after the rational first-factor filter. |
| Degeneracy maps and Lemmas 4.2--4.4 | Good Hecke operators commute with the `p`-degeneracy maps. Their formulas depend on Hecke roots and their differences, not on division by `k°`. |
| Cycle counting in Lemma 4.5 | Its setup precedes the positivity restriction. For the first factor the indexing set is empty and `p^{k°}=1`; the finite-map counts still make sense. |
| Ordinary root denominators | At the classical weights used here, each ordinary root is a unit and the other root has positive valuation; their differences are nonzero. |

### Rational extension-class argument

**Projected edge proposition (deduced here).** Let the DR22 family be
defined for three ordinary cuspidal Hida families at an odd prime `p`.
Fix a crystalline balanced specialization of weights `(2,k,k)`, with
`k>2`, trivial first nebentype, product of the three nebentypes one,
and tame conductors prime to `p`. Use the same good-Hecke
normalization, ordinary roots, `p`-degeneracy maps, and rational
Scholl conventions as DR22. In the first factor use the cuspidal
component of `f`; in DR14 Definition 3.2 use a cusp basepoint.
Then the specialization of this **DR22-defined full Galois class**,
after the `p`-degeneracy map to tame level and projection to that
component, is a nonzero scalar multiple of the projected étale
Abel--Jacobi class of the DR14 `(2,k,k)` cycle. This statement is
about full classes before an ordinary scalar regulator pairing.
It permits both classes to be zero: the same nonzero scalar relates
them. No identification with a separately defined CH family is part
of the proposition.

Here is how to perform the required comparison, rather than infer it
from null-homology alone. The argument uses the **DR22-defined family**
and its moment maps. All groups in this paragraph have characteristic-zero
coefficients; no assertion about integral torsion or exactness modulo
arbitrary powers of `p` is made.

Let `L=H^0 boxtimes H^r boxtimes H^r` be the coefficient sheaf on
the threefold of modular curves. For a support `Z` containing the
diagonal and the finitely many Hecke translates in `theta_q`, localization
has the segment
\[
 0\longrightarrow H^3(X^3,L)(2)
 \longrightarrow H^3(X^3\setminus Z,L)(2)
 \longrightarrow H_Z^4(X^3,L)(2)
 \xrightarrow{\partial}H^4(X^3,L)(2).                \tag{3a}
\]
One need not make the last group zero. For any Galois-equivariant
residue generator `b:Q_p(t)->H_Z^4(X^3,L)(2)` with `partial b=0`,
pullback along `b` gives a short exact sequence, hence an extension
class. Pushing out its left term to the desired `H^1` tensor quotient
then gives the projected Abel--Jacobi class. This elementary
pullback/pushout statement is functorial in a morphism of localization
sequences.

The universal class in DR22 is defined using the **modified** cycle
`Delta^o=theta_q Delta`, not an unmodified diagonal whose boundary is
being assumed zero. Apply the moment maps in (1.20) and (3.6) to its
localization diagram. Their functoriality with good Hecke
correspondences sends the residue generator to the `theta_q`-modified
version of `(X_2Y_3-Y_2X_3)^r`, precisely the generator identified by
Lemma 3.2 at the edge. Its boundary vanishes: the only possible
degree-four Kunneth term is
\[
 H^2(X,Q_p)\otimes H^1(X,H^r)\otimes H^1(X,H^r),
\]
and the first factor of `theta_q` contains `T_q-(q+1)`. Equivalently,
one can apply `R_f` before the final `f`-projection. The degree-three
term has only the `H^1 tensor H^1 tensor H^1` contribution because
the two positive-weight coefficient sheaves have vanishing `H^0`
and `H^2` after passing to their Scholl pieces.

Thus the specialized universal extension maps to the pullback of
(3a) along this modified generator. By the functorial
pullback/pushout observation, their projected extension classes
coincide. This is the argument of DR22 Theorem 3.1 with the boundary
kernel retained; its proof does not require surjectivity onto the
whole residue space after that modification. It repairs exactly the
use of `H^4=0` in (3.5).

The same construction over the tame and intermediate levels gives
the projected counterpart of (4.9) and Proposition 4.6. Section 2
identifies the resulting raw projected cycle with the projected
DR14 cycle, including its cusp correction. The good-Hecke filter
commutes with the `p`-degeneracy maps; therefore Lemmas 4.2--4.5
and the final algebraic Euler-factor calculation apply to these
extension classes at exponent zero as well. This proves the
**rational projective extension** of the DR22 geometric comparison
to `(2,k,k)`, for the specified cuspidal component and cusp correction.
The argument deliberately does not assert an integral extension,
nor an equality of differently defined historical families.

All normalization factors in this comparison are nonzero at a fixed
classical weight. In particular, for `(2,k,k)` the four balanced Euler
factors have complex root-product absolute value `p^{-1/2}`. The
ordinary denominators `1-beta/alpha` are nonzero. These statements
justify projective comparison; they do not assert a uniform integral
bound on the scalars. Keeping a projective conclusion also avoids
silently identifying conventions for the Scholl factorials and the
overall Abel--Jacobi sign.

The remaining family-identification obligation is now explicit: use
this DR22-defined class throughout, or prove its equality (up to an
appropriate regular scalar) with the independently named CH class.
The argument above asks for neither a rational point nor nonzero
localization as a premise.

## 4. Which family the inverse Bol operator represents

Let
\[
 g_s=\theta(\psi\rho_s),\qquad
 h_s=\theta(\psi^{-1}\rho_s),\qquad W=6^s-1,
\]
with the same CM type, as fixed in `analytic_target_audit/README.md`.
For prime-to-five ideals, the normalization there gives
`rho_s rho_s^c=N_s`, and conjugation changes `psi` to `psi^{-1}`.
Consequently
\[
             d^{-s}g_s^{[5]}=h_{-s}^{[5]}.            \tag{3}
\]
At the arithmetic weights `s=4*5^n`, principal-unit powers agree with
the ordinary algebraic powers on prime-to-five integers. Since
`k=1+s`, (3) is exactly `d^{1-k}g_k^{[5]}`. It has weight
`1-s=2-k`; multiplying by `h_s`, of weight `1+s=k`, gives weight two.
At a tame oldmap `V_d`, the extra scalar is `d^{-s}`; analytically it is
`<d>^{-s}` in the stated branch.

The arithmetic diagonal is still `(2,k,k)`. The appearance of `h_{-s}`
is an analytic expression for the inverse Bol primitive. It is **not**
permission to change the global Galois family to the weight line
`(2,k,2-k)`. That line changes the CM block and its local condition;
CH Proposition 5.2 explicitly uses such an opposite-weight line in a
different, vanishing construction.

The induced-representation identity, with the central norm twist, is
\[
 \operatorname{Ind}(\psi\rho_s)\otimes
 \operatorname{Ind}(\psi^{-1}\rho_s)\otimes N_s^{-1}
 \simeq
 \operatorname{Ind}(\rho_s/\rho_s^c)
 \oplus \operatorname{Ind}(\psi^2).                  \tag{4}
\]
In a contragredient convention both characters may invert. The first
summand varies, the second is constant. CH (3.12) and CDo (5.8)--(5.9)
implement this decomposition for Galois cohomology. At the relaxed
local prime the varying block has the full two-dimensional elliptic
representation, not just its ordinary line.

## 5. Full logarithm, local character, and the PR normalization

At an arithmetic weight `s=k-1>=1`, the relaxed variable block is a
positive cyclotomic/Lubin--Tate twist of `V_pE`, with an unramified
rank-one factor. Its filtration jumps are `-s-1` and `-s`, so its
`Fil^0` is zero. There is no Hodge-filtration reason for its
Bloch--Kato logarithm to forget one of the two elliptic coordinates.
The holomorphic CM tensor is a test vector for this full local block;
identifying its basis with a chosen CM period is an additional
normalization, rather than a further dimension reduction.

There is also a useful exact local-character check. With
`omega^2-omega+18=0`, `omega=2 mod 5`, the ordinary norm-five ideal
has seventh power generated by
\[
 \theta=-281+4\omega,\quad
 \bar\theta=-277-4\omega,\quad
 \theta\bar\theta=5^7.
\]
For the two ordinary roots `a_s,c_s`, the shared CM type gives
\[
           (a_sc_s5^{-s})^7
              =(\theta/\bar\theta)^s.              \tag{5}
\]
This matches the inverse norm of the relative Lubin--Tate parameter
in CH Section 3.4 when the selected prime is fixed as above. Equal
inertia characters and equal seventh Frobenius powers identify the
rank-one crystalline twists over the unramified degree-seven field.
A possible unramified character of order seven disappears on that
field; on a connected analytic disk an analytic seventh-root-of-unity
ambiguity normalized to one at `s=0` is constant. A change of basis in
this rank-one crystalline line contributes a nonzero scalar to a
projective comparison.

This check does **not** license replacement of CH (3.9) by an ordinary
trace. Equation (3.9) includes the action of `sigma_0`, the factor
`h_e`, and the relative-LT to cyclotomic period comparison. These must
be retained when identifying the computed vector with its normalized
Coleman output.

For clarity, in the convention where the arithmetic specialization is
`j=-s` in CH Theorem 3.4 and `varphi=F/p`, its test-vector operator is
\[
 A_{-s}^{\rm test}
 = (1-p^{-s}F^{-1})(1-p^{s-1}F)^{-1}.
\]
The symplectic adjoint satisfies `F^dagger=p F^{-1}`, so the operator
on the logarithm **vector** is
\[
 K_s=(A_{-s}^{\rm test})^\dagger
     =(1-p^{-s-1}F)(1-p^sF^{-1})^{-1}.                \tag{6}
\]
This is a formal consequence of the literal CH interpolation formula
in the specified dictionary. The scalar factorial in that formula
cancels the `(k-2)!` in the fixed-weight syntomic calculation.
Projectively the dominant part of (6) is `F`, with errors of valuation
growing linearly in `s`. Thus it cancels the `F^{-1}` in the syntomic
limiting operator. The separate `pr_syntomic_comparison/` note records
that operator calculation in detail.

Accordingly, if the common full-class and common normalized de Rham
identifications are supplied, the limiting PR matrix is
\[
                 K_0=C_0^{-1}N,
\]
whereas the fixed-weight syntomic matrix is
`M_0=C_0^{-1}F^{-1}N`. These are different maps. For the pilot,
`F^2+3F+5=0` and the trace parameter `tau` of the fixed-weight note give
\[
 K_0^{-1}=\frac{(5-\tau)-2(\tau+1)F}{9}.
\]
Applying it formally to the previously computed PR annihilator
`zeta=(20-13F)omega/45` yields
\[
 K_0^{-1}\zeta
 =-\frac{(50\tau+10)+(35\tau+61)F}{135}\,\omega.    \tag{7}
\]
Equation (7) is a normalization diagnostic, **not a certified arithmetic
exceptional line**. Declaring the syntomic vector to be the PR vector
would instead give a different answer. Neither line may be substituted
for the DL candidate until the full specialization and normalized
Coleman comparison are completed.

## 6. No-circularity checkpoint

A precise use of the projected edge proposition in the current
research therefore retains two separate premises:

1. **Chosen family and test vectors.** Either use the DR22-defined
   class consistently, including its CM projection and test-vector
   maps, or identify it with the named CH class in full Galois
   cohomology. Equality of scalar reciprocity laws is not this
   identification. A construction that changes the chosen family
   must also recheck the global symmetry and Selmer hypotheses used
   in its later derived-class step.
2. **Normalized local identification.** Match the full syntomic/BK
   vector, in its CM period and elliptic cup basis, with CH (3.9)
   and Theorem 3.4, including the selected local prime, the twist
   `j=-s`, `sigma_0`, and the LT/cyclotomic period. Equations (5)
   and (6) remove specific ambiguities; they do not replace this
   comparison by definition.

A valid continuation can use the following independent inputs: the
explicit cycle family and its rational projected moment diagram;
the CM representation identity; the full fixed-weight syntomic
calculation; and CH's full local interpolation theorem. The projective
analytic continuation then uses zeros of an analytic wedge and needs
no bound on the nonzero pointwise period scalars.

It cannot use any of the following as a replacement: equality of a
single ordinary regulator coordinate; an assumed nonzero finite
localization; an identification of the opposite-weight analytic
primitive with a different global weight line; or an unweighted trace
in place of (3.9). The finite two-slope calculation remains valuable,
but its arithmetic interpretation requires the exact full comparison
described here.
