# Arithmetic specialization at the weight-two edge

Date: 2026-11-27. This is a continuation of the independent source audit.
It does not change the frozen fixed-weight or finite-computation files.

## Current status and correction

The previous Section 3 claimed that a raw moment/localization argument
proved the normalized specialization of the DR22 family at `(2,k,k)`.
That claim is withdrawn: the argument did not establish compatibility
with the dual ordinary specialization defining the family. Killing an
extra boundary term was insufficient. The precise diagnosis is in
[the independent edge audit](../edge_specialization_audit/README.md).

The current proof uses the **BSV family** instead. The replacement
[full specialization proof](../general_criterion/BSV_REPAIR.md) starts
from BSV Theorem 8.1, which already covers balanced weight-two triples,
then proves the required exponent-zero extensions of its finite
p-stabilization and geometric cycle comparisons. The rational cuspidal
filter in Section 2 below remains valid. The local-character and
operator calculations in Sections 4--5 also remain valid.

The global comparison is generic proportionality of BSV and CH in the
same rank-one Selmer module. Reflection and global division continue to
use the actual CH class. No equality of the historical BSV and DR22
families is asserted.

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
  Theorem 8.1 is full Galois-class specialization for every balanced
  classical triple, including `(2,k,k)`. Proposition 8.3 and Section 3.2
  print positive-weight restrictions; their required finite and geometric
  extensions are proved in the replacement note. The standing prime
  restriction is `p >= 5`, visually checked on page 3; our earlier reading
  as `p>5` was a text-extraction error. The official erratum preserves the
  ordinary duality used by this construction.
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

Equality of ordinary outputs does not identify full classes. The current
proof explicitly chooses the BSV family for the geometric comparison and
uses the rank-one Selmer theorem to compare it generically with CH. The
reflected construction is still performed on CH, so no unproved transfer
of its global symmetry to a different normalization is required.

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

## 3. Replacement for the withdrawn DR22 specialization argument

The former argument in this section used raw covariant moment maps as
though they were the normalized dual ordinary comparison in DR22.
The independent audit explains the mismatch and the trace-degree factors
that raw moments acquire. It does not claim that the actual published
family or its theorem is false. The proof formerly written here was
incomplete, and is not an input to the current localization theorem.

The replacement is
[BSV_REPAIR.md](../general_criterion/BSV_REPAIR.md). It proves:

> For ordinary Hida families satisfying BSV's actual hypotheses, at a
> crystalline balanced triple `(2,k,k)`, `k>=3`, the full BSV class after
> the specified ordinary-to-tame map is a nonzero scalar multiple of the
> full cuspidally projected etale Abel--Jacobi class of the DR I cycle.

The proof uses BSV Theorem 8.1 for its normalized family specialization,
extends the three finite push-pull steps of Proposition 8.3 with the
coefficient map `Sym^0(lambda)=id`, and identifies the edge diagonal's
relative invariant with `(X_2Y_3-Y_2X_3)^(k-2)`. Functorial Gysin,
Leray and Hochschild--Serre maps identify the full extension class.
The rational cusp filter of Section 2 identifies the corrected DR I
cycle with the same projected class. All four resulting Euler factors
are nonzero at these classical weights, by their complex absolute values.
No integral-unit assertion is required.

Use the sequence `s_n=2(p-1)p^n`, hence `s_n=8*5^n` in this pilot,
to satisfy BSV's congruence modulo `2(p-1)` at the weight-one CM center.
The analytic wedge proof is unchanged for this sequence. Its source
hypotheses, including ordinary duality in the official erratum and the
weight-one non-real-multiplication condition, are checked in the
replacement note.

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
At the arithmetic weights `s=8*5^n`, principal-unit powers agree with
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

1. **Chosen family and test vectors.** Use the BSV-defined class
   consistently in the geometric comparison, with its CM projection
   and test-vector maps. Compare it generically with CH in full
   cohomology using the rank-one Selmer argument. Equality of scalar
   reciprocity laws is not this comparison. Reflection and division
   remain constructions on the actual CH family.
2. **Normalized local identification.** Match the full syntomic/BK
   vector, in its CM period and elliptic cup basis, with CH (3.9)
   and Theorem 3.4, including the selected local prime, the twist
   `j=-s`, `sigma_0`, and the LT/cyclotomic period. Equations (5)
   and (6) remove specific ambiguities; they do not replace this
   comparison by definition.

A valid continuation can use the following independent inputs: the
normalized BSV specialization and its rational projected cycle comparison;
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
