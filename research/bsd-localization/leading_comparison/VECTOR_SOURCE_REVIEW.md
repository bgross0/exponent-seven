# The local direction omitted by the three scalar reciprocity laws

Date: 2026-11-27. Pilot: E389.a1, K=Q(sqrt(-71)), p=5.

## Result of this bounded review

The reviewed reciprocity theorems do not identify

    B = M(0) im(P(0))

for the full inverse-Bol de Rham family in `README.md`. There is a precise
structural reason: the f-, g-, and h-unbalanced laws all first discard the
same submodule F3. For the CM pair in this pilot, that submodule is the
ordinary local direction of the variable anticyclotomic block. Rotating
the roles of the three forms therefore does not recover a second
coordinate of that block.

There is also a genuine full syntomic formula in Darmon--Rotger I,
Theorem 3.8. Its comparison with the inverse-Bol expression is stated only
after ordinary projection in Theorems 3.12--3.14. This gives a concrete
place to investigate an extension, rather than a theorem that already
discharges the required line comparison.

This conclusion is scoped to the sources and statements below. It is not
a claim that every possible result in the literature has been exhausted.
In particular, it does not promote B_DL to the arithmetic line B.

## 1. The quotient used by Castella--Do and BSV

Use Castella--Do's ordinary filtrations and suppress the common
self-dualizing character twist in this paragraph. Their equations
(4.6)--(4.7), in Section 4.3, give

\[
 F^3=V_f^+\otimes V_g^+\otimes V_h^+,
\]

\[
 F^{\mathrm{bal}}/F^3
 =V_f^{gh}\oplus V_g^{fh}\oplus V_h^{fg},
\]

where

\[
\begin{aligned}
 V_f^{gh}&=V_f^-\otimes V_g^+\otimes V_h^+,\\
 V_g^{fh}&=V_f^+\otimes V_g^-\otimes V_h^+,\\
 V_h^{fg}&=V_f^+\otimes V_g^+\otimes V_h^-.
\end{aligned}
\]

The regulator in (4.8), the localization/projection in (4.9), and
**Theorem 4.3.2** use the first quotient summand. Their g- and h-versions
use the other two. The source identifies this result with BSV's
**Theorem A**, whose three scalar laws are constructed in **Section 7.3,
Proposition 7.3**. None is a regulator on the full rank-four balanced
local module before taking this quotient.

An elementary consequence is that every class in the image of
`H^1(Q_p,F3)` is in the kernel of all three quotient maps. This statement
does not require the map from that cohomology group to be injective: its
image suffices. Thus combining all three laws cannot recover information
discarded by the common quotient.

## 2. Identifying the discarded direction in this CM pilot

This is visible directly in Castella--Do's CM decomposition, rather than
being an analogy between ordinary and finite directions.

Let `T=T_f^vee(1-r)` in their notation, with r=1 for the elliptic curve,
and write

\[
 \chi_1=\xi_1^{-1}\xi_2^{-1}\Psi_{W_1}^{1-c},\qquad
 \chi_2=\xi_1^{-1}\xi_2^{-c}\Psi_{W_2}^{1-c}.
\]

Equation (5.5) decomposes the fixed-f triple representation into the two
CM-induced blocks. Equation (5.9), in the proof of Proposition 5.3.1,
describes its balanced local module at the selected prime as

\[
 F^{\mathrm{bal}}\simeq
 (T\otimes\chi_1)
 \oplus(T^+\otimes\chi_2)
 \oplus(T^+\otimes\chi_2^c).
                                                        \tag{1}
\]

The first displayed calculation in the proof of **Theorem 5.4.1**, printed
page 41, identifies

\[
 F^3=T^+\otimes\chi_1.                               \tag{2}
\]

Together, (1)--(2) yield

\[
 F^{\mathrm{bal}}/F^3\simeq
 (T^-\otimes\chi_1)
 \oplus(T^+\otimes\chi_2)
 \oplus(T^+\otimes\chi_2^c).                          \tag{3}
\]

The proof explicitly matches these to the f-, h-, and g-quotient pieces,
respectively. The theorem specializes one CM family to weight two, but
(1) is the preceding fixed-f, two-CM-variable decomposition. Equation (2)
also follows before that specialization by selecting both CM plus lines
in the tensor product. Consequently the same identification applies to
the pilot's weight diagonal.

For `xi1=psi`, `xi2=psi^(-1)`, one has

    xi1^(-1) xi2^(-1) = 1,
    xi1^(-1) xi2^(-c) = psi^(-2).

On the diagonal used in the package, W1 varies and W2=0. Hence:

| Published quotient | CM block on this diagonal | Information supplied |
|---|---|---|
| f quotient | T^- tensor the variable anticyclotomic character | The known singular/ordinary scalar law |
| h quotient | T^+ tensor psi^(-2) | An auxiliary block |
| g quotient | T^+ tensor psi^2 | The conjugate auxiliary block |
| F3, removed before all three | T^+ tensor the variable character | The missing local direction of the variable block |

The labels of the two primes exchange under complex conjugation; that
does not change the block distinction. At the base, the local-control
identification in `../finite_log_reciprocity/` relates the variable
ordinary direction to the finite local line.

This explains exactly why a second scalar obtained merely by relabelling
f, g and h is not a second row of the desired regulator on
`loc_p(kappa_1)`. It belongs to a different CM block.

## 3. Consequence for the projective comparison

The known f-law determines the image of the variable localization under
the projection to `H^1(K_p,T^- tensor chi1)`, followed by its scalar
regulator. It does not determine an embedding of the specialized image
line into both coordinates of the analytic de Rham space.

The projective question asks for precisely that embedding. The remaining
freedom is the shear already exhibited in `README.md`, Section 6: keeping
the ordinary row fixed does not fix the line `M(0)im(P0)`. The other two
laws in (3) add no equation on the missing variable coordinate and hence
do not remove that freedom.

This is an insufficiency statement about these formulas. It does not
assert the existence of different arithmetic realizations with arbitrary
shears, or prove that no additional geometric relation can fix the line.

## 4. The finite-slope theorem has an explicit quotient too

Huang's current version, arXiv:2403.18620v2, **Proposition 4.21** states
that its three-variable regulator factors through the rank-one
trianguline quotient

    M_f = F^-M(f) tensor F^+M(g) tensor F^+M(h)

with the specified self-dualizing twist. **Theorem 4.23** evaluates this
scalar regulator on the diagonal class. Definitions 4.19 and the
filtration immediately before it make the analogue of F3 explicit.
Thus, for a fixed choice of triangulations, this extension retains the
same omitted direction.

There are two additional requirements before changing the elliptic
refinement could be used as another equation for this pilot:

1. The proof of **Theorem 3.9**, leading to **Theorem 3.10**, uses the
   chosen Frobenius lift `eta_f^a` under the inequality `a<k_f-1` in
   Section 3.2. For the other elliptic refinement here,
   `a=v5(beta_f)=1=k_f-1`; direct substitution at weight two is outside
   that stated splitting hypothesis. A Coleman-family continuation may
   be a possible route, but its regular specialization is extra work.
2. One must compare the resulting diagonal family and triangulation with
   the same Castella--Hsieh variable localization and the same analytic
   inverse-Bol vector. The existence of another refined-family scalar
   law does not itself prove that comparison.

The earlier BSV paper *Diagonal classes and the Bloch--Kato conjecture*,
**Theorem A**, similarly assumes `ord_p(alpha_f)<k_f-1` and evaluates a
single selected Frobenius lift. It does not already cover that boundary
by naming the other root alpha_f.

## 5. The genuinely vector-valued syntomic starting point

Darmon--Rotger I provides more than a scalar law at geometric balanced
weights:

* **Proposition 3.7** constructs a proper de Rham class with vanishing
  annular residues from a finite-polynomial primitive.
* **Equation (72)** defines `xi(omega_g,omega_h)` by applying the inverse
  Frobenius polynomial.
* **Theorem 3.8, equation (74)** pairs this class with arbitrary `eta` in
  the indicated first-factor cohomology to give the diagonal cycle's
  Abel--Jacobi value.

This is a full de Rham comparison for that syntomic class. However,
**Theorems 3.12--3.13** compare it with an inverse differential product
only after `e_(f*,ord)`. **Theorem 3.14** consequently evaluates only on
the unit-root test subspace. These are not the asserted full-vector
identity for the package's inverse-Bol family.

The proof indicates a specific extension worth examining for our
special weight pattern `(2,k,k)`. In this case the inverse differential
is exactly the inverse Bol operator `d^(1-k)`, and the resulting product
has fixed weight two. Equations (98)--(99) give the vector-valued
primitives. Contraction from the two Sym^(k-2) factors to their determinant
power selects the last primitive coefficient, proportional to

    (-1)^(k-2) (k-2)! d^(1-k)(g^[p]) * h.

The proof's passage from equation (95) to (96) uses Lemma 2.17 to remove
U-annihilated products after ordinary projection. In the package's proper
weight-two cohomology, U is invertible, so such products also have zero
full cohomology class whenever the indicated products belong to that
cohomology construction. This suggests retaining the Frobenius operator
instead of substituting its ordinary eigenvalue.

That observation is a route to a new proof, not a statement of the cited
theorem. A completion must track the full contractions, Frobenius/Tate
twists, all stabilization maps, and the second CM embedding. It must then
interpolate the full syntomic expression near weight one and identify
the resulting class with the actual CH localization. Factorials and
non-unit-root terms cannot simply be specialized by formally putting
k=1 in a classical formula.

Until those steps are done, neither the full syntomic theorem nor the
existing ordinary inverse-Bol comparison establishes `B=B_DL`.

## 6. A recent Euler-system comparison does not match this base point

Alonso--Omil-Pazos--Rivero, *Anticyclotomic diagonal classes and
Beilinson--Flach elements* (IMRN 2026, rnag236), compares classes using a
CM family specializing to the irregular weight-one Eisenstein series
`Eis_1(epsilon_K)`; see its Section 1.1. Its Theorem 1.2.1 also specifies
a rank-one enlarged Selmer-module hypothesis and a nonzero g-unbalanced
p-adic L-function. Our two order-seven CM forms are cuspidal and regular
at weight one. No specialization or class comparison transferring that
theorem to the present reflected class has been established here.

This is a direct hypothesis mismatch, rather than a reason to disregard
the comparison method in a future construction.

## Primary sources and locations

* **CD:** Castella--Do, *Diagonal cycles and anticyclotomic Iwasawa theory
  of modular forms*, author version August 4, 2025. Section 4.3,
  equations (4.6)--(4.9), Theorem 4.3.2; equation (5.9),
  Proposition 5.3.1; Theorem 5.4.1 and its proof.
  https://kimtuando.github.io/website/Schoen_CM.pdf
* **BSV22:** Bertolini--Seveso--Venerucci, *Reciprocity laws for balanced
  diagonal classes*, Theorem A and Section 7.3, Proposition 7.3.
  The author-hosted collected volume places this paper after the
  Darmon--Rotger contributions; its own page numbers begin again at 1.
  https://www.math.mcgill.ca/darmon/pub/Articles/Research/70.DR3/asterisque.pdf
* **BSV20:** Bertolini--Seveso--Venerucci, *Diagonal classes and the
  Bloch--Kato conjecture*, Muenster J. Math. 13 (2020), 317--352,
  Theorem A and Sections 1.1, 3.1.3, 4.
  https://www.uni-muenster.de/FB10/mjm/vol_13/mjm_vol_13_09.pdf
* **Huang:** *Triple product p-adic L-functions for finite slope families
  and a p-adic Gross--Zagier formula*, arXiv:2403.18620v2,
  November 2026. Section 3.2, Theorems 3.9--3.10,
  Definition 4.19, Proposition 4.21, Theorem 4.23.
  https://arxiv.org/html/2403.18620v2
* **DR I:** Darmon--Rotger, *Diagonal cycles and Euler systems I:
  A p-adic Gross--Zagier formula*, author PDF; Section 3,
  Proposition 3.7, Theorems 3.8 and 3.12--3.14, equations (72),
  (74), (95)--(99).
  https://www.math.mcgill.ca/darmon/pub/Articles/Research/62.DR-Diagonal1/paper.pdf
* **AOR:** Alonso--Omil-Pazos--Rivero, *Anticyclotomic diagonal classes
  and Beilinson--Flach elements*, IMRN 2026, rnag236,
  Section 1.1 and Theorem 1.2.1.
  https://doi.org/10.1093/imrn/rnag236
  Preprint: https://arxiv.org/abs/2509.07564
