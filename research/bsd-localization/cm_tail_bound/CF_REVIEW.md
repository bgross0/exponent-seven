# Discharging the qualitative CM-family realization

Date: 2026-11-27. This is a source review and mathematical argument for the
pilot in `README.md`. The quantitative theorem and its checker are frozen.

## Conclusion and precise scope

For the actual normalized ordinary CM family attached to the order-seven
class character of K=Q(sqrt(-71)), hypothesis **(CF)** of the accompanying
note follows from published Coleman-family and eigencurve theory, together
with the explicit change of chart below. It does not require a new
nonvanishing conjecture or an effective initial radius. This conclusion is
at the level of the cited analytic theorems; it has not been formalized in
Lean or certified by the finite q-expansion checker.

The assertion concerns the entire ideal-sum family defined in
`../reflected_pilot/README.md`, not a family inferred from its saved finite
coefficient archive. It supplies qualitative overconvergence of the three
fixed-weight jets. The quantitative radius and norm then come from the
independent argument in `README.md`, Sections 2--4.

It does not execute a Katz-to-pole reduction, identify the integral lattice
used by a numerical backend, or prove a regulator comparison with a global
Galois-cohomology class.

## 1. Exact results used

* **[BD, Theorem 1.1, Corollary 1.2, Theorem 7.2]:** the regular weight-one
  point is smooth, with an etale weight map outside the specified
  real-quadratic exception; its CM branch is unique; adjoining the bad
  tame Hecke operators does not change the local eigencurve.
* **[C, Proposition B5.6]:** the finite-slope Hecke algebra and the
  finite-slope cuspform module are perfectly paired by `a_1(tm)`.
  Its setup permits an arbitrary center of the weight disk.
* **[C, Section B4, definition]:** a family of type i is represented by
  dividing its q-expansion by the fixed Eisenstein series E to the varying
  weight; the resulting function has diamond character omega^i.
* **[C, Section B1 and Lemma B1.2]:** E=E_(1,0) has weight one and character
  omega^(-1); E^(p-1) reduces to the Hasse invariant on the canonical
  ordinary component.

Here C is Robert F. Coleman, *P-adic Banach spaces and families of modular
forms*, Inventiones Mathematicae 127 (1997), 417--479;
[author PDF](https://wstein.org/people/coleman/papers/p-adic_banach_spaces.pdf).
The relevant printed pages are 447--449, 458--459, and 465--466.

BD is Joel Bellaiche and Mladen Dimitrov, *On the eigencurve at classical
weight one points*, [arXiv:1301.0712](https://arxiv.org/abs/1301.0712),
[PDF, version 2](https://arxiv.org/pdf/1301.0712).
The theorem locations are pages 2--3 and 20 of that PDF.

**A restriction that matters:** C, Corollary B5.7.1 assumes that the base
weight exceeds slope+1. It cannot by itself produce this slope-zero
family centered at weight one. The argument below uses Proposition B5.6
and the etale Hecke branch instead. The inequality in Theorem B5.7 is
needed only when identifying the nearby classical specializations.

## 2. Why the pilot has an etale ordinary branch

The base theta form is the new cuspidal weight-one form induced from the
nontrivial unramified class character psi of order seven. It has tame level
71. The prime 5 splits in K: the polynomial X^2-X+18 has the distinct roots
2 and 4 modulo 5. Its two weight-one 5-refinement eigenvalues are zeta7^2
and zeta7^5. They are distinct even in the residue field, so each refinement
is regular and ordinary. For the inverse-character family h the same two
roots occur in the opposite order.

The Artin representation is Ind_K^Q(psi), with dihedral image D_14.
This group has just one index-two subgroup, the rotation subgroup C_7.
If restriction to another quadratic field were reducible, Clifford theory
would give another quadratic inducing field (equivalently another
quadratic self-twist). There is none: the inducing quadratic field is K,
which is imaginary. Thus the real-quadratic exception in BD cannot occur.

After extending the coefficient field if necessary and shrinking an
affinoid weight disk about weight one, the full Hecke eigencurve therefore
has a section through the chosen refinement, isomorphic to that disk.
Let A be the disk's analytic function ring and let

    lambda : R -> A

be the corresponding character of the full finite-slope Hecke algebra.
The slope is zero after shrinking, since its U5 eigenvalue is a unit at
the center. Bad tame eigenvalues, including U71, belong to this character;
this is why the full-Hecke conclusion in BD, Theorem 7.2 is recorded.

## 3. Producing a genuine normalized eigenfamily

Let H be Coleman's finite-slope cuspform module on this disk, realized on
a common strict ordinary neighborhood. The pairing in Proposition B5.6
identifies H with Hom_A(R,A). Define m to be the element corresponding to
lambda. For every t,r in R,

    <r, (t-lambda(t))m>
      = lambda(rt)-lambda(t)lambda(r) = 0.

Perfection gives `tm=lambda(t)m`, and taking r=1 gives `a_1(m)=1`.
Furthermore, `a_n(m)=lambda(T_n)` for every n. This constructs an actual
Banach-valued family, not only formal Hecke eigenvalues. Its normalization
also removes a potentially varying scalar before the chart change.

The package's ideal-sum formula gives the normalized ordinary theta
specializations at integer weights

    k_n = 1 + 4*5^n,       s_n = k_n-1.

These are classical cuspidal forms for k_n>1, and approach the specified
weight-one refinement. In a sufficiently small finite ordinary Hecke
chart they lie on its unique branch. They have the same normalization
a_1=1. Hence the q-coefficients of m and of the ideal-sum family agree on
an infinite sequence accumulating at an interior point of the disk.
The one-variable rigid analytic identity theorem identifies each full
coefficient function.

Equivalently one can use the unique normalized primitive Hida family in
BD, Corollary 1.2. The sequence argument explains which normalization and
weight coordinate are being compared. Only classical specializations
with k_n>1 use classicality; no weight-one classicality inequality is
silently invoked.

Write the resulting family as h_s, where the actual modular weight is
1+s and W=6^s-1. The same reasoning applies to both CM embeddings and to
the inverse class character.

Any finite coefficient-field extension used to split the local Hecke
chart introduces no period normalization: the explicit q-expansion lies
in the original unramified field containing zeta7. Uniqueness and the
q-expansion principle descend the normalized jets to that field. Thus
their Katz-coefficient valuations have the integer value group used in
the companion tail bound.

## 4. The exact E4 chart comparison

Coleman's fixed weight-one Eisenstein series E lives on the canonical
Gamma_1(5) cover. On the type-one component, the family just constructed
is represented by the overconvergent function

\[
 B_s(q)=\frac{h_s(q)}{E(q)^{1+s}}.
\]

The quotient notation at noninteger weights denotes the analytic
trivialization in C, Section B4. The function B_s has diamond character
omega. The series E itself has weight one and diamond character
omega^(-1).

Put

\[
 S=\frac{E^4}{E_4}.
\]

This is a scalar function of weight zero and trivial diamond character.
Both its numerator and denominator reduce to the Hasse invariant on the
canonical ordinary component. Consequently S reduces to 1 in the
geometric ordinary model. This is stronger than knowing its expansion at
one cusp is congruent to 1.

The denominator is invertible on the ordinary affinoid, and S extends to
a strict neighborhood. By shrinking that neighborhood, `|S-1|<1`
uniformly. Its Banach-valued logarithm exists. On a sufficiently small
weight disk the exponential

\[
 S^{s/4}=\exp\bigl((s/4)\log S\bigr)
\]

therefore converges. Define

\[
 \boxed{F_s=E\,S^{s/4}B_s.}                         \tag{CF-chart}
\]

It is a family of sections of fixed weight one. The residual diamond
characters cancel, so it descends from the canonical Gamma_1(5) cover
to the tame-level-71 ordinary neighborhood. C, Section B2, identifies
this cover with the canonical-subgroup neighborhood; the finite diamond
quotient is precisely the descent used here. The tame character chi_-71
is unchanged.

At q-expansions, the normalized constant terms of E and E4 are one, so
their logarithms and the indicated powers give exactly

\[
 E\,(E^4/E_4)^{s/4}\frac{h_s}{E^{1+s}}
       =E_4^{-s/4}h_s.
\]

Taking the first three Taylor coefficients yields the fixed-weight jets
in (CF) on a common positive-radius neighborhood. No effective lower
bound for that initial radius or for the size of the weight disk is
needed for this conclusion.

## 5. The operator identity and rescaling finite jets

Let j=s/4, G=E4/V5(E4). At integer s divisible by 4, the q-expansion rule
`U5((V5 a)b)=a U5(b)` gives

\[
 U_5(G^j F_s)
 =U_5\bigl(h_s/(V_5E_4)^j\bigr)
 =E_4^{-j}U_5(h_s)
 =\alpha(s)F_s.
\]

On a sufficiently small common disk all quantities are analytic. The
identity at the accumulating classical weights proves the identity of
Banach-valued families, or coefficientwise by q-expansion injectivity.
This proves the second assertion in (CF), including its specified
trivialization. The ideal-sum construction supplies the integral
W-coefficients and the unit ordinary eigenvalue used separately in the
quantitative norm proof.

There is a useful distinction between a small disk and a finite jet.
For W=125u, the bound `m_(4/25)(log G)>=-1` in `README.md` gives

    m((s/4)log G) >= 1 > 1/(5-1),

so the full operator multiplier exponential converges on the unit u-disk.
This estimate alone does not guarantee that the eigenfamily is defined
on that entire weight disk; its initial disk can be smaller. The
existence argument only requires an analytic germ. Its two derivatives
can be rescaled over the coefficient field to W=25w independently of
the original disk size. The integral q-coefficients then enter the
minimum-norm argument of `README.md`; no unmeasured Cauchy constant is
inserted in that bound.

Thus the qualitative input CF is discharged for this explicit CM family
at the level of the cited theorems. The quantitative tail statement still
uses the saturated Katz and pole lattices specified in the companion
note, and a numerical output still needs the separate backend lattice,
precision, and global arithmetic comparisons.

## Context in the source used by the project

Darmon--Lauder, *Stark points and Perrin-Riou's philosophy*, Section 1
uses the local weight coordinate supplied by Bellaiche--Dimitrov; Section
2 explains the unique Hida family attached to each regular refinement.
Those statements agree with the branch identification above. The
additional work here is the explicit fixed-weight E4 chart and the
normalized Banach-section argument needed by the quantitative certificate.
[Author PDF](https://people.maths.ox.ac.uk/lauder/papers/DL.pdf).
