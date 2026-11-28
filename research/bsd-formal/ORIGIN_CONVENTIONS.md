# CM origins and the theta functional equation

The finite CM generator chooses a cycle origin algorithmically. A distinguished
arithmetic Gross point can have a different origin. Translation multiplies a
theta element by a group element, and changes its functional-equation
multiplier. The formal certificate must retain that multiplier until an origin
identification is proved.

## 1. E433: the actual raw symmetry is not strict inversion

Write gamma=1+T and let star send gamma to gamma inverse. The raw finite element
is

\[
G(\gamma)=\gamma(\gamma-1)^2.
\]

Therefore

\[
G^*=\gamma^{-3}(\gamma-1)^2,
\qquad G=\gamma^4G^*.
\]

`BSDThetaCertificate.finite433_inversion_symmetry` proves this identity using
the genuine Mathlib power-series substitution, over any commutative ring.

The first concrete 5-adic specialization in this formalization accidentally
set the functional-equation multiplier to one. Its proof was a correct
conditional proof, but those specialized hypotheses could not apply to the
displayed raw finite representative with unit ordinary scale. Statement review
caught this before publication.

The incompatibility can be seen already in degree three. For

\[
F=c_2T^2+c_3T^3+O(T^4),
\quad F^*=c_2T^2+(-2c_2-c_3)T^3+O(T^4),
\]

strict inversion requires c3=-c2. The E433 raw representative has c2=c3=1
modulo five. The finite-level relation starts in degree five modulo five,
and the ordinary trace correction starts in degree four, so neither can fix
that degree-three mismatch.

The corrected theorem assumes

\[
F=WF^*,\qquad W(0)=1.
\]

The generic certificate theorem already had this correct form. Exact constant
zero still forces exact linear zero, because the multiplier's constant
coefficient is one. `raw_five_adic_inputs` now proves that all corrected
premises are jointly satisfied by F=T²+T³, W=(1+T)^4, ordinary scale one, and
zero correction/error terms. This is a proved algebraic nonvacuity example.

A strictly symmetric origin can be obtained for this raw expression by
multiplying it by gamma inverse squared:

\[
\gamma^{-2}G=\gamma+\gamma^{-1}-2.
\]

Its order-five coefficient vector is (-2,1,0,0,1). That reindexing preserves
order and the unit leading coefficient; it changes the displayed finite vector.

## 2. E389: preserve the same distinction

The original raw finite representative is

\[
G=5-\gamma-\gamma^2+5\gamma^3-8\gamma^4.
\]

Modulo five, its quadratic and cubic coefficients are respectively one and
three. They also do not satisfy strict inversion in this raw origin. In the
order-five group ring one instead has G=gamma³G-star. Multiplying that finite
representative by gamma yields the symmetric coefficient vector

\[
(-8,5,-1,-1,5).
\]

These last finite reindexing statements are explanatory calculations; the
new explicit substitution/nonvacuity Lean theorems above concern E433.
A compatible infinite origin change must be justified through the tower; a
finite reindexing alone does not identify an infinite arithmetic normalization.

The original E389 mathematical certificate already discusses the translated
functional equation: see the paragraph after strict symmetry in Section 9 of
[`research/theta-certificate.md` at the shared handoff](https://github.com/bgross0/exponent-seven/blob/cf84450fb80b673c9b32c5abb71d7e26d4e87957/research/bsd-theta/research/theta-certificate.md).
Read strict symmetry in the neighboring arithmetic audit as a statement about
the distinguished normalization, and retain the multiplier after changing the
CM origin. The preserved source and earlier verification receipts are not
rewritten here.

## 3. Consequence for the proof boundary

The theta order/unit argument uses a functional equation with multiplier
constant one, so this correction preserves that argument. What must be proved
arithmetically is the equation with the multiplier for the actual computed
origin, together with the integral finite approximation for that same series.

This check illustrates why a successful Lean build and a review of the theorem
statement are both needed. The final package contains the corrected statement,
its proof, and an explicit witness showing that its hypotheses can hold.
