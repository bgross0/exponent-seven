# A big-image certificate for E389 at five

Date: 2026-11-27. Curve `y^2+y=x^3+x^2-2x`.

## Result and purpose

The image of the five-adic Tate-module representation contains
`SL2(Z5)`. This verifies the **big image** hypothesis in Castella--Do,
Notation 3.3.2, for the pilot. The finite certificate below establishes
the input arithmetic; the infinite-image conclusion also uses Tate
uniformization and the stated closed-subgroup lifting theorem.

This is a hypothesis check for an existing arithmetic theorem. It does
not evaluate a diagonal class or establish nonzero localization.

## 1. Arithmetic inputs

Direct invariant formulas give

    c4 = 112,       c6 = -856,       Delta = 389,
    j = 1404928/389.

The integral model is minimal at 389, since a reduction in discriminant
valuation would subtract a positive multiple of twelve from valuation
one. The unit c4 gives multiplicative reduction there. At all other
primes Delta is a unit. Thus the conductor is 389.

Exact enumeration gives `#E(F3)=6` and `#E(F5)=9`. In particular,
`a3=-2`, `a5=-3`, and the curve is ordinary at five. The residual
Frobenius at three has characteristic polynomial

    X^2 + 2X + 3,

whose discriminant is 2 modulo five and which has no root in F5.
Consequently it preserves no F5-line. This fact alone proves
irreducibility over F5; absolute irreducibility will follow from the
larger image established next.

## 2. The inertia transvection

Over an unramified extension where the multiplicative reduction splits,
Tate uniformization gives `E = G_m/q^Z` with
`v389(q) = -v389(j) = 1`. Adjoining `q^(1/5)` has ramification degree
five, while fifth roots of unity lie in an unramified extension.
On the basis represented by `zeta5` and `q^(1/5)`, an inertia element
therefore acts by

    U = [[1,1],[0,1]].

The nonsplit quadratic twist is unramified and has no effect on inertia.
The uniformization, valuation and Galois compatibility used here are
the standard Tate theorem; a primary-source exposition is Helminck,
[Section 5 and the torsion-basis argument in Section 6](https://arxiv.org/pdf/1803.00079).
We use its uniformization statement, not its separate theorem about
edges of semistable coverings.

## 3. Residual image: a proof and an exhaustive certificate

Let G be the residual image. The transvection U has a unique fixed line
L. A Frobenius element at three moves L, since it has no F5 eigenline.
Conjugating U by that element gives a transvection with a different
fixed line. In a basis of the two fixed lines these transvections have
the forms `[[1,a],[0,1]]` and `[[1,0],[b,1]]`, with a,b nonzero. Taking
powers yields every upper and lower elementary matrix over F5. These
generate SL2(F5). Thus G contains SL2(F5), and its natural representation
is absolutely irreducible, including after restriction to G_K.

For an independently executable finite certificate, put the inertia
transvection in the displayed standard basis. The Frobenius matrix in
that same basis is unknown, but has trace -2 and determinant 3. There
are exactly twenty such matrices over F5. `check_image.py` enumerates
**all twenty**, and verifies that each, together with U, generates all
480 elements of GL2(F5). This avoids assuming an unjustified simultaneous
basis for inertia and Frobenius.

The checker also verifies that the standard upper and lower elementary
matrices generate all 120 elements of SL2(F5). Replacing the transvection
by the identity, or replacing the irreducible Frobenius by a reducible
diagonal matrix, fails the full-image check as expected.

## 4. From the residual image to the closed five-adic image

Let H be the closure of the commutator subgroup of the actual five-adic
image. Then H is a closed subgroup of SL2(Z5), and its residual image
is SL2(F5), the commutator subgroup of GL2(F5). The standard lifting
lemma for primes at least five gives `H=SL2(Z5)`. The precise statement
is Serre, *Abelian l-adic representations and elliptic curves*,
IV.3.4 Lemma 3; it is also explicitly stated in the introduction of
[Landesman--Swaminathan--Tao--Xu](https://arxiv.org/pdf/1607.04698).
We use that g=1 statement, not their g>=2 main theorem.

This proves the required big-image inclusion. Since K/Q is abelian,
the image of G_K still contains this commutator subgroup. The Weil
pairing and surjectivity of the cyclotomic determinant would further
give the full GL2(Z5) image over Q, but that strengthening is unnecessary
for the application.

## 5. Other elementary inputs for the rank-one Selmer theorem

The following are checked in `result.json`, or follow by the standard
interpretations specified here:

| Hypothesis | Pilot verification |
|---|---|
| p splits in K | `X^2-X+18` has roots 2,4 modulo5 |
| p does not divide h_K | the seven reduced forms of discriminant -71 give h_K=7 |
| N^- squarefree with an odd number of factors | 389 is prime and inert in K |
| `(pN,cD_K)=1`, with c=1 | `gcd(5*389,71)=1` |
| Trivial character, j=0, r=1 | conductor one, prime-to-five finite part; `p>2r-2` |
| Residual absolute irreducibility | the SL2(F5) inclusion above |
| p-distinguished | ordinary inertia characters are 1 and the nontrivial mod5 cyclotomic character |
| Non-CM | the nonintegral rational j above cannot be a CM j-invariant |
| Big image | the SL2(Z5) inclusion above |

The arithmetic rank-one application is in
`../global_class_comparison/README.md`. Its source is
[Castella--Do](https://kimtuando.github.io/website/Schoen_CM.pdf),
Theorem 3.3.3 and the proof of Theorem 5.6.1, with the hypotheses of
Theorem 5.5.1. The implication involving a nonzero complex central
L-value in Theorem 5.5.1 is not an added hypothesis of Theorem 5.6.1.

## Reproduction and limits

    python research/bsd-localization/galois_image/check_image.py --check

The saved certificate includes all twenty possible residual Frobenius
matrices and their generated group orders. It is exact finite arithmetic.
The standard Galois, reduction, CM and lifting theorems used to interpret
it are written mathematical inputs, not conclusions of a Python test or
new Lean proofs.
