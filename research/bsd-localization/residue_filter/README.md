# Removing the residue quotient without losing a 5-adic digit

This note supplies an exact filter for the open modular-curve cohomology
that occurs before the proper de Rham projection. It applies at level389,
p=5, and to the geometric Frobenius extended linearly over the external
coefficient field.

## Result

Let z be a class in the open cohomology, U=U5 its Verschiebung operator,
and F_E the crystalline Frobenius on H1_dR(E), with

    F_E^2+3*F_E+5=0.

Then (U^2-1)z lies in proper cohomology. If P_E is the elliptic Hecke
projector there, the elliptic component of the canonical Frobenius-split
proper projection is

\[
\boxed{
 \Pi_E(z)=-\frac{F_E+2I}{9}\,P_E\bigl((U^2-1)z\bigr).
}
\]

On an F_E-stable integral lattice, the factor multiplying P_E and its
inverse are integral at 5. The correction introduces no 5-adic precision
loss in that lattice; the saved crystalline basis is such a model. A
merely Hecke-stable lattice need not be F_E-stable, so a change of lattice
must have its denominators recorded separately. This does not replace
the earlier one-digit Hecke projection bound or the separate cost of
representing the input class.

## 1. All boundary points are defined over F25

For p=5 the unique geometric supersingular j-invariant is zero. The
model y^2=x^3+1 over F5 has six points, hence Frobenius trace zero. Its
Frobenius pi satisfies pi^2=[-5]. Therefore pi^2 fixes every cyclic
389-subgroup of its prime-to-5 torsion.

There are 390 lines in P1(F389). The effective automorphism group at j=0
has order three. Its order-three action has no fixed line because
389=2 modulo3, so X0(389) has 390/3=130 geometric supersingular points.
All are fixed by the square of Frobenius. The two cusps of this
prime-level modular curve are rational.

The checker counts the points on the supersingular model and explicitly
partitions P1(F389) into 130 order-three orbits. The geometric implication
from pi^2=[-5] is the argument above, not a statistical inference from
those orbits.

## 2. The residue exact sequence

For a model permitting simple cusp residues, the open cohomology has

    proper dimension: 64,
    residue quotient dimension: (130+2)-1=131,
    total dimension: 195.

On residues, geometric Frobenius acts as five times the permutation of
the boundary points, with the corresponding residue-field action. Every
permutation cycle has length one or two, so F^2=25 on the quotient.
Coleman's relation F*U=5 makes U^2=1 on that quotient. Consequently
(U^2-1)z has zero residues and is a proper class.

The canonical Frobenius splitting is compatible with this filter. On the
residue summand the filter vanishes; on the proper summand it acts by its
usual polynomial in U. This is the needed relationship with the proper
projection used by Darmon--Lauder.

If one works in the cuspidal open space, the two unnecessary cusp residue
directions can be omitted. The stated 195-dimensional model deliberately
allows them and remains valid for the input.

## 3. The inverse is an integral polynomial on E

The elliptic characteristic polynomial gives

    U_E=5*F_E^(-1)=-F_E-3I.

Thus

    U_E^2-I = 3*(F_E+I),
    det(3*(F_E+I))=27.

Moreover

    (F_E+I)*(-F_E-2I)=3I,

so

    (U_E^2-I)^(-1)=-(F_E+2I)/9.

All these identities hold exactly in Q5[F_E], not merely at the saved
precision. The checker also verifies their concrete matrices modulo5^8
using the earlier crystalline certificate. Since nine and27 are units
at5, the correction does not discard either elliptic Frobenius direction.

## 4. Scope and implementation

A direct q-series application of U5^2 would require coefficients at
25 times the desired output indices. In a validated finite-cohomology
or Katz representation, apply the stored operator twice instead. The
filter does not excuse an unproved finite truncation of the input.

The operator P_E in the displayed formula acts on the resulting proper
class. Its old 65-dimensional Manin matrix is not applied directly to
raw q-coefficients. The remaining numerical work is to supply the class
and the operators in a compatible bounded-precision representation.

With coefficients in Q5(zeta7+zeta7^-1), use geometric Q5-linear
Frobenius tensor the identity on that coefficient field. A program that
also Frobenius-twists the external coefficients computes a different
semilinear operation and cannot use this formula unchanged.

The [de Rham strategy](../de_rham_strategy/README.md) describes a small
pole-order quotient and a cup-product alternative. They may use this
filter to avoid constructing an explicit residue basis.

## Reproduction and sources

```sh
python research/bsd-localization/residue_filter/check_filter.py --check
```

The script uses only the standard library. `--write` explicitly refreshes
[result.json](result.json).

The cohomological input is Coleman, *Classical and overconvergent modular
forms*, Theorems5.1 and5.4, and the Frobenius-split residue sequence in
Darmon--Lauder, Section1, equation(5):

* https://wstein.org/people/coleman/papers/classical_and_overconvergent_forms.pdf
* https://people.maths.ox.ac.uk/lauder/papers/DL.pdf

The supersingular classification at5 follows from the Hasse invariant
E4 modulo5; its zero is j=0. The genus and divisor degree can also be
checked from the standard prime-level modular-curve dimension formula.
The filter and its inverse are derived in this note and independently
reviewed, without a claim of novelty or Lean verification.
