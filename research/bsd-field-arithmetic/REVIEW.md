# Independent statement and arithmetic review

Date: 2026-11-28. Review performed by a separate agent from the two proof
authors, using the existing ideal-arithmetic sources and the new module
statements. The first review preceded compilation; successful kernel replay
is a separate requirement recorded in `verification/receipt.json`.

## Findings

The class-group argument concerns `ClassGroup (Exp7.OK 71)`. The prime-power
certificate has parameters `l=2`, `t=0`, `n=7`, `u=10`, `y=1`. Its norm
condition is `100+10+18=128`, and its coprimality condition is `2` not
dividing `11`. Both are correct.

For the norm-24 relation, `t=-2` is zero modulo 2 and one modulo 3. Thus
`(2+omega)` gives the cube of the selected norm-two class times the
conjugate norm-three class. Conjugation inverts the latter, yielding the
stated cube relation with the correct orientation.

The generation bound is four. It requires both root residues zero and one
for primes two and three; the second root gives the inverse class. The
cardinality proof uses cyclic generation and order exactly seven, not a
class-group exponent assumption or an assumed finite type.

The local maps use roots twelve and fourteen of `X^2-X+18` modulo 25.
Conjugation sends twelve to fourteen. For the chosen orientation, the
principal generator has images twenty-two and twenty-four, with inverses
eight and twenty-four. The quotient is an actual unit and equals three.
Reversing the orientation gives seventeen, its inverse. Both have order
twenty, so the orientation is consistent with the claimed local arithmetic.

An independent elementary Python cross-check found the seven primitive
reduced forms `(1,1,18)`, `(2,±1,9)`, `(3,±1,6)`, and `(4,±3,5)` of
discriminant -71 and confirmed the modular unit orders. This check is
corroboration only; the Lean proofs do not rely on an enumeration of forms
or on that Python computation.

## Boundaries checked

No claim identifies the seven polynomial roots with CM classes, or the
literal Phi2 graph with an ideal-class action. The new chosen generator
supplies a cyclic indexing domain, but the existing E389 coefficient vector
still requires its actual CM-evaluation identification.

The local unit calculation does not assume or establish an exact sequence
for nonmaximal-order Picard groups. The maximal-order class group must not
be substituted for those groups. The source also makes no Selmer or Sha
claim.

The development uses Lean 4.37.0-rc1; the old BSD proof package uses 4.36.0.
Linking the status documents is safe, while formal consumption requires a
source port or a shared-pin rebuild.

## Final compiled-source review

After successful compilation, the reviewer reread both frozen proof sources
and these status documents. The added absolute-norm proof correctly applies
the multiplicative ideal norm to the seventh-power identity. The coordinate
equivalence is a genuine group equivalence, with explicit proofs for the
additive residue one and for every integer residue. The full local unit
order is twenty. The concrete `Fact` instances are local and add no assumed
arithmetic hypotheses.

No mathematical defect or scope overclaim was found. The exact source
SHA-256 hashes reviewed were:

| Source | SHA-256 |
| --- | --- |
| `SeventyOne.lean` | `937f9af1b17c84b5adf50844d6a45af475261be5b637e6fcc4123337ec630e7a` |
| `SeventyOneLocal.lean` | `efec87a9364cfe8d1944eb05efc9f137084c484f7538e9659126de57b203a601` |

This review is independent of the separate kernel replay and axiom audit.
