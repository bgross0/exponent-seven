# Actual field arithmetic for the BSD pilot at discriminant -71

This development supplies the maximal-order ideal-class arithmetic and a local
unit calculation needed by the original E389 BSD pilot. It uses the native
`Exp7Lean` pin, Lean 4.37.0-rc1 and Mathlib
`31ce06eaadf4a200c0e1407c5f10953cf606b8f8`.

Verification completed on 2026-11-28: **26 exported theorems** passed the
axiom audit, and all **13 project modules** in their import closure passed
separate kernel replay. The five private proof helpers are checked with
their containing module. The receipt below records the exact verified
source and object hashes.

The mathematical objects are Mathlib's actual quadratic order, ideals,
ideal class group, algebra homomorphisms, and units. The results do not
assume an exponent-seven classification, GRH, a class-number table, CM
identification, or a Selmer bound.

## Class group and chosen generator

Write

\[
\mathcal O=\operatorname{Exp7.OK}(71)=\mathbb Z[\omega],
\qquad \omega^2=\omega-18,
\qquad P=(2,\omega),\quad g=[P].
\]

The class-group module proves

\[
\operatorname{ord}(g)=7,\qquad
\langle g\rangle=\operatorname{Cl}(\mathcal O),\qquad
\#\operatorname{Cl}(\mathcal O)=7.
\]

It also proves that the class of `(3, omega)` is `g^3`. A coordinate
equivalence with the additive group `ZMod 7`, written multiplicatively,
specifies the chosen generator. The coordinate one is the additive residue
one, not the multiplicative identity.

Source: [SeventyOne.lean](../../Exp7Lean/Exp7Lean/ClassGroup/SeventyOne.lean).

The proof has four arithmetic steps:

1. The explicit principal-power identity
   \(P^7=(10+\omega)\), with \(N(10+\omega)=128\), gives \(g^7=1\).
2. The existing nonprincipality theorem applies because \(4\cdot2<71\),
   so \(g\ne1\). Since seven is prime, its order is exactly seven.
3. The norm identity \(N(2+\omega)=24\) gives
   \(g^3\overline{[(3,\omega)]}=1\). Conjugation inverts the split ideal
   class, so \([(3,\omega)]=g^3\).
4. The existing sharp generation theorem reduces all classes to split prime
   ideals of norm at most \(\lfloor\sqrt{71/3}\rfloor=4\). Only 2 and 3
   occur. Their two roots give the class already treated and its inverse.

The cardinality conclusion follows from generation and the exact order. No
pre-existing finiteness hypothesis is needed, and exponent seven by itself
is not used to infer class number seven.

## Principal ideal and actual local evaluations

The local module proves the equality of ideals

\[
(2,\omega)^7=(10+\omega),\qquad N(10+\omega)=128,
\qquad \operatorname{absNorm}(2,\omega)=2.
\]

It constructs actual algebra homomorphisms

\[
\mathcal O\longrightarrow\mathbb Z/25\mathbb Z,
\qquad \omega\longmapsto12\quad\hbox{and}\quad\omega\longmapsto14,
\]

and proves that conjugation exchanges them. For \(\alpha=10+\omega\),
the two images are the units 22 and 24. Their ratio \(r\) is formed in the
unit group, with explicit inverses, and satisfies

\[
r=3\pmod{25},\qquad \operatorname{ord}(r)=20,
\qquad \operatorname{ord}(r\bmod5)=4,
\qquad r^4=1+5\pmod{25}.
\]

The last equality is the first nonzero principal-unit digit needed for a
prospective five-adic lifting argument. Reversing the embedding inverts
the ratio; the source consistently uses the orientation above.

Source: [SeventyOneLocal.lean](../../Exp7Lean/Exp7Lean/ClassGroup/SeventyOneLocal.lean).

## How this fits the BSD work

The original pilot is

\[
E_{389}:y^2+y=x^3+x^2-2x,\qquad K=\mathbb Q(\sqrt{-71}),\qquad p=5.
\]

The prior BSD arithmetic status is recorded at
[the 320-theorem source snapshot](https://github.com/bgross0/exponent-seven/blob/42521920ce4b38bddf458128b61d389f27b14313/research/bsd-formal/E389_ARITHMETIC_STATUS.md).
It identified this maximal-order class-group calculation as a focused reuse
opportunity. This development supplies that calculation and its local input.

The following remain distinct obligations:

- Prove the Picard-group exact sequence for the nonmaximal orders
  \(\mathbb Z+5^m\mathcal O\), with compatible transition maps. Their
  ring-class groups are not the maximal-order class group proved here.
- Identify the candidate polynomial roots and their isogeny graph with
  actual CM points and the action of the chosen ideal class.
- Identify the supplied E389 finite values with actual CM evaluations in
  the cyclic order, then prove the arithmetic theta tower relations.
- Formalize the required theta-to-Selmer and Kummer/Sha arithmetic.

The local order-20 result is consistent with the expected conductor-25
class number 140, but it is not by itself a proof of that Picard-group
cardinality or of the CM construction. The terminal rank-and-five-primary-Sha
pilot remains open in Lean.

The existing BSD package is pinned to Lean 4.36.0. These results are proved
in the native exponent-seven Lean 4.37.0-rc1 project. Direct consumption by
the BSD package requires a source port or migration and rebuild; objects
from the two toolchains must not be mixed.

## Verification

From the repository root:

```sh
python3 research/bsd-field-arithmetic/verify.py
```

When Lake is not on `PATH`, pass `--lake /absolute/path/to/lake`.

The verifier checks that every public theorem in both modules appears in
the axiom inventory, performs a build with source rehashing, prints theorem
signatures and axiom dependencies, and replays every project module in the
import closure in a separate `leanchecker` process. This includes the
existing ideal-arithmetic and generation-bound dependencies. Each replay
uses the pinned compiled Mathlib imports; it does not replay all Mathlib
from an empty environment.

The only accepted axioms are `propext`, `Classical.choice`, and `Quot.sound`.
No `sorry`, custom axiom, or `native_decide` is used in the new proof sources.
The source hashes, toolchain, Mathlib revision, command results, and object
hashes are recorded in [verification/receipt.json](verification/receipt.json).
The [independent source review](REVIEW.md) states what was reviewed and the
arithmetic interpretation limits.

## Coordination

This branch is based on `main` at
`6b2ee722784e2f1a05ee34f6cfb072c7631af8ba` and adds only the field-arithmetic
modules and their verification/documentation. It is separate from the agent
connecting the height-60 cubic verifier to the smoothed Haar correlation,
and separate from the agent extending `proof-complexity-lab`.
