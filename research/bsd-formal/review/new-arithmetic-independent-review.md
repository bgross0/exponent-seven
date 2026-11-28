# Independent review of the new arithmetic modules

Review date: 2026-11-28. This review is independent of the implementation
agents and made no edits to their Lean sources.

## Exact degree-seven horizontal correspondence

The proposed endpoint is an exact equation for the existing seven roots of
the displayed degree-seven integer polynomial, in the already constructed
completed quadratic order. It is not an identification of that polynomial
with the analytic Hilbert class polynomial or an identification of the
literal Phi_2 polynomial with an arithmetic isogeny correspondence.

### Independent finite and polynomial checks

The implementation agent's generator uses SymPy algebraic-field arithmetic
to discover a quadratic common factor and clear its denominators. The
independent checker `check_horizontal71.py` does not use that field
arithmetic or SymPy. It represents bivariate polynomials by dictionaries of
integer coefficients and expands both identities exactly. The final run
reads all coefficients, root pairs, and adjacency lists directly from the
Lean source literals, so it is bound to the actual proved tables:

\[
D^2\Phi_2(X,Y)=Q(X,Y)L(X,Y)+H(X)R_\Phi(X,Y),
\]

\[
D^2H(Y)=Q(X,Y)S(X,Y)+H(X)R_H(X,Y).
\]

Both differences have identically zero integer coefficient dictionaries.
The denominator is

```
39303964708877730179484455866007199769
```

and is congruent to 405 modulo 433, with gcd one against `433^4`.
The independent checker also verifies, in the literal quadratic coordinate
ring modulo `433^4`:

| Check | Count | Result |
| --- | ---: | --- |
| Existing canonical pairs satisfy H | 7 | Pass |
| H derivative has unit norm at each pair | 7 | Pass |
| Q vanishes precisely on the supplied directed edges | All 49 ordered pairs | Pass |
| Q derivative has unit norm on every edge | 14 | Pass |
| Literal Phi_2 vanishes modulo the modulus on every edge | 14 | Pass |
| Literal Phi_2 has unit norm on every nonedge | 35 | Pass |

The canonical extracted-certificate SHA-256 is
`e031728ca59b5870709fa372dddb50d22ece75dd9d81bfe64968222f672bc8fd`.
The independent checker SHA-256 is
`470ac481b2c7cf9934ace48dda6d1f783fb10bda9c27406666dbf0ce095f362d`.
The machine-readable receipt is `horizontal71-independent-receipt.json`.
It binds the exact Lean input hashes. The reviewed completed module has
SHA-256 `05aa1224b2e7a05676f01755ef5cb7594ea2dfc32249f1177d2b0a898ffaf865`.

These are independent computation checks, not a replacement for the Lean
proof and kernel replay.

### Why a domain assumption is unnecessary

Let `C` be the existing completed quadratic order and `I` its completed
`(433^4)` ideal. Adic completeness supplies `I ⊆ Jacobson(C)`. Consequently,
an element that is a unit modulo I lifts to a unit of C. The finite norm
certificates therefore establish the units needed below. No integral-domain
claim is necessary.

For an edge `(i,j)`, take the existing actual root `a=root71 i` and use the
existing actual root `root71 j` as a Hensel seed for `Q(a,Y)`. Their proved
canonical residues transfer the numerical checks into

\[
Q(a,\operatorname{root71}(j))\in I,
\qquad Q_Y(a,\operatorname{root71}(j))\bmod I\text{ a unit}.
\]

Simple-root Hensel lifting gives b congruent to `root71 j` modulo I with
`Q(a,b)=0`. Since `H(a)=0`, the two polynomial identities and the unit `D^2`
give `H(b)=0` and `Phi_2(a,b)=0`.

To identify b with the pre-existing root, apply Taylor's formula to H at
`root71 j`. For two roots a and b congruent modulo I it gives

\[
(b-a)\bigl(H'(a)+(b-a)c\bigr)=0.
\]

The second factor is a unit because its reduction is the unit `H'(a)`.
Cancelling that unit yields `a=b`; cancellation of a potentially nonunit
element is never needed. This establishes the exact edge equation for the
specified pre-existing roots.

For a nonedge, the finite norm check makes the actual Phi_2 value a unit of
C. Nontriviality of C, already proved in `BSDHenselLift`, prevents that unit
from being zero. Thus both directions of the exact graph characterization
are justified.

The completed source's `root71_horizontal_edge`, `root71_nonedge_isUnit`,
`root71_exact_graph`, `root71_exact_cycle`, and `root71_cycle_injective`
follow this argument. The final source review found no hidden domain,
irreducibility, exhaustion, or CM-identification assumption. The cycle
statement uses cyclic addition in `Fin 7`, including the wraparound edge.

### Limits of the reviewed statement

The proof is valid for these seven simple roots. The degree-140 family has
nonunit derivatives, so the same simple-root uniqueness argument does not
automatically apply there. The certificate also does not need or prove
irreducibility of H, exhaustion of all roots, CM theory, or an arithmetic
interpretation of the graph.

## Actual rational-point independence on E389

Reviewed source SHA-256:

```
BSDRationalPoints.lean
2eacb411a16e10439e3105c5b834076115851d84b7e86bb9e487df477f78586e
```

The source hash above is recorded after the completed source review; if the
module changes, update this receipt after reviewing the relevant changes.

The source resolves `E` directly to `BSDOrdinary.curve389 ℚ`. That definition
has Weierstrass coefficients `[0,1,1,-2,0]`, hence is the intended equation

\[
y^2+y=x^3+x^2-2x.
\]

The elliptic instance proves nonzero discriminant over Q. P and Q are
Mathlib's actual `Affine.Point.mk` points with coordinates `(0,0)` and
`(1,0)`. Their membership and sum are proved using the actual curve
equation and group law.

The source handles the point at infinity before applying the duplication
formula. It uses the exact monic rational-root theorem, verified quartics
modulo eleven, and the verified cubic modulo four. It proves every integer
relation is divisible by each power of two, then uses unboundedness of those
powers to show both coefficients vanish. This is the same mathematically
sound descent strategy checked in the earlier scope audit.

The terminal declarations are:

```
relation_zero (m n : ℤ) (h : m • P + n • Q = 0) : m = 0 ∧ n = 0

pointCombination_injective :
  Function.Injective (fun c : ℤ × ℤ => c.1 • P + c.2 • Q)

points_linearIndependent : LinearIndependent ℤ ![P, Q]
```

They have no hidden rational-point-independence, Mordell–Weil finite
generation, reduction-map, Selmer, or Sha hypothesis. The only relation
hypothesis is the one whose coefficients are proved zero.

### Finrank review

The endpoint deliberately uses Z-linear independence. It does not claim
`finrank` of an arbitrary potentially infinite-dimensional object is at
least two, and does not assume finite generation of the entire rational-point
group. This avoids the misleading zero value a natural-number finrank can
have in infinite rank. Mathematically it supplies a rank lower bound and
an embedded free subgroup on two generators. It proves neither the rank
upper bound nor finiteness of a primary Sha group.

This is a source/statement audit. The parent verification process is
responsible for the compile, axiom inventory, and leanchecker receipts.
