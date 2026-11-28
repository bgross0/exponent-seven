# Reusing the exponent-seven arithmetic for the original BSD pilot

Source snapshot: `72e9f63708fbe3b48342de296a60979e32bb8c31`.
This is a source audit and proposed proof route, not an additional compiled
Lean result in the 320-theorem package.

## Existing actual arithmetic

The exponent-seven project uses the actual Mathlib ideal class group of
`Exp7.OK q`, the quadratic order with `omega²=omega-(q+1)/4`. Its Dedekind
instance is proved using the fundamental-discriminant integral-closure
theorem. Relevant existing declarations are:

| Declaration | Existing result |
| --- | --- |
| `Exp7.isExp7_of_mem_known` | Exponent seven for the actual class group of each listed field, including q=71; no remaining generation hypothesis |
| `Exp7.genBound_sqrt_div_three` | Generation by the split primes of norm at most floor(sqrt(q/3)); for q=71 only primes 2 and 3 occur |
| `Exp7.classOf_ne_one` | The norm-two class is nontrivial because 8<71 |
| `Exp7.idealI_mul`, `Exp7.classOf_mul` | Explicit ideal and ideal-class multiplication identities |
| `Exp7.idealI_norm`, `Exp7.classOf_eq_one` | Principal ideal/class relations from the norm of omega minus an integer |
| `Exp7.idealI_shift`, `Exp7.classOf_congr` | Reduction of ideal generators to residue representatives |
| `Exp7.idealI_mul_map`, `Exp7.map_star_idealI` | Conjugate split ideal classes have principal product |
| `Exp7.idealI_pow_eq_span` | Exact principal-generator certificate for a prime-ideal power |

See the repository's `Exp7Lean/Exp7Lean/Step1.lean` and
`Exp7Lean/Exp7Lean/ClassGroup/{Defs,Converse,Criterion,GenBoundProof,KnownData,Results}.lean`.

## Proposed short theorem: actual class number seven and norm-two generator

Exponent seven alone does not imply class number seven. The sharp generation
bound and explicit principal relation supply a route to the stronger result.
Set

\[
g=[(2,\omega)],\qquad h=[(3,\omega)].
\]

The norm identity `Norm(omega)=18` should give `g*h²=1` using the existing
ideal identities. Together with the proved exponent-seven result this gives
`h=g³`. The other split roots modulo 2 and 3 give the conjugate, hence inverse,
classes. The generation bound then implies `Subgroup.zpowers g=⊤`.
Nontriviality of g and `g⁷=1` give order exactly seven.

The resulting new endpoints should be actual `orderOf g=7`, cyclic generation,
and `Nat.card (ClassGroup (OK 71))=7` or an explicit cyclic-group equivalence.
These endpoints were not found as named theorems in the inspected source and
have not been added as unproved placeholders here.

## Explicit input for a coherent ring-class generator

The existing principal-power lemma can be specialized at
`q=71, l=2, t=0, n=7, u=10, y=1` to obtain

\[
(2,\omega)^7=(10+\omega),
\qquad\operatorname{Norm}(10+\omega)=128.
\]

At five, the two roots of `X²-X+18` modulo 25 are 12 and 14. With the first
choice, the local ratio is

\[
\frac{10+\omega}{10+\bar\omega}\equiv\frac{22}{24}\equiv3\pmod{25}.
\]

The residue 3 has order four modulo 5, and `3⁴-1≡5 (mod25)`. After proving
the needed local-unit and conductor exact-sequence statements, this is a
compact route to norm-two generation of the ring-class groups of
`Z+5^m OK`, with order `28*5^(m-1)` for m≥1. It matches the conductor25
size 140 used by the finite theta computation.

The proposed route still needs the actual Picard groups of proper invertible
ideals in the nonmaximal orders, their exact sequence, compatible transition
maps, and the action on actual CM points. Nonmaximal orders are not Dedekind;
their ring-class groups cannot be replaced by `ClassGroup (OK 71)`.

## Toolchain integration is explicit work

| Project | Lean | Mathlib |
| --- | --- | --- |
| `Exp7Lean` |4.37.0-rc1|`31ce06eaadf4a200c0e1407c5f10953cf606b8f8`|
| `research/bsd-formal` |4.36.0|`fc4f59e577feb1a4956671bc04ac18aaaf8cd842`|

Reusing these results requires a source port and rebuild under a shared
pin, or a separately verified development with a proved model bridge.
Compiled objects from the two toolchains cannot simply be mixed.
