# Primary-source review, 26 November 2026

This note records source inspection and published independent verification
reports. It does not claim that the combined exponent-seven/GRH development
has been compiled by this project.

## Direct GRH input

The compact Alpöge–Claude development is available at
<https://github.com/lsernau/grh-lean>, commit
`72fead102f663d5c7a407964a13dc0cf9d977207`, directory `grh-compact`.
Its `src/Statements.lean` imports only Mathlib and defines
`DirichletLZerosOnLine` as the assertion that, for every positive modulus,
every Dirichlet character, and every zero in the open critical strip, the
real part is `1 / 2`. Its `src/Main.lean` proves
`LFunction_eq_zero_re : DirichletLZerosOnLine` using `New.grh`.

This is stronger than `Exp7.GRHPrimeConductor` at exponent-seven commit
`d9bc0f602f364e37820fd000a5f3a320357892ec`. No primitivity proof is needed for
specialization: instantiate the modulus with the prime `q` and the character
with `Exp7.chi q`.

Independent primary verification reports for the same pinned source:

- Michael Rubinstein, Waterloo:
  <https://mrubinst.github.io/grh-lean-compact-check/>
- Andrew Sutherland, MIT:
  <https://math.mit.edu/~drew/shortgrh/>
- Alpöge's original announcement: <https://alpo.ge/remark.pdf>

The reports describe compilation, standard-axiom audits, kernel replay, and
multiple independent kernel checks. MIT reports sandboxed checks on two
machines. The source README explicitly distinguishes machine checking from
a mathematician's complete reading of the argument.

The source pins Lean `v4.35.0` and Mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679`; exponent-seven's supplied checkpoint
pins Lean `v4.37.0-rc1` and Mathlib
`31ce06eaadf4a200c0e1407c5f10953cf606b8f8`. A common-toolchain rebuild remains
necessary. Source comparison at these two exact Mathlib revisions found:

- Identical bodies for `DirichletCharacter.LFunction` and `ZMod.LFunction`.
- Byte-identical `HurwitzZeta.lean` and `HurwitzZetaOdd.lean`.
- Only two proof-lemma renames in `HurwitzZetaEven.lean`.
- Minor proof changes and two added gamma-factor lemmas in
  `DirichletContinuation.lean`, without a changed L-function definition.

These observations support the intended semantic match; they are not a
formal equivalence between two complete Mathlib environments.

## OpenAI results

- Official release:
  <https://openai.com/index/sharing-ai-progress-in-mathematics/>
- Quasi-RH formalization scope:
  <https://github.com/openai/math/blob/main/lean/docs/003.md>
- Exact Dirichlet statement:
  <https://github.com/openai/math/blob/main/lean/ComparatorChallenges/DirichletSevenEighths.lean>

The scope is a uniform zero-free half-plane `Re(s) > 7/8` for all Dirichlet
characters, with principal poles excluded. This is weaker than GRH and does
not imply the zero-rectangle hypothesis at `Re(s) <= 0.51`.

The September Millennium announcement,
<https://openai.com/index/navier-stokes-solution/>, concerns forced
finite-time singularities in the C/D versions of the Navier–Stokes problem.
It is a research precedent, not an analytic number-theory input here.

## Historical baseline and a separate unrefereed preprint

- Elsenhans–Klüners–Nicolae: <https://arxiv.org/abs/1803.02056>.
  The paper gives 33 exponent-seven fields through `3.1e20`, largest
  discriminant magnitude `118843`, and an ERH-based bound `3.9e30`.
  Its statement that unconditional finiteness for exponent seven was unknown
  is historical, not an assessment of the November 2026 proof artifacts.
- Heath-Brown (2008): <https://doi.org/10.1515/FORUM.2008.014>.
  Finiteness for exponent five, and hence exponent at most six, uses a
  square-sieve/integral-point argument.
- Bhattacharjee (11 November 2026):
  <https://www.preprints.org/manuscript/202611.1131>.
  This exists, is marked not peer-reviewed, and states explicit split-prime
  bounds conditionally on zero-free half-plane hypotheses. Its full
  quantitative proof has not been independently checked in this review.
  None of its numerical constants is needed by the direct GRH bridge.

## Consequence for this project

Prioritize a checked specialization of the pinned compact GRH theorem while
finishing row margins, SearchHigh and SearchLow. Separately verify the
global argument for `q > 10^32`: a theorem explicitly restricted to
`q <= 10^32` remains restricted after removing its GRH hypothesis.
