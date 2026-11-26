# Frontier research and integration handoff

26 November 2026. Work is isolated on `grh-import-audit`; main is not modified.
Project source pin: `be878187267cd97bf3016c21b7182968898ba242`.

## Three concrete results

### 1. An exact interface to the published compact Dirichlet-GRH proof

The public theorem `LFunction_eq_zero_re` in `lsernau/grh-lean` at
`72fead102f663d5c7a407964a13dc0cf9d977207` specializes directly to the
project's `GRHPrimeConductor`. Both use Mathlib's `DirichletCharacter.LFunction`.
The source pins, actual adapters, preparation script, build runner, and source
review are in `grh-integration/`.

The external development uses Lean 4.35 / Mathlib `56a00585`; exponent-seven
uses Lean 4.37-rc1 / Mathlib `31ce06ea`. A source-level match alone does not
establish an integrated theorem. The build gates distinguish the implication
check, import of the real GRH proof, and final classification wrapper.

At the pinned project commit, `Final4.lean` already proves both collections of
row margins. Its bounded classification still takes `GRHPrimeConductor`,
`SearchHigh`, and `SearchLow`. The proposed imported theorem removes only
the first of these after a successful common-environment build.

### 2. A route to the entire range above 10^32 using existing analytic tools

`Above.lean` still obtains a small split prime through `Published.ekn3`.
The new derivation in `chebyshev-tail/` avoids that separate published input:

* Use the existing two-cell test vector `[1,-1]` and its explicit formula.
* Bound its inert prime sum with elementary `Chebyshev.theta` and
  `Chebyshev.psi` estimates already in Mathlib.
* Use dyadic scales `X=2^n`, `n>=19`. A single rational base comparison and
  geometric induction establish the same inequality for every larger scale.
* Deduce the uniform candidate bound `q < 2^135`.
* Cover `10^32 <= q <= 2^135` with one finite row, `X=30000`, `[1,-1]`.

The full analytic derivation has two independent mathematical checks. The
finite bridge was evaluated with integer intervals and has a positive margin
at least `7.445605` with the sharper J estimate. The exact gate is
`4*30000^7 < 10^32`; the row has 3,320 prime-power terms.

This argument still uses EF and GRH. Importing the actual GRH theorem would
supply that input. It is not yet a connected Lean proof of the upper-range
exclusion: the weighted Abel-summation bounds, test-function lemmas, and finite
row must be connected to the existing formal statements. The derivation and
review enumerate these obligations explicitly. No assertion of novelty is made.

### 3. A stronger independent zero obstruction, checked without floating point

The separate research argument in `zero-audit/` shows that an exponent-seven
field with `3.9*10^30 <= |D| <= 10^162` would force a zero of its quadratic
Dirichlet L-function with `Re(s)>51/100` and `|Im(s)|<=60`, conditional on the
documented analytic derivation and numerical inequalities. No GRH assumption
enters this necessary-condition argument. It does not itself exclude a field.

The improvement from height 1000 comes from a logarithmic derivative at
`s=T+1` for the high zeros and the exact sign and variation of the smoothed
Haar kernel for the low zeros. The original and stronger computations agree
between an mpmath interval implementation and an independent integer implementation.

The latter, `zero-integer/verify.py`, uses only Python's standard library:
integer interval endpoints, exact prime sieving, explicit log/exp series,
integer square roots, Machin's pi formula, and a proved harmonic-number
enclosure for Euler's constant. Its four lower residual endpoints at height
60 are `1.040803`, `0.253506`, `23.119888`, and `75.929004`.

These are external arithmetic checks, not Lean certificates. The distinction
between a tested calculation, an audited analytic argument, a compiled helper,
and an integrated theorem is retained throughout the handoff.

## Reproduce the finite computations

From the repository root:

```bash
python frontier/zero-integer/test_verify.py
python frontier/zero-integer/verify.py
python frontier/chebyshev-tail/verify_induction.py
python frontier/chebyshev-tail/verify_bridge.py
```

The original interval pilot is retained in `zero_rectangle.py` for comparison.
The integer checker does not import or depend on that implementation.

## Remaining classification work

The two finite search statements remain separate proof obligations. The
upper-range argument above targets a different gap and does not establish
either `SearchHigh` or `SearchLow`. No new field has been found, and this
handoff does not claim that the complete unconditional classification has
been proved in Lean.
