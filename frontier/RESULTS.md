# Frontier research and integration handoff

26 November 2026. The Precision 7670 built handoff commit
`248889f68a9a399ac1c4a011f89af1c4aa87ecd3` on `grh-worker-precision7670`.
Project source pin: `be878187267cd97bf3016c21b7182968898ba242`.

## Four concrete results

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

The Precision compiled the smoke adapter, the complete external `Main`, and
`Exp7GRHBridge.Imported` in the same pinned Lean 4.35 environment. A fresh
Lean invocation checked both declarations and printed their axioms.
[Exact Lean output](grh-integration/precision7670/imported-declarations.log)

```text
LFunction_eq_zero_re : DirichletLZerosOnLine
'LFunction_eq_zero_re' depends on axioms: [propext, Classical.choice, Quot.sound]
Exp7.GRHIntegration.primeConductor : Exp7.GRHPrimeConductor
'Exp7.GRHIntegration.primeConductor' depends on axioms: [propext, Classical.choice, Quot.sound]
```

| Gate | Exit | Elapsed |
|---|---:|---:|
| [Smoke](grh-integration/precision7670/smoke.json) | 0 | 46.154 s |
| [External](grh-integration/precision7670/external.json) | 0 | 3,546.752 s |
| [Imported](grh-integration/precision7670/imported.json) | 0 | 10.365 s |
| [Classification](grh-integration/precision7670/final.json) | 1 | 146.032 s |

The first bounded-classification build failed in four prerequisite modules.
The first error was `Real.exp_natCast_mul` at `Digamma.lean:493`. A separate
Lean check confirmed that `Real.exp_nat_mul` supplies that rewrite in 4.35.
The remaining errors include changed circle-average and scalar-multiplication
signatures and a missing `MeromorphicOn.log_norm_meromorphicTrailingCoeffAt`.
The wrapper retains `SearchHigh`, `SearchLow`, and the bound `q ≤ QTOP`.
[Final build log](grh-integration/precision7670/final.log) ·
[API check](grh-integration/precision7670/final-api-check.log) ·
[Machine, source pins, and timings](grh-integration/precision7670/precision7670-summary.json)

#### Bounded classification after the 4.35 backport

The repair on `grh-final435-precision7670` compiles `Exp7GRHBridge.Final`.
Theorem D takes `SearchHigh` and `SearchLow`. For a prime `q` with
`q % 4 = 3` and `q ≤ QTOP`, it yields `IsExp7 q ↔ q ∈ known`.
Theorem A takes `SearchHigh` and excludes `IsExp7 q` in the range
`QLOW ≤ q ≤ QTOP` under the same prime and congruence conditions.
Here `QTOP = 10^32`. Lean reports exactly `propext`, `Classical.choice`, and
`Quot.sound` for both theorems. The two finite search proofs remain open.
[Lean signatures and axioms](grh-integration/precision7670/classification435/declarations.log) ·
[Final gate receipt](grh-integration/precision7670/classification435/final.json)

The backport proves the centred Poisson–Jensen identity using the pinned
Mathlib’s canonical decomposition, including the contribution of boundary zeros.
It proves the two needed Dirichlet-character nonvanishing lemmas from the existing
functional equation and L-function nonvanishing. Six existing proof files have
API adjustments. The final bridge, search propositions, numerical inputs, and
pinned dependencies match the first build byte for byte.
[Proof files, caller patch, and hashes](grh-integration/compat435/final)

#### Certificate build on the updated project pin

The Precision's next build uses exponent-seven `aae4b20` with the same Lean 4.35
and external GRH pins. All four pilot certificates compiled and a fresh Lean
process imported them. The printed axioms for main primes 701 and 2767 and
low-range primes 11 and 1009 were exactly `propext`, `Classical.choice`, and
`Quot.sound`. The low-range generator also checked the pinned C survivor list.
[Lean pilot output](grh-integration/precision7670/certificates435/pilots-import.log) ·
[Pilot timings and peak RSS](grh-integration/precision7670/certificates435/pilots.json)

The main sieve bridge and assembly, the low-range sieve modules, and
`Fundamental.lean` compiled on 4.35. The genus reduction uses an additional
integral-closure proof for even fundamental discriminants. The two conditional
fundamental statements retain their upstream definitions and hypotheses.
[Fundamental build](grh-integration/precision7670/certificates435/03-fundamental.log) ·
[Re-pinned GRH import](grh-integration/precision7670/certificates435/imported.log)

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
at least `7.445605` with the sharper J estimate, and at least `3.898286` with
the simpler bound `J<=4`. The exact gate is
`4*30000^7 < 10^32`; the row has 3,320 prime-power terms.

The complete arithmetic comparison is now kernel-checked in Lean 4.35:
`ChebyshevTailArithmetic.haarLowerBound_gt` proves it for every `n>=19`,
using actual `log 2` and real roots, with no numerical assumptions.
`exists_dyadic_index_of_mod_four` supplies the needed dyadic scale for every
`q>=2^135` with `q%4=3`. Both print only `propext`, `Classical.choice`, and
`Quot.sound`. The source hash, successful command, and complete output are
in `chebyshev-tail/arithmetic-lean-receipt.json`.

The companion lemmas `Jplus_haar_le_four` and `Jterm_haar_le_four` have now
also compiled, against unchanged `Autocorr` and `JBound`, with only the
standard axioms. See `chebyshev-tail/haar-build-receipt.json`.
The remaining central analytic work is the lower bound for the actual inert
prime sum, using the three weighted Abel-summation estimates.

The finite row also has an exact preflight using the existing 64-cell evaluator:
32 entries +1 followed by 32 entries -1. Extending the prime table to 30000
and its power loop gives a margin above `7.5227702413`. The required 3245
prime-table entries can retain the existing width-16 log bounds by verifying
them with the already available higher-precision P26 routine. This preflight
is not yet a Lean certificate; the minimal changes are documented in
`chebyshev-tail/IMPLEMENTATION_PLAN.md`.

This argument still uses EF and GRH. The imported theorem supplies the
project’s GRH input in the pinned 4.35 environment. The upper-range exclusion
still requires the weighted Abel-summation bounds, test-function lemmas, and
finite row to be connected to the existing formal statements. The derivation and
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

### 4. Kernel-checked fourfold compression of root representatives

`root-period/RootPeriod.lean` proves that the original predicate
`x^2+3*y^2 == 4*p^7 (mod 8*y^2)` has period `2*y^2`, using the parity forced
by that same predicate. It compiled with only the standard axioms. This
shortens the representative range by four while retaining the original
congruence modulus. The resulting progressions are longer, so this is a
proved reduction in root enumeration, not a claimed fourfold runtime gain.
The generator integration is still separate.

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

## Ready worker for Kubuntu and other Linux CPU nodes

`grh-integration/worker.py` installs a SHA-256-verified official Lean release
inside a dedicated work directory, checks out both exact source pins, applies
the proved compatibility patch, obtains the matching Mathlib cache, and runs
the smoke, external, and imported build gates. It preserves logs and reuses
completed modules on restart. It chooses conservative thread counts from
available RAM and CPU count, locks its work directory, and verifies a manifest
of every prepared Lean source and Lake configuration file.

`COMPUTE_HANDOFF.md` gives the Precision 7670/Kubuntu commands and exact
acceptance criteria. The separate public CI workflow uses the same worker.

## Remaining classification work

The two finite search statements remain separate proof obligations. The
upper-range argument above targets a different gap and does not establish
either `SearchHigh` or `SearchLow`. No new field has been found, and this
handoff does not claim that the complete unconditional classification has
been proved in Lean.
