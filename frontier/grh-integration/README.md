# Importing the compact Dirichlet-GRH proof into exponent-seven

The Precision 7670 compiled `Main` and `Exp7GRHBridge.Imported` on 26 November
2026. Lean reported exactly `propext`, `Classical.choice`, and `Quot.sound`
for both `LFunction_eq_zero_re` and `Exp7.GRHIntegration.primeConductor`.
The separate bounded-classification gate also compiles on
`grh-final435-precision7670` with the compatibility proofs in `compat435/final`.
Both wrapper theorems have the same three axioms. Theorem D retains
`SearchHigh`, `SearchLow`, primality, the congruence, and `q ≤ QTOP`.
[Classification declarations](precision7670/classification435/declarations.log) ·
[Final build receipt](precision7670/classification435/final.json) ·
[Original build and failure diagnosis](precision7670/precision7670-summary.json)

The isolated 4.35 trial exposed a real dependency added after Mathlib 4.35: the integral-closure theorem for quadratic orders. `compat435/QuadraticIntegralClosure.lean` now proves the squarefree-discriminant case needed by Step1, using trace/norm integrality and rational denominators. This standalone proof compiled successfully in Lean 4.35 with exactly `propext`, `Classical.choice`, and `Quot.sound`. The patched project dependency chain and smoke adapter then compiled successfully as well: Lake reported 9,055 jobs, exit status 0. The adapter's axioms are exactly the same three standard axioms. Its conclusion is still an implication taking `DirichletLZerosOnLine` as an input. See `compat435/smoke-verification.json` and the complete `smoke-build.log`; they do not establish the full external-proof import.

## What the exact statements establish

At the pinned external commit, `grh-compact/src/Statements.lean` imports only Mathlib and defines:

```lean
def DirichletLZerosOnLine : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
    0 < s.re → s.re < 1 →
      DirichletCharacter.LFunction χ s = 0 → s.re = 1 / 2
```

Its `src/Main.lean` imports `New.Main` and proves:

```lean
theorem LFunction_eq_zero_re : DirichletLZerosOnLine :=
  New.zeros_on_line New.grh
```

This statement covers every Dirichlet character of every nonzero natural modulus. Specializing to the project's quadratic character `Exp7.chi q` proves precisely `Exp7.GRHFor q`. A prime `q` supplies `NeZero q`; neither character primitivity nor a further analytic identification is needed in the adapter because both projects use Mathlib's `DirichletCharacter.LFunction`.

A correct adapter is small. Its dependency graph is not: the external theorem's full proof must be checked in the same environment as the project's definitions. Building two incompatible packages separately, copying theorem text, or declaring the desired statement as an axiom does not establish the combined result.

## Source pins and compatibility

| Component | Pinned source | Lean | Mathlib |
|---|---|---|---|
| exponent-seven | `aae4b2012f80bcb5cbe7b30c13debf0704f07266` | `v4.37.0-rc1` | `31ce06eaadf4a200c0e1407c5f10953cf606b8f8` |
| compact GRH | `72fead102f663d5c7a407964a13dc0cf9d977207` | `v4.35.0` | `56a005855ea17e0b0958f73ec801ae140b0a1679` |

The compact source is an Apache-2.0 research artifact. Preserve its LICENSE, NOTICE, and ATTRIBUTION.md when copying it. It is not advertised as a maintained package. Its README reports machine verification and explicitly says no mathematician has read the full proof.

The GRH proof's `Lib/General/LinearAlgebra/Base.lean` changes instance priorities, introduces classical decidability instances, and changes the simp set. These changes are not additional axioms, but they matter when elaborating new files that import the proof. Keep the external import confined to the bridge; do not add it to the beginning of every existing project file. Module names `Main`, `Statements`, `Lib.*`, and `New.*` are global and could collide with other dependencies. The project currently uses the distinct `Exp7Lean.*` module prefix.

## Three separate build gates

1. **Smoke.lean** imports the external statement and the project's actual `Analytic/Statement.lean`. It proves only the implication `DirichletLZerosOnLine → GRHPrimeConductor`. Success checks the interface and part of source compatibility. It does **not** remove an assumption.
2. **Imported.lean** imports the actual external `Main` and applies `LFunction_eq_zero_re`. Success gives `Exp7.GRHIntegration.primeConductor : Exp7.GRHPrimeConductor` in the common environment.
3. **Final.lean** imports the two certified searches and `Fundamental`. It applies the search proofs and the imported GRH theorem to A and D for prime conductors and negative fundamental discriminants up to `10^32`.

Each file prints the relevant axioms. The allowed list is a subset of `propext`, `Classical.choice`, and `Quot.sound`; inspect actual output, including any unexpected `sorryAx` or evaluator axiom. A build log is required before changing the prepared status.

## Isolated build workspace

`prepare.py` consumes two clean git checkouts at the exact commits above and a nonexistent output path. It refuses wrong commits, dirty inputs, existing output, and output inside an input checkout.

Example, from a checkout containing this handoff:

```bash
python frontier/grh-integration/prepare.py \
  --exponent-seven /absolute/path/to/pinned-exponent-seven \
  --grh /absolute/path/to/pinned-grh-lean \
  --output /absolute/path/to/exp7-grh-435 \
  --environment external435
```

It copies the compact project as the root Lake project, copies the project's source library to `src/Exp7Lean`, and adds `src/Exp7GRHBridge`. In particular, `Analytic/Statement.lean`, `Final4.lean`, and the external `Statements.lean` and `Main.lean` are copied byte for byte, with SHA-256 receipts. It never changes the two input checkouts.

For `external435`, preparation then applies the explicit, hash-guarded `compat435/Step1.patch` by default. It embeds the proved squarefree-discriminant integral-closure helpers and replaces the newer natural-number multiplicity aliases with existing generic finite-multiplicity theorems. All existing project definitions and theorem statements are preserved. The source and result hashes must match the recorded receipt. Use `--no-compat435` to reproduce the unpatched compatibility failure; `project437` never applies this backport. A fresh-workspace reproduction check confirmed that the preparation script produces exactly the patched Step1 bytes used by the trial build.

The same preparation now applies the classification caller patch and copies the
three proof modules from `compat435/final`. It checks the before and after hashes
for all ten affected paths. The genus-theory backport covers the even fundamental discriminants. To reproduce all gates on this branch, run the
worker in its own dedicated build directory.

```bash
python3 frontier/grh-integration/worker.py \
  --work-root "$HOME/exp7-grh-certificates-worker" \
  --certificate-jobs 4 --stages smoke external imported final
```

The added `Exp7Lean` library restores its original Lean options locally, including the default `autoImplicit = true`, rather than inheriting the compact project's `autoImplicit = false`. The compact project's larger heartbeat and stack limits remain resource settings for the isolated build. Lake appends library Lean options after package options, so these local overrides take effect.

The default `external435` route preserves the independently checked external proof's Lean/Mathlib pins and attempts to backport the smaller exponent-seven codebase. Any necessary proof-API edits must be explicit in the isolated integration worktree, followed by a full rebuild and fresh receipts. Preserve theorem statements. The alternate `project437` route retains exponent-seven's environment and ports the compact proof; it changes the copied root's Mathlib pin, changes the toolchain, and discards the old manifest before dependency resolution.

The certificate stage needs Python with SymPy and GNU time. The Precision
runs four single-threaded Lean checks at once. The worker runs the pinned
`run_all.sh` and `run_low.sh`, preserves a raw Lean log per prime, and
checks coverage against all 465 main and 401 low-range primes. Each acceptance
requires the compiled object, the runner's successful timing record, and the
exact axiom line. Direct per-prime Lean invocations use the compact project's
`maxHeartbeats = 4000000` setting. The low-range generator also checks the
pinned C survivor list.

The generators write their sources under `combined/Exp7Lean`. The two
`All.lean` modules import the per-prime objects in the shared Lake environment.
The final gate compiles `src/Exp7GRHBridge/Final.lean` against those objects,
then starts a fresh Lean process to import the result, print the declarations,
and check their axioms. Repeating the worker command reuses completed primes.
The worker records its logs, coverage manifests, object hashes, and final
declaration check under `combined/integration-receipts/`.

## What current main already proves, and what is still missing

At the pinned exponent-seven commit, `Final4.lean` imports `Rows.Margins` and calls `rowMargins_allRows` and `rowMargins_lowRows`. The old final statement listing row margins as open inputs is therefore stale. Its current bounded classification is:

```lean
theorem theoremD_rows
    (hGRH : GRHPrimeConductor)
    (hS : SearchHigh) (hSL : SearchLow)
    {q : ℕ} (hq : q.Prime) (h4 : q % 4 = 3) (hhi : q ≤ QTOP) :
    IsExp7 q ↔ q ∈ known
```

After the actual GRH import is compiled, only `SearchHigh` and `SearchLow` remain as named computational hypotheses **in this bounded theorem**. They are not automatically proved by GRH. The conclusion still applies only to prime `q ≡ 3 mod 4` with `q ≤ 10^32`.

The unbounded classification has an additional formal gap. `Above.lean` proves the numerical inequality
`4 * (1.881 * log D + 6.18)^14 < D` for `D ≥ 10^32`. Its exclusion theorem still obtains a sufficiently small split prime from the field `Published.ekn3`. That field is a precise imported *hypothesis*, not a theorem established from `GRHPrimeConductor` in the inspected code:

```lean
∀ q : ℕ, q.Prime → q % 4 = 3 → Real.exp 25 < (q : ℝ) →
  ∃ p : ℕ, p.Prime ∧ Splits q p ∧
    (p : ℝ) ≤ (1881 / 1000 * Real.log q + 309 / 50)^2
```

The source cites Elsenhans–Klüners–Nicolae Theorem 3 / Bach–Sorenson. Even after a successful GRH import, this explicit split-prime theorem needs its own formal proof or a different proved upper-bound argument. Filling that gap is distinct from adapting the zero-on-line statement. The `Published` structure also contains the old low-range classification input, which can eventually be replaced by the project's new low-range proof once the searches are discharged.

At this project pin, `Fundamental.lean` supplies the genus-theory reduction for negative fundamental discriminants. Its bounded classification uses the same GRH and search inputs as `Final4.lean`. The bridge applies those inputs to both formulations.

## Primary sources inspected

- [Pinned project statement](https://github.com/bgross0/exponent-seven/blob/aae4b2012f80bcb5cbe7b30c13debf0704f07266/Exp7Lean/Exp7Lean/Analytic/Statement.lean)
- [Pinned Final4](https://github.com/bgross0/exponent-seven/blob/aae4b2012f80bcb5cbe7b30c13debf0704f07266/Exp7Lean/Exp7Lean/Final4.lean)
- [Pinned Above](https://github.com/bgross0/exponent-seven/blob/aae4b2012f80bcb5cbe7b30c13debf0704f07266/Exp7Lean/Exp7Lean/Above.lean)
- [Pinned external statement](https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Statements.lean)
- [Pinned external Main](https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Main.lean)
- [Pinned external README](https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md)
- [Waterloo compact verification report](https://mrubinst.github.io/grh-lean-compact-check/)
- [MIT independent verification report](https://math.mit.edu/~drew/shortgrh/)

