# Finite bridge and Haar J integration plan

Source review: 26 November 2026. This plan reads the actual verified evaluator
in `Exp7Lean/Rows/`, not the explicitly unverified `Numerics/RowPrototype`.
No upstream file was changed for this review. Root subsequently authorized
an isolated Lean build; its successful outcome is recorded in section 5.

## 1. Use the existing 64-cell evaluator for the finite bridge

The target is one `RowOK` statement with

```text
X = 30000
Q = 2^135 = 43556142965880123323311949751266331066368
v = [1,...,1,-1,...,-1]       (32 copies of each sign)
sq = 64
```

`Rows.Corr.PackOK` requires exactly 64 cells. The normalized autocorrelation
of this vector is the same Haar function used in the independent bridge
calculation. Its integer correlation numerators are

```text
cn[j] = 64-3j       for 0 <= j <= 32,
cn[j] = j-64        for 32 <= j <= 64.
pack  = sum_{j=0}^{64} (cn[j]+2^62)*(2^64)^j.
```

Generate the literal vector and pack, then let the existing `packCheck`
certify their relation. Retain the existing `jHi`/`le_jHi` calculation.
This finite-row route does not require a new theorem equating two-cell and
64-cell step functions: `rowCheck_sound` certifies the actual 64-cell vector
directly. The separate `HaarJBound.lean` lemma is for the uniform dyadic tail.

An exact integer translation of the existing routines, with only the
table/fuel extensions described below, gave:

| quantity | integer at scale `10^20` |
| --- | ---: |
| `logLo P20 30000` | 1030895266064429242735 |
| `logHi P20 30000` | 1030895266064429242751 |
| `totalLo` | 9924256547414500872107 |
| `jHi` | 37551662288337042754 |
| `logHi P20w (2^135)` | 9357486937559261677170 |
| row constant lower bound | 223059076563587229937 |
| final margin lower bound | **752277024130489382120** |

Thus the planned evaluator's margin is `7.52277024130489382120`, with
3,245 primes, 3,320 prime-power terms, and zero `cellOK` fallbacks. This is
a preflight of the integer computation, **not a Lean theorem**. It exceeds
the separate `J<=4` bridge margin because the existing 64-cell `Jplus`
calculation gives the much smaller upper bound `0.37551662288337042754`.

The complete preflight is saved in [planned_row_preflight.py](planned_row_preflight.py)
and its output in [planned-row-preflight.json](planned-row-preflight.json).
Run it with `--existing-table PATH/TO/Numerics/PrimeTable.lean` to also check
its translations against all 834 existing certified entries.

## 2. The minimal mathematical parameterization

Only three restrictions need changing. The per-term arithmetic and proofs,
including their log width 16, can stay as they are.

1. **Context.** `Rows.PrimePart.RowCtx.hX' : X <= 6400` is used only in
   `totalLo_le`, for table completeness and exponent coverage. Move these
   two obligations to the total-sum theorem. Remove this field from the
   shared context, or parameterize its bound. The cleaner small refactor is
   to remove it and pass `X <= B` and `X <= 2^(fuel+1)` to the total theorem.
   Keep the original `rowCheck`'s explicit `X <= 6400` test as its wrapper.

2. **Table.** Generalize the last fold to a literal table `T`, accompanied
   by: no repeated first components; first components exactly the primes
   below `B`; and the existing width-16 log/width-1 sqrt bounds for every
   entry. `tableSumZ_le_aux` already accepts an arbitrary table.
   `Numerics.PrimeSum.toFinset_filter_lt` already accepts an arbitrary bound.
   Define `totalLoWith T fuel ...`; retain the current `totalLo` as the
   specialization to `primeTable6400` and fuel 13. A new specialization uses
   `primeTable30000`, bound 30000, and fuel 14.

3. **Prime powers.** Apply `Rows.InertSum.inertSum_eq` with **K=15** because
   `30000 <= 2^15 = 32768`. Its exponent set is `Finset.Ico 1 15`, hence
   exponents **1 through 14 inclusive**. Call the existing `primeLo` with
   **fuel 14, initial k=1**. The current implementation uses fuel 13 and
   K=14; retaining those would omit the nonzero term at `2^14=16384`.

Add a `rowCoreWith`/`rowCheckWith` specialization, or a small isolated
`rowCore30000`/`rowCheck30000`, using the same `jHi`, constant, `P20w` log Q,
and `packCheck`. The proof of `rowCore_sound` then changes only which
total-sum lower-bound theorem it invokes. The generic J proof does not use
the context's old upper bound and needs no analytic change.

## 3. Certify the larger table without changing width-16 arithmetic

Generate `primeList30000` and `primeTable30000` as decreasing literal lists.
There are 3,245 entries. For each prime use

```text
L = logLo P20 p
S = sqrtLo20 p.
```

Certify list completeness against `primesBelow 30000`, as the existing
prime-list file does, then certify these four predicates for each entry:

```text
L = logLo P20 p
logHi P26 p <= (L+16)*10^6
S = sqrtLo20 p
sqrtHi20 p <= S+1.
```

All four checks pass in an exact integer mirror. The lower log inequality
uses `logLo_le P20_valid`, which is valid for every positive input. The
upper inequality uses existing `le_logHi P26_valid` and `hi_rescale` with
`D=10^20`, `M=10^6`; it proves the same `10^20 log p <= L+16` interface.
The sqrt bounds use the existing unconditional evaluator soundness plus
the per-entry width check. A new all-integers accuracy theorem is unnecessary.

**Do not just extend `log_sqrt_accuracy_check` to 30000 with its old test.**
For primes below 30000, `logHi P20 p - logLo P20 p` reaches 17 on 210 primes;
over all integers 2 through 30000 it reaches 18. The first prime failing
the old width-16 test is 11587. This is excess enclosure width, not proof
that `L+16` lies below the true logarithm. The P26 upper certification above
passes for every table prime; its largest `ceil(logHi P26 p/10^6)-L` is
only 13. All sqrt widths remain one. The P20/sqrt translation was also
checked against all 834 existing literal table entries, matching exactly.

No change to `P20` or `P20w` is needed: `30000 < 2^16` fits P20's exponent
search, and `2^135 < 2^256` fits P20w's search. The larger exponent increases
the Q-log enclosure width to 135 integer units, still far below the margin.
Neither parameter's soundness is range limited; these ranges concern
accuracy and efficient reduction.

## 4. Final assembly and meaningful checks

First compile the table completeness/specification, then the generalized
total-sum proof, then a single literal `rowOK_of_check`-style theorem using
`decide +kernel`. Inspect its axioms; no `native_decide` is required. The
finite row should import the real `Analytic.Reduce.rowMargin` and use
`split_prime_of_row` directly.

For `10^32 <= q <= 2^135`, its split prime satisfies `p<30000`. The exact
integer gate is

```text
4*30000^7 = 87480000000000000000000000000000 < 10^32.
```

Together with the existing norm obstruction `q <= 4*p^7`, this is a
contradiction. This supplies the finite bridge to the proposed uniform
dyadic tail. The EF/GRH inputs remain explicit until their own integration
has compiled; a positive row alone does not discharge them.

## 5. HaarJBound source review and build dependency

The proposed `Jplus_haar_le_four` proof uses the exact existing definitions:
`corr [1,-1] 1=-1/2`, `corr [1,-1] 2=0`, 16 middle subcells,
`aKer(u)*u<=1`, and the existing tail expression. Its tail argument works
already for `L>=1`. The bound actually obtained is `3/2+3/2+4/5=19/5<4`.
I found no mathematical sign, endpoint, or normalization error in the file.

All named source lemmas and their argument orders were checked. The concrete
`corr` simplification and final `simpa only` were reviewed as potential
elaboration-sensitive sites; both compiled successfully without any edit.
The proof has no `sorry`.

Its local import closure, in dependency order, is exactly:

```text
Basic, Main, Above, Low, Step1, Final,
Analytic.Statement, Analytic.Autocorr, Analytic.JBound.
```

`Exp7GRHBridge.Smoke` imports `Statements` and
`Exp7Lean.Analytic.Statement`. It therefore covers the first seven project
modules, but **does not build Autocorr, JBound, or HaarJBound**. Once root
authorized a further single-threaded job, the dependency chain built
successfully: Autocorr 47s, JBound 47s, HaarJBound 45s. Both new lemmas have
exactly `[propext, Classical.choice, Quot.sound]`. No source modification was
needed. The checked environment is Lean 4.35.0 with Mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679`. Exact source hashes and command are
in [haar-build-receipt.json](haar-build-receipt.json); full output is in
[haar-build.log](haar-build.log). The original creation-time comment in the
Lean file was retained to preserve exact compiled source bytes.

No external GRH proof module, prime table, row evaluator, or class-group
computation is needed for this local lemma's dependency closure. This
successful build does not yet certify the finite 30000 row or the complete
Chebyshev analytic tail.
