# Lean formalization (partial)

A Lean 4 / Mathlib formalization of the argument, with the inputs it does not formalize stated as explicit hypotheses.

## What is proved

`Exp7.classification` (in `Exp7Lean/Above.lean`):

```lean
theorem classification {IsExp7 : ℕ → Prop} (H : Inputs IsExp7) (P : Published IsExp7) {q : ℕ}
    (hq : q.Prime) (h4 : q % 4 = 3) : IsExp7 q ↔ q ∈ known
```

That is: given the inputs below, a prime `q ≡ 3 (mod 4)` has class group of exponent 7 if and only if it is one of the 33 listed primes.

`Exp7.theoremD` (in `Exp7Lean/Low.lean`) proves the same equivalence for every `q ≤ 10^32` without assuming any published table:

```lean
theorem theoremD {IsExp7 : ℕ → Prop} (H : Inputs IsExp7) (L : LowInputs IsExp7) {q : ℕ}
    (hq : q.Prime) (h4 : q % 4 = 3) (hhi : q ≤ QTOP) : IsExp7 q ↔ q ∈ known
```

On the way the development proves:

- `Exp7.theoremA` (`Main.lean`): Theorem A, no exponent-7 `q` with `3.1·10^20 ≤ q ≤ 10^32`.
- `Exp7.above_bound` (`Above.lean`): `4 (1.881 log D + 6.18)^14 < D` for every real `D ≥ 10^32`, proved from Mathlib's bounds on `e` and `log 2`.
- `Exp7.not_exp7_above`: no exponent-7 `q ≥ 10^32`.

Lean checks all of the following:
- every step that connects the inputs
- the bootstrap chain from `10^32` down to `4·4297^7`, including the prime gaps it uses
- that every prime `≤ 691` is inert, and that `q ≡ 3 (mod 8)`
- the existence of the least split prime and its range `701 ≤ p ≤ 4297`
- the Jacobi-symbol conditions
- the ladder lower bounds `Qlo p`
- all the exact arithmetic

`#print axioms` shows only Lean's standard axioms, `propext`, `Classical.choice` and `Quot.sound`. The source contains no `sorry`, no `native_decide` and no added axioms.

## What is assumed (not formalized)

These are the fields of `Inputs` and `Published`. Each is a precise statement of what the note establishes outside Lean, or imports from the literature.

| Field | Statement | Established by |
|---|---|---|
| `Inputs.normEq` | exponent 7 and `p` split ⇒ `4p^7 = x² + qy²` with `y ≥ 1` | Step 1 (algebraic number theory of `ℚ(√-q)`) |
| `Inputs.cert` | each of the 51 certificate rows `⟨Q, X⟩` forces a split prime below `X` | Steps 2–3: explicit formula under GRH; rows verified by `kernel_verify.py` and `independent/verify_fixedpoint.cjs` |
| `Inputs.search` | no survivor for the 465 primes `701 ≤ p ≤ 4297` | Step 4: three independent search programs |
| `Published.ekn3` | under ERH, a split prime `p ≤ (1.881 log q + 6.18)^2` exists for `q > e^25` | Elsenhans–Klüners–Nicolae, Theorem 3 (from Bach–Sorenson) |
| `Published.ekn1` | the exponent-7 list below `3.1·10^20` | Elsenhans–Klüners–Nicolae, Theorem 1 and Table 1 (used by `classification` only) |
| `LowInputs.normEqPrim` | as `normEq`, with `p ∤ y` | Step 1 and the primitivity remark |
| `LowInputs.certLow` | each of the 124 extra rows forces a split prime below `X` | explicit formula under GRH; rows verified by both verifiers |
| `LowInputs.direct` | the exponent-7 list below `10^5` | `lowrange/direct.py` |
| `LowInputs.searchLow` | for `3 ≤ p < 2760` and `q < 3.1·10^20`, the only prime survivor with exponent 7 is `118843` | `lowrange/lowsearch.c` and `lowrange/classify.py` |
| `LowInputs.exp118843` | `ℚ(√-118843)` has exponent 7 | class group computation |

`Splits q p` is defined by the Dedekind–Kummer criterion: `2` splits iff `q ≡ 7 (mod 8)`, and an odd `p` splits iff the Jacobi symbol `(-q/p)` is 1. `IsExp7` is a parameter, so the theorem holds for any predicate that satisfies the inputs. Connecting it to Mathlib's `ClassGroup` is part of formalizing `normEq`. The reduction from fundamental discriminants `D` to primes `q` (Step 0, genus theory) is also not formalized.

The certificate rows in `Basic.lean` and `Low.lean` are generated from `../certificate.json` and `../lowrange/certificate_full.json`. As a check that the search hypotheses state exactly what was computed, `Qlo p` evaluated in Lean equals the lower bound in the production logs for all 465 primes, and `QloFull p` equals the lower bound in `lowrange/low_run.log` for all 401 primes.

## Build

    curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh
    cd Exp7Lean
    lake exe cache get      # prebuilt Mathlib
    lake build

The toolchain is Lean `v4.37.0-rc1` with the matching Mathlib.

## Next steps toward a full formalization

1. `cert`: the explicit formula for `L(s, χ)` is not in Mathlib. That is the main gap.
2. `normEq` and Step 0: class groups of `ℚ(√-q)` and genus theory, using Mathlib's `NumberField` and `ClassGroup`.
3. `search`: about 10^15 candidates are beyond direct kernel checking. A verified sieve with a small checkable certificate would be needed.
