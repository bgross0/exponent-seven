import Exp7Lean.Step1

/-!
Exponent 7: the theorems for Mathlib's class group, with Step 1 proved.

`IsExp7 q` (defined in `Step1.lean`) says that `Monoid.exponent (ClassGroup (OK q)) = 7`, where
`OK q = ℤ[ω]`, `ω^2 = ω - (q+1)/4`, is the ring of integers of `ℚ(√-q)`.

The structures below list what is still assumed. Compared with `Inputs` and `LowInputs`, the
norm equation (Step 1) is no longer among the assumptions: it is `normEq_classGroup`.
-/

namespace Exp7

/-- What is still assumed for Theorem A: the certificate rows and the search. -/
structure Computed : Prop where
  cert : ∀ r ∈ allRows, ∀ q, q.Prime → q % 4 = 3 → r.X < q → q ≤ r.Q →
    ∃ p, p.Prime ∧ p < r.X ∧ Splits q p
  search : ∀ p, p.Prime → 701 ≤ p → p ≤ 4297 → ∀ x y q : ℕ, 1 ≤ y →
    4 * p ^ 7 = x ^ 2 + q * y ^ 2 → Qlo p ≤ q → q % 8 = 3 →
    (∀ l, l.Prime → 3 ≤ l → l < p → jacobiSym (-(q : ℤ)) l = -1) → False

/-- What is still assumed for Theorem D, in addition to `Computed`. -/
structure ComputedLow : Prop where
  certLow : ∀ r ∈ lowRows, ∀ q, q.Prime → q % 4 = 3 → r.X < q → q ≤ r.Q →
    ∃ p, p.Prime ∧ p < r.X ∧ Splits q p
  direct : ∀ q, q.Prime → q % 4 = 3 → q < B → (IsExp7 q ↔ q ∈ known)
  searchLow : ∀ p, p.Prime → 3 ≤ p → p < 2760 → ∀ x y q : ℕ, 1 ≤ y → ¬ p ∣ y →
    4 * p ^ 7 = x ^ 2 + q * y ^ 2 → QloFull p ≤ q → q < QLOW → q % 8 = 3 →
    (∀ l, l.Prime → 3 ≤ l → l < p → jacobiSym (-(q : ℤ)) l = -1) →
    q.Prime → IsExp7 q → q = 118843
  exp118843 : IsExp7 118843

theorem inputs_of_computed (C : Computed) : Inputs IsExp7 where
  normEq q hq h4 hE p hp hpq hs := by
    obtain ⟨x, y, hy, -, he⟩ := normEq_classGroup q hq h4 hE p hp hpq hs
    exact ⟨x, y, hy, he⟩
  cert := C.cert
  search := C.search

theorem lowInputs_of_computed (L : ComputedLow) : LowInputs IsExp7 where
  normEqPrim q hq h4 hE p hp hp2 hpq hs := by
    obtain ⟨x, y, hy, hprim, he⟩ := normEq_classGroup q hq h4 hE p hp hpq hs
    exact ⟨x, y, hy, hprim hp2, he⟩
  certLow := L.certLow
  direct := L.direct
  searchLow := L.searchLow
  exp118843 := L.exp118843

/-- **Theorem A** for Mathlib's class group: no prime `q ≡ 3 (mod 4)` with
`3.1·10^20 ≤ q ≤ 10^32` has `ClassGroup` of exponent 7, given the certificate rows and the search. -/
theorem theoremA_classGroup (C : Computed) {q : ℕ} (hq : q.Prime) (h4 : q % 4 = 3)
    (hlow : QLOW ≤ q) (hhi : q ≤ QTOP) : ¬ IsExp7 q :=
  theoremA (inputs_of_computed C) hq h4 hlow hhi

/-- **Theorem D** for Mathlib's class group: for a prime `q ≡ 3 (mod 4)` with `q ≤ 10^32`, the
class group of `ℚ(√-q)` has exponent 7 iff `q` is one of the 33 listed primes. -/
theorem theoremD_classGroup (C : Computed) (L : ComputedLow) {q : ℕ} (hq : q.Prime)
    (h4 : q % 4 = 3) (hhi : q ≤ QTOP) : IsExp7 q ↔ q ∈ known :=
  theoremD (inputs_of_computed C) (lowInputs_of_computed L) hq h4 hhi

end Exp7
