import Exp7Lean.Witness.Assemble
import Exp7Lean.ClassGroup.Results
import Exp7Lean.Analytic.Reduce

/-!
Exponent 7: what is still assumed, after the class-group computations are proved.

Compared with `Final.lean`:
* the class groups below `10^5` and of `ℚ(√-118843)` are proved (`ClassGroup/Results.lean`,
  `Witness/Direct.lean`);
* the classification of the survivors of the low-range search is proved
  (`Witness/Survivors.lean`), so the search only has to be complete: every solution it should find
  is in the list `survivorQs`;
* the certificate rows are derived from the explicit formula, GRH, and numerical row margins
  (`Analytic/Reduce.lean`).
-/

namespace Exp7

theorem known_prime : ∀ q ∈ known, q.Prime ∧ q % 4 = 3 := by
  unfold known
  simp only [List.forall_mem_cons]
  norm_num

theorem classNumberOne_prime : ∀ q ∈ [3, 7, 11, 19, 43, 67, 163], q.Prime ∧ q % 4 = 3 := by
  simp only [List.forall_mem_cons]
  norm_num

theorem isExp7_of_known_all : ∀ q ∈ known, IsExp7 q := fun q hk =>
  isExp7_of_mem_known q hk (known_prime q hk).1 (known_prime q hk).2

theorem not_isExp7_classNumberOne_all : ∀ q ∈ [3, 7, 11, 19, 43, 67, 163], ¬ IsExp7 q :=
  fun q hq1 => not_isExp7_of_mem_classNumberOne q hq1 (classNumberOne_prime q hq1).1
    (classNumberOne_prime q hq1).2

/-- The row margins: each certificate row has a kernel vector with positive margin. -/
def RowMargins (rows : List Row) : Prop :=
  ∀ r ∈ rows, 2 ≤ r.X ∧ ∃ v : List ℝ, (∃ t ∈ v, t ≠ 0) ∧ 0 < rowMargin r.Q r.X v

/-- Completeness of the main search: no solution for the 465 primes `701 ≤ p ≤ 4297`. -/
def SearchHigh : Prop :=
  ∀ p, p.Prime → 701 ≤ p → p ≤ 4297 → ∀ x y q : ℕ, 1 ≤ y →
    4 * p ^ 7 = x ^ 2 + q * y ^ 2 → Qlo p ≤ q → q % 8 = 3 →
    (∀ l, l.Prime → 3 ≤ l → l < p → jacobiSym (-(q : ℤ)) l = -1) → False

/-- Completeness of the low-range search: every solution for `3 ≤ p < 2760` has `q` in the list of
6608 survivors. -/
def SearchLow : Prop :=
  ∀ p, p.Prime → 3 ≤ p → p < 2760 → ∀ x y q : ℕ, 1 ≤ y → ¬ p ∣ y →
    4 * p ^ 7 = x ^ 2 + q * y ^ 2 → QloFull p ≤ q → q < QLOW → q % 8 = 3 →
    (∀ l, l.Prime → 3 ≤ l → l < p → jacobiSym (-(q : ℤ)) l = -1) → q.Prime →
    q ∈ survivorQs

/-- **Theorem A**, for Mathlib's class group, from: the explicit formula, GRH for the characters of
prime conductor, the numerical margins of the 51 rows, and completeness of the main search. -/
theorem theoremA_final (hEF : ExplicitFormulaBound) (hGRH : GRHPrimeConductor)
    (hM : RowMargins allRows) (hS : SearchHigh) {q : ℕ} (hq : q.Prime) (h4 : q % 4 = 3)
    (hlow : QLOW ≤ q) (hhi : q ≤ QTOP) : ¬ IsExp7 q :=
  theoremA_classGroup ⟨cert_of_margins hEF hGRH allRows hM, hS⟩ hq h4 hlow hhi

/-- **Theorem D**, for Mathlib's class group, from: the explicit formula, GRH, the numerical margins
of all 175 rows, and completeness of the two searches. -/
theorem theoremD_final (hEF : ExplicitFormulaBound) (hGRH : GRHPrimeConductor)
    (hM : RowMargins allRows) (hML : RowMargins lowRows) (hS : SearchHigh) (hSL : SearchLow)
    {q : ℕ} (hq : q.Prime) (h4 : q % 4 = 3) (hhi : q ≤ QTOP) : IsExp7 q ↔ q ∈ known :=
  theoremD_classGroup ⟨cert_of_margins hEF hGRH allRows hM, hS⟩
    (computedLow_of_tables (cert_of_margins hEF hGRH lowRows hML) isExp7_of_known_all
      not_isExp7_classNumberOne_all hSL) hq h4 hhi

end Exp7
