import Exp7Lean.Arithmetic.NormBounds
import Exp7Lean.Analytic.Reduce

/-!
Bridge the unconditional norm threshold to the existing analytic prime-sum API.
These results use reciprocity and Step 1, but neither GRH nor an explicit-formula
inequality. An analytic argument can consume the equality proved here separately.
-/

namespace Exp7

/-- Every prime at or below the norm cutoff has quadratic-character value -1. -/
theorem IsExp7.legendre_eq_neg_one_of_cutoff {q X : ℕ} [Fact q.Prime]
    (hE : IsExp7 q) (hX : 4 * X ^ 7 < q) {p : ℕ} (hp : p.Prime) (hpX : p ≤ X) :
    legendreSym q p = -1 := by
  have hns := hE.no_split_le hX hp hpX
  have hXq := cutoff_lt_conductor hX
  obtain ⟨_, h4, _⟩ := hE
  exact legendreSym_eq_neg_one_of_not_splits h4 hp (by omega) hns

/-- The corresponding prime-power signs require no assumption about zeros. -/
theorem IsExp7.legendre_pow_of_cutoff {q X : ℕ} [Fact q.Prime]
    (hE : IsExp7 q) (hX : 4 * X ^ 7 < q) {p : ℕ} (hp : p.Prime) (hpX : p ≤ X)
    (k : ℕ) : legendreSym q ((p ^ k : ℕ) : ℤ) = (-1 : ℤ) ^ k := by
  rw [legendreSym_natCast_pow, hE.legendre_eq_neg_one_of_cutoff hX hp hpX]

/-- Feed the existing inert prime sum directly from the class-group hypothesis. -/
theorem IsExp7.primeSum_eq_inertSum_of_cutoff {q X : ℕ} [Fact q.Prime]
    (hE : IsExp7 q) (hX : 4 * X ^ 7 < q) (f : ℝ → ℝ) :
    primeSum q f X = inertSum f X := by
  have hns : ∀ p, p.Prime → p < X → ¬ Splits q p :=
    fun p hp hpX => hE.no_split_le hX hp hpX.le
  have hXq := cutoff_lt_conductor hX
  obtain ⟨_, h4, _⟩ := hE
  exact primeSum_eq_inertSum h4 f hXq.le hns

end Exp7
