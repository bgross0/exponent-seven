import Exp7Lean.Arithmetic.LeastSplitClass

/-! Positive controls demonstrating why the conductor cutoff and least-prime conditions matter. -/

namespace Exp7.LeastSplitExamples

/-- The smallest prime splits at the known conductor 71. -/
theorem least_two : LeastSplit 71 2 := by
  refine ⟨Nat.prime_two, ?_, fun l hl _ => hl.two_le⟩
  norm_num [Splits]

/-- Below the exclusion range there really is a seventh norm at the least split prime. -/
example : ∃ x y : ℕ, 1 ≤ y ∧ 4 * 2 ^ 7 = x ^ 2 + 71 * y ^ 2 := by
  exact ⟨21, 1, by norm_num, by norm_num⟩

/-- A larger split prime also exists, so splitness alone does not express minimality. -/
example : Splits 71 3 ∧ ¬ LeastSplit 71 3 := by
  constructor
  · norm_num [Splits]
  · intro h
    have := h.minimal 2 Nat.prime_two least_two.splits
    omega

/-- Check that the generalized local principal-power bridge really instantiates at power 1. -/
example {q p : ℕ} [Fact q.Prime] [Fact (q % 4 = 3)]
    (hp : p.Prime) (hpq : p ≠ q) {t : ℤ} (ht : (p : ℤ) ∣ t ^ 2 - t - aOf q)
    (hP : (idealI q p t).IsPrincipal) :
    ∃ x y : ℕ, 1 ≤ y ∧ 4 * p = x ^ 2 + q * y ^ 2 := by
  simpa using norm_eq_of_principal_odd_power hp hpq ht (by decide : Odd 1)
    (by simpa using hP)

end Exp7.LeastSplitExamples

#print axioms Exp7.LeastSplit.no_norm_seven
#print axioms Exp7.LeastSplit.no_norm_odd_le_seven
#print axioms Exp7.LeastSplit.nine_le_class_order_of_odd
