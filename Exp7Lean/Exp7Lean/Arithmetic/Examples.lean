import Exp7Lean.Arithmetic.TwoSplitPrimes
import Exp7Lean.Arithmetic.InertThreshold

/-! Small exact examples and boundary checks for the arithmetic lemma chain. -/

namespace Exp7.ArithmeticExamples

/-- These are actual norm witnesses over the known conductor 71. -/
theorem witness_two : NormWitness 71 2 21 1 := by
  constructor <;> norm_num

theorem witness_three : NormWitness 71 3 92 2 := by
  constructor <;> norm_num

example : (92 : ℕ) * 1 ≠ 21 * 2 :=
  witness_three.cross_products_ne witness_two (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

example : (2074 : ℤ) ^ 2 + 71 * 50 ^ 2 = 16 * 6 ^ 7 := by
  convert witness_three.composition_identity witness_two using 1 <;> norm_num

/-- At equality in the first-slice bound, `y = 2` is possible. -/
theorem boundary_witness : NormWitness 128 2 0 2 := by
  constructor <;> norm_num

example : 4 * 2 ^ 7 = 4 * 128 ∧ (2 : ℕ) ≠ 1 := by norm_num

/-- Above this bound the second slice disappears, including for composite candidate q. -/
example {x y : ℕ} (h : NormWitness 509 2 x y) : y = 1 :=
  h.y_eq_one (by norm_num)

end Exp7.ArithmeticExamples

#print axioms Exp7.IsExp7.exists_normWitness
#print axioms Exp7.NormWitness.y_eq_one
#print axioms Exp7.NormWitness.not_dvd_x
#print axioms Exp7.NormWitness.determinant_ne_zero
#print axioms Exp7.NormWitness.composition_identity
#print axioms Exp7.IsExp7.exists_paired_normWitness
#print axioms Exp7.not_isExp7_of_no_paired_normWitness
#print axioms Exp7.IsExp7.primeSum_eq_inertSum_of_cutoff
