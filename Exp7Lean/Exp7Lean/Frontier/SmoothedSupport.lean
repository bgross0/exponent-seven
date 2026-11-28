import Exp7Lean.Frontier.SmoothedNorm

/-!
# Continuity, support and symmetry of the actual correlation
-/

namespace Exp7.Frontier

open Complex MeasureTheory
open scoped Convolution

theorem integrable_smoothedHaarReal {a : ℝ} (ha : 0 ≤ a) (b : ℝ) :
    Integrable (smoothedHaarReal a b) :=
  (continuous_smoothedHaarReal a b).integrable_of_hasCompactSupport
    (hasCompactSupport_smoothedHaarReal ha b)

theorem hasCompactSupport_smoothedHaar {a : ℝ} (ha : 0 ≤ a) (b : ℝ) :
    HasCompactSupport (smoothedHaar a b) := by
  apply HasCompactSupport.intro (isCompact_Icc (a := -(a + b)) (b := a + b))
  intro x hx
  rw [smoothedHaar_eq_ofReal, smoothedHaarReal_zero_of_abs_ge ha, ofReal_zero]
  simp only [Set.mem_Icc, not_and_or, not_le] at hx
  rcases hx with h | h
  · exact (neg_le_abs x).trans' (by linarith)
  · exact h.le.trans (le_abs_self x)

theorem continuous_smoothCorrelation {a : ℝ} (ha : 0 ≤ a) (b : ℝ) :
    Continuous (smoothCorrelation a b) := by
  have hc : Continuous (fun x : ℝ ↦ smoothedHaar a b (-x)) :=
    (continuous_smoothedHaar a b).comp continuous_neg
  have hs : HasCompactSupport (fun x : ℝ ↦ smoothedHaar a b (-x)) := by
    apply HasCompactSupport.intro (isCompact_Icc (a := -(a + b)) (b := a + b))
    intro x hx
    rw [smoothedHaar_eq_ofReal, smoothedHaarReal_zero_of_abs_ge ha, ofReal_zero]
    rw [abs_neg]
    simp only [Set.mem_Icc, not_and_or, not_le] at hx
    rcases hx with h | h
    · exact (neg_le_abs x).trans' (by linarith)
    · exact h.le.trans (le_abs_self x)
  exact (hs.continuous_convolution_right (L := ContinuousLinearMap.mul ℂ ℂ)
    ((continuous_smoothedHaar a b).locallyIntegrable) hc).div_const _

theorem smoothCorrelation_zero_of_abs_ge {a b u : ℝ} (ha : 0 ≤ a)
    (hu : 2 * (a + b) ≤ |u|) : smoothCorrelation a b u = 0 := by
  rw [smoothCorrelation_eq_ofReal]
  have he : ∀ x : ℝ, smoothedHaarReal a b x * smoothedHaarReal a b (x - u) = 0 := by
    intro x
    by_cases hx : a + b ≤ |x|
    · rw [smoothedHaarReal_zero_of_abs_ge ha hx, zero_mul]
    · rw [smoothedHaarReal_zero_of_abs_ge (x := x - u) ha, mul_zero]
      have htri : |u| ≤ |x| + |x - u| := by
        simpa using abs_sub x (x - u)
      linarith [not_le.mp hx]
  simp only [he, integral_zero, zero_div, ofReal_zero]

theorem hasCompactSupport_smoothCorrelation {a : ℝ} (ha : 0 ≤ a) (b : ℝ) :
    HasCompactSupport (smoothCorrelation a b) := by
  apply HasCompactSupport.intro
    (isCompact_Icc (a := -(2 * (a + b))) (b := 2 * (a + b)))
  intro u hu
  apply smoothCorrelation_zero_of_abs_ge ha
  simp only [Set.mem_Icc, not_and_or, not_le] at hu
  rcases hu with h | h
  · exact (neg_le_abs u).trans' (by linarith)
  · exact h.le.trans (le_abs_self u)

theorem integrable_smoothCorrelation {a : ℝ} (ha : 0 ≤ a) (b : ℝ) :
    Integrable (smoothCorrelation a b) :=
  (continuous_smoothCorrelation ha b).integrable_of_hasCompactSupport
    (hasCompactSupport_smoothCorrelation ha b)

theorem smoothCorrelation_neg (a b u : ℝ) :
    smoothCorrelation a b (-u) = smoothCorrelation a b u := by
  simp only [smoothCorrelation_eq_ofReal, sub_neg_eq_add]
  congr 2
  have h := integral_add_right_eq_self (μ := volume)
    (fun x : ℝ ↦ smoothedHaarReal a b x * smoothedHaarReal a b (x - u)) u
  simpa only [add_sub_cancel_right, mul_comm] using h

end Exp7.Frontier
