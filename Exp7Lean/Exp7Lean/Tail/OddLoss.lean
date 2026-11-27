import Exp7Lean.Tail.LogWeight

/-! # The triangular weight for the odd prime-power loss -/

namespace Exp7.ChebyshevTail

open Finset MeasureTheory
open scoped ArithmeticFunction.vonMangoldt

private noncomputable def psiMajorant (t : ℝ) :=
  Real.log 4 * t + 2 * Real.sqrt t * Real.log t

/-- The weighted sum bounding the negative odd-power contribution at cutoff Y. -/
theorem odd_loss_le {Y : ℝ} (hY : 1 < Y) :
    (∑ n ∈ Ioc 0 ⌊Y⌋₊, logWeight (Real.log Y) n * Λ n) ≤
      4 * Real.log 4 * Real.sqrt Y / Real.log Y + Real.log Y ^ 2 / 6 + Real.log Y := by
  let L := Real.log Y
  have hL : 0 < L := Real.log_pos hY
  have hpos {t : ℝ} (ht : t ∈ Set.Icc 1 Y) : 0 < t := lt_of_lt_of_le zero_lt_one ht.1
  have hc : ContinuousOn (logKernel L) (Set.Icc 1 Y) :=
    fun _ ht ↦ (logKernel_continuousAt L (hpos ht)).continuousWithinAt
  have hd (t : ℝ) (ht : t ∈ Set.Icc 1 Y) := logWeight_hasDerivAt hL (hpos ht)
  have hder : ContinuousOn (deriv (logWeight L)) (Set.Icc 1 Y) :=
    hc.neg.congr (fun t ht ↦ (hd t ht).deriv)
  have habel := sum_mul_eq_sub_integral_mul₀ (fun n ↦ Λ n) (f := logWeight L) (by simp) Y
    (fun t ht ↦ (hd t ht).differentiableAt) hder.integrableOn_Icc
  have hend : logWeight L Y = 0 := by simp [logWeight, L, (Real.log_pos hY).ne']
  rw [← add_sum_Ioc_eq_sum_Icc (Nat.zero_le _), hend, zero_mul, zero_sub,
    ← intervalIntegral.integral_of_le hY.le, ← intervalIntegral.integral_neg] at habel
  simp only [ArithmeticFunction.map_zero, mul_zero, zero_add] at habel
  have hidentity : (∑ n ∈ Ioc 0 ⌊Y⌋₊, logWeight L n * Λ n) =
      ∫ t in 1..Y, logKernel L t * Chebyshev.psi t := by
    refine habel.trans (intervalIntegral.integral_congr fun t ht ↦ ?_)
    rw [Set.uIcc_of_le hY.le] at ht
    rw [(hd t ht).deriv, neg_mul, neg_neg, Chebyshev.psi_eq_sum_Icc]
  have hi : IntervalIntegrable (fun t ↦ logKernel L t * Chebyshev.psi t) volume 1 Y := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le hY.le).mpr
    simp_rw [Chebyshev.psi_eq_sum_Icc]
    exact integrableOn_mul_sum_Icc _ zero_le_one hc.integrableOn_Icc
  have hj : IntervalIntegrable (fun t ↦ logKernel L t * psiMajorant t) volume 1 Y := by
    apply ContinuousOn.intervalIntegrable_of_Icc hY.le
    refine hc.mul fun t ht ↦ ContinuousAt.continuousWithinAt ?_
    have ht' := (hpos ht).ne'
    unfold psiMajorant
    fun_prop
  rw [hidentity]
  calc
    _ ≤ ∫ t in 1..Y, logKernel L t * psiMajorant t := by
      apply intervalIntegral.integral_mono_on hY.le hi hj
      intro t ht
      exact mul_le_mul_of_nonneg_left (Chebyshev.psi_le ht.1)
        (logKernel_nonneg hL (hpos ht) (Real.log_le_log (hpos ht) ht.2))
    _ = weightPrimitive (Real.log 4) 1 L Y - weightPrimitive (Real.log 4) 1 L 1 := by
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ hj
      intro t ht
      rw [Set.uIcc_of_le hY.le] at ht
      simpa only [psiMajorant, one_mul] using weightPrimitive_hasDerivAt (Real.log 4) 1 hL (hpos ht)
    _ ≤ _ := by
      change _ ≤ 4 * Real.log 4 * Real.sqrt Y / L + L ^ 2 / 6 + L
      simp only [weightPrimitive, Real.log_one, Real.sqrt_one, one_mul]
      change Real.log 4 * Real.sqrt Y * (1 + 4 / L - L / L) + ((1 + 2 / L) / 2 * L ^ 2 -
        L ^ 3 / (3 * L)) - _ ≤ _
      field_simp [hL.ne']
      nlinarith [Real.log_pos (show (1 : ℝ) < 4 by norm_num),
        mul_pos (Real.log_pos (show (1 : ℝ) < 4 by norm_num)) hL]

end Exp7.ChebyshevTail
