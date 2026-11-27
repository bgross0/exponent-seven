import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! # Partial summation with the logarithmic Haar weight -/

namespace Exp7.ChebyshevTail

open Finset MeasureTheory
open scoped ArithmeticFunction.vonMangoldt

/-- The logarithmic weight in the Haar row with upper endpoint exp L. -/
noncomputable def logWeight (L t : ℝ) := (1 - Real.log t / L) / Real.sqrt t

/-- The negative derivative of the logarithmic weight on the positive axis. -/
noncomputable def logKernel (L t : ℝ) :=
  (1 / 2 + 1 / L - Real.log t / (2 * L)) / (t * Real.sqrt t)

theorem logWeight_hasDerivAt {L t : ℝ} (hL : 0 < L) (ht : 0 < t) :
    HasDerivAt (logWeight L) (-logKernel L t) t := by
  have hs := Real.sqrt_pos.mpr ht
  have hsq := Real.sq_sqrt ht.le
  convert (((hasDerivAt_const t (1 : ℝ)).sub ((Real.hasDerivAt_log ht.ne').div_const L)).div
    (Real.hasDerivAt_sqrt ht.ne') hs.ne') using 1 <;> try rfl
  unfold logKernel
  simp only [Pi.sub_apply]
  field_simp [hL.ne', ht.ne', hs.ne']
  ring_nf
  simp only [hsq]

theorem logKernel_continuousAt (L : ℝ) {t : ℝ} (ht : 0 < t) :
    ContinuousAt (logKernel L) t := by
  unfold logKernel
  fun_prop (disch := positivity)

theorem logKernel_nonneg {L t : ℝ} (hL : 0 < L) (ht : 0 < t) (hlt : Real.log t ≤ L) :
    0 ≤ logKernel L t := by
  unfold logKernel
  apply div_nonneg _ (by positivity)
  have : Real.log t / (2 * L) ≤ 1 / 2 := (div_le_iff₀ (by positivity)).mpr (by linarith)
  linarith [one_div_pos.mpr hL]

/-- A primitive for the linear and square-root-log terms in the Chebyshev bounds. -/
noncomputable def weightPrimitive (a b L t : ℝ) :=
  a * Real.sqrt t * (1 + 4 / L - Real.log t / L) +
    b * ((1 + 2 / L) / 2 * Real.log t ^ 2 - Real.log t ^ 3 / (3 * L))

theorem weightPrimitive_hasDerivAt (a b : ℝ) {L t : ℝ} (hL : 0 < L) (ht : 0 < t) :
    HasDerivAt (weightPrimitive a b L)
      (logKernel L t * (a * t + b * (2 * Real.sqrt t * Real.log t))) t := by
  have hs := Real.sqrt_pos.mpr ht
  have hsq := Real.sq_sqrt ht.le
  have hl := Real.hasDerivAt_log ht.ne'
  have hr := Real.hasDerivAt_sqrt ht.ne'
  have ha := ((hr.const_mul a).mul
    ((hasDerivAt_const t (1 + 4 / L)).sub (hl.div_const L)))
  have hb := (hl.pow 2).const_mul ((1 + 2 / L) / 2)
  convert ha.add ((hb.sub ((hl.pow 3).div_const (3 * L))).const_mul b) using 1 <;> try rfl
  unfold logKernel
  simp only [Pi.sub_apply]
  field_simp [hL.ne', ht.ne', hs.ne']
  ring_nf
  simp only [hsq]
  ring

end Exp7.ChebyshevTail
