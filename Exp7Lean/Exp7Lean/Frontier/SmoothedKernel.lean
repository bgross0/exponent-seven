import Exp7Lean.Frontier.ComplexTransform

/-!
# The entire transform of the smoothed Haar function

`smoothG` agrees with the complex Fourier transform of the actual convolution,
including at zero. `smoothH` is its normalized product at opposite frequencies.
The normalization constant is explicit. Its equality to the squared L2 norm
is proved separately in `SmoothedNorm`, rather than assumed in these definitions.
-/

namespace Exp7.Frontier

open Complex MeasureTheory

noncomputable def complexSinc : ℂ → ℂ := dslope Complex.sin 0

theorem complexSinc_zero : complexSinc 0 = 1 := by
  simp [complexSinc, Complex.deriv_sin]

theorem complexSinc_of_ne_zero {z : ℂ} (hz : z ≠ 0) :
    complexSinc z = Complex.sin z / z := by
  simp [complexSinc, dslope_of_ne _ hz, slope_def_field]

@[fun_prop]
theorem analyticAt_complexSinc (z : ℂ) : AnalyticAt ℂ complexSinc z :=
  Complex.analyticAt_sin.dslope 0

theorem complexSinc_neg (z : ℂ) : complexSinc (-z) = complexSinc z := by
  by_cases hz : z = 0
  · simp [hz]
  rw [complexSinc_of_ne_zero (neg_ne_zero.mpr hz), complexSinc_of_ne_zero hz]
  simp

theorem complexSinc_ofReal (t : ℝ) : complexSinc (t : ℂ) = (Real.sinc t : ℂ) := by
  by_cases ht : t = 0
  · simp [ht, complexSinc_zero]
  rw [complexSinc_of_ne_zero (by exact_mod_cast ht), Real.sinc_of_ne_zero ht]
  simp

noncomputable def smoothG (a b : ℝ) (z : ℂ) : ℂ :=
  -I * (a : ℂ) ^ 2 * z * complexSinc (a * z / 2) ^ 2 * complexSinc (b * z)

noncomputable def smoothH (a b : ℝ) (z : ℂ) : ℂ :=
  (a : ℂ) ^ 4 * z ^ 2 * complexSinc (a * z / 2) ^ 4 * complexSinc (b * z) ^ 2 /
    (2 * a - 2 * b)

theorem smoothG_zero (a b : ℝ) : smoothG a b 0 = 0 := by simp [smoothG]

theorem smoothH_zero (a b : ℝ) : smoothH a b 0 = 0 := by simp [smoothH]

theorem analyticAt_smoothG (a b : ℝ) (z : ℂ) : AnalyticAt ℂ (smoothG a b) z := by
  unfold smoothG
  fun_prop

theorem analyticAt_smoothH (a b : ℝ) (z : ℂ) : AnalyticAt ℂ (smoothH a b) z := by
  unfold smoothH
  fun_prop

theorem smoothG_neg (a b : ℝ) (z : ℂ) : smoothG a b (-z) = -smoothG a b z := by
  simp only [smoothG, mul_neg, neg_div, complexSinc_neg]
  ring

theorem smoothH_product (a b : ℝ) (z : ℂ) :
    smoothH a b z = smoothG a b z * smoothG a b (-z) / (2 * a - 2 * b) := by
  rw [smoothG_neg]
  unfold smoothH smoothG
  ring_nf
  simp [Complex.I_sq]

theorem smoothG_closed {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    {z : ℂ} (hz : z ≠ 0) :
    smoothG a b z =
      -2 * I * (1 - Complex.cos (a * z)) * Complex.sin (b * z) / (b * z ^ 2) := by
  have ha0 : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have hb0 : (b : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
  have hhalf : (a : ℂ) * z / 2 ≠ 0 := div_ne_zero (mul_ne_zero ha0 hz) (by norm_num)
  have hc : 1 - Complex.cos (a * z) = 2 * Complex.sin (a * z / 2) ^ 2 := by
    have h := Complex.cos_two_mul_eq_one_sub (x := (a : ℂ) * z / 2)
    rw [show 2 * ((a : ℂ) * z / 2) = a * z by ring] at h
    rw [h]
    ring
  rw [smoothG, complexSinc_of_ne_zero hhalf,
    complexSinc_of_ne_zero (mul_ne_zero hb0 hz), hc]
  field_simp

/-- Identity with the actual convolution transform at every complex frequency. -/
theorem complexTransform_smoothedHaar_eq_smoothG {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (z : ℂ) : complexTransform (smoothedHaar a b) z = smoothG a b z := by
  by_cases hz : z = 0
  · rw [hz, complexTransform_smoothedHaar_zero ha.le, smoothG_zero]
  rw [complexTransform_smoothedHaar ha.le hb hz, smoothG_closed ha hb hz]

theorem smoothH_closed {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    {z : ℂ} (hz : z ≠ 0) :
    smoothH a b z =
      4 * (1 - Complex.cos (a * z)) ^ 2 * Complex.sin (b * z) ^ 2 /
        ((2 * a - 2 * b) * b ^ 2 * z ^ 4) := by
  rw [smoothH_product, smoothG_neg, smoothG_closed ha hb hz]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring_nf
  simp [Complex.I_sq]

theorem smoothH_ofReal (a b t : ℝ) :
    smoothH a b (t : ℂ) =
      ((a ^ 4 * t ^ 2 * Real.sinc (a * t / 2) ^ 4 * Real.sinc (b * t) ^ 2 /
        (2 * a - 2 * b) : ℝ) : ℂ) := by
  unfold smoothH
  push_cast
  rw [show (a : ℂ) * (t : ℂ) / 2 = ((a * t / 2 : ℝ) : ℂ) by push_cast; rfl,
    show (b : ℂ) * (t : ℂ) = ((b * t : ℝ) : ℂ) by push_cast; rfl]
  rw [complexSinc_ofReal, complexSinc_ofReal]

theorem smoothH_real_nonneg {a b : ℝ} (hab : b < a) (t : ℝ) :
    0 ≤ (smoothH a b (t : ℂ)).re := by
  rw [smoothH_ofReal, ofReal_re]
  have hN : 0 < 2 * a - 2 * b := by linarith
  positivity

theorem smoothH_real_im (a b t : ℝ) : (smoothH a b (t : ℂ)).im = 0 := by
  rw [smoothH_ofReal, ofReal_im]

end Exp7.Frontier
