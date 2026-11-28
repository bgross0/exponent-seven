import Exp7Lean.Frontier.SmoothedShape

/-!
# Exact L2 normalization of the smoothed Haar function

The central ramp, plateau and outer ramp determine the squared norm. This
proves the denominator used by the transform and correlation is the actual
squared L2 norm when the smoothing intervals do not overlap.
-/

namespace Exp7.Frontier

open Complex MeasureTheory

theorem smoothedHaarReal_sq_central_integral {a b : ℝ} (hb : 0 < b) (hab : 2 * b ≤ a) :
    (∫ x in (0 : ℝ)..b, smoothedHaarReal a b x ^ 2) = b / 3 := by
  calc
    _ = ∫ x in (0 : ℝ)..b, x ^ 2 / b ^ 2 := by
      apply intervalIntegral.integral_congr
      intro x hx
      dsimp only
      rw [Set.uIcc_of_le hb.le] at hx
      rw [smoothedHaarReal_central hab hx.1 hx.2]
      ring
    _ = _ := by
      rw [intervalIntegral.integral_div, integral_pow]
      norm_num
      field_simp

theorem smoothedHaarReal_sq_plateau_integral {a b : ℝ} (hb : 0 < b)
    (hab : 2 * b ≤ a) :
    (∫ x in b..(a - b), smoothedHaarReal a b x ^ 2) = a - 2 * b := by
  calc
    _ = ∫ _ in b..(a - b), (1 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro x hx
      dsimp only
      rw [Set.uIcc_of_le (by linarith)] at hx
      rw [smoothedHaarReal_plateau hb hx.1 hx.2]
      norm_num
    _ = _ := by simp; ring

theorem smoothedHaarReal_sq_outer_integral {a b : ℝ} (hb : 0 < b)
    (hab : 2 * b ≤ a) :
    (∫ x in (a - b)..(a + b), smoothedHaarReal a b x ^ 2) = 2 * b / 3 := by
  calc
    _ = ∫ x in (a - b)..(a + b), (x - (a + b)) ^ 2 / (4 * b ^ 2) := by
      apply intervalIntegral.integral_congr
      intro x hx
      dsimp only
      rw [Set.uIcc_of_le (by linarith)] at hx
      rw [smoothedHaarReal_outer hb.le hab hx.1 hx.2]
      ring
    _ = _ := by
      rw [intervalIntegral.integral_div,
        intervalIntegral.integral_comp_sub_right (fun x : ℝ ↦ x ^ 2), integral_pow]
      norm_num
      field_simp
      ring

theorem smoothedHaarReal_sq_positive_integral {a b : ℝ} (hb : 0 < b)
    (hab : 2 * b ≤ a) :
    (∫ x in (0 : ℝ)..(a + b), smoothedHaarReal a b x ^ 2) = a - b := by
  have hc : Continuous (fun x ↦ smoothedHaarReal a b x ^ 2) :=
    (continuous_smoothedHaarReal a b).pow 2
  have h1 := intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (μ := volume) 0 b) (hc.intervalIntegrable (μ := volume) b (a - b))
  have h2 := intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (μ := volume) 0 (a - b)) (hc.intervalIntegrable (μ := volume) (a - b) (a + b))
  rw [smoothedHaarReal_sq_central_integral hb hab,
    smoothedHaarReal_sq_plateau_integral hb hab] at h1
  rw [smoothedHaarReal_sq_outer_integral hb hab] at h2
  linarith

theorem smoothedHaarReal_sq_integral {a b : ℝ} (hb : 0 < b) (hab : 2 * b ≤ a) :
    (∫ x : ℝ, smoothedHaarReal a b x ^ 2) = 2 * a - 2 * b := by
  have ha : 0 ≤ a := by linarith
  have hc : Continuous (fun x ↦ smoothedHaarReal a b x ^ 2) :=
    (continuous_smoothedHaarReal a b).pow 2
  have he : (∫ x in -(a + b)..(a + b), smoothedHaarReal a b x ^ 2) =
      ∫ x : ℝ, smoothedHaarReal a b x ^ 2 := by
    apply intervalIntegral.integral_eq_integral_of_support_subset
    intro x hx
    simp only [Function.mem_support, ne_eq, pow_eq_zero_iff (by norm_num : 2 ≠ 0)] at hx
    have hlt : |x| < a + b := by
      by_contra h
      exact hx (smoothedHaarReal_zero_of_abs_ge ha (not_lt.mp h))
    exact ⟨(abs_lt.mp hlt).1, (abs_lt.mp hlt).2.le⟩
  have hneg : (∫ x in -(a + b)..0, smoothedHaarReal a b x ^ 2) =
      ∫ x in (0 : ℝ)..(a + b), smoothedHaarReal a b x ^ 2 := by
    calc
      _ = ∫ x in -(a + b)..0, smoothedHaarReal a b (-x) ^ 2 := by
        simp only [smoothedHaarReal_neg, neg_sq]
      _ = _ := by simpa using (intervalIntegral.integral_comp_neg (f := fun x ↦ smoothedHaarReal a b x ^ 2)
        (a := -(a + b)) (b := 0))
  have hs := intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (μ := volume) (-(a + b)) 0) (hc.intervalIntegrable (μ := volume) 0 (a + b))
  rw [he, hneg, smoothedHaarReal_sq_positive_integral hb hab] at hs
  linarith

theorem smoothedHaar_norm_sq_integral {a b : ℝ} (hb : 0 < b) (hab : 2 * b ≤ a) :
    (∫ x : ℝ, ‖smoothedHaar a b x‖ ^ 2) = 2 * a - 2 * b := by
  simpa only [smoothedHaar_eq_ofReal, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    using smoothedHaarReal_sq_integral hb hab

theorem smoothCorrelation_eq_ofReal (a b u : ℝ) :
    smoothCorrelation a b u =
      (((∫ x : ℝ, smoothedHaarReal a b x * smoothedHaarReal a b (x - u)) /
        (2 * a - 2 * b) : ℝ) : ℂ) := by
  simp only [smoothCorrelation, convolution_mul, neg_sub, smoothedHaar_eq_ofReal]
  rw [ofReal_div]
  congr 1
  · simp_rw [← ofReal_mul]
    exact integral_complex_ofReal
  · push_cast
    rfl

theorem smoothCorrelation_im (a b u : ℝ) : (smoothCorrelation a b u).im = 0 := by
  rw [smoothCorrelation_eq_ofReal, ofReal_im]

theorem smoothCorrelation_zero {a b : ℝ} (hb : 0 < b) (hab : 2 * b ≤ a) :
    smoothCorrelation a b 0 = 1 := by
  have hN : 0 < 2 * a - 2 * b := by linarith
  rw [smoothCorrelation_eq_ofReal]
  simp only [sub_zero, ← sq, smoothedHaarReal_sq_integral hb hab,
    div_self hN.ne', ofReal_one]

end Exp7.Frontier
