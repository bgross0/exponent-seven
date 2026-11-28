import Exp7Lean.Frontier.SmoothedCorrelation

/-!
# The actual smoothed Haar function in the spatial variable

Interval overlap gives a real, continuous formula for the convolution. Endpoint
choices of the interval indicators disappear under Lebesgue integration.
-/

namespace Exp7.Frontier

open Complex MeasureTheory
open scoped Convolution

noncomputable def intervalOverlap (l r u v x : ℝ) : ℝ :=
  max (min r (x - u) - max l (x - v)) 0

theorem intervalBox_product_ae (l r u v x : ℝ) :
    (fun t ↦ intervalBox l r t * intervalBox u v (x - t)) =ᵐ[volume]
      (Set.Ioo (max l (x - v)) (min r (x - u))).indicator (fun _ ↦ (1 : ℂ)) := by
  filter_upwards [Measure.ae_ne volume l, Measure.ae_ne volume (x - u)] with t hl hu
  have he : (t ∈ Set.Ico l r ∧ x - t ∈ Set.Ico u v) ↔
      t ∈ Set.Ioo (max l (x - v)) (min r (x - u)) := by
    simp only [Set.mem_Ico, Set.mem_Ioo, max_lt_iff, lt_min_iff]
    constructor
    · rintro ⟨⟨h1,h2⟩,h3,h4⟩
      exact ⟨⟨lt_of_le_of_ne h1 (Ne.symm hl), by linarith⟩, h2, by
        apply lt_of_le_of_ne (by linarith)
        exact hu⟩
    · rintro ⟨⟨h1,h2⟩,h3,h4⟩
      exact ⟨⟨h1.le,h3⟩, by linarith, by linarith⟩
  by_cases h1 : t ∈ Set.Ico l r <;> by_cases h2 : x - t ∈ Set.Ico u v <;>
    simp_all [intervalBox]

theorem integrable_intervalBox_product (l r u v x : ℝ) :
    Integrable (fun t ↦ intervalBox l r t * intervalBox u v (x - t)) := by
  apply Integrable.congr _ (intervalBox_product_ae l r u v x).symm
  have h : IntegrableOn (fun _ : ℝ ↦ (1 : ℂ))
      (Set.Icc (max l (x - v)) (min r (x - u))) :=
    (continuous_const : Continuous (fun _ : ℝ ↦ (1 : ℂ))).continuousOn.integrableOn_Icc
  exact (integrable_indicator_iff measurableSet_Ioo).mpr
    (h.mono_set Set.Ioo_subset_Icc_self)

theorem intervalBox_convolution (l r u v x : ℝ) :
    (intervalBox l r ⋆[ContinuousLinearMap.mul ℂ ℂ] intervalBox u v) x =
      (intervalOverlap l r u v x : ℂ) := by
  rw [convolution_mul, integral_congr_ae (intervalBox_product_ae l r u v x),
    integral_indicator measurableSet_Ioo]
  simp [intervalOverlap, Real.volume_real_Ioo]

noncomputable def smoothedHaarReal (a b x : ℝ) : ℝ :=
  (intervalOverlap (-a) 0 (-b) b x - intervalOverlap 0 a (-b) b x) / (2 * b)

theorem smoothedHaar_eq_ofReal (a b x : ℝ) :
    smoothedHaar a b x = (smoothedHaarReal a b x : ℂ) := by
  unfold smoothedHaar
  rw [convolution_mul]
  have he : (fun t ↦ haarBase a t * averagingBox b (x - t)) =
      fun t ↦ (2 * (b : ℂ))⁻¹ *
        (intervalBox (-a) 0 t * intervalBox (-b) b (x - t) -
          intervalBox 0 a t * intervalBox (-b) b (x - t)) := by
    funext t
    simp only [haarBase, averagingBox]
    ring
  rw [he, integral_const_mul, integral_sub
    (integrable_intervalBox_product (-a) 0 (-b) b x)
    (integrable_intervalBox_product 0 a (-b) b x)]
  change (2 * (b : ℂ))⁻¹ *
    ((intervalBox (-a) 0 ⋆[ContinuousLinearMap.mul ℂ ℂ] intervalBox (-b) b) x -
      (intervalBox 0 a ⋆[ContinuousLinearMap.mul ℂ ℂ] intervalBox (-b) b) x) = _
  rw [intervalBox_convolution, intervalBox_convolution]
  simp only [smoothedHaarReal, ofReal_div, ofReal_sub, ofReal_mul, ofReal_ofNat]
  ring

theorem continuous_smoothedHaarReal (a b : ℝ) : Continuous (smoothedHaarReal a b) := by
  unfold smoothedHaarReal intervalOverlap
  fun_prop

theorem continuous_smoothedHaar (a b : ℝ) : Continuous (smoothedHaar a b) := by
  have he : smoothedHaar a b = fun x ↦ (smoothedHaarReal a b x : ℂ) :=
    funext (smoothedHaar_eq_ofReal a b)
  rw [he]
  exact Complex.continuous_ofReal.comp (continuous_smoothedHaarReal a b)

theorem smoothedHaar_im (a b x : ℝ) : (smoothedHaar a b x).im = 0 := by
  rw [smoothedHaar_eq_ofReal, ofReal_im]

theorem intervalOverlap_zero_left {l r u v x : ℝ} (hx : x ≤ l + u) :
    intervalOverlap l r u v x = 0 := by
  unfold intervalOverlap
  apply max_eq_right
  have h1 := min_le_right r (x - u)
  have h2 := le_max_left l (x - v)
  linarith

theorem intervalOverlap_zero_right {l r u v x : ℝ} (hx : r + v ≤ x) :
    intervalOverlap l r u v x = 0 := by
  unfold intervalOverlap
  apply max_eq_right
  have h1 := min_le_left r (x - u)
  have h2 := le_max_right l (x - v)
  linarith

theorem intervalOverlap_reflect (l r u v x : ℝ) :
    intervalOverlap l r u v (-x) = intervalOverlap (-r) (-l) (-v) (-u) x := by
  have h1 : min r (-x - u) = -max (-r) (x + u) := by
    by_cases h : r ≤ -x - u
    · rw [min_eq_left h, max_eq_left (by linarith)]
      ring
    · rw [min_eq_right (by linarith), max_eq_right (by linarith)]
      ring
  have h2 : max l (-x - v) = -min (-l) (x + v) := by
    by_cases h : l ≤ -x - v
    · rw [max_eq_right h, min_eq_right (by linarith)]
      ring
    · rw [max_eq_left (by linarith), min_eq_left (by linarith)]
      ring
  unfold intervalOverlap
  rw [h1,h2]
  simp only [sub_neg_eq_add]
  congr 1
  ring

theorem smoothedHaarReal_neg (a b x : ℝ) :
    smoothedHaarReal a b (-x) = -smoothedHaarReal a b x := by
  simp only [smoothedHaarReal, intervalOverlap_reflect, neg_zero, neg_neg]
  ring

theorem smoothedHaarReal_zero_of_abs_ge {a b x : ℝ} (ha : 0 ≤ a)
    (hx : a + b ≤ |x|) : smoothedHaarReal a b x = 0 := by
  rcases le_abs.mp hx with h | h
  · rw [smoothedHaarReal, intervalOverlap_zero_right (by linarith),
      intervalOverlap_zero_right h]
    simp
  · rw [smoothedHaarReal, intervalOverlap_zero_left (by linarith),
      intervalOverlap_zero_left (by linarith)]
    simp

theorem hasCompactSupport_smoothedHaarReal {a : ℝ} (ha : 0 ≤ a) (b : ℝ) :
    HasCompactSupport (smoothedHaarReal a b) := by
  apply HasCompactSupport.intro' (isCompact_Icc (a := -(a + b)) (b := a + b))
    isClosed_Icc
  intro x hx
  apply smoothedHaarReal_zero_of_abs_ge ha
  simp only [Set.mem_Icc, not_and_or, not_le] at hx
  rcases hx with h | h
  · exact (neg_le_abs x).trans' (by linarith)
  · exact h.le.trans (le_abs_self x)

theorem smoothedHaarReal_central {a b x : ℝ} (hab : 2 * b ≤ a)
    (hx0 : 0 ≤ x) (hxb : x ≤ b) : smoothedHaarReal a b x = -x / b := by
  have hleft : intervalOverlap (-a) 0 (-b) b x = b - x := by
    simp only [intervalOverlap, sub_neg_eq_add]
    rw [min_eq_left (by linarith), max_eq_right (show -a ≤ x - b by linarith),
      max_eq_left (by linarith)]
    ring
  have hright : intervalOverlap 0 a (-b) b x = x + b := by
    simp only [intervalOverlap, sub_neg_eq_add]
    rw [min_eq_right (by linarith), max_eq_left (show x - b ≤ 0 by linarith)]
    simp only [sub_zero]
    rw [max_eq_left (by linarith)]
  rw [smoothedHaarReal, hleft, hright]
  ring

theorem smoothedHaarReal_plateau {a b x : ℝ} (hb : 0 < b)
    (hx0 : b ≤ x) (hxa : x ≤ a - b) : smoothedHaarReal a b x = -1 := by
  have hleft : intervalOverlap (-a) 0 (-b) b x = 0 :=
    intervalOverlap_zero_right (by linarith)
  have hright : intervalOverlap 0 a (-b) b x = 2 * b := by
    simp only [intervalOverlap, sub_neg_eq_add]
    rw [min_eq_right (by linarith), max_eq_right (show 0 ≤ x - b by linarith),
      max_eq_left (by linarith)]
    ring
  rw [smoothedHaarReal, hleft, hright]
  field_simp
  ring

theorem smoothedHaarReal_outer {a b x : ℝ} (_hb : 0 ≤ b) (hab : 2 * b ≤ a)
    (hx0 : a - b ≤ x) (hxa : x ≤ a + b) :
    smoothedHaarReal a b x = (x - a - b) / (2 * b) := by
  have hleft : intervalOverlap (-a) 0 (-b) b x = 0 :=
    intervalOverlap_zero_right (by linarith)
  have hright : intervalOverlap 0 a (-b) b x = a - x + b := by
    simp only [intervalOverlap, sub_neg_eq_add]
    rw [min_eq_left (by linarith), max_eq_right (show 0 ≤ x - b by linarith),
      max_eq_left (by linarith)]
    ring
  rw [smoothedHaarReal, hleft, hright]
  ring

end Exp7.Frontier
