import Exp7Lean.Analytic.EF.TestFunction

/-!
# Complex Fourier transforms and box smoothing

The frequency can be complex. Compactly supported interval functions remain
integrable after the exponential twist, so convolution factorization holds
off the real axis as well. No explicit-formula hypothesis is used here.
-/

namespace Exp7.Frontier

open Complex MeasureTheory
open scoped Convolution

noncomputable def expTwist (z : ℂ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  f x * Complex.exp (z * I * x)

noncomputable def complexTransform (f : ℝ → ℂ) (z : ℂ) : ℂ :=
  ∫ x : ℝ, expTwist z f x

theorem expTwist_convolution (f g : ℝ → ℂ) (z : ℂ) :
    expTwist z (f ⋆[ContinuousLinearMap.mul ℂ ℂ] g) =
      (expTwist z f) ⋆[ContinuousLinearMap.mul ℂ ℂ] (expTwist z g) := by
  funext x
  simp only [expTwist, convolution_def, ContinuousLinearMap.mul_apply']
  rw [← integral_mul_const]
  apply integral_congr_ae
  filter_upwards with t
  have he : Complex.exp (z * I * x) =
      Complex.exp (z * I * t) * Complex.exp (z * I * (x - t)) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  rw [he]
  push_cast
  ring

theorem complexTransform_convolution {f g : ℝ → ℂ} (z : ℂ)
    (hf : Integrable (expTwist z f)) (hg : Integrable (expTwist z g)) :
    complexTransform (f ⋆[ContinuousLinearMap.mul ℂ ℂ] g) z =
      complexTransform f z * complexTransform g z := by
  unfold complexTransform
  rw [expTwist_convolution]
  exact integral_convolution (ContinuousLinearMap.mul ℂ ℂ) hf hg

noncomputable def intervalBox (a b : ℝ) : ℝ → ℂ :=
  (Set.Ico a b).indicator (fun _ ↦ 1)

theorem expTwist_intervalBox (a b : ℝ) (z : ℂ) :
    expTwist z (intervalBox a b) =
      (Set.Ico a b).indicator (fun x : ℝ ↦ Complex.exp (z * I * x)) := by
  funext x
  by_cases hx : x ∈ Set.Ico a b <;> simp [expTwist, intervalBox, hx]

theorem integrable_expTwist_intervalBox (a b : ℝ) (z : ℂ) :
    Integrable (expTwist z (intervalBox a b)) := by
  rw [expTwist_intervalBox, integrable_indicator_iff measurableSet_Ico]
  exact (Continuous.continuousOn (by fun_prop)).integrableOn_Icc.mono_set
    Set.Ico_subset_Icc_self

theorem complexTransform_intervalBox (a b : ℝ) (hab : a ≤ b) {z : ℂ} (hz : z ≠ 0) :
    complexTransform (intervalBox a b) z =
      (Complex.exp (z * I * b) - Complex.exp (z * I * a)) / (z * I) := by
  rw [complexTransform, expTwist_intervalBox, integral_indicator measurableSet_Ico,
    integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab,
    integral_exp_mul_complex (mul_ne_zero hz Complex.I_ne_zero)]

theorem complexTransform_intervalBox_zero (a b : ℝ) (hab : a ≤ b) :
    complexTransform (intervalBox a b) 0 = (b - a : ℝ) := by
  simp only [complexTransform, expTwist_intervalBox, zero_mul, Complex.exp_zero]
  rw [integral_indicator measurableSet_Ico]
  simp [Real.volume_real_Ico_of_le hab]

/-- The unsmoothed signed Haar function, represented in the complex scalars. -/
noncomputable def haarBase (a : ℝ) (x : ℝ) : ℂ :=
  intervalBox (-a) 0 x - intervalBox 0 a x

/-- A probability box (up to the immaterial choice of endpoint values). -/
noncomputable def averagingBox (b : ℝ) (x : ℝ) : ℂ :=
  (2 * (b : ℂ))⁻¹ * intervalBox (-b) b x

/-- The actual convolution used in the smoothed-Haar argument. -/
noncomputable def smoothedHaar (a b : ℝ) : ℝ → ℂ :=
  haarBase a ⋆[ContinuousLinearMap.mul ℂ ℂ] averagingBox b

theorem expTwist_haarBase (a : ℝ) (z : ℂ) :
    expTwist z (haarBase a) =
      expTwist z (intervalBox (-a) 0) - expTwist z (intervalBox 0 a) := by
  funext x
  simp [expTwist, haarBase, sub_mul]

theorem expTwist_averagingBox (b : ℝ) (z : ℂ) :
    expTwist z (averagingBox b) =
      fun x ↦ (2 * (b : ℂ))⁻¹ * expTwist z (intervalBox (-b) b) x := by
  funext x
  simp [expTwist, averagingBox, mul_assoc]

theorem integrable_expTwist_haarBase (a : ℝ) (z : ℂ) :
    Integrable (expTwist z (haarBase a)) := by
  rw [expTwist_haarBase]
  exact (integrable_expTwist_intervalBox (-a) 0 z).sub
    (integrable_expTwist_intervalBox 0 a z)

theorem integrable_expTwist_averagingBox (b : ℝ) (z : ℂ) :
    Integrable (expTwist z (averagingBox b)) := by
  rw [expTwist_averagingBox]
  exact (integrable_expTwist_intervalBox (-b) b z).const_mul _

theorem integrable_expTwist_smoothedHaar (a b : ℝ) (z : ℂ) :
    Integrable (expTwist z (smoothedHaar a b)) := by
  rw [smoothedHaar, expTwist_convolution]
  exact (integrable_expTwist_haarBase a z).integrable_convolution
    (ContinuousLinearMap.mul ℂ ℂ) (integrable_expTwist_averagingBox b z)

theorem complexTransform_smoothedHaar_factor (a b : ℝ) (z : ℂ) :
    complexTransform (smoothedHaar a b) z =
      complexTransform (haarBase a) z * complexTransform (averagingBox b) z :=
  complexTransform_convolution z (integrable_expTwist_haarBase a z)
    (integrable_expTwist_averagingBox b z)

theorem complexTransform_haarBase {a : ℝ} (ha : 0 ≤ a) {z : ℂ} (hz : z ≠ 0) :
    complexTransform (haarBase a) z = -2 * I * (1 - Complex.cos (a * z)) / z := by
  unfold complexTransform
  rw [expTwist_haarBase]
  simp only [Pi.sub_apply]
  rw [integral_sub (integrable_expTwist_intervalBox (-a) 0 z)
    (integrable_expTwist_intervalBox 0 a z)]
  change complexTransform (intervalBox (-a) 0) z -
    complexTransform (intervalBox 0 a) z = _
  rw [complexTransform_intervalBox _ _ (by linarith) hz,
    complexTransform_intervalBox _ _ ha hz]
  simp only [mul_zero, Complex.exp_zero, ofReal_zero, ofReal_neg]
  have h1 : z * I * (a : ℂ) = a * z * I := by ring
  have h2 : z * I * -(a : ℂ) = -(a * z) * I := by ring
  rw [h1, h2, Complex.cos]
  field_simp
  ring_nf
  simp [Complex.I_sq]
  ring

theorem complexTransform_averagingBox {b : ℝ} (hb : 0 < b) {z : ℂ} (hz : z ≠ 0) :
    complexTransform (averagingBox b) z = Complex.sin (b * z) / (b * z) := by
  have hb0 : (b : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
  unfold complexTransform
  rw [expTwist_averagingBox, integral_const_mul]
  change (2 * (b : ℂ))⁻¹ * complexTransform (intervalBox (-b) b) z = _
  rw [complexTransform_intervalBox _ _ (by linarith) hz]
  have h1 : z * I * (b : ℂ) = b * z * I := by ring
  have h2 : z * I * -(b : ℂ) = -(b * z) * I := by ring
  rw [ofReal_neg, h1, h2, Complex.sin]
  field_simp
  ring_nf
  simp [Complex.I_sq]
  ring

/-- The closed transform follows from the actual convolution at every nonzero complex frequency. -/
theorem complexTransform_smoothedHaar {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b)
    {z : ℂ} (hz : z ≠ 0) :
    complexTransform (smoothedHaar a b) z =
      -2 * I * (1 - Complex.cos (a * z)) * Complex.sin (b * z) / (b * z ^ 2) := by
  rw [complexTransform_smoothedHaar_factor, complexTransform_haarBase ha hz,
    complexTransform_averagingBox hb hz]
  ring

theorem complexTransform_smoothedHaar_zero {a b : ℝ} (ha : 0 ≤ a) :
    complexTransform (smoothedHaar a b) 0 = 0 := by
  rw [complexTransform_smoothedHaar_factor]
  suffices complexTransform (haarBase a) 0 = 0 by rw [this, zero_mul]
  unfold complexTransform
  rw [expTwist_haarBase]
  simp only [Pi.sub_apply]
  rw [integral_sub (integrable_expTwist_intervalBox (-a) 0 0)
    (integrable_expTwist_intervalBox 0 a 0)]
  change complexTransform (intervalBox (-a) 0) 0 -
    complexTransform (intervalBox 0 a) 0 = 0
  rw [complexTransform_intervalBox_zero _ _ (by linarith),
    complexTransform_intervalBox_zero _ _ ha]
  push_cast
  ring

end Exp7.Frontier
