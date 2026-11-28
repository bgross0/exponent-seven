import Exp7Lean.Frontier.SmoothedSupport
import Exp7Lean.Frontier.SmoothedSum
import Exp7Lean.Frontier.DampedFormula

/-!
# Admissibility of the concrete smoothed Haar correlation

Fourier inversion connects the real correlation with the real-axis restriction
of its entire transform. Combined with exact normalization and support, this
provides the existing `WeilAdmissible` interface without a new hypothesis.
-/

namespace Exp7.Frontier

open Complex MeasureTheory Exp7.EF

noncomputable def smoothSpectrum (a b t : ℝ) : ℝ := (smoothH a b (t : ℂ)).re

theorem continuous_smoothSpectrum (a b : ℝ) : Continuous (smoothSpectrum a b) := by
  have hc : Continuous (smoothH a b) := continuous_iff_continuousAt.mpr
    (fun z ↦ (analyticAt_smoothH a b z).continuousAt)
  exact Complex.continuous_re.comp (hc.comp Complex.continuous_ofReal)

theorem smoothH_real_decay {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : b < a) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t : ℝ, ‖smoothH a b (t : ℂ)‖ ≤ K / (1 + t ^ 2) := by
  obtain ⟨K,hK,hbound⟩ := smoothH_strip_weight_bound (d := 0) ha hb hab
  refine ⟨K,hK,fun t ↦ ?_⟩
  have h := hbound (t : ℂ) (by simp)
  simp only [ofReal_re] at h
  exact h.trans (div_le_div_of_nonneg_left hK (by positivity) (by linarith))

theorem integrable_smoothH_real {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : b < a) :
    Integrable (fun t : ℝ ↦ smoothH a b (t : ℂ)) := by
  obtain ⟨K,hK,hbound⟩ := smoothH_real_decay ha hb hab
  have hc : Continuous (fun t : ℝ ↦ smoothH a b (t : ℂ)) :=
    (continuous_iff_continuousAt.mpr
      (fun z ↦ (analyticAt_smoothH a b z).continuousAt)).comp Complex.continuous_ofReal
  apply (integrable_inv_one_add_sq.const_mul K).mono' hc.aestronglyMeasurable
  filter_upwards with t
  simpa only [← div_eq_mul_inv] using hbound t

open scoped FourierTransform in
theorem fourier_smoothCorrelation {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    𝓕 (smoothCorrelation a b) =
      fun ξ : ℝ ↦ smoothH a b ((-(2 * Real.pi) * ξ : ℝ) : ℂ) := by
  funext ξ
  rw [← complexTransform_smoothCorrelation ha hb]
  rw [Real.fourier_real_eq_integral_exp_smul]
  unfold complexTransform
  apply integral_congr_ae
  filter_upwards with u
  simp only [smul_eq_mul, expTwist]
  rw [mul_comm]
  congr 1
  congr 1
  push_cast
  ring

open scoped FourierTransform in
theorem smoothCorrelation_fourier_inverse {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hab : b < a) (u : ℝ) :
    smoothCorrelation a b u = ∫ ξ : ℝ,
      Complex.exp (((2 * Real.pi * ξ * u : ℝ) : ℂ) * I) *
        smoothH a b ((-(2 * Real.pi) * ξ : ℝ) : ℂ) := by
  have hF : Integrable (𝓕 (smoothCorrelation a b)) := by
    rw [fourier_smoothCorrelation ha hb]
    exact (integrable_smoothH_real ha hb hab).comp_mul_left'
      (R := -(2 * Real.pi)) (neg_ne_zero.mpr (by positivity))
  have hinv := congr_fun ((continuous_smoothCorrelation ha.le b).fourierInv_fourier_eq
    (integrable_smoothCorrelation ha.le b) hF) u
  rw [Real.fourierInv_eq', fourier_smoothCorrelation ha hb] at hinv
  refine hinv.symm.trans ?_
  apply integral_congr_ae
  filter_upwards with ξ
  simp only [smul_eq_mul]
  congr 3
  simp [mul_comm, mul_assoc, mul_left_comm]

theorem smoothCorrelation_cosine_inverse {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hab : b < a) (u : ℝ) :
    (smoothCorrelation a b u).re =
      1 / (2 * Real.pi) * ∫ t : ℝ, smoothSpectrum a b t * Real.cos (t * u) := by
  have hscaled := (integrable_smoothH_real ha hb hab).comp_mul_left'
    (R := -(2 * Real.pi)) (neg_ne_zero.mpr (by positivity))
  have hi : Integrable (fun ξ : ℝ ↦
      Complex.exp (((2 * Real.pi * ξ * u : ℝ) : ℂ) * I) *
        smoothH a b ((-(2 * Real.pi) * ξ : ℝ) : ℂ)) := by
    refine hscaled.norm.mono' ?_ ?_
    · exact (by fun_prop : Continuous (fun ξ : ℝ ↦
        Complex.exp (((2 * Real.pi * ξ * u : ℝ) : ℂ) * I))).aestronglyMeasurable.mul
          hscaled.aestronglyMeasurable
    · filter_upwards with ξ
      rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  have hr : (smoothCorrelation a b u).re =
      ∫ ξ : ℝ, (fun t : ℝ ↦ smoothSpectrum a b t * Real.cos (t * u))
        (-(2 * Real.pi) * ξ) := by
    rw [smoothCorrelation_fourier_inverse ha hb hab]
    have he := (integral_re hi).symm
    change (∫ ξ : ℝ, Complex.exp (((2 * Real.pi * ξ * u : ℝ) : ℂ) * I) *
      smoothH a b ((-(2 * Real.pi) * ξ : ℝ) : ℂ)).re = _ at he
    rw [he]
    apply integral_congr_ae
    filter_upwards with ξ
    change (Complex.exp (((2 * Real.pi * ξ * u : ℝ) : ℂ) * I) *
      smoothH a b ((-(2 * Real.pi) * ξ : ℝ) : ℂ)).re = _
    simp only [Complex.mul_re, smoothH_real_im, mul_zero, sub_zero,
      Complex.exp_ofReal_mul_I_re, smoothSpectrum]
    rw [show -(2 * Real.pi) * ξ * u = -(2 * Real.pi * ξ * u) by ring, Real.cos_neg]
    ring
  rw [hr, Measure.integral_comp_mul_left
    (fun t : ℝ ↦ smoothSpectrum a b t * Real.cos (t * u)) (-(2 * Real.pi)),
    smul_eq_mul, abs_inv, abs_neg,
    abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi), one_div]

theorem weilAdmissible_smoothCorrelation {a b : ℝ} (hb : 0 < b) (hab : 2 * b ≤ a) :
    WeilAdmissible (fun u ↦ (smoothCorrelation a b u).re) (2 * (a + b))
      (smoothSpectrum a b) := by
  have ha : 0 < a := by linarith
  have hba : b < a := by linarith
  obtain ⟨K,hK,hbound⟩ := smoothH_real_decay ha hb hba
  refine ⟨continuous_smoothSpectrum a b, smoothH_real_nonneg hba,
    ⟨K,fun t ↦ ?_⟩, smoothCorrelation_cosine_inverse ha hb hba, ?_, ?_⟩
  · exact (le_abs_self _).trans ((abs_re_le_norm _).trans (hbound t))
  · rw [smoothCorrelation_zero hb hab, one_re]
  · intro u hu
    rw [smoothCorrelation_zero_of_abs_ge ha.le (hu.trans (le_abs_self u)), zero_re]

theorem smoothSpectrum_integral {a b : ℝ} (hb : 0 < b) (hab : 2 * b ≤ a) :
    (∫ t : ℝ, smoothSpectrum a b t) = 2 * Real.pi :=
  (weilAdmissible_smoothCorrelation hb hab).integral_eq

theorem smoothCorrelation_abs_le_one {a b : ℝ} (hb : 0 < b) (hab : 2 * b ≤ a)
    (u : ℝ) : |(smoothCorrelation a b u).re| ≤ 1 := by
  have hf := weilAdmissible_smoothCorrelation hb hab
  have hi : Integrable (fun t : ℝ ↦ smoothSpectrum a b t * Real.cos (t * u)) :=
    hf.integrable.mul_bdd (c := 1) (by fun_prop) (.of_forall fun t ↦ by
      simpa using Real.abs_cos_le_one (t * u))
  have hbound : (∫ t : ℝ, |smoothSpectrum a b t * Real.cos (t * u)|) ≤
      ∫ t : ℝ, smoothSpectrum a b t := by
    apply integral_mono hi.abs hf.integrable
    intro t
    dsimp only
    rw [abs_mul, abs_of_nonneg (hf.nonneg t)]
    exact mul_le_of_le_one_right (hf.nonneg t) (Real.abs_cos_le_one _)
  rw [hf.inv u, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 1 / (2 * Real.pi))]
  calc
    _ ≤ 1 / (2 * Real.pi) * (∫ t : ℝ, |smoothSpectrum a b t * Real.cos (t * u)|) :=
      mul_le_mul_of_nonneg_left (abs_integral_le_integral_abs) (by positivity)
    _ ≤ 1 / (2 * Real.pi) * (∫ t : ℝ, smoothSpectrum a b t) :=
      mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = 1 := by rw [hf.integral_eq]; field_simp

/-- The exact shape parameters used by the four height-60 rows. -/
theorem weilAdmissible_smoothCorrelation_row {X : ℕ} (hX : 1 < X) :
    WeilAdmissible
      (fun u ↦ (smoothCorrelation (99 * Real.log X / 200) (Real.log X / 200) u).re)
      (Real.log X) (smoothSpectrum (99 * Real.log X / 200) (Real.log X / 200)) := by
  have hL : 0 < Real.log (X : ℝ) := Real.log_pos (by exact_mod_cast hX)
  convert weilAdmissible_smoothCorrelation
    (a := 99 * Real.log X / 200) (b := Real.log X / 200) (by positivity)
    (by linarith) using 1
  ring

variable (q : ℕ) [Fact q.Prime]

/-- The unconditional damped formula is now instantiated with the actual row kernel.
This does not yet continue the identity to zero damping. -/
theorem smoothed_row_damped_formula (hq : q % 4 = 3) {X : ℕ} (hX : 1 < X)
    {δ : ℝ} (hδ : 1 / 2 < δ) :
    offLineZeroSideR q (smoothSpectrum (99 * Real.log X / 200) (Real.log X / 200)) δ =
      arithSideR q
        (fun u ↦ (smoothCorrelation (99 * Real.log X / 200) (Real.log X / 200) u).re)
        X δ :=
  offLineZeroSideR_eq_arithSideR_of_half_lt q hq
    (weilAdmissible_smoothCorrelation_row hX) hδ

end Exp7.Frontier
