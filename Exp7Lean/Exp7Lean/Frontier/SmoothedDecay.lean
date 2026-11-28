import Exp7Lean.Frontier.SmoothedKernel
import Exp7Lean.Frontier.ZeroLoss

/-!
# Quartic decay for the actual smoothed Haar transform

The strip bound is uniform in the real part of the frequency. Applied to actual
completed-L-function zeros, it supplies the high-zero estimate without GRH.
-/

namespace Exp7.Frontier

open Complex Exp7.EF

theorem norm_cos_le_cosh_im (z : ℂ) : ‖Complex.cos z‖ ≤ Real.cosh z.im := by
  rw [Complex.cos, norm_div, Real.cosh_eq]
  norm_num only [norm_ofNat]
  apply div_le_div_of_nonneg_right _ (by norm_num)
  calc
    _ ≤ ‖Complex.exp (z * I)‖ + ‖Complex.exp (-z * I)‖ := norm_add_le _ _
    _ = _ := by simp only [Complex.norm_exp_mul_I, neg_im, neg_neg]; ring

theorem norm_sin_le_cosh_im (z : ℂ) : ‖Complex.sin z‖ ≤ Real.cosh z.im := by
  rw [Complex.sin, norm_div, norm_mul, norm_I, mul_one, Real.cosh_eq]
  norm_num only [norm_ofNat]
  apply div_le_div_of_nonneg_right _ (by norm_num)
  calc
    _ ≤ ‖Complex.exp (-z * I)‖ + ‖Complex.exp (z * I)‖ := norm_sub_le _ _
    _ = _ := by simp only [Complex.norm_exp_mul_I, neg_im, neg_neg]

noncomputable def smoothTailConstant (a b d : ℝ) : ℝ :=
  4 * (1 + Real.cosh (a * d)) ^ 2 * Real.cosh (b * d) ^ 2 /
    ((2 * a - 2 * b) * b ^ 2)

theorem smoothTailConstant_nonneg {a b : ℝ} (hab : b < a) (d : ℝ) :
    0 ≤ smoothTailConstant a b d := by
  have hN : 0 < 2 * a - 2 * b := by linarith
  unfold smoothTailConstant
  positivity

theorem cosh_mul_im_le {c d : ℝ} (hc : 0 ≤ c) {z : ℂ} (hz : |z.im| ≤ d) :
    Real.cosh (((c : ℂ) * z).im) ≤ Real.cosh (c * d) := by
  apply Real.cosh_le_cosh.mpr
  have hd : 0 ≤ d := (abs_nonneg _).trans hz
  simpa [mul_im, abs_mul, abs_of_nonneg hc, abs_of_nonneg (mul_nonneg hc hd)] using
    mul_le_mul_of_nonneg_left hz hc

theorem smoothH_strip_bound {a b d : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : b < a)
    {z : ℂ} (hz : z ≠ 0) (hstrip : |z.im| ≤ d) :
    ‖smoothH a b z‖ ≤ smoothTailConstant a b d / ‖z‖ ^ 4 := by
  have hN : 0 < 2 * a - 2 * b := by linarith
  have hcos : ‖1 - Complex.cos (a * z)‖ ≤ 1 + Real.cosh (a * d) := by
    calc
      _ ≤ ‖(1 : ℂ)‖ + ‖Complex.cos (a * z)‖ := norm_sub_le _ _
      _ ≤ _ := by
        simp only [norm_one]
        exact add_le_add_right ((norm_cos_le_cosh_im _).trans (cosh_mul_im_le ha.le hstrip)) 1
  have hsin : ‖Complex.sin (b * z)‖ ≤ Real.cosh (b * d) :=
    (norm_sin_le_cosh_im _).trans (cosh_mul_im_le hb.le hstrip)
  rw [smoothH_closed ha hb hz]
  simp only [norm_div, norm_mul, norm_pow]
  have hNc : ‖(2 * (a : ℂ) - 2 * b)‖ = 2 * a - 2 * b := by
    rw [show (2 * (a : ℂ) - 2 * b) = ((2 * a - 2 * b : ℝ) : ℂ) by push_cast; rfl]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hN]
  rw [hNc, norm_real, Real.norm_eq_abs, abs_of_pos hb]
  norm_num only [norm_ofNat]
  unfold smoothTailConstant
  rw [div_div]
  gcongr

theorem smoothH_quartic_bound {a b d : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : b < a)
    {z : ℂ} (hz : z.re ≠ 0) (hstrip : |z.im| ≤ d) :
    ‖smoothH a b z‖ ≤ smoothTailConstant a b d / z.re ^ 4 := by
  have hz0 : z ≠ 0 := by intro h; apply hz; simp [h]
  apply (smoothH_strip_bound ha hb hab hz0 hstrip).trans
  apply div_le_div_of_nonneg_left (smoothTailConstant_nonneg hab d) (by positivity)
  calc
    z.re ^ 4 = |z.re| ^ 4 := by rw [← abs_pow, abs_of_nonneg (by positivity)]
    _ ≤ ‖z‖ ^ 4 := pow_le_pow_left₀ (abs_nonneg _) (abs_re_le_norm z) _

theorem zeroFrequency_parts (ρ : ℂ) :
    ((ρ - 1 / 2) / I).re = ρ.im ∧ ((ρ - 1 / 2) / I).im = 1 / 2 - ρ.re := by
  simp [Complex.div_I, mul_re, mul_im]

variable (q : ℕ) [Fact q.Prime]

theorem smoothH_zero_quartic_bound (hq : q % 4 = 3) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hab : b < a) {ρ : ℂ}
    (hm : mult q ρ ≠ 0) (ht : ρ.im ≠ 0) :
    |(smoothH a b ((ρ - 1 / 2) / I)).re| ≤
      smoothTailConstant a b (1 / 2) / ρ.im ^ 4 := by
  obtain ⟨hlo, hhi, _⟩ := mult_ne_zero_imp q hq hm
  have hp := zeroFrequency_parts ρ
  have hs : |((ρ - 1 / 2) / I).im| ≤ (1 / 2 : ℝ) := by
    rw [hp.2, abs_le]
    constructor <;> linarith
  exact (abs_re_le_norm _).trans (by
    simpa only [hp.1] using smoothH_quartic_bound ha hb hab (by rwa [hp.1]) hs)

theorem smoothH_high_zero_loss_le (hq : q % 4 = 3) {a b T : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hab : b < a) (hT : 0 < T) :
    Summable (fun ρ : ℂ ↦ if T < |ρ.im| then
      (mult q ρ : ℝ) * |(smoothH a b ((ρ - 1 / 2) / I)).re| else 0) ∧
    (∑' ρ : ℂ, if T < |ρ.im| then
      (mult q ρ : ℝ) * |(smoothH a b ((ρ - 1 / 2) / I)).re| else 0) ≤
      (smoothTailConstant a b (1 / 2) * (((T + 1) ^ 2 + T ^ 2) / T ^ 4)) *
        (logDerivativeMass q (T + 1) / T) := by
  apply high_zero_loss_le q hq hT (smoothTailConstant_nonneg hab _) _
  intro ρ hm ht
  exact smoothH_zero_quartic_bound q hq ha hb hab hm (by
    intro h; simp only [h, abs_zero] at ht; linarith)

end Exp7.Frontier
