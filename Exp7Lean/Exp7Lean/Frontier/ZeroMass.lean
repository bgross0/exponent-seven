import Exp7Lean.Analytic.EF.Pointwise

/-!
# Unconditional weighted zero masses

The zeros here are those of the actual completed quadratic Dirichlet L-function,
with the existing `EF.mult` multiplicities. No critical-line hypothesis is used.
The shifted mass at `sigma = T + 1` is the analytic source of the improved
high-zero bound in `frontier/zero-audit/AUDIT.md`, Section 8.
-/

namespace Exp7.Frontier

open Complex
open Exp7.EF

variable (q : ℕ) [Fact q.Prime]

/-- Real partial-fraction kernel with the real part of the zero retained. -/
noncomputable def realZeroKernel (σ : ℝ) (ρ : ℂ) : ℝ :=
  (σ - ρ.re) / ((σ - ρ.re) ^ 2 + ρ.im ^ 2)

theorem re_one_div_real_sub (σ : ℝ) (ρ : ℂ) :
    (1 / ((σ : ℂ) - ρ)).re = realZeroKernel σ ρ := by
  simp [realZeroKernel, one_div, Complex.inv_re, Complex.normSq_apply, pow_two]

/-- The actual real logarithmic derivative, including conductor and gamma terms. -/
noncomputable def logDerivativeMass (σ : ℝ) : ℝ :=
  (logDeriv (chi q).LFunction (σ : ℂ)).re + Real.log q / 2 +
    (logDeriv (chi q).gammaFactor (σ : ℂ)).re

theorem summable_realZeroKernel (hq : q % 4 = 3) (σ : ℝ) :
    Summable (fun ρ : ℂ ↦ (mult q ρ : ℝ) * realZeroKernel σ ρ) := by
  have h := (summable_norm_analyticOrderNatAt_completedLFunction_mul_re_one_div_sub
    (chi q) (chi_isPrimitive q hq) (chi_ne_one q hq) (σ : ℂ)).of_norm
  simpa only [re_one_div_real_sub, mult] using h

/-- Unconditional real-axis partial fractions, at any `sigma > 1`. -/
theorem realZeroKernel_tsum (hq : q % 4 = 3) {σ : ℝ} (hσ : 1 < σ) :
    ∑' ρ : ℂ, (mult q ρ : ℝ) * realZeroKernel σ ρ = logDerivativeMass q σ := by
  have h := re_logDeriv_LFunction_add_eq_tsum (chi q)
    (chi_isPrimitive q hq) (chi_ne_one q hq)
    (s := (σ : ℂ)) (by simpa using (show 0 < σ by linarith))
    (DirichletCharacter.LFunction_ne_zero_of_one_le_re (chi q)
      (.inl (chi_ne_one q hq)) (by simpa using hσ.le))
  simpa only [re_one_div_real_sub, mult, logDerivativeMass] using h.symm

/-- The same identity with the odd gamma factor evaluated as a digamma term. -/
theorem logDerivativeMass_eq (hq : q % 4 = 3) {σ : ℝ} (hσ : 1 < σ) :
    logDerivativeMass q σ = Real.log ((q : ℝ) / Real.pi) / 2 +
      (digamma (((σ + 1) / 2 : ℝ) : ℂ)).re / 2 +
      (logDeriv (chi q).LFunction (σ : ℂ)).re := by
  have hG := logDeriv_gammaFactor_odd (chi_odd q hq)
    (s := (σ : ℂ)) (by simpa using (show 0 < σ by linarith))
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero
  unfold logDerivativeMass
  rw [hG, Real.log_div hq0 Real.pi_ne_zero]
  push_cast
  simp only [Complex.sub_re, Complex.div_ofNat_re, Complex.ofReal_re]
  ring

theorem realZeroKernel_nonneg {σ : ℝ} (hσ : 1 ≤ σ) {ρ : ℂ}
    (hρ : ρ.re ≤ 1) : 0 ≤ realZeroKernel σ ρ := by
  unfold realZeroKernel
  exact div_nonneg (by linarith) (by positivity)

/-- The sharper factor 2 comparison at sigma = 2 (the old density proof used 4). -/
theorem standard_weight_le_kernel {ρ : ℂ} (h0 : 0 ≤ ρ.re) (h1 : ρ.re ≤ 1) :
    1 / (1 + ρ.im ^ 2) ≤ 2 * realZeroKernel 2 ρ := by
  have hd : 0 < (2 - ρ.re) ^ 2 + ρ.im ^ 2 := by nlinarith [sq_nonneg ρ.im]
  unfold realZeroKernel
  rw [← mul_div_assoc, div_le_div_iff₀ (by positivity) hd]
  nlinarith [mul_nonneg h0 (show 0 ≤ 2 - ρ.re by linarith),
    mul_nonneg (sq_nonneg ρ.im) (show 0 ≤ 1 - ρ.re by linarith)]

/-- Total standard weighted zero mass, with multiplicities. -/
theorem standard_mass_le (hq : q % 4 = 3) :
    (∑' ρ : ℂ, (mult q ρ : ℝ) / (1 + ρ.im ^ 2)) ≤
      2 * logDerivativeMass q 2 := by
  rw [← realZeroKernel_tsum q hq (by norm_num : (1 : ℝ) < 2), ← tsum_mul_left]
  apply Summable.tsum_le_tsum _ (summable_mult_div q hq)
    ((summable_realZeroKernel q hq 2).mul_left 2)
  intro ρ
  by_cases hm : mult q ρ = 0
  · simp [hm]
  obtain ⟨h0, h1, -⟩ := mult_ne_zero_imp q hq hm
  have h := mul_le_mul_of_nonneg_left (standard_weight_le_kernel h0.le h1.le)
    (Nat.cast_nonneg (mult q ρ) : (0 : ℝ) ≤ _)
  convert h using 1 <;> ring

/-- At sigma = T+1 every nontrivial zero dominates the shifted weight. -/
theorem shifted_weight_le_kernel {T : ℝ} (hT : 0 < T) {ρ : ℂ}
    (h0 : 0 ≤ ρ.re) (h1 : ρ.re ≤ 1) :
    T / ((T + 1) ^ 2 + ρ.im ^ 2) ≤ realZeroKernel (T + 1) ρ := by
  have ha : 0 < T + 1 - ρ.re := by linarith
  have hd : 0 < (T + 1 - ρ.re) ^ 2 + ρ.im ^ 2 := by positivity
  have he : 0 < (T + 1) ^ 2 + ρ.im ^ 2 := by positivity
  have hsq : (T + 1 - ρ.re) ^ 2 ≤ (T + 1) ^ 2 := by
    nlinarith [mul_nonneg h0 (show 0 ≤ 2 * (T + 1) - ρ.re by linarith)]
  calc T / ((T + 1) ^ 2 + ρ.im ^ 2)
      ≤ (T + 1 - ρ.re) / ((T + 1) ^ 2 + ρ.im ^ 2) :=
        div_le_div_of_nonneg_right (by linarith) he.le
    _ ≤ (T + 1 - ρ.re) / ((T + 1 - ρ.re) ^ 2 + ρ.im ^ 2) :=
        div_le_div_of_nonneg_left ha.le hd (by linarith)

theorem summable_shifted_weight (hq : q % 4 = 3) {T : ℝ} (hT : 0 < T) :
    Summable (fun ρ : ℂ ↦ (mult q ρ : ℝ) / ((T + 1) ^ 2 + ρ.im ^ 2)) := by
  refine Summable.of_nonneg_of_le (fun ρ ↦ by positivity) (fun ρ ↦ ?_)
    (summable_mult_div q hq)
  exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity) (by nlinarith)

/-- The shifted mass estimate, directly from the existing unconditional Hadamard theorem. -/
theorem shifted_mass_le (hq : q % 4 = 3) {T : ℝ} (hT : 0 < T) :
    (∑' ρ : ℂ, (mult q ρ : ℝ) / ((T + 1) ^ 2 + ρ.im ^ 2)) ≤
      logDerivativeMass q (T + 1) / T := by
  apply (le_div_iff₀ hT).2
  rw [← tsum_mul_right, ← realZeroKernel_tsum q hq (by linarith : 1 < T + 1)]
  apply Summable.tsum_le_tsum _ ((summable_shifted_weight q hq hT).mul_right T)
    (summable_realZeroKernel q hq (T + 1))
  intro ρ
  by_cases hm : mult q ρ = 0
  · simp [hm]
  obtain ⟨h0, h1, -⟩ := mult_ne_zero_imp q hq hm
  have h := mul_le_mul_of_nonneg_left (shifted_weight_le_kernel hT h0.le h1.le)
    (Nat.cast_nonneg (mult q ρ) : (0 : ℝ) ≤ _)
  simpa only [mul_div_assoc, div_mul_eq_mul_div, mul_comm] using h

end Exp7.Frontier
