import Exp7Lean.Analytic.EF.Pointwise

/-!
# The pointwise explicit-formula identity without GRH

Unlike `EF.zerosKer`, this kernel retains each zero's real part. Its Poisson
width is `1/2 + delta - Re rho`, not `delta`. For `delta > 1/2` all widths
are positive. This is the unconditional starting point for the smoothed
explicit formula; it does not yet assert the undamped formula.
-/

namespace Exp7.Frontier

open Complex Exp7.EF

/-- The zero kernel before imposing any critical-line hypothesis. -/
noncomputable def offLineZerosKernel (q : ℕ) [Fact q.Prime] (δ t : ℝ) : ℝ :=
  ∑' ρ : ℂ, (mult q ρ : ℝ) * poissonKer (1 / 2 + δ - ρ.re) (t - ρ.im)

theorem re_one_div_sub_eq_offLine (δ t : ℝ) (ρ : ℂ) :
    (1 / (((1 / 2 + δ : ℝ) : ℂ) + (t : ℂ) * I - ρ)).re =
      poissonKer (1 / 2 + δ - ρ.re) (t - ρ.im) := by
  simp [one_div, Complex.inv_re, Complex.normSq_apply, poissonKer, pow_two]

variable (q : ℕ) [Fact q.Prime]

theorem summable_offLineZerosKernel (hq : q % 4 = 3) (δ t : ℝ) :
    Summable (fun ρ : ℂ ↦
      (mult q ρ : ℝ) * poissonKer (1 / 2 + δ - ρ.re) (t - ρ.im)) := by
  have h := (summable_norm_analyticOrderNatAt_completedLFunction_mul_re_one_div_sub
    (chi q) (chi_isPrimitive q hq) (chi_ne_one q hq)
    (((1 / 2 + δ : ℝ) : ℂ) + (t : ℂ) * I)).of_norm
  simpa only [re_one_div_sub_eq_offLine, mult] using h

/-- The old pointwise formula, with zero real parts retained and no GRH input. -/
theorem pointwise_identity_unconditional (hq : q % 4 = 3) {δ : ℝ}
    (hδ : 1 / 2 < δ) (t : ℝ) :
    Real.log (q / Real.pi) / 2
        + (digamma (((3 / 4 + δ / 2 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * I)).re / 2
        - dirichletR q δ t = offLineZerosKernel q δ t := by
  set s : ℂ := ((1 / 2 + δ : ℝ) : ℂ) + (t : ℂ) * I with hs
  have hsre : s.re = 1 / 2 + δ := by simp [hs]
  have hs1 : 1 ≤ s.re := by rw [hsre]; linarith
  have hs0 : 0 < s.re := by linarith
  have H1 := re_logDeriv_LFunction_add_eq_tsum (chi q)
    (chi_isPrimitive q hq) (chi_ne_one q hq) hs0
    (DirichletCharacter.LFunction_ne_zero_of_one_le_re (chi q)
      (.inl (chi_ne_one q hq)) hs1)
  have D2 : (logDeriv (chi q).LFunction s).re = -dirichletR q δ t :=
    re_logDeriv_LFunction q δ hδ t
  have G5 := logDeriv_gammaFactor_odd (chi_odd q hq) hs0
  have hs2 : (s + 1) / 2 =
      ((3 / 4 + δ / 2 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * I := by
    simp only [hs]
    push_cast
    ring
  have hG : (logDeriv (chi q).gammaFactor s).re =
      (digamma (((3 / 4 + δ / 2 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * I)).re / 2
        - Real.log Real.pi / 2 := by
    rw [G5, hs2]
    simp
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero
  have hterm : ∀ ρ : ℂ,
      (analyticOrderNatAt (chi q).completedLFunction ρ : ℝ) * (1 / (s - ρ)).re =
        (mult q ρ : ℝ) * poissonKer (1 / 2 + δ - ρ.re) (t - ρ.im) := by
    intro ρ
    rw [hs, re_one_div_sub_eq_offLine]
    rfl
  rw [offLineZerosKernel, ← tsum_congr hterm, ← H1, D2, hG,
    Real.log_div hq0 Real.pi_ne_zero]
  ring

/-- Compatibility check: imposing GRH recovers the existing zero kernel exactly. -/
theorem offLineZerosKernel_eq_of_GRH (hq : q % 4 = 3) (hGRH : GRHFor q) (δ t : ℝ) :
    offLineZerosKernel q δ t = zerosKer q δ t := by
  apply tsum_congr
  intro ρ
  by_cases hm : mult q ρ = 0
  · simp [hm]
  rw [re_eq_half_of_mult_ne_zero q hq hGRH hm]
  congr 2
  ring

end Exp7.Frontier
