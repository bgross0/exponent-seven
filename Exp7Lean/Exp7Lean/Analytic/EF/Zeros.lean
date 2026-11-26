import Exp7Lean.Analytic.EF.Character
import Exp7Lean.Analytic.EF.HadamardInput

/-!
# Explicit formula blueprint: location and density of the zeros

Leaves **L2a, L2c** and the proved corollary **L2b** of `BLUEPRINT.md`.
-/

namespace Exp7.EF

variable (q : ℕ) [Fact q.Prime]

/-- **L2a** (M). A point of positive multiplicity for the completed `L`-function of `chi q` lies in
the open critical strip and is a zero of `L(s, χ)`.

Proof sketch (Mathlib only): `mult q ρ ≠ 0` gives `completedLFunction χ ρ = 0`
(`analyticOrderNatAt`, `AnalyticAt.analyticOrderAt_eq_zero`, `differentiable_completedLFunction`).
For `1 ≤ Re ρ`: `LFunction_eq_completed_div_gammaFactor` and `LFunction_ne_zero_of_one_le_re`.
For `Re ρ ≤ 0`: the functional equation `IsPrimitive.completedLFunction_one_sub`
(with `rootNumber_ne_zero`, `χ⁻¹` again primitive and nonprincipal) reduces to the previous case.
In the strip `Γ_ℝ(ρ+1) ≠ 0` (`Gammaℝ_ne_zero_of_re_pos`), so `L(ρ, χ) = 0`. -/
theorem mult_ne_zero_imp (hq : q % 4 = 3) {ρ : ℂ} (h : mult q ρ ≠ 0) :
    0 < ρ.re ∧ ρ.re < 1 ∧ (chi q).LFunction ρ = 0 := by
  have hne : chi q ≠ 1 := chi_ne_one q hq
  have hprim : (chi q).IsPrimitive := chi_isPrimitive q hq
  have hq1 : q ≠ 1 := (Fact.out : q.Prime).ne_one
  have hΛ : (chi q).completedLFunction ρ = 0 :=
    apply_eq_zero_of_analyticOrderNatAt_ne_zero h
  have h1 : ρ.re < 1 := by
    by_contra hcon
    exact DirichletCharacter.completedLFunction_ne_zero_of_one_le_re (chi q) (.inl hne)
      (not_lt.mp hcon) hΛ
  have h0 : 0 < ρ.re := by
    by_contra hcon
    have hre : 1 ≤ (1 - ρ).re := by
      have := not_lt.mp hcon
      simp only [Complex.sub_re, Complex.one_re]
      linarith
    have hinv : (chi q)⁻¹ ≠ 1 := fun hc ↦ hne (inv_eq_one.mp hc)
    have hfe := hprim.completedLFunction_one_sub (1 - ρ)
    rw [sub_sub_cancel, hΛ] at hfe
    have hqne : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero
    have hpow : (q : ℂ) ^ (1 - ρ - 1 / 2) ≠ 0 := by
      rw [Ne, Complex.cpow_eq_zero_iff]
      exact fun hc ↦ hqne hc.1
    exact mul_ne_zero (mul_ne_zero hpow (DirichletCharacter.rootNumber_ne_zero hprim))
      (DirichletCharacter.completedLFunction_ne_zero_of_one_le_re (chi q)⁻¹ (.inl hinv) hre)
      hfe.symm
  refine ⟨h0, h1, ?_⟩
  rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor (chi q) ρ (.inr hq1), hΛ,
    zero_div]

/-- **L2b** (proved). Under GRH every zero counted by `mult` has real part `1/2`. -/
theorem re_eq_half_of_mult_ne_zero (hq : q % 4 = 3) (hGRH : GRHFor q) {ρ : ℂ}
    (h : mult q ρ ≠ 0) : ρ.re = 1 / 2 := by
  obtain ⟨h0, h1, hz⟩ := mult_ne_zero_imp q hq h
  exact hGRH ρ h0 h1 hz

/-- **L2c** (M). `∑_ρ m(ρ) / (1 + (Im ρ)²) < ∞`.

Proof sketch: H2 at `s = 2` gives summability of `m(ρ) Re (1/(2-ρ))`, and for `0 < Re ρ < 1`
(L2a) `Re (1/(2-ρ)) = (2-β)/((2-β)²+γ²) ≥ 1/(4(1+γ²))`; compare. -/
theorem summable_mult_div (hq : q % 4 = 3) :
    Summable (fun ρ : ℂ ↦ (mult q ρ : ℝ) / (1 + ρ.im ^ 2)) := by
  have hH2 := summable_norm_analyticOrderNatAt_completedLFunction_mul_re_one_div_sub (chi q)
    (chi_isPrimitive q hq) (chi_ne_one q hq) 2
  refine Summable.of_nonneg_of_le (fun ρ ↦ by positivity) (fun ρ ↦ ?_) (hH2.mul_left 4)
  change (mult q ρ : ℝ) / (1 + ρ.im ^ 2) ≤ 4 * ‖(mult q ρ : ℝ) * (1 / (2 - ρ)).re‖
  by_cases hm : mult q ρ = 0
  · simp [hm]
  obtain ⟨h0, h1, -⟩ := mult_ne_zero_imp q hq hm
  have hre : (1 / (2 - ρ)).re = (2 - ρ.re) / ((2 - ρ.re) * (2 - ρ.re) + ρ.im * ρ.im) := by
    rw [one_div, Complex.inv_re, Complex.normSq_apply]
    simp
  have hden : 0 < (2 - ρ.re) * (2 - ρ.re) + ρ.im * ρ.im := by nlinarith [sq_nonneg ρ.im]
  have hkey : 1 / (1 + ρ.im ^ 2) ≤
      4 * ((2 - ρ.re) / ((2 - ρ.re) * (2 - ρ.re) + ρ.im * ρ.im)) := by
    rw [← mul_div_assoc, div_le_div_iff₀ (by positivity) hden]
    nlinarith [sq_nonneg ρ.im, mul_nonneg (sq_nonneg ρ.im) (sub_nonneg.mpr h1.le)]
  have hpos : 0 ≤ (2 - ρ.re) / ((2 - ρ.re) * (2 - ρ.re) + ρ.im * ρ.im) :=
    div_nonneg (by linarith) hden.le
  have hm0 : (0 : ℝ) ≤ (mult q ρ : ℝ) := Nat.cast_nonneg _
  rw [hre, Real.norm_of_nonneg (mul_nonneg hm0 hpos)]
  calc (mult q ρ : ℝ) / (1 + ρ.im ^ 2) = (mult q ρ : ℝ) * (1 / (1 + ρ.im ^ 2)) := by ring
    _ ≤ (mult q ρ : ℝ) * (4 * ((2 - ρ.re) / ((2 - ρ.re) * (2 - ρ.re) + ρ.im * ρ.im))) :=
        mul_le_mul_of_nonneg_left hkey hm0
    _ = 4 * ((mult q ρ : ℝ) * ((2 - ρ.re) / ((2 - ρ.re) * (2 - ρ.re) + ρ.im * ρ.im))) := by
        ring

end Exp7.EF
