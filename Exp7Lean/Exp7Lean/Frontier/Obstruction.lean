import Exp7Lean.Frontier.ZeroLoss
import Exp7Lean.Arithmetic.InertThreshold

/-!
# Conditional assembly of the low-height zero obstruction

Reflection of actual L-function zeros is proved here. The smoothed explicit
formula, its convergence and test-function bounds remain explicit hypotheses
of the assembly theorem. Thus this is not a completed height-60 theorem.
-/

namespace Exp7.Frontier

open Complex Exp7.EF

variable (q : ℕ) [Fact q.Prime]

/-- Only zeros at height at most T are constrained. -/
def LowZeroStrip (d T : ℝ) : Prop :=
  ∀ ρ : ℂ, mult q ρ ≠ 0 → |ρ.im| ≤ T → |ρ.re - 1 / 2| ≤ d

/-- Reflection preserves the actual completed-L-function multiplicity. -/
theorem mult_reflection (hq : q % 4 = 3) (ρ : ℂ) :
    mult q (1 - (starRingEnd ℂ) ρ) = mult q ρ := by
  have h := Fallback.analyticOrderNatAt_xi_one_sub_conj (chi q)
    (chi_isPrimitive q hq) (chi_ne_one q hq) ρ
  simpa only [Fallback.analyticOrderNatAt_xi (chi q) (chi_ne_one q hq), mult] using h

/-- A violation on either side of the critical line gives a zero on the right,
at the same height. The conclusion is stated for the actual Dirichlet L-function. -/
theorem exists_right_zero_of_not_lowStrip (hq : q % 4 = 3) {d T : ℝ}
    (h : ¬ LowZeroStrip q d T) :
    ∃ ρ : ℂ, 0 < ρ.re ∧ ρ.re < 1 ∧ (chi q).LFunction ρ = 0 ∧
      1 / 2 + d < ρ.re ∧ |ρ.im| ≤ T := by
  classical
  unfold LowZeroStrip at h
  push Not at h
  obtain ⟨ρ, hm, ht, hd⟩ := h
  rcases lt_abs.mp hd with hr | hl
  · obtain ⟨h0, h1, hz⟩ := mult_ne_zero_imp q hq hm
    exact ⟨ρ, h0, h1, hz, by linarith, ht⟩
  · have hm' : mult q (1 - (starRingEnd ℂ) ρ) ≠ 0 := by
      rwa [mult_reflection q hq]
    obtain ⟨h0, h1, hz⟩ := mult_ne_zero_imp q hq hm'
    refine ⟨1 - (starRingEnd ℂ) ρ, h0, h1, hz, ?_, ?_⟩
    · simp only [Complex.sub_re, Complex.one_re, Complex.conj_re]
      linarith
    · simpa using ht

/-- A negative explicit-formula margin forces a low zero to the right of the strip.
The hypotheses expose all test-function and identity obligations. -/
theorem exists_right_zero_of_margin (hq : q % 4 = 3) {d T A C R : ℝ}
    (hT : 0 < T) (hA : 0 ≤ A) (hC : 0 ≤ C) (F : ℂ → ℝ)
    (hsum : Summable (fun ρ : ℂ ↦ (mult q ρ : ℝ) * F ρ))
    (hidentity : (∑' ρ : ℂ, (mult q ρ : ℝ) * F ρ) = R)
    (hlow : ∀ ρ, mult q ρ ≠ 0 → |ρ.im| ≤ T → |ρ.re - 1 / 2| ≤ d →
      -A / (1 + ρ.im ^ 2) ≤ F ρ)
    (hhigh : ∀ ρ, mult q ρ ≠ 0 → T < |ρ.im| → |F ρ| ≤ C / ρ.im ^ 4)
    (hmargin : R < -(A * (2 * logDerivativeMass q 2) +
      (C * (((T + 1) ^ 2 + T ^ 2) / T ^ 4)) *
        (logDerivativeMass q (T + 1) / T))) :
    ∃ ρ : ℂ, 0 < ρ.re ∧ ρ.re < 1 ∧ (chi q).LFunction ρ = 0 ∧
      1 / 2 + d < ρ.re ∧ |ρ.im| ≤ T := by
  apply exists_right_zero_of_not_lowStrip q hq
  intro hstrip
  have hbound := zero_sum_lower_bound q hq hT hA hC F hsum
    (fun ρ hm ht ↦ hlow ρ hm ht (hstrip ρ hm ht)) hhigh
  rw [hidentity] at hbound
  exact (not_lt_of_ge hbound) hmargin

/-- Connect the obstruction to the existing exponent-seven norm cutoff and inert sum.
No GRH hypothesis is introduced by this arithmetic step. -/
theorem zero_obstruction_of_inert_certificate {X : ℕ} (hE : IsExp7 q)
    (hcut : 4 * X ^ 7 < q) {d T A C J : ℝ}
    (hT : 0 < T) (hA : 0 ≤ A) (hC : 0 ≤ C) (f : ℝ → ℝ) (F : ℂ → ℝ)
    (hsum : Summable (fun ρ : ℂ ↦ (mult q ρ : ℝ) * F ρ))
    (hEF : (∑' ρ : ℂ, (mult q ρ : ℝ) * F ρ) =
      Real.log ((q : ℝ) / Real.pi) + psi34 + Jterm f - primeSum q f X)
    (hJ : Jterm f ≤ J)
    (hlow : ∀ ρ, mult q ρ ≠ 0 → |ρ.im| ≤ T → |ρ.re - 1 / 2| ≤ d →
      -A / (1 + ρ.im ^ 2) ≤ F ρ)
    (hhigh : ∀ ρ, mult q ρ ≠ 0 → T < |ρ.im| → |F ρ| ≤ C / ρ.im ^ 4)
    (hmargin : Real.log ((q : ℝ) / Real.pi) + psi34 + J - inertSum f X <
      -(A * (2 * logDerivativeMass q 2) +
        (C * (((T + 1) ^ 2 + T ^ 2) / T ^ 4)) *
          (logDerivativeMass q (T + 1) / T))) :
    ∃ ρ : ℂ, 0 < ρ.re ∧ ρ.re < 1 ∧ (chi q).LFunction ρ = 0 ∧
      1 / 2 + d < ρ.re ∧ |ρ.im| ≤ T := by
  have hprime := hE.primeSum_eq_inertSum_of_cutoff hcut f
  apply exists_right_zero_of_margin q hE.2.1 hT hA hC F hsum hEF hlow hhigh
  rw [hprime]
  linarith

end Exp7.Frontier
