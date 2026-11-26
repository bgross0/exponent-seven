import Exp7Lean.Analytic.EF.Zeros
import Exp7Lean.Analytic.EF.Digamma
import Exp7Lean.Analytic.EF.DirichletSeries

/-!
# Explicit formula blueprint: the pointwise identity on the line `Re s = 1/2 + δ`, `δ > 1/2`

Node **P0** of `BLUEPRINT.md`.
-/

namespace Exp7.EF

open Complex

variable (q : ℕ) [Fact q.Prime]

/-- Helper for **P0**: on the critical line `Re ρ = 1/2`, the real part of `1 / (s - ρ)` at
`s = 1/2 + δ + it` is the Poisson kernel `δ / (δ² + (t - Im ρ)²)`. -/
theorem re_one_div_sub_eq_poissonKer (δ t : ℝ) {ρ : ℂ} (hρ : ρ.re = 1 / 2) :
    (1 / (((1 / 2 + δ : ℝ) : ℂ) + (t : ℂ) * I - ρ)).re = poissonKer δ (t - ρ.im) := by
  have hre : (((1 / 2 + δ : ℝ) : ℂ) + (t : ℂ) * I - ρ).re = δ := by
    simp [hρ]
  have him : (((1 / 2 + δ : ℝ) : ℂ) + (t : ℂ) * I - ρ).im = t - ρ.im := by
    simp
  rw [one_div, Complex.inv_re, Complex.normSq_apply, hre, him, poissonKer]
  ring

/-- **P0** (M, assembly of H1, L1, L2b, G5, D2). Under GRH, for `δ > 1/2` and all real `t`,

`½ log(q/π) + ½ Re ψ(3/4 + δ/2 + it/2) - ∑ₙ Λ(n)χ(n) n^{-1/2-δ} cos(t log n)
    = ∑_ρ m(ρ) δ / (δ² + (t - Im ρ)²)`.

Proof: H1 at `s = 1/2 + δ + it` (there `Re s > 1`, so `L(s) ≠ 0` by
`DirichletCharacter.LFunction_ne_zero_of_one_le_re`); `γ'/γ` by G5 with `(s+1)/2 = 3/4 + δ/2 + it/2`;
`L'/L` by D2; and for `m(ρ) ≠ 0`, `ρ = 1/2 + iγ` (L2b) gives
`Re (1/(s-ρ)) = Re (1/(δ + i(t-γ))) = δ/(δ²+(t-γ)²)`; `log q - log π = log (q/π)`. -/
theorem pointwise_identity (hq : q % 4 = 3) (hGRH : GRHFor q) {δ : ℝ} (hδ : 1 / 2 < δ) (t : ℝ) :
    Real.log (q / Real.pi) / 2
        + (digamma (((3 / 4 + δ / 2 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * I)).re / 2
        - dirichletR q δ t
      = zerosKer q δ t := by
  have hprim := chi_isPrimitive q hq
  have hne := chi_ne_one q hq
  have hodd := chi_odd q hq
  set s : ℂ := ((1 / 2 + δ : ℝ) : ℂ) + (t : ℂ) * I with hs
  have hsre : s.re = 1 / 2 + δ := by simp [hs]
  have hs1 : 1 ≤ s.re := by rw [hsre]; linarith
  have hs0 : 0 < s.re := by linarith
  have hL : (chi q).LFunction s ≠ 0 :=
    DirichletCharacter.LFunction_ne_zero_of_one_le_re (chi q) (Or.inl hne) hs1
  have H1 := re_logDeriv_LFunction_add_eq_tsum (chi q) hprim hne hs0 hL
  have D2 : (logDeriv (chi q).LFunction s).re = -dirichletR q δ t :=
    re_logDeriv_LFunction q δ hδ t
  have G5 := logDeriv_gammaFactor_odd hodd hs0
  have hs2 : (s + 1) / 2 = ((3 / 4 + δ / 2 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * I := by
    simp only [hs]
    push_cast
    ring
  have hG : (logDeriv (chi q).gammaFactor s).re
      = (digamma (((3 / 4 + δ / 2 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * I)).re / 2
        - Real.log Real.pi / 2 := by
    rw [G5, hs2]
    simp
  have hq0 : (q : ℝ) ≠ 0 := by
    exact_mod_cast (Fact.out : q.Prime).ne_zero
  have hlog : Real.log (q / Real.pi) = Real.log q - Real.log Real.pi :=
    Real.log_div hq0 Real.pi_ne_zero
  have hterm : ∀ ρ : ℂ, (analyticOrderNatAt (chi q).completedLFunction ρ : ℝ) * (1 / (s - ρ)).re
      = (mult q ρ : ℝ) * poissonKer δ (t - ρ.im) := by
    intro ρ
    by_cases hm : mult q ρ = 0
    · have hm' : analyticOrderNatAt (chi q).completedLFunction ρ = 0 := hm
      simp [hm, hm']
    · have hρ := re_eq_half_of_mult_ne_zero q hq hGRH hm
      rw [hs, re_one_div_sub_eq_poissonKer δ t hρ]
      rfl
  rw [zerosKer, ← tsum_congr hterm, ← H1, D2, hG, hlog]
  ring

end Exp7.EF
