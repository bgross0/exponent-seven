import Exp7Lean.Analytic.EF.HadamardInput

/-!
# Explicit formula blueprint: in-house decomposition of the Hadamard input (fallback)

**Not on the import path of `Main.lean`.**  This file only records the statements into which
H1/H2 of `HadamardInput.lean` decompose if the Tau Ceti library is *not* imported.  See
`BLUEPRINT.md`, section "The Hadamard input", for the proof plan and size estimates.

Route: differentiated Poisson–Jensen formula on discs `|z| < R`, `R → ∞`
(Mathlib: `MeromorphicOn.circleAverage_log_norm` and the Poisson–Jensen formula in
`Mathlib/Analysis/Complex/JensenFormula.lean`; the Schwarz/Herglotz kernel calculus
`hasDerivAt_circleAverage_herglotzRieszKernel_smul` in `Mathlib/Analysis/Complex/Poisson.lean`)
instead of canonical products.
-/

namespace Exp7.EF.Fallback

open Complex

variable {N : ℕ} [NeZero N]

/-- The entire completion `ξ_χ(s) = N^{s/2} Λ(s, χ)` (so that `ξ_χ(1-s) = W(χ) ξ_{χ⁻¹}(s)`). -/
noncomputable def xi (χ : DirichletCharacter ℂ N) (s : ℂ) : ℂ :=
  (N : ℂ) ^ (s / 2) * χ.completedLFunction s

/-- **HF1** (XL, pure complex analysis). Hadamard's partial fractions for an entire function with
`F 0 ≠ 0` and `log ‖F z‖ ≤ C (1+‖z‖) log (2+‖z‖)`: the zeros satisfy `∑ m_ρ/(1+|ρ|²) < ∞` and
`F'/F(s) = F'/F(0) + ∑_ρ m_ρ (1/(s-ρ) + 1/ρ)` (absolutely convergent) off the zeros.

Plan: (i) Jensen (`AnalyticOnNhd.circleAverage_log_norm`) gives `n(R) ≤ C' R log R`, hence the
summability; (ii) differentiate the Poisson–Jensen representation of `log ‖F‖` on `|z| < R` to get
`F'/F(s) - F'/F(0) = ∑_{|ρ|<R} m_ρ (1/(s-ρ) + 1/ρ) + E_R(s)` with
`|E_R(s)| ≤ C'' |s| (log R)/R` for `R ≥ 2|s|` (uses only the *upper* bound on `log ‖F‖` and Jensen
for `∫ |log ‖F‖|`); (iii) let `R → ∞`. -/
theorem logDeriv_eq_add_tsum_of_order_one {F : ℂ → ℂ} (hF : Differentiable ℂ F) (h0 : F 0 ≠ 0)
    (hgrowth : ∃ C : ℝ, ∀ z : ℂ, ‖F z‖ ≤ Real.exp (C * (1 + ‖z‖) * Real.log (2 + ‖z‖))) :
    Summable (fun ρ : ℂ ↦ (analyticOrderNatAt F ρ : ℝ) / (1 + ‖ρ‖ ^ 2)) ∧
    (∀ s : ℂ, Summable (fun ρ : ℂ ↦ ‖(analyticOrderNatAt F ρ : ℂ) * (1 / (s - ρ) + 1 / ρ)‖)) ∧
    ∀ s : ℂ, F s ≠ 0 →
      logDeriv F s = logDeriv F 0 +
        ∑' ρ : ℂ, (analyticOrderNatAt F ρ : ℂ) * (1 / (s - ρ) + 1 / ρ) := by
  sorry

/-- **HF2** (L). `ξ_χ` has order at most one. For `Re s ≥ 1/2`: `‖L(s,χ)‖ ≤ C N ‖s‖` (partial
summation, cf. `LSeries_eq_mul_integral` in `Mathlib/NumberTheory/LSeries/SumCoeff.lean`),
`‖Γ(z)‖ ≤ Γ(Re z) ≤ exp (C |z| log |z|)`; for `Re s ≤ 1/2` use the functional equation
`IsPrimitive.completedLFunction_one_sub` and `norm_rootNumber`. -/
theorem xi_growth (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) (hne : χ ≠ 1) :
    ∃ C : ℝ, ∀ z : ℂ, ‖xi χ z‖ ≤ Real.exp (C * (1 + ‖z‖) * Real.log (2 + ‖z‖)) := by
  sorry

/-- **HF3** (S). `ξ_χ` is entire and does not vanish at `0`
(`differentiable_completedLFunction`; `Λ(0,χ) = W Λ(1,χ⁻¹) ≠ 0`). -/
theorem xi_differentiable_and_ne_zero (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive)
    (hne : χ ≠ 1) : Differentiable ℂ (xi χ) ∧ xi χ 0 ≠ 0 := by
  sorry

/-- **HF4** (M). Functional equation for the logarithmic derivative, valid at every `s`. -/
theorem logDeriv_xi_one_sub (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) (hne : χ ≠ 1)
    (s : ℂ) :
    logDeriv (xi χ) (1 - s) = -logDeriv (xi χ⁻¹) s := by
  sorry

/-- **HF5** (M). Symmetry of the zeros with multiplicity under `ρ ↦ 1 - conj ρ`
(functional equation composed with complex conjugation `Λ(conj s, χ⁻¹) = conj Λ(s, χ)`). -/
theorem analyticOrderNatAt_xi_one_sub_conj (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive)
    (hne : χ ≠ 1) (ρ : ℂ) :
    analyticOrderNatAt (xi χ) (1 - (starRingEnd ℂ) ρ) = analyticOrderNatAt (xi χ) ρ := by
  sorry

/- **HF6** (L): H1 and H2 of `HadamardInput.lean` from HF1–HF5.
`Re B(χ) = -∑ m_ρ Re (1/ρ)` by pairing `ρ ↔ 1 - conj ρ` (HF4 at `s = 0, 1`, HF5), then take real
parts in HF1; `logDeriv (xi χ) = ½ log N + logDeriv gammaFactor + logDeriv LFunction` on `Re s > 0`
off the zeros; the multiplicities of `xi χ` and of `completedLFunction χ` agree. -/

end Exp7.EF.Fallback
