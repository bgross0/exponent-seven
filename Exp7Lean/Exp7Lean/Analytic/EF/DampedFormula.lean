import Exp7Lean.Analytic.EF.Pointwise
import Exp7Lean.Analytic.EF.Pairing

/-!
# Explicit formula blueprint: the damped explicit formula for `δ > 1/2`

Node **C1** of `BLUEPRINT.md`, *proved* from P0 and I1–I3, A1, A2.
-/

namespace Exp7.EF

open Real MeasureTheory Complex

variable (q : ℕ) [Fact q.Prime] {f h : ℝ → ℝ} {X : ℕ}

/-- **C1** (proved from P0, I1, I2, I3, A1, A2). The damped explicit formula in the region of
absolute convergence: under GRH, for `δ > 1/2`,
`∑_ρ m(ρ) (1/π) ∫ h(t) δ/(δ²+(t-Im ρ)²) dt
   = log(q/π) + ψ(3/4+δ/2) + ∫₀^∞ 2e^{-(3/2+δ)u}/(1-e^{-2u}) (1-f u) du
     - 2 ∑_{n<X} Λ(n)χ(n) f(log n) n^{-1/2-δ}`. -/
theorem zeroSideR_eq_arithSideR_of_half_lt (hq : q % 4 = 3) (hGRH : GRHFor q)
    (hf : WeilAdmissible f (Real.log X) h) {δ : ℝ} (hδ : 1 / 2 < δ) :
    zeroSideR q h δ = arithSideR q f X δ := by
  have hδ0 : 0 < δ := by linarith
  obtain ⟨-, hZ⟩ := integral_h_mul_zerosKer q hq hf hδ0
  obtain ⟨hDi, hD⟩ := integral_h_mul_dirichletR q hf hδ
  obtain ⟨hGi, hG⟩ := integral_h_mul_re_digamma hf hδ0.le
  have hhi := hf.integrable
  have hh := hf.integral_eq
  have key : ∫ t, h t * zerosKer q δ t =
      ∫ t, (Real.log (q / π) / 2 * h t
        + 1 / 2 * (h t * (digamma (((3 / 4 + δ / 2 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * I)).re)
        - h t * dirichletR q δ t) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun t ↦ ?_)
    simp only
    rw [← pointwise_identity q hq hGRH hδ t]
    ring
  have i1 : Integrable (fun t ↦ Real.log (q / π) / 2 * h t) := hhi.const_mul _
  have i2 : Integrable (fun t : ℝ ↦
      1 / 2 * (h t * (digamma (((3 / 4 + δ / 2 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * I)).re)) :=
    hGi.const_mul _
  have i12 : Integrable (fun t : ℝ ↦ Real.log (q / π) / 2 * h t
      + 1 / 2 * (h t * (digamma (((3 / 4 + δ / 2 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * I)).re)) :=
    i1.add i2
  rw [integral_sub i12 hDi, integral_add i1 i2, integral_const_mul, integral_const_mul,
    hh, hG, hD, hZ] at key
  have hπ : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  have h2 : π * zeroSideR q h δ = π * arithSideR q f X δ := by
    rw [key, arithSideR]; ring
  exact mul_left_cancel₀ hπ h2

end Exp7.EF
