import Exp7Lean.Frontier.Pointwise
import Exp7Lean.Analytic.EF.Pairing

/-!
# The unconditional damped explicit formula

This proves the identity in the half-plane of absolute convergence. Each zero
retains its real part, and the integral/sum exchange is proved using the
existing weighted zero density and a uniform Poisson bound. Continuing to
zero damping for the smoothed entire kernel remains a separate obligation.
-/

namespace Exp7.Frontier

open Real MeasureTheory Complex Exp7.EF

noncomputable def offLineZeroSideR (q : ℕ) [Fact q.Prime] (h : ℝ → ℝ) (δ : ℝ) : ℝ :=
  ∑' ρ : ℂ, (mult q ρ : ℝ) *
    (1 / π * ∫ t : ℝ, h t * poissonKer (1 / 2 + δ - ρ.re) (t - ρ.im))

variable (q : ℕ) [Fact q.Prime] {f h : ℝ → ℝ}

/-- The bound is uniform over the horizontal positions of all nontrivial zeros. -/
theorem offLine_poisson_bound {L : ℝ} (hq : q % 4 = 3)
    (hf : WeilAdmissible f L h) {δ : ℝ} (hδ : 1 / 2 < δ) :
    ∃ C : ℝ, ∀ ρ : ℂ, mult q ρ ≠ 0 →
      Integrable (fun t : ℝ ↦ h t * poissonKer (1 / 2 + δ - ρ.re) (t - ρ.im)) ∧
      ∫ t : ℝ, h t * poissonKer (1 / 2 + δ - ρ.re) (t - ρ.im) ≤ C / (1 + ρ.im ^ 2) := by
  obtain ⟨C, hC⟩ := hf.exists_poisson_bound
    (a := δ - 1 / 2) (b := δ + 1 / 2) (by linarith)
  refine ⟨C, fun ρ hm ↦ ?_⟩
  obtain ⟨h0, h1, -⟩ := mult_ne_zero_imp q hq hm
  let w := 1 / 2 + δ - ρ.re
  have hw : 0 < w := by dsimp [w]; linarith
  have hwa : δ - 1 / 2 ≤ (w : ℂ).re := by
    simp only [ofReal_re]
    dsimp [w]
    linarith
  have hwb : ‖(w : ℂ)‖ ≤ δ + 1 / 2 := by
    rw [Complex.norm_real, Real.norm_of_nonneg hw.le]
    dsimp [w]
    linarith
  obtain ⟨hint, hle⟩ := hC (w : ℂ) hwa hwb ρ.im
  have key : ∀ t : ℝ, (w : ℂ) / ((w : ℂ) ^ 2 + ((t - ρ.im : ℝ) : ℂ) ^ 2) =
      ((poissonKer w (t - ρ.im) : ℝ) : ℂ) := by
    intro t
    simp [poissonKer]
  have hpos : ∀ t : ℝ, 0 ≤ poissonKer w (t - ρ.im) := by
    intro t
    unfold poissonKer
    positivity
  constructor
  · refine hint.re.congr (Filter.Eventually.of_forall fun t ↦ ?_)
    simp only [key, ← Complex.ofReal_mul]
    rfl
  · simpa only [key, Complex.norm_real, Real.norm_of_nonneg (hpos _)] using hle

/-- The exchange of the zero sum and real integral, without a critical-line hypothesis. -/
theorem integral_h_mul_offLineZerosKernel {L : ℝ} (hq : q % 4 = 3)
    (hf : WeilAdmissible f L h) {δ : ℝ}
    (hδ : 1 / 2 < δ) :
    Integrable (fun t ↦ h t * offLineZerosKernel q δ t) ∧
      ∫ t, h t * offLineZerosKernel q δ t = π * offLineZeroSideR q h δ := by
  classical
  -- the countable support of `mult q`
  have hL2c := summable_mult_div q hq
  set S : Set ℂ := Function.support (fun ρ : ℂ ↦ (mult q ρ : ℝ) / (1 + ρ.im ^ 2)) with hS
  have : Countable S := hL2c.countable_support.to_subtype
  have hzero : ∀ ρ : ℂ, ρ ∉ S → (mult q ρ : ℝ) = 0 := by
    intro ρ hρ
    have h1 : (mult q ρ : ℝ) / (1 + ρ.im ^ 2) = 0 := by
      by_contra hne
      exact hρ hne
    have h2 : (1 + ρ.im ^ 2 : ℝ) ≠ 0 := by positivity
    exact (div_eq_zero_iff.mp h1).resolve_right h2
  have hm : ∀ ρ : S, mult q ρ ≠ 0 := by
    intro ρ hn
    have hp := ρ.property
    change (mult q ρ : ℝ) / (1 + (ρ : ℂ).im ^ 2) ≠ 0 at hp
    simp [hn] at hp
  obtain ⟨C, hC⟩ := offLine_poisson_bound q hq hf hδ
  -- the family of nonnegative terms
  let G : S → ℝ → ℝ := fun ρ t ↦ h t * ((mult q ρ : ℝ) *
    poissonKer (1 / 2 + δ - (ρ : ℂ).re) (t - (ρ : ℂ).im))
  have hG_int : ∀ ρ, Integrable (G ρ) := fun ρ ↦ by
    have hc := ((hC (ρ : ℂ) (hm ρ)).1).const_mul (mult q ρ : ℝ)
    refine hc.congr (Filter.Eventually.of_forall fun t ↦ ?_)
    simp only [G]
    ring
  have hG_nonneg : ∀ ρ t, 0 ≤ G ρ t := fun ρ t ↦
    mul_nonneg (hf.nonneg t) (mul_nonneg (Nat.cast_nonneg _) (by
      have hz := (mult_ne_zero_imp q hq (hm ρ)).2.1
      have hw : 0 < 1 / 2 + δ - (ρ : ℂ).re := by linarith
      unfold poissonKer
      positivity))
  have hG_eq : ∀ ρ : S, ∫ t, G ρ t
      = (mult q ρ : ℝ) *
        ∫ t, h t * poissonKer (1 / 2 + δ - (ρ : ℂ).re) (t - (ρ : ℂ).im) := fun ρ ↦ by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t ↦ ?_)
    simp only [G]
    ring
  have hG_sum : Summable fun ρ : S ↦ ∫ t, G ρ t := by
    have hbig : Summable fun ρ : S ↦ C * ((mult q ρ : ℝ) / (1 + (ρ : ℂ).im ^ 2)) :=
      (hL2c.mul_left C).comp_injective Subtype.coe_injective
    refine Summable.of_nonneg_of_le (fun ρ ↦ integral_nonneg (hG_nonneg ρ)) (fun ρ ↦ ?_) hbig
    rw [hG_eq]
    calc (mult q ρ : ℝ) * ∫ t, h t * poissonKer (1 / 2 + δ - (ρ : ℂ).re) (t - (ρ : ℂ).im)
        ≤ (mult q ρ : ℝ) * (C / (1 + (ρ : ℂ).im ^ 2)) :=
          mul_le_mul_of_nonneg_left (hC (ρ : ℂ) (hm ρ)).2 (Nat.cast_nonneg _)
      _ = C * ((mult q ρ : ℝ) / (1 + (ρ : ℂ).im ^ 2)) := by ring
  obtain ⟨hint, hval⟩ := i3_integrable_tsum_of_nonneg hG_int hG_nonneg hG_sum
  have hfun : (fun t ↦ h t * offLineZerosKernel q δ t) = fun t ↦ ∑' ρ : S, G ρ t := by
    funext t
    unfold offLineZerosKernel
    have hsub : Function.support (fun ρ : ℂ ↦ (mult q ρ : ℝ) *
        poissonKer (1 / 2 + δ - ρ.re) (t - ρ.im)) ⊆ S := by
      intro ρ hρ
      by_contra hn
      exact hρ (by simp [hzero ρ hn])
    rw [← tsum_subtype_eq_of_support_subset hsub, ← tsum_mul_left]
  rw [hfun]
  refine ⟨hint, ?_⟩
  rw [hval]
  unfold offLineZeroSideR
  have hsub : Function.support
      (fun ρ : ℂ ↦ (mult q ρ : ℝ) *
        (1 / π * ∫ t : ℝ, h t * poissonKer (1 / 2 + δ - ρ.re) (t - ρ.im))) ⊆ S := by
    intro ρ hρ
    by_contra hn
    exact hρ (by simp [hzero ρ hn])
  rw [← tsum_subtype_eq_of_support_subset hsub, ← tsum_mul_left]
  refine tsum_congr fun ρ ↦ ?_
  rw [hG_eq]
  field_simp

variable {X : ℕ}

/-- Unconditional integrated identity for every existing Weil-admissible test function. -/
theorem offLineZeroSideR_eq_arithSideR_of_half_lt (hq : q % 4 = 3)
    (hf : WeilAdmissible f (Real.log X) h) {δ : ℝ} (hδ : 1 / 2 < δ) :
    offLineZeroSideR q h δ = arithSideR q f X δ := by
  have hδ0 : 0 < δ := by linarith
  obtain ⟨-, hZ⟩ := integral_h_mul_offLineZerosKernel q hq hf hδ
  obtain ⟨hDi, hD⟩ := integral_h_mul_dirichletR q hf hδ
  obtain ⟨hGi, hG⟩ := integral_h_mul_re_digamma hf hδ0.le
  have hhi := hf.integrable
  have hh := hf.integral_eq
  have key : ∫ t, h t * offLineZerosKernel q δ t =
      ∫ t, (Real.log (q / π) / 2 * h t
        + 1 / 2 * (h t * (digamma (((3 / 4 + δ / 2 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * I)).re)
        - h t * dirichletR q δ t) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun t ↦ ?_)
    simp only
    rw [← pointwise_identity_unconditional q hq hδ t]
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
  have h2 : π * offLineZeroSideR q h δ = π * arithSideR q f X δ := by
    rw [key, arithSideR]; ring
  exact mul_left_cancel₀ hπ h2

end Exp7.Frontier
