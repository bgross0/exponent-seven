import Exp7Lean.Analytic.EF.HadamardHF1Poisson
import Exp7Lean.Analytic.EF.HadamardHF1Boundary

/-!
# HF1: Hadamard's partial fractions for entire functions of order ≤ 1

`Exp7.EF.HF1.logDeriv_eq_add_tsum_of_order_one` has verbatim the statement of leaf **HF1**
(`Exp7.EF.Fallback.logDeriv_eq_add_tsum_of_order_one` in `HadamardFallback.lean`) and is proved
here, without `sorry` (`#print axioms`: `propext`, `Classical.choice`, `Quot.sound`), from

* `HadamardHF1Counting.lean` (Jensen zero counting, convergence exponent),
* `HadamardHF1Poisson.lean` (differentiated Poisson–Jensen formula on a disc),
* `HadamardHF1Boundary.lean` (error terms).

See `HADAMARD_BLUEPRINT.md`.  This file does not import `HadamardFallback.lean`, so that file can
later import this one and close HF1 by `exact Exp7.EF.HF1.logDeriv_eq_add_tsum_of_order_one ..`.

Proof.  Let `m ρ = analyticOrderNatAt F ρ` and `S R` the finite set of zeros in `‖ρ‖ < R`.
Subtracting the differentiated Poisson–Jensen formula (P1) at `w = 0` from the one at `w = s`
(same radius `R ≥ 2‖s‖ + 1`):

`F'/F(s) - F'/F(0) - ∑_{ρ ∈ S R} m ρ (1/(s-ρ) + 1/ρ)
   = [I_R(s) - I_R(0)] + ∑_{ρ ∈ S R} m ρ (ρ̄/(R² - ρ̄ s) - ρ̄/R²)`,

and both terms on the right are `O(‖s‖ log (2+R) / R)` by B1, B2', B3 and the counting bound J1.
Let `R → ∞`; the finite sums converge to the `tsum` by absolute convergence (J2, J3).
-/

namespace Exp7.EF.HF1

open Complex Filter Topology Metric
open scoped ComplexConjugate

/-- **T1** (proved). Partial sums of a summable family over an exhaustion `S R` of its support by
"balls" converge to the `tsum`. -/
theorem tendsto_sum_of_exhaustion {g : ℂ → ℂ} (hg : Summable g) (S : ℝ → Finset ℂ)
    (hS : ∀ R ρ, ‖ρ‖ < R → ρ ∉ S R → g ρ = 0) :
    Tendsto (fun R ↦ ∑ ρ ∈ S R, g ρ) atTop (𝓝 (∑' ρ, g ρ)) := by
  classical
  have h : Tendsto (fun T : Finset ℂ ↦ ∑ ρ ∈ T, g ρ) atTop (𝓝 (∑' ρ, g ρ)) := hg.hasSum
  rw [Metric.tendsto_atTop] at h ⊢
  intro ε hε
  obtain ⟨T₀, hT₀⟩ := h ε hε
  refine ⟨1 + ∑ ρ ∈ T₀, ‖ρ‖, fun R hR ↦ ?_⟩
  have hsub : ∑ ρ ∈ S R, g ρ = ∑ ρ ∈ S R ∪ T₀, g ρ := by
    refine Finset.sum_subset Finset.subset_union_left fun x hx hxS ↦ ?_
    have hxT : x ∈ T₀ := by
      rcases Finset.mem_union.mp hx with h | h
      · exact absurd h hxS
      · exact h
    have hle : ‖x‖ ≤ ∑ ρ ∈ T₀, ‖ρ‖ :=
      Finset.single_le_sum (f := fun ρ : ℂ ↦ ‖ρ‖) (fun ρ _ ↦ norm_nonneg ρ) hxT
    exact hS R x (by linarith) hxS
  rw [hsub]
  exact hT₀ _ Finset.subset_union_right

/-- **HF1** (proved, no `sorry`). Hadamard's partial fractions for an entire function with
`F 0 ≠ 0` and `log ‖F z‖ ≤ C (1+‖z‖) log (2+‖z‖)`.  Verbatim the statement of
`Exp7.EF.Fallback.logDeriv_eq_add_tsum_of_order_one`. -/
theorem logDeriv_eq_add_tsum_of_order_one {F : ℂ → ℂ} (hF : Differentiable ℂ F) (h0 : F 0 ≠ 0)
    (hgrowth : ∃ C : ℝ, ∀ z : ℂ, ‖F z‖ ≤ Real.exp (C * (1 + ‖z‖) * Real.log (2 + ‖z‖))) :
    Summable (fun ρ : ℂ ↦ (analyticOrderNatAt F ρ : ℝ) / (1 + ‖ρ‖ ^ 2)) ∧
    (∀ s : ℂ, Summable (fun ρ : ℂ ↦ ‖(analyticOrderNatAt F ρ : ℂ) * (1 / (s - ρ) + 1 / ρ)‖)) ∧
    ∀ s : ℂ, F s ≠ 0 →
      logDeriv F s = logDeriv F 0 +
        ∑' ρ : ℂ, (analyticOrderNatAt F ρ : ℂ) * (1 / (s - ρ) + 1 / ρ) := by
  obtain ⟨C, hC⟩ := hgrowth
  obtain ⟨A, hA0, hA⟩ := sum_analyticOrderNatAt_le hF h0 hC
  have hsum := summable_div_one_add_sq_of_count hA
  have habs := fun s ↦ summable_norm_mul_one_div_sub_add hsum s
  refine ⟨hsum, habs, fun s hs ↦ ?_⟩
  obtain ⟨B, hB0, hB⟩ := circleAverage_abs_log_norm_le hF h0 hC
  -- the finite sets of zeros in open balls
  have hfin : ∀ R : ℝ, {ρ : ℂ | analyticOrderNatAt F ρ ≠ 0 ∧ ‖ρ‖ < R}.Finite := fun R ↦
    (finite_setOf_ne_zero_norm_le hsum R).subset fun ρ hρ ↦ ⟨hρ.1, hρ.2.le⟩
  let S : ℝ → Finset ℂ := fun R ↦ (hfin R).toFinset
  have hS : ∀ R ρ, ρ ∈ S R ↔ ‖ρ‖ < R ∧ F ρ = 0 := by
    intro R ρ
    simp only [S, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
    rw [analyticOrderNatAt_ne_zero_iff hF h0 ρ, and_comm]
  set g : ℂ → ℂ := fun ρ ↦ (analyticOrderNatAt F ρ : ℂ) * (1 / (s - ρ) + 1 / ρ) with hg
  have hgsum : Summable g := (habs s).of_norm
  -- partial sums over balls converge to the `tsum`
  have hlim1 : Tendsto (fun R ↦ ∑ ρ ∈ S R, g ρ) atTop (𝓝 (∑' ρ, g ρ)) := by
    refine tendsto_sum_of_exhaustion hgsum S fun R ρ hρR hρS ↦ ?_
    have h : analyticOrderNatAt F ρ = 0 := by
      by_contra h
      exact hρS ((hS R ρ).mpr ⟨hρR, (analyticOrderNatAt_ne_zero_iff hF h0 ρ).mp h⟩)
    simp [hg, h]
  -- the error estimate at radius `R`
  have hest : ∀ R : ℝ, 1 ≤ R → 2 * ‖s‖ + 1 ≤ R →
      ‖logDeriv F s - logDeriv F 0 - ∑ ρ ∈ S R, g ρ‖
        ≤ (20 * B + 2 * A) * ‖s‖ * (Real.log (2 + R) / R) := by
    intro R hR1 hRs
    have hs0 : 0 ≤ ‖s‖ := norm_nonneg s
    have hR : 0 < R := by linarith
    have hs2 : 2 * ‖s‖ ≤ R := by linarith
    have hsR : ‖s‖ < R := by linarith
    have h0R : ‖(0 : ℂ)‖ < R := by simpa using hR
    have e1 := logDeriv_eq_circleAverage_add_sum hF hR (hS R) hsR hs
    have e2 := logDeriv_eq_circleAverage_add_sum hF hR (hS R) h0R h0
    have hu : CircleIntegrable (fun ζ ↦ Real.log ‖F ζ‖) 0 R :=
      MeromorphicOn.circleIntegrable_log_norm fun z _ ↦ (hF.analyticAt z).meromorphicAt
    have b1 := norm_circleAverage_kernel_sub_le hR hu hs2
    have b2 : ‖∑ ρ ∈ S R, (analyticOrderNatAt F ρ : ℂ) *
        (conj ρ / ((R : ℂ) ^ 2 - conj ρ * s) - conj ρ / ((R : ℂ) ^ 2 - conj ρ * 0))‖
          ≤ 2 * ‖s‖ / R ^ 2 * (A * R * Real.log (2 + R)) := by
      calc ‖∑ ρ ∈ S R, (analyticOrderNatAt F ρ : ℂ) *
            (conj ρ / ((R : ℂ) ^ 2 - conj ρ * s) - conj ρ / ((R : ℂ) ^ 2 - conj ρ * 0))‖
          ≤ ∑ ρ ∈ S R, ‖(analyticOrderNatAt F ρ : ℂ) *
            (conj ρ / ((R : ℂ) ^ 2 - conj ρ * s) - conj ρ / ((R : ℂ) ^ 2 - conj ρ * 0))‖ :=
            norm_sum_le _ _
        _ ≤ ∑ ρ ∈ S R, (analyticOrderNatAt F ρ : ℝ) * (2 * ‖s‖ / R ^ 2) := by
            refine Finset.sum_le_sum fun ρ hρ ↦ ?_
            rw [norm_mul, Complex.norm_natCast]
            gcongr
            exact norm_reflected_sub_le hR ((hS R ρ).mp hρ).1.le hs2
        _ = 2 * ‖s‖ / R ^ 2 * ∑ ρ ∈ S R, (analyticOrderNatAt F ρ : ℝ) := by
            rw [← Finset.sum_mul, mul_comm]
        _ ≤ 2 * ‖s‖ / R ^ 2 * (A * R * Real.log (2 + R)) := by
            gcongr
            exact hA R hR1 (S R) fun ρ hρ ↦ ((hS R ρ).mp hρ).1.le
    have hterm : ∑ ρ ∈ S R, (analyticOrderNatAt F ρ : ℂ) *
        (conj ρ / ((R : ℂ) ^ 2 - conj ρ * s) - conj ρ / ((R : ℂ) ^ 2 - conj ρ * 0))
        = ∑ ρ ∈ S R, (analyticOrderNatAt F ρ : ℂ) *
            (1 / (s - ρ) + conj ρ / ((R : ℂ) ^ 2 - conj ρ * s))
          - ∑ ρ ∈ S R, (analyticOrderNatAt F ρ : ℂ) *
            (1 / (0 - ρ) + conj ρ / ((R : ℂ) ^ 2 - conj ρ * 0))
          - ∑ ρ ∈ S R, g ρ := by
      rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun ρ _ ↦ ?_
      simp only [hg, zero_sub, one_div, inv_neg]
      ring
    have hdecomp : logDeriv F s - logDeriv F 0 - ∑ ρ ∈ S R, g ρ =
        (Real.circleAverage (fun ζ ↦ (2 * ζ / (ζ - s) ^ 2) • ((Real.log ‖F ζ‖ : ℝ) : ℂ)) 0 R
          - Real.circleAverage (fun ζ ↦ (2 * ζ / (ζ - 0) ^ 2) • ((Real.log ‖F ζ‖ : ℝ) : ℂ)) 0 R)
        + ∑ ρ ∈ S R, (analyticOrderNatAt F ρ : ℂ) *
            (conj ρ / ((R : ℂ) ^ 2 - conj ρ * s) - conj ρ / ((R : ℂ) ^ 2 - conj ρ * 0)) := by
      rw [hterm, e1, e2]
      ring
    rw [hdecomp]
    calc ‖_ + _‖ ≤ ‖_‖ + ‖_‖ := norm_add_le _ _
      _ ≤ 20 * ‖s‖ / R ^ 2 * Real.circleAverage (fun ζ ↦ |Real.log ‖F ζ‖|) 0 R
          + 2 * ‖s‖ / R ^ 2 * (A * R * Real.log (2 + R)) := add_le_add b1 b2
      _ ≤ 20 * ‖s‖ / R ^ 2 * (B * R * Real.log (2 + R))
          + 2 * ‖s‖ / R ^ 2 * (A * R * Real.log (2 + R)) := by
          gcongr
          exact hB R hR1
      _ = (20 * B + 2 * A) * ‖s‖ * (Real.log (2 + R) / R) := by
          field_simp
  -- the error bound tends to zero
  have hlog : Tendsto (fun R : ℝ ↦ (20 * B + 2 * A) * ‖s‖ * (Real.log (2 + R) / R)) atTop
      (𝓝 0) := by
    have h1 : Tendsto (fun R : ℝ ↦ Real.log (2 + R) / R) atTop (𝓝 0) := by
      have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 (-2) 1 one_ne_zero).comp
        (tendsto_atTop_add_const_left atTop (2 : ℝ) tendsto_id)
      refine h.congr fun R ↦ ?_
      simp
    simpa using h1.const_mul ((20 * B + 2 * A) * ‖s‖)
  have hlim2 : Tendsto (fun R ↦ logDeriv F s - logDeriv F 0 - ∑ ρ ∈ S R, g ρ) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hlog
    filter_upwards [eventually_ge_atTop (1 : ℝ), eventually_ge_atTop (2 * ‖s‖ + 1)] with R h1 h2
      using hest R h1 h2
  have hlim3 : Tendsto (fun _ : ℝ ↦ logDeriv F s - logDeriv F 0) atTop
      (𝓝 (0 + ∑' ρ, g ρ)) := by
    refine (hlim2.add hlim1).congr fun R ↦ ?_
    ring
  have hfinal := tendsto_nhds_unique tendsto_const_nhds hlim3
  rw [zero_add] at hfinal
  rw [← hfinal]
  ring

end Exp7.EF.HF1

