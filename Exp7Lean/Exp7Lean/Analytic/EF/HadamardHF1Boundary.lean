import Exp7Lean.Analytic.EF.HadamardHF1Counting

/-!
# HF1, part 3: the error terms of the differentiated Poisson–Jensen formula

Nodes **B1, B2, B2', B3** of `HADAMARD_BLUEPRINT.md`, all proved (no `sorry`).  Pure complex
analysis; this file must not import `HadamardFallback.lean`.

In `logDeriv_eq_circleAverage_add_sum` (P1) taken at `w = s` and at `w = 0` with the same radius
`R ≥ 2‖s‖`, the difference of the two boundary integrals and the difference of the two "reflected"
sums are both `O(‖s‖ log R / R)`:

* `circleAverage_abs_log_norm_le` (B1): `(1/2π) ∫ |log ‖F(Re^{iθ})‖| dθ ≤ A R log (2 + R)`;
* `norm_kernel_sub_le` (B2): `‖2ζ/(ζ-w)² - 2ζ/ζ²‖ ≤ 20‖w‖/R²` on `‖ζ‖ = R ≥ 2‖w‖`;
* `norm_circleAverage_kernel_sub_le` (B2'): hence the bound for the difference of the integrals;
* `norm_reflected_sub_le` (B3): `‖ρ̄/(R² - ρ̄ w) - ρ̄/R²‖ ≤ 2‖w‖/R²` for `‖ρ‖ ≤ R`, `2‖w‖ ≤ R`.
-/

namespace Exp7.EF.HF1

open Complex Filter Topology Metric
open scoped ComplexConjugate

/-! ## B1: the mean of `|log ‖F‖|` on circles -/

/-- **B1** (proved). For an entire function of order ≤ 1 with `F 0 ≠ 0`, the circle mean of
`|log ‖F‖|` is `O(R log R)`.

Proof sketch: `|x| = 2 max x 0 - x`.  The mean of `max (log ‖F‖) 0` is at most
`max C 0 * (1 + R) * log (2 + R)` by the growth bound (`Real.circleAverage_mono_on_of_le_circle`).
The mean of `log ‖F‖` is at least `log ‖F 0‖` by Jensen's formula
`AnalyticOnNhd.circleAverage_log_norm` (every term `divisor · log (R ‖u‖⁻¹)` of the `finsum` is
nonnegative: `AnalyticOnNhd.divisor_nonneg`, and `‖u‖ ≤ R` on the support).  Circle integrability
of `log ‖F ·‖` is `MeromorphicOn.circleIntegrable_log_norm`. -/
theorem circleAverage_abs_log_norm_le {F : ℂ → ℂ} (hF : Differentiable ℂ F) (h0 : F 0 ≠ 0)
    {C : ℝ} (hgrowth : ∀ z : ℂ, ‖F z‖ ≤ Real.exp (C * (1 + ‖z‖) * Real.log (2 + ‖z‖))) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ R : ℝ, 1 ≤ R →
      Real.circleAverage (fun ζ ↦ |Real.log ‖F ζ‖|) 0 R ≤ A * R * Real.log (2 + R) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  set C' := max C 0 with hC'
  have hC'0 : 0 ≤ C' := le_max_right _ _
  set L0 := |Real.log ‖F 0‖| with hL0
  have hL00 : 0 ≤ L0 := abs_nonneg _
  refine ⟨4 * C' + L0 / Real.log 2, by positivity, fun R hR1 ↦ ?_⟩
  have hR : 0 < R := by linarith
  have hlogR : Real.log 2 ≤ Real.log (2 + R) := Real.log_le_log (by norm_num) (by linarith)
  have hlogR0 : 0 < Real.log (2 + R) := lt_of_lt_of_le hlog2 hlogR
  set K := C' * (1 + R) * Real.log (2 + R) with hK
  have hK0 : 0 ≤ K := by positivity
  have hu : CircleIntegrable (fun ζ ↦ Real.log ‖F ζ‖) 0 R :=
    MeromorphicOn.circleIntegrable_log_norm fun z _ ↦ (hF.analyticAt z).meromorphicAt
  have huabs : CircleIntegrable (fun ζ ↦ |Real.log ‖F ζ‖|) 0 R := hu.abs
  -- pointwise: `|u| ≤ 2K - u` because `u ≤ K`
  have hpt : ∀ ζ ∈ sphere (0 : ℂ) |R|, |Real.log ‖F ζ‖| ≤ 2 * K - Real.log ‖F ζ‖ := by
    intro ζ hζ
    rw [mem_sphere_zero_iff_norm, abs_of_pos hR] at hζ
    have hle : Real.log ‖F ζ‖ ≤ K := by
      rcases eq_or_ne (F ζ) 0 with h | h
      · simp [h, hK0]
      · calc Real.log ‖F ζ‖
            ≤ Real.log (Real.exp (C * (1 + ‖ζ‖) * Real.log (2 + ‖ζ‖))) :=
              Real.log_le_log (norm_pos_iff.mpr h) (hgrowth ζ)
          _ = C * (1 + R) * Real.log (2 + R) := by rw [Real.log_exp, hζ]
          _ ≤ K := by
              have : C ≤ C' := le_max_left _ _
              rw [hK]
              gcongr
    rw [abs_le]
    constructor <;> linarith
  -- Jensen: the mean of `log ‖F‖` is at least `log ‖F 0‖`
  have hJ : Real.log ‖F 0‖ ≤ Real.circleAverage (fun ζ ↦ Real.log ‖F ζ‖) 0 R := by
    have han : AnalyticOnNhd ℂ F (closedBall 0 |R|) := fun x _ ↦ hF.analyticAt x
    rw [han.circleAverage_log_norm h0]
    have hnn : 0 ≤ ∑ᶠ u, (MeromorphicOn.divisor F (closedBall 0 |R|) u : ℝ)
        * Real.log (R * ‖(0 : ℂ) - u‖⁻¹) := by
      refine finsum_nonneg fun x ↦ ?_
      by_cases hx : x ∈ closedBall (0 : ℂ) |R|
      · refine mul_nonneg (by exact_mod_cast MeromorphicOn.AnalyticOnNhd.divisor_nonneg han x) ?_
        rcases eq_or_ne x 0 with rfl | hx0
        · simp
        · apply Real.log_nonneg
          rw [mem_closedBall_zero_iff, abs_of_pos hR] at hx
          rw [zero_sub, norm_neg, ← div_eq_mul_inv, one_le_div (norm_pos_iff.mpr hx0)]
          exact hx
      · simp [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hx]
    linarith
  have hconst : CircleIntegrable (fun _ : ℂ ↦ 2 * K) 0 R := circleIntegrable_const _ _ _
  calc Real.circleAverage (fun ζ ↦ |Real.log ‖F ζ‖|) 0 R
      ≤ Real.circleAverage (fun ζ ↦ 2 * K - Real.log ‖F ζ‖) 0 R :=
        Real.circleAverage_mono huabs (hconst.fun_sub hu) hpt
    _ = 2 * K - Real.circleAverage (fun ζ ↦ Real.log ‖F ζ‖) 0 R := by
        rw [Real.circleAverage_fun_sub hconst hu, Real.circleAverage_const]
    _ ≤ 2 * K + L0 := by
        have := neg_le_abs (Real.log ‖F 0‖)
        linarith
    _ ≤ (4 * C' + L0 / Real.log 2) * R * Real.log (2 + R) := by
        have h1 : 2 * K ≤ 4 * C' * (R * Real.log (2 + R)) := by
          rw [hK]
          nlinarith [mul_nonneg hC'0 hlogR0.le]
        have h3 : L0 ≤ L0 / Real.log 2 * (R * Real.log (2 + R)) := by
          rw [div_mul_eq_mul_div, le_div_iff₀ hlog2]
          have : Real.log 2 ≤ R * Real.log (2 + R) := by nlinarith
          exact mul_le_mul_of_nonneg_left this hL00
        nlinarith

/-! ## B2: the kernel difference -/

/-- **B2** (proved). Pointwise bound for the difference of the differentiated Herglotz–Riesz kernels
at `w` and at `0`. -/
theorem norm_kernel_sub_le {R : ℝ} {w ζ : ℂ} (hR : 0 < R) (hζ : ‖ζ‖ = R) (hw : 2 * ‖w‖ ≤ R) :
    ‖2 * ζ / (ζ - w) ^ 2 - 2 * ζ / (ζ - 0) ^ 2‖ ≤ 20 * ‖w‖ / R ^ 2 := by
  have hw0 : 0 ≤ ‖w‖ := norm_nonneg w
  have hζ0 : ζ ≠ 0 := norm_pos_iff.mp (by rw [hζ]; exact hR)
  have hden : R / 2 ≤ ‖ζ - w‖ := by
    have := norm_sub_norm_le ζ w
    linarith
  have hdenpos : 0 < ‖ζ - w‖ := by linarith
  have hden0 : ζ - w ≠ 0 := norm_pos_iff.mp hdenpos
  have heq : 2 * ζ / (ζ - w) ^ 2 - 2 * ζ / (ζ - 0) ^ 2
      = 2 * w * (2 * ζ - w) / (ζ * (ζ - w) ^ 2) := by
    rw [sub_zero]
    field_simp
    ring
  have hnum : ‖2 * ζ - w‖ ≤ 5 * R / 2 := by
    calc ‖2 * ζ - w‖ ≤ ‖2 * ζ‖ + ‖w‖ := norm_sub_le _ _
      _ ≤ 5 * R / 2 := by
        rw [norm_mul, hζ]
        norm_num
        linarith
  have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
  rw [heq, norm_div, norm_mul, norm_mul, norm_mul, norm_pow, hζ, h2,
    div_le_div_iff₀ (by positivity) (by positivity)]
  have h4 : R ^ 2 / 4 ≤ ‖ζ - w‖ ^ 2 := by nlinarith
  calc 2 * ‖w‖ * ‖2 * ζ - w‖ * R ^ 2 ≤ 2 * ‖w‖ * (5 * R / 2) * R ^ 2 := by gcongr
    _ = 20 * ‖w‖ * (R * (R ^ 2 / 4)) := by ring
    _ ≤ 20 * ‖w‖ * (R * ‖ζ - w‖ ^ 2) := by gcongr

/-- **B2'** (proved). The difference of the boundary integrals at `w` and at `0`.

Proof sketch: both integrands are circle integrable (`CircleIntegrable.continuousOn_smul`, the
kernels are continuous on the sphere since `‖w‖ < R`); `Real.circleAverage_fun_sub`,
`Real.norm_circleAverage_le_circleAverage_norm`, then `Real.circleAverage_mono` with
`norm_kernel_sub_le` and `Real.circleAverage_fun_smul`. -/
theorem norm_circleAverage_kernel_sub_le {u : ℂ → ℝ} {R : ℝ} (hR : 0 < R)
    (hu : CircleIntegrable u 0 R) {w : ℂ} (hw : 2 * ‖w‖ ≤ R) :
    ‖Real.circleAverage (fun ζ ↦ (2 * ζ / (ζ - w) ^ 2) • ((u ζ : ℝ) : ℂ)) 0 R
      - Real.circleAverage (fun ζ ↦ (2 * ζ / (ζ - 0) ^ 2) • ((u ζ : ℝ) : ℂ)) 0 R‖
      ≤ 20 * ‖w‖ / R ^ 2 * Real.circleAverage (fun ζ ↦ |u ζ|) 0 R := by
  have hw0 : 0 ≤ ‖w‖ := norm_nonneg w
  have huc : CircleIntegrable (fun ζ ↦ ((u ζ : ℝ) : ℂ)) 0 R := by
    simp only [CircleIntegrable, intervalIntegrable_iff] at hu ⊢
    exact Complex.ofRealCLM.integrable_comp hu
  have hcont : ∀ v : ℂ, ‖v‖ < R →
      ContinuousOn (fun ζ : ℂ ↦ 2 * ζ / (ζ - v) ^ 2) (sphere 0 |R|) := by
    intro v hv
    have hnum : Continuous fun ζ : ℂ ↦ 2 * ζ := continuous_const.mul continuous_id
    have hdn : Continuous fun ζ : ℂ ↦ (ζ - v) ^ 2 := (continuous_id.sub continuous_const).pow 2
    refine hnum.continuousOn.div hdn.continuousOn fun ζ hζ ↦ ?_
    rw [mem_sphere_zero_iff_norm, abs_of_pos hR] at hζ
    refine pow_ne_zero 2 (sub_ne_zero.mpr ?_)
    rintro rfl
    exact hv.ne hζ
  have hi : ∀ v : ℂ, ‖v‖ < R →
      CircleIntegrable (fun ζ ↦ (2 * ζ / (ζ - v) ^ 2) • ((u ζ : ℝ) : ℂ)) 0 R :=
    fun v hv ↦ huc.fun_continuousOn_smul (hcont v hv)
  have hwR : ‖w‖ < R := by linarith
  have h0R : ‖(0 : ℂ)‖ < R := by simpa using hR
  rw [← Real.circleAverage_fun_sub (hi w hwR) (hi 0 h0R)]
  refine (Real.norm_circleAverage_le_circleAverage_norm).trans ?_
  have habs : CircleIntegrable (fun ζ ↦ |u ζ|) 0 R := hu.abs
  rw [← smul_eq_mul, ← Real.circleAverage_fun_smul]
  refine Real.circleAverage_mono ?_ ?_ fun ζ hζ ↦ ?_
  · have h := (hi w hwR).fun_sub (hi 0 h0R)
    rw [circleIntegrable_def] at h ⊢
    exact h.norm
  · exact CircleIntegrable.const_smul (𝕜 := ℝ) (a := 20 * ‖w‖ / R ^ 2) habs
  · rw [mem_sphere_zero_iff_norm, abs_of_pos hR] at hζ
    rw [← sub_smul, norm_smul, Complex.norm_real, Real.norm_eq_abs, smul_eq_mul]
    gcongr
    exact norm_kernel_sub_le hR hζ hw

/-! ## B3: the reflected terms -/

/-- **B3** (proved). Pointwise bound for the difference of the reflected terms at `w` and at `0`. -/
theorem norm_reflected_sub_le {R : ℝ} {w ρ : ℂ} (hR : 0 < R) (hρ : ‖ρ‖ ≤ R) (hw : 2 * ‖w‖ ≤ R) :
    ‖conj ρ / ((R : ℂ) ^ 2 - conj ρ * w) - conj ρ / ((R : ℂ) ^ 2 - conj ρ * 0)‖
      ≤ 2 * ‖w‖ / R ^ 2 := by
  have hw0 : 0 ≤ ‖w‖ := norm_nonneg w
  have hρ0 : 0 ≤ ‖ρ‖ := norm_nonneg ρ
  have hRc : (R : ℂ) ≠ 0 := ofReal_ne_zero.mpr hR.ne'
  have hR2 : ‖(R : ℂ) ^ 2‖ = R ^ 2 := by
    rw [norm_pow, Complex.norm_real, Real.norm_of_nonneg hR.le]
  have hden : R ^ 2 / 2 ≤ ‖(R : ℂ) ^ 2 - conj ρ * w‖ := by
    have h1 : ‖conj ρ * w‖ ≤ R ^ 2 / 2 := by
      rw [norm_mul, RCLike.norm_conj]
      nlinarith
    have := norm_sub_norm_le ((R : ℂ) ^ 2) (conj ρ * w)
    linarith
  have hdenpos : 0 < ‖(R : ℂ) ^ 2 - conj ρ * w‖ := lt_of_lt_of_le (by positivity) hden
  have hden0 : (R : ℂ) ^ 2 - conj ρ * w ≠ 0 := norm_pos_iff.mp hdenpos
  have heq : conj ρ / ((R : ℂ) ^ 2 - conj ρ * w) - conj ρ / ((R : ℂ) ^ 2 - conj ρ * 0)
      = conj ρ ^ 2 * w / ((R : ℂ) ^ 2 * ((R : ℂ) ^ 2 - conj ρ * w)) := by
    rw [mul_zero, sub_zero]
    field_simp
    ring
  rw [heq, norm_div, norm_mul, norm_mul, norm_pow, RCLike.norm_conj, hR2,
    div_le_div_iff₀ (by positivity) (by positivity)]
  have h3 : ‖ρ‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ hρ0 hρ 2
  calc ‖ρ‖ ^ 2 * ‖w‖ * R ^ 2 ≤ R ^ 2 * ‖w‖ * R ^ 2 := by gcongr
    _ = 2 * ‖w‖ * (R ^ 2 * (R ^ 2 / 2)) := by ring
    _ ≤ 2 * ‖w‖ * (R ^ 2 * ‖(R : ℂ) ^ 2 - conj ρ * w‖) := by gcongr

end Exp7.EF.HF1
