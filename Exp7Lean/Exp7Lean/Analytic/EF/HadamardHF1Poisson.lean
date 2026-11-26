import Exp7Lean.Analytic.EF.HadamardHF1Counting

/-!
# HF1, part 2: the differentiated Poisson–Jensen formula on a disc

Nodes **P1a–P1e** and **P1** of `HADAMARD_BLUEPRINT.md`, all proved (no `sorry`).  Pure complex
analysis; this file must not import `HadamardFallback.lean`.

Main statement (`logDeriv_eq_circleAverage_add_sum`, **P1**): for `F` entire, `R > 0`, `S` the
finite set of zeros of `F` in `‖ρ‖ < R`, and `‖w‖ < R` with `F w ≠ 0`,

`F'/F(w) = (1/2π) ∫₀^{2π} 2ζ/(ζ-w)² · log ‖F ζ‖ dθ  +  ∑_{ρ ∈ S} m ρ · (1/(w-ρ) + ρ̄/(R² - ρ̄ w))`,

`ζ = R e^{iθ}`.  It is obtained by "differentiating" Mathlib's Poisson–Jensen formula
`MeromorphicOn.log_norm_meromorphicTrailingCoeffAt` in `w`: both sides are locally real parts of
holomorphic functions (`exists_hasDerivAt_re_eq_log_norm`,
`exists_hasDerivAt_re_eq_poissonIntegral`), and two holomorphic functions whose real parts agree
near `w` have the same derivative at `w` (`eq_of_hasDerivAt_of_re_eventuallyEq`).

Zeros on the circle `‖ρ‖ = R` are allowed (Mathlib's formula handles them), so no choice of
"good radii" is needed.
-/

namespace Exp7.EF.HF1

open Complex Filter Topology Metric
open scoped ComplexConjugate

/-! ## P1a: real parts determine the derivative -/

/-- **P1a** (proved). If two functions are complex differentiable at `w` and their real parts agree
near `w`, their derivatives at `w` agree (Cauchy–Riemann). -/
theorem eq_of_hasDerivAt_of_re_eventuallyEq {g₁ g₂ : ℂ → ℂ} {a b w : ℂ}
    (h₁ : HasDerivAt g₁ a w) (h₂ : HasDerivAt g₂ b w)
    (hre : (fun z ↦ (g₁ z).re) =ᶠ[𝓝 w] fun z ↦ (g₂ z).re) : a = b := by
  have h := (h₁.sub h₂).hasFDerivAt.restrictScalars ℝ
  have hR := Complex.reCLM.hasFDerivAt.comp w h
  have hzero : (Complex.reCLM ∘ (g₁ - g₂)) =ᶠ[𝓝 w] fun _ ↦ (0 : ℝ) := by
    filter_upwards [hre] with z hz
    simp only [Function.comp_apply, Pi.sub_apply, reCLM_apply, sub_re]
    rw [hz, sub_self]
  have h0 : HasFDerivAt (Complex.reCLM ∘ (g₁ - g₂)) (0 : ℂ →L[ℝ] ℝ) w :=
    (hasFDerivAt_const (0 : ℝ) w).congr_of_eventuallyEq hzero
  have huniq := hR.unique h0
  have e1 := DFunLike.congr_fun huniq (1 : ℂ)
  have e2 := DFunLike.congr_fun huniq Complex.I
  simp at e1 e2
  apply sub_eq_zero.mp
  apply Complex.ext
  · simp only [sub_re, zero_re]
    linarith
  · simp only [sub_im, zero_im]
    linarith

/-! ## P1b: local holomorphic logarithm -/

/-- **P1b** (proved). Near a point where `f` is differentiable and nonzero, `log ‖f‖` is the real
part of a function with complex derivative `f'/f` at that point. -/
theorem exists_hasDerivAt_re_eq_log_norm {f : ℂ → ℂ} {w : ℂ} (hf : DifferentiableAt ℂ f w)
    (hw : f w ≠ 0) :
    ∃ g : ℂ → ℂ, HasDerivAt g (logDeriv f w) w ∧ ∀ᶠ z in 𝓝 w, (g z).re = Real.log ‖f z‖ := by
  refine ⟨fun z ↦ Complex.log (f z / f w) + ((Real.log ‖f w‖ : ℝ) : ℂ), ?_, ?_⟩
  · have h1 : HasDerivAt (fun z ↦ f z / f w) (deriv f w / f w) w := hf.hasDerivAt.div_const (f w)
    have h2 := h1.clog (by rw [div_self hw]; exact one_mem_slitPlane)
    have h3 := h2.add_const ((Real.log ‖f w‖ : ℝ) : ℂ)
    convert h3 using 1
    rw [logDeriv_apply, div_self hw, div_one]
  · filter_upwards [hf.continuousAt.eventually_ne hw] with z hz
    rw [add_re, ofReal_re, Complex.log_re, norm_div,
      Real.log_div (norm_ne_zero_iff.mpr hz) (norm_ne_zero_iff.mpr hw)]
    ring

/-! ## P1c: the Poisson integral -/

/-- **P1c** (proved). The Poisson integral of a circle-integrable real function is, inside the disc,
the real part of the Herglotz–Riesz integral, whose derivative is the integral against
`2ζ/(ζ-w)²` (`hasDerivAt_circleAverage_herglotzRieszKernel_smul`). -/
theorem exists_hasDerivAt_re_eq_poissonIntegral {u : ℂ → ℝ} {R : ℝ} (hR : 0 < R)
    (hu : CircleIntegrable u 0 R) {w : ℂ} (hw : ‖w‖ < R) :
    ∃ g : ℂ → ℂ,
      HasDerivAt g (Real.circleAverage (fun ζ ↦ (2 * ζ / (ζ - w) ^ 2) • ((u ζ : ℝ) : ℂ)) 0 R) w ∧
      ∀ᶠ z in 𝓝 w, (g z).re = Real.circleAverage (poissonKernel 0 z • u) 0 R := by
  have huc : CircleIntegrable (fun ζ ↦ ((u ζ : ℝ) : ℂ)) 0 R := by
    simp only [CircleIntegrable, intervalIntegrable_iff] at hu ⊢
    exact Complex.ofRealCLM.integrable_comp hu
  have hsph : ∀ z : ℂ, ‖z‖ < R → z ∉ sphere (0 : ℂ) |R| := by
    intro z hz hmem
    rw [mem_sphere_zero_iff_norm, abs_of_pos hR] at hmem
    exact hz.ne hmem
  refine ⟨fun z ↦ Real.circleAverage (fun ζ ↦ herglotzRieszKernel 0 z ζ • ((u ζ : ℝ) : ℂ)) 0 R,
    hasDerivAt_circleAverage_herglotzRieszKernel_smul huc (hsph w hw), ?_⟩
  have hev : ∀ᶠ z in 𝓝 w, ‖z‖ < R := continuous_norm.continuousAt.eventually (gt_mem_nhds hw)
  filter_upwards [hev] with z hz
  rw [re_circleAverage_herglotzRieszKernel_smul hu (hsph z hz),
    poissonKernel_eq_re_herglotzRieszKernel]

/-! ## P1d: logarithmic derivative of the canonical (Blaschke) factor -/

/-- **P1d** (proved). `d/dw log ((R² - ρ̄ w) / (R (w - ρ))) = -(1/(w-ρ) + ρ̄/(R² - ρ̄ w))`. -/
theorem logDeriv_canonicalFactor {R : ℝ} {ρ w : ℂ} (hR : 0 < R) (hρ : ‖ρ‖ < R) (hw : ‖w‖ < R)
    (hne : w ≠ ρ) :
    logDeriv (Complex.canonicalFactor R ρ) w =
      -(1 / (w - ρ) + conj ρ / ((R : ℂ) ^ 2 - conj ρ * w)) := by
  have hRc : (R : ℂ) ≠ 0 := ofReal_ne_zero.mpr hR.ne'
  have hwρ : w - ρ ≠ 0 := sub_ne_zero.mpr hne
  have hnum : (R : ℂ) ^ 2 - conj ρ * w ≠ 0 := by
    intro h
    have h1 : ‖(R : ℂ) ^ 2‖ = ‖conj ρ * w‖ := by rw [sub_eq_zero.mp h]
    rw [norm_pow, norm_mul, Complex.norm_real, Real.norm_of_nonneg hR.le, RCLike.norm_conj] at h1
    nlinarith [norm_nonneg ρ, norm_nonneg w]
  have hd : HasDerivAt (Complex.canonicalFactor R ρ)
      ((-conj ρ * ((R : ℂ) * (w - ρ)) - ((R : ℂ) ^ 2 - conj ρ * w) * (R : ℂ))
        / ((R : ℂ) * (w - ρ)) ^ 2) w := by
    have h1 : HasDerivAt (fun z : ℂ ↦ (R : ℂ) ^ 2 - conj ρ * z) (-conj ρ) w := by
      simpa using ((hasDerivAt_id w).const_mul (conj ρ)).const_sub ((R : ℂ) ^ 2)
    have h2 : HasDerivAt (fun z : ℂ ↦ (R : ℂ) * (z - ρ)) (R : ℂ) w := by
      simpa using ((hasDerivAt_id w).sub_const ρ).const_mul (R : ℂ)
    exact h1.div h2 (mul_ne_zero hRc hwρ)
  rw [logDeriv_apply, hd.deriv, Complex.canonicalFactor_apply]
  field_simp
  ring

/-! ## P1e: Poisson–Jensen in `Finset` form -/

/-- **P1e** (proved). Mathlib's Poisson–Jensen formula
`MeromorphicOn.log_norm_meromorphicTrailingCoeffAt` (centre `0`) for an entire function, with the
`finsum` over the divisor on the open ball rewritten as a sum over the finite zero set `S` and
`analyticOrderNatAt`.

Proof sketch: `AnalyticAt.meromorphicTrailingCoeffAt_of_ne_zero` for the left side;
`AnalyticAt.meromorphicOrderAt_eq` for the order-zero hypothesis; `AnalyticOnNhd.divisor_apply` on
`ball 0 R` plus finiteness of the order (`F z ≠ 0`, identity theorem) to identify the divisor with
`analyticOrderNatAt`; `finsum_eq_sum_of_support_subset`. -/
theorem log_norm_eq_circleAverage_sub_sum {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    {R : ℝ} {S : Finset ℂ} (hS : ∀ ρ, ρ ∈ S ↔ ‖ρ‖ < R ∧ F ρ = 0)
    {z : ℂ} (hz : ‖z‖ < R) (hFz : F z ≠ 0) :
    Real.log ‖F z‖ = Real.circleAverage (poissonKernel 0 z • fun ζ ↦ Real.log ‖F ζ‖) 0 R
      - ∑ ρ ∈ S, (analyticOrderNatAt F ρ : ℝ) * Real.log ‖Complex.canonicalFactor R ρ z‖ := by
  have hzb : z ∈ ball (0 : ℂ) R := by simpa using hz
  have han : AnalyticOnNhd ℂ F (closedBall 0 R) := fun x _ ↦ hF.analyticAt x
  have hanb : AnalyticOnNhd ℂ F (ball 0 R) := fun x _ ↦ hF.analyticAt x
  have hord : meromorphicOrderAt F z = 0 := by
    rw [(hF.analyticAt z).meromorphicOrderAt_eq, (hF.analyticAt z).analyticOrderAt_eq_zero.mpr hFz]
    rfl
  have h := MeromorphicOn.log_norm_meromorphicTrailingCoeffAt hzb hord han.meromorphicOn
  rw [(hF.analyticAt z).meromorphicTrailingCoeffAt_of_ne_zero hFz] at h
  rw [h]
  congr 1
  have hdiv : ∀ ρ, ‖ρ‖ < R →
      ((MeromorphicOn.divisor F (ball 0 R) ρ : ℤ) : ℝ) = (analyticOrderNatAt F ρ : ℝ) := by
    intro ρ hρ
    have htop : analyticOrderAt F ρ ≠ ⊤ := analyticOrderAt_ne_top_of_entire hF hFz ρ
    rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hanb (by simpa using hρ),
      ← Nat.cast_analyticOrderNatAt htop]
    simp
  rw [finsum_eq_sum_of_support_subset (s := S)]
  · refine Finset.sum_congr rfl fun ρ hρS ↦ ?_
    rw [sub_zero, sub_zero, hdiv ρ ((hS ρ).mp hρS).1]
  · intro ρ hρ
    rw [Function.mem_support] at hρ
    rw [Finset.mem_coe, hS]
    by_contra hcon
    apply hρ
    by_cases hρR : ‖ρ‖ < R
    · have hFρ : F ρ ≠ 0 := fun h ↦ hcon ⟨hρR, h⟩
      have h0 : analyticOrderNatAt F ρ = 0 := (analyticOrderNatAt_eq_zero_iff hF hFz ρ).mpr hFρ
      rw [hdiv ρ hρR, h0]
      simp
    · have hnb : ρ ∉ ball (0 : ℂ) R := by simpa using hρR
      rw [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hnb]
      simp

/-! ## P1: the differentiated formula -/

/-- **P1** (proved from P1a–P1e). Differentiated Poisson–Jensen formula on the disc `‖w‖ < R`. -/
theorem logDeriv_eq_circleAverage_add_sum {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    {R : ℝ} (hR : 0 < R) {S : Finset ℂ} (hS : ∀ ρ, ρ ∈ S ↔ ‖ρ‖ < R ∧ F ρ = 0)
    {w : ℂ} (hw : ‖w‖ < R) (hFw : F w ≠ 0) :
    logDeriv F w =
      Real.circleAverage (fun ζ ↦ (2 * ζ / (ζ - w) ^ 2) • ((Real.log ‖F ζ‖ : ℝ) : ℂ)) 0 R
      + ∑ ρ ∈ S, (analyticOrderNatAt F ρ : ℂ) *
          (1 / (w - ρ) + conj ρ / ((R : ℂ) ^ 2 - conj ρ * w)) := by
  have hu : CircleIntegrable (fun ζ ↦ Real.log ‖F ζ‖) 0 R :=
    MeromorphicOn.circleIntegrable_log_norm fun z _ ↦ (hF.analyticAt z).meromorphicAt
  obtain ⟨g₁, hg₁, hg₁re⟩ := exists_hasDerivAt_re_eq_log_norm (hF w) hFw
  obtain ⟨gP, hgP, hgPre⟩ := exists_hasDerivAt_re_eq_poissonIntegral hR hu hw
  have hρ : ∀ ρ ∈ S, ∃ g : ℂ → ℂ,
      HasDerivAt g (logDeriv (Complex.canonicalFactor R ρ) w) w ∧
      ∀ᶠ z in 𝓝 w, (g z).re = Real.log ‖Complex.canonicalFactor R ρ z‖ := by
    intro ρ hρS
    have hρ' := (hS ρ).mp hρS
    have hne : w ≠ ρ := by
      rintro rfl
      exact hFw hρ'.2
    exact exists_hasDerivAt_re_eq_log_norm
      (Complex.analyticOnNhd_canonicalFactor R ρ w hne).differentiableAt
      (Complex.canonicalFactor_ne_zero (by simpa using hρ'.1) (by simpa using hw.le) hne)
  choose! gc hgc hgcre using hρ
  have hg₂ : HasDerivAt (fun z ↦ gP z - ∑ ρ ∈ S, (analyticOrderNatAt F ρ : ℂ) * gc ρ z)
      (Real.circleAverage (fun ζ ↦ (2 * ζ / (ζ - w) ^ 2) • ((Real.log ‖F ζ‖ : ℝ) : ℂ)) 0 R
        - ∑ ρ ∈ S, (analyticOrderNatAt F ρ : ℂ) * logDeriv (Complex.canonicalFactor R ρ) w) w :=
    hgP.sub (HasDerivAt.fun_sum fun ρ hρS ↦ (hgc ρ hρS).const_mul _)
  have hre : (fun z ↦ (g₁ z).re) =ᶠ[𝓝 w]
      fun z ↦ (gP z - ∑ ρ ∈ S, (analyticOrderNatAt F ρ : ℂ) * gc ρ z).re := by
    have h1 : ∀ᶠ z in 𝓝 w, ‖z‖ < R := continuous_norm.continuousAt.eventually (gt_mem_nhds hw)
    have h2 : ∀ᶠ z in 𝓝 w, F z ≠ 0 := (hF w).continuousAt.eventually_ne hFw
    have h3 : ∀ᶠ z in 𝓝 w, ∀ ρ ∈ S, (gc ρ z).re = Real.log ‖Complex.canonicalFactor R ρ z‖ :=
      (eventually_all_finset S).mpr hgcre
    filter_upwards [h1, h2, h3, hg₁re, hgPre] with z hz1 hz2 hz3 hz4 hz5
    rw [hz4, sub_re, hz5, re_sum, log_norm_eq_circleAverage_sub_sum hF hS hz1 hz2]
    congr 1
    refine Finset.sum_congr rfl fun ρ hρS ↦ ?_
    rw [← ofReal_natCast, re_ofReal_mul, hz3 ρ hρS]
  rw [eq_of_hasDerivAt_of_re_eventuallyEq hg₁ hg₂ hre, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl fun ρ hρS ↦ ?_
  have hρ' := (hS ρ).mp hρS
  have hne : w ≠ ρ := by
    rintro rfl
    exact hFw hρ'.2
  rw [logDeriv_canonicalFactor hR hρ'.1 hw hne]
  ring

end Exp7.EF.HF1
