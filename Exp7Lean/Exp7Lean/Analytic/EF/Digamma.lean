import Exp7Lean.Analytic.EF.Defs

/-!
# Explicit formula blueprint: the digamma function

Leaves **G1–G7** of `BLUEPRINT.md`.  Mathlib (`Mathlib/Analysis/SpecialFunctions/Gamma/Digamma.lean`)
has `Complex.digamma = logDeriv Gamma`, the recurrence, reflection and duplication formulas and
`digamma_one_half`, but neither Gauss' series nor Gauss' integral.

G1/G2 are verbatim `Complex.digamma_eq_gaussSeries` / `Complex.summable_gaussSeries` of
`TauCeti/Analysis/SpecialFunctions/Gamma/GaussSeries.lean`; G6 is `Complex.analyticOnNhd_digamma_re_pos`
of `TauCeti/Analysis/SpecialFunctions/Gamma/Digamma.lean`; G5 is `Complex.logDeriv_Gammaℝ` of
`TauCeti/Analysis/SpecialFunctions/Gamma/LogDeriv.lean` composed with `Odd.gammaFactor_def`.
-/

namespace Exp7.EF

open Complex MeasureTheory

/-- A complex number with positive real part is not a nonpositive integer. -/
theorem ne_neg_natCast_of_re_pos {s : ℂ} (hs : 0 < s.re) (m : ℕ) : s ≠ -(m : ℂ) := by
  intro h
  have h' := congrArg Complex.re h
  simp only [neg_re, natCast_re] at h'
  have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  linarith

/-- Norm bound for one term of Gauss' series, given `‖s + n‖ ≥ c (n + 1)`. -/
theorem gaussSeries_term_norm_le {s : ℂ} {n : ℕ} {c : ℝ} (hc : 0 < c)
    (h : c * ((n : ℝ) + 1) ≤ ‖s + n‖) :
    ‖1 / ((n : ℂ) + 1) - 1 / (s + n)‖ ≤ ‖s - 1‖ / c * (1 / ((n : ℝ) + 1) ^ 2) := by
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hn1 : (n : ℂ) + 1 ≠ 0 := Nat.cast_add_one_ne_zero n
  have hsn : s + n ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at h
    nlinarith
  have e : 1 / ((n : ℂ) + 1) - 1 / (s + n) = (s - 1) / (((n : ℂ) + 1) * (s + n)) := by
    field_simp
    ring
  have hnorm : ‖(n : ℂ) + 1‖ = (n : ℝ) + 1 := by
    rw [← Nat.cast_add_one, Complex.norm_natCast]
    push_cast
    rfl
  rw [e, norm_div, norm_mul, hnorm, div_mul_eq_mul_div, mul_one_div, div_div]
  apply div_le_div_of_nonneg_left (norm_nonneg _) (by positivity)
  calc ((n : ℝ) + 1) ^ 2 * c = ((n : ℝ) + 1) * (c * ((n : ℝ) + 1)) := by ring
    _ ≤ ((n : ℝ) + 1) * ‖s + n‖ := by gcongr

/-- The comparison series `∑ C / (n + 1)^2` is summable. -/
theorem summable_const_mul_one_div_succ_sq (C : ℝ) :
    Summable (fun n : ℕ ↦ C * (1 / ((n : ℝ) + 1) ^ 2)) := by
  refine Summable.mul_left _ ?_
  have := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
  simpa using this

/-- **G1** (M). Gauss' paired series is absolutely summable. -/
theorem summable_gaussSeries (s : ℂ) :
    Summable (fun n : ℕ ↦ 1 / ((n : ℂ) + 1) - 1 / (s + n)) := by
  refine Summable.of_norm_bounded_eventually_nat
    (summable_const_mul_one_div_succ_sq (‖s - 1‖ / (1 / 2))) ?_
  filter_upwards [Filter.eventually_ge_atTop ⌈2 * ‖s‖ + 1⌉₊] with n hn
  refine gaussSeries_term_norm_le (by norm_num) ?_
  have hn' : 2 * ‖s‖ + 1 ≤ n := Nat.ceil_le.mp hn
  have h1 : ‖(n : ℂ)‖ ≤ ‖s + n‖ + ‖s‖ := by
    have := norm_sub_le (s + n) s
    rwa [add_sub_cancel_left] at this
  rw [Complex.norm_natCast] at h1
  linarith

/-- Partial sums of Gauss' series, via the digamma recurrence. -/
theorem digamma_add_nat_sub_digamma_nat_add_one {s : ℂ} (hs : ∀ m : ℕ, s ≠ -(m : ℂ)) (N : ℕ) :
    digamma (s + N) - digamma ((N : ℂ) + 1) =
      digamma s + Real.eulerMascheroniConstant -
        ∑ n ∈ Finset.range N, (1 / ((n : ℂ) + 1) - 1 / (s + n)) := by
  have h1 : ∀ m : ℕ, (1 : ℂ) ≠ -(m : ℂ) := ne_neg_natCast_of_re_pos (by simp)
  have e1 : ∑ k ∈ Finset.range N, ((1 : ℂ) + k)⁻¹ = ∑ n ∈ Finset.range N, 1 / ((n : ℂ) + 1) :=
    Finset.sum_congr rfl fun k _ ↦ by rw [one_div, add_comm]
  have e2 : ∑ k ∈ Finset.range N, (s + k)⁻¹ = ∑ n ∈ Finset.range N, 1 / (s + n) :=
    Finset.sum_congr rfl fun k _ ↦ by rw [one_div]
  rw [add_comm (N : ℂ) 1, digamma_apply_add_nat hs, digamma_apply_add_nat h1, digamma_one,
    Finset.sum_sub_distrib, e1, e2]
  ring

/-- Gauss' series at `s` is equivalent to `ψ(s + N) - ψ(N + 1) → 0`. -/
theorem digamma_eq_gaussSeries_iff_tendsto {s : ℂ} (hs : ∀ m : ℕ, s ≠ -(m : ℂ)) :
    digamma s = -Real.eulerMascheroniConstant +
        ∑' n : ℕ, (1 / ((n : ℂ) + 1) - 1 / (s + n)) ↔
      Filter.Tendsto (fun N : ℕ ↦ digamma (s + N) - digamma ((N : ℂ) + 1))
        Filter.atTop (nhds 0) := by
  have hS := (summable_gaussSeries s).hasSum.tendsto_sum_nat
  have hfun : (fun N : ℕ ↦ digamma (s + N) - digamma ((N : ℂ) + 1)) =
      fun N : ℕ ↦ digamma s + Real.eulerMascheroniConstant -
        ∑ n ∈ Finset.range N, (1 / ((n : ℂ) + 1) - 1 / (s + n)) :=
    funext (digamma_add_nat_sub_digamma_nat_add_one hs)
  rw [hfun]
  constructor
  · intro h
    have h2 := (tendsto_const_nhds (x := digamma s + (Real.eulerMascheroniConstant : ℂ))
      (f := Filter.atTop (α := ℕ))).sub hS
    have e : digamma s + (Real.eulerMascheroniConstant : ℂ) -
        ∑' n : ℕ, (1 / ((n : ℂ) + 1) - 1 / (s + n)) = 0 := by
      linear_combination h
    rwa [e] at h2
  · intro h
    have h2 := (tendsto_const_nhds (x := digamma s + (Real.eulerMascheroniConstant : ℂ))
      (f := Filter.atTop (α := ℕ))).sub h
    have h3 : Filter.Tendsto
        (fun N : ℕ ↦ ∑ n ∈ Finset.range N, (1 / ((n : ℂ) + 1) - 1 / (s + n))) Filter.atTop
        (nhds (digamma s + (Real.eulerMascheroniConstant : ℂ) - 0)) := by
      refine h2.congr fun N ↦ ?_
      ring
    have h4 := tendsto_nhds_unique hS h3
    rw [h4]
    ring

/-- Gauss' series propagates from `s + 1` to `s`. -/
theorem digamma_eq_gaussSeries_of_add_one {s : ℂ} (hs : ∀ m : ℕ, s ≠ -(m : ℂ))
    (h : digamma (s + 1) = -Real.eulerMascheroniConstant +
      ∑' n : ℕ, (1 / ((n : ℂ) + 1) - 1 / (s + 1 + n))) :
    digamma s = -Real.eulerMascheroniConstant +
      ∑' n : ℕ, (1 / ((n : ℂ) + 1) - 1 / (s + n)) := by
  have hs1 : ∀ m : ℕ, s + 1 ≠ -(m : ℂ) := fun m hm ↦
    hs (m + 1) (by push_cast; linear_combination hm)
  rw [digamma_eq_gaussSeries_iff_tendsto hs1] at h
  rw [digamma_eq_gaussSeries_iff_tendsto hs, ← Filter.tendsto_add_atTop_iff_nat 1]
  have h2 : Filter.Tendsto (fun N : ℕ ↦ (1 : ℂ) / ((N : ℂ) + 1)) Filter.atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have h3 := h.sub h2
  rw [sub_zero] at h3
  refine h3.congr fun N ↦ ?_
  have hN : ∀ m : ℕ, (N : ℂ) + 1 ≠ -(m : ℂ) := ne_neg_natCast_of_re_pos (by
    simp only [add_re, natCast_re, one_re]
    positivity)
  rw [Nat.cast_add_one, digamma_apply_add_one _ hN, show s + ((N : ℂ) + 1) = s + 1 + N by ring,
    one_div]
  ring

/-- On the positive reals `Re ψ` is the derivative of `log ∘ Γ`. -/
theorem re_digamma_ofReal_eq_deriv {x : ℝ} (hx : 0 < x) :
    (digamma (x : ℂ)).re = deriv (Real.log ∘ Real.Gamma) x := by
  have hne : ∀ m : ℕ, (x : ℂ) ≠ -(m : ℂ) := ne_neg_natCast_of_re_pos (by simpa using hx)
  have hd : HasDerivAt Gamma (deriv Gamma (x : ℂ)) (x : ℂ) :=
    (differentiableAt_Gamma _ hne).hasDerivAt
  have hr : HasDerivAt Real.Gamma (deriv Gamma (x : ℂ)).re x := hd.real_of_complex
  have hl : HasDerivAt (Real.log ∘ Real.Gamma) ((deriv Gamma (x : ℂ)).re / Real.Gamma x) x :=
    hr.log (Real.Gamma_pos_of_pos hx).ne'
  rw [hl.deriv, digamma_def, logDeriv_apply, Complex.Gamma_ofReal, Complex.div_ofReal_re]

/-- `ψ` is real on the real axis. -/
theorem im_digamma_ofReal (x : ℝ) : (digamma (x : ℂ)).im = 0 := by
  have hfun : (starRingEnd ℂ) ∘ Gamma ∘ (starRingEnd ℂ) = Gamma := by
    funext z
    simp [Gamma_conj]
  have hderiv : (starRingEnd ℂ) (deriv Gamma (x : ℂ)) = deriv Gamma (x : ℂ) := by
    have h := congrFun (deriv_conj_conj (f := Gamma)) (x : ℂ)
    rw [hfun] at h
    simpa using h.symm
  have hG : (starRingEnd ℂ) (Gamma (x : ℂ)) = Gamma (x : ℂ) := by
    rw [← Gamma_conj, conj_ofReal]
  have h1 : (deriv Gamma (x : ℂ)).im = 0 := conj_eq_iff_im.mp hderiv
  have h2 : (Gamma (x : ℂ)).im = 0 := conj_eq_iff_im.mp hG
  rw [digamma_def, logDeriv_apply, div_im, h1, h2]
  simp

/-- `Re ψ` is monotone on the positive reals (log-convexity of `Γ`). -/
theorem re_digamma_ofReal_mono {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    (digamma (x : ℂ)).re ≤ (digamma (y : ℂ)).re := by
  have hy : 0 < y := hx.trans_le hxy
  rw [re_digamma_ofReal_eq_deriv hx, re_digamma_ofReal_eq_deriv hy]
  refine Real.convexOn_log_Gamma.monotoneOn_deriv (fun z hz ↦ ?_) hx hy hxy
  have hz' : (0 : ℝ) < z := hz
  have hd : DifferentiableAt ℝ Real.Gamma z := Real.differentiableAt_Gamma fun m h ↦ by
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  exact hd.log (Real.Gamma_pos_of_pos hz').ne'

/-- For real `x ∈ [1, 2]`, `ψ(x + N) - ψ(N + 1) → 0`. -/
theorem tendsto_digamma_ofReal_add_nat_sub {x : ℝ} (h1 : 1 ≤ x) (h2 : x ≤ 2) :
    Filter.Tendsto (fun N : ℕ ↦ digamma ((x : ℂ) + N) - digamma ((N : ℂ) + 1))
      Filter.atTop (nhds 0) := by
  refine squeeze_zero_norm (fun N ↦ ?_) (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have ha : (x : ℂ) + N = ((x + N : ℝ) : ℂ) := by push_cast; ring
  have hb : (N : ℂ) + 1 = ((N + 1 : ℝ) : ℂ) := by push_cast; ring
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hN : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hc : (digamma ((N + 2 : ℝ) : ℂ)).re = (digamma ((N + 1 : ℝ) : ℂ)).re + 1 / ((N : ℝ) + 1) := by
    have h := digamma_apply_add_one ((N + 1 : ℝ) : ℂ)
      (ne_neg_natCast_of_re_pos (by rw [Complex.ofReal_re]; exact hN))
    have e : ((N + 1 : ℝ) : ℂ) + 1 = ((N + 2 : ℝ) : ℂ) := by push_cast; ring
    rw [e] at h
    rw [h, Complex.add_re, ← Complex.ofReal_inv, Complex.ofReal_re, one_div]
  rw [ha, hb]
  set D : ℂ := digamma ((x + N : ℝ) : ℂ) - digamma ((N + 1 : ℝ) : ℂ) with hD
  have him : D.im = 0 := by
    rw [hD, Complex.sub_im, im_digamma_ofReal, im_digamma_ofReal, sub_zero]
  have hre0 : 0 ≤ D.re := by
    rw [hD, Complex.sub_re]
    have := re_digamma_ofReal_mono (x := (N : ℝ) + 1) (y := x + N) hN (by linarith)
    linarith
  have hre1 : D.re ≤ 1 / ((N : ℝ) + 1) := by
    rw [hD, Complex.sub_re]
    have := re_digamma_ofReal_mono (x := x + N) (y := (N : ℝ) + 2) (by linarith) (by linarith)
    linarith
  have hDre : D = (D.re : ℂ) := Complex.ext (by simp) (by simp [him])
  rw [hDre, Complex.norm_real, Real.norm_of_nonneg hre0]
  exact hre1

/-- Gauss' series on the real segment `[1, 2]`. -/
theorem digamma_eq_gaussSeries_of_mem_Icc {x : ℝ} (h1 : 1 ≤ x) (h2 : x ≤ 2) :
    digamma (x : ℂ) = -Real.eulerMascheroniConstant +
      ∑' n : ℕ, (1 / ((n : ℂ) + 1) - 1 / ((x : ℂ) + n)) :=
  (digamma_eq_gaussSeries_iff_tendsto
    (ne_neg_natCast_of_re_pos (by rw [Complex.ofReal_re]; linarith))).mpr
    (tendsto_digamma_ofReal_add_nat_sub h1 h2)

/-- Gauss' series is analytic on the right half-plane. -/
theorem analyticOnNhd_gaussSeries_re_pos :
    AnalyticOnNhd ℂ (fun s : ℂ ↦ ∑' n : ℕ, (1 / ((n : ℂ) + 1) - 1 / (s + n)))
      {s : ℂ | 0 < s.re} := by
  intro s₀ hs₀
  have hs₀' : 0 < s₀.re := hs₀
  set r : ℝ := s₀.re / 2 with hr
  have hr0 : 0 < r := by positivity
  set c : ℝ := min r 1 with hcdef
  have hc : 0 < c := lt_min hr0 one_pos
  have hcr : c ≤ r := min_le_left r 1
  have hc1 : c ≤ 1 := min_le_right r 1
  have hU : IsOpen (Metric.ball s₀ r) := Metric.isOpen_ball
  have hball : ∀ w ∈ Metric.ball s₀ r, ‖w - s₀‖ < r := fun w hw ↦ by
    rwa [Metric.mem_ball, dist_eq_norm] at hw
  have hre : ∀ w ∈ Metric.ball s₀ r, r < w.re := by
    intro w hw
    have h1 : |(w - s₀).re| ≤ ‖w - s₀‖ := Complex.abs_re_le_norm _
    have h3 := abs_lt.mp (h1.trans_lt (hball w hw))
    rw [Complex.sub_re] at h3
    linarith [h3.1]
  have hdiff : DifferentiableOn ℂ
      (fun w : ℂ ↦ ∑' n : ℕ, (1 / ((n : ℂ) + 1) - 1 / (w + n))) (Metric.ball s₀ r) := by
    refine differentiableOn_tsum_of_summable_norm
      (F := fun (n : ℕ) (w : ℂ) ↦ 1 / ((n : ℂ) + 1) - 1 / (w + n))
      (summable_const_mul_one_div_succ_sq ((‖s₀‖ + r + 1) / c)) (fun n w hw ↦ ?_) hU
      (fun n w hw ↦ ?_)
    · have hwn : w + n ≠ 0 := by
        intro h0
        have h4 := congrArg Complex.re h0
        simp only [add_re, natCast_re, zero_re] at h4
        have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        linarith [hre w hw]
      have hd : DifferentiableAt ℂ (fun w : ℂ ↦ 1 / ((n : ℂ) + 1) - 1 / (w + n)) w := by
        fun_prop (disch := exact hwn)
      exact hd.differentiableWithinAt
    · have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have hb : c * ((n : ℝ) + 1) ≤ ‖w + n‖ := by
        have h1 : (w + n).re ≤ ‖w + n‖ := Complex.re_le_norm _
        simp only [add_re, natCast_re] at h1
        have h3 : c * ((n : ℝ) + 1) ≤ r + n := by nlinarith
        linarith [hre w hw]
      refine (gaussSeries_term_norm_le hc hb).trans ?_
      have hw1 : ‖w - 1‖ ≤ ‖s₀‖ + r + 1 := by
        have h5 : ‖w - 1‖ ≤ ‖w - s₀‖ + ‖s₀ - 1‖ := by
          have := norm_add_le (w - s₀) (s₀ - 1)
          rwa [sub_add_sub_cancel] at this
        have h6 : ‖s₀ - 1‖ ≤ ‖s₀‖ + 1 := by simpa using norm_sub_le s₀ 1
        linarith [hball w hw]
      gcongr
  exact hdiff.analyticAt (hU.mem_nhds (Metric.mem_ball_self hr0))

/-- `ψ` is analytic on the right half-plane (local copy, used for the identity theorem). -/
theorem analyticOnNhd_digamma_re_pos_aux : AnalyticOnNhd ℂ digamma {s : ℂ | 0 < s.re} := by
  have hopen : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hG : AnalyticOnNhd ℂ Gamma {s : ℂ | 0 < s.re} :=
    DifferentiableOn.analyticOnNhd (fun s hs ↦
      (differentiableAt_Gamma s (ne_neg_natCast_of_re_pos hs)).differentiableWithinAt) hopen
  exact hG.deriv.div hG fun s hs ↦ Gamma_ne_zero_of_re_pos hs

/-- Gauss' series on the right half-plane, by the identity theorem. -/
theorem digamma_eq_gaussSeries_of_re_pos {s : ℂ} (hs : 0 < s.re) :
    digamma s = -Real.eulerMascheroniConstant +
      ∑' n : ℕ, (1 / ((n : ℂ) + 1) - 1 / (s + n)) := by
  have hU : IsPreconnected {s : ℂ | 0 < s.re} := (convex_halfSpace_re_gt 0).isPreconnected
  have hg : AnalyticOnNhd ℂ (fun s : ℂ ↦ -(Real.eulerMascheroniConstant : ℂ) +
      ∑' n : ℕ, (1 / ((n : ℂ) + 1) - 1 / (s + n))) {s : ℂ | 0 < s.re} :=
    analyticOnNhd_const.add analyticOnNhd_gaussSeries_re_pos
  have h0 : ((3 / 2 : ℝ) : ℂ) ∈ {s : ℂ | 0 < s.re} := by
    change 0 < ((3 / 2 : ℝ) : ℂ).re
    rw [Complex.ofReal_re]
    norm_num
  have hz : Filter.Tendsto (fun x : ℝ ↦ (x : ℂ)) (nhdsWithin (3 / 2 : ℝ) {(3 / 2 : ℝ)}ᶜ)
      (nhdsWithin ((3 / 2 : ℝ) : ℂ) {((3 / 2 : ℝ) : ℂ)}ᶜ) :=
    Complex.continuous_ofReal.continuousWithinAt.tendsto_nhdsWithin
      fun x hx h ↦ hx (Complex.ofReal_injective h)
  have hev : ∀ᶠ x : ℝ in nhdsWithin (3 / 2 : ℝ) {(3 / 2 : ℝ)}ᶜ,
      digamma (x : ℂ) = -(Real.eulerMascheroniConstant : ℂ) +
        ∑' n : ℕ, (1 / ((n : ℂ) + 1) - 1 / ((x : ℂ) + n)) := by
    have hI : ∀ᶠ x : ℝ in nhds (3 / 2 : ℝ), x ∈ Set.Icc (1 : ℝ) 2 :=
      Icc_mem_nhds (by norm_num) (by norm_num)
    exact (hI.filter_mono nhdsWithin_le_nhds).mono fun x hx ↦
      digamma_eq_gaussSeries_of_mem_Icc hx.1 hx.2
  exact analyticOnNhd_digamma_re_pos_aux.eqOn_of_preconnected_of_frequently_eq hg hU h0
    (hz.frequently hev.frequently) hs

/-- **G2** (L). Gauss' series: `ψ(s) = -γ + ∑ₙ (1/(n+1) - 1/(s+n))` away from the poles.

Proof sketch: both sides satisfy `F(s+1) = F(s) + 1/s` (`digamma_apply_add_one`), so the difference
is `1`-periodic and analytic on `Re s > 0`; on the positive reals `log x - 1/x ≤ ψ(x) ≤ log x`
(log-convexity, `Real.convexOn_log_Gamma`) and the series is `log x + γ + o(1)`, so the difference
tends to `0` along `x → +∞`, hence vanishes on `(0,∞)`, hence on `Re s > 0` (identity theorem), hence
everywhere by the recurrence. Value check at `s = 1`: `digamma_one`. -/
theorem digamma_eq_gaussSeries {s : ℂ} (hs : ∀ m : ℕ, s ≠ -(m : ℂ)) :
    digamma s = -Real.eulerMascheroniConstant +
      ∑' n : ℕ, (1 / ((n : ℂ) + 1) - 1 / (s + n)) := by
  have key : ∀ k : ℕ, ∀ z : ℂ, (∀ m : ℕ, z ≠ -(m : ℂ)) → -(k : ℝ) < z.re →
      digamma z = -Real.eulerMascheroniConstant +
        ∑' n : ℕ, (1 / ((n : ℂ) + 1) - 1 / (z + n)) := by
    intro k
    induction k with
    | zero =>
      intro z _ h
      exact digamma_eq_gaussSeries_of_re_pos (by simpa using h)
    | succ k ih =>
      intro z hz h
      have hz1 : ∀ m : ℕ, z + 1 ≠ -(m : ℂ) := fun m hm ↦
        hz (m + 1) (by push_cast; linear_combination hm)
      refine digamma_eq_gaussSeries_of_add_one hz (ih (z + 1) hz1 ?_)
      rw [Complex.add_re, Complex.one_re]
      push_cast at h
      linarith
  obtain ⟨k, hk⟩ := exists_nat_gt (-s.re)
  exact key k s hs (by linarith)

/-- Pointwise domination of Gauss' kernel by a decaying exponential (helper for G3a). -/
theorem gaussKernel_norm_le {a : ℝ} (ha : 0 < a) (τ : ℝ) {w : ℝ} (hw : 0 < w) :
    ‖Real.exp (-a * w) * (1 - Real.cos (τ * w)) / (1 - Real.exp (-w))‖ ≤
      τ ^ 2 / 2 * (2 / a + 8 / a ^ 2) * Real.exp (-(a / 2) * w) := by
  have hE : 0 < Real.exp (-a * w) := Real.exp_pos _
  have hD : 0 < 1 - Real.exp (-w) := by
    have : Real.exp (-w) < 1 := by rw [Real.exp_lt_one_iff]; linarith
    linarith
  have hc0 : 0 ≤ 1 - Real.cos (τ * w) := by linarith [Real.cos_le_one (τ * w)]
  have hc : 1 - Real.cos (τ * w) ≤ τ ^ 2 / 2 * (w * w) := by
    have := Real.one_sub_sq_div_two_le_cos (x := τ * w)
    nlinarith
  have h2 : w ≤ (1 - Real.exp (-w)) * (1 + w) := by
    have h1 : 1 + w ≤ Real.exp w := by linarith [Real.add_one_le_exp w]
    have h3 : Real.exp (-w) * Real.exp w = 1 := by rw [← Real.exp_add]; simp
    have h4 : Real.exp (-w) * (1 + w) ≤ 1 := by
      calc Real.exp (-w) * (1 + w) ≤ Real.exp (-w) * Real.exp w :=
            mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
        _ = 1 := h3
    nlinarith
  have h3 : w * (1 + w) ≤ (2 / a + 8 / a ^ 2) * Real.exp (a * w / 2) := by
    have hx : 0 ≤ a * w / 2 := by positivity
    have hq := Real.quadratic_le_exp_of_nonneg hx
    have hx1 : a * w / 2 ≤ Real.exp (a * w / 2) := by nlinarith [sq_nonneg (a * w / 2)]
    have hx2 : (a * w / 2) ^ 2 / 2 ≤ Real.exp (a * w / 2) := by nlinarith [sq_nonneg (a * w / 2)]
    have e : w * (1 + w) = 2 / a * (a * w / 2) + 8 / a ^ 2 * ((a * w / 2) ^ 2 / 2) := by
      field_simp
      ring
    rw [e, add_mul]
    gcongr
  have h4 : Real.exp (-a * w) * Real.exp (a * w / 2) = Real.exp (-(a / 2) * w) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [Real.norm_of_nonneg (div_nonneg (mul_nonneg hE.le hc0) hD.le), div_le_iff₀ hD]
  calc Real.exp (-a * w) * (1 - Real.cos (τ * w))
      ≤ Real.exp (-a * w) * (τ ^ 2 / 2 * (w * w)) := by gcongr
    _ ≤ Real.exp (-a * w) * (τ ^ 2 / 2 * (w * ((1 - Real.exp (-w)) * (1 + w)))) := by gcongr
    _ = Real.exp (-a * w) * (τ ^ 2 / 2) * (1 - Real.exp (-w)) * (w * (1 + w)) := by ring
    _ ≤ Real.exp (-a * w) * (τ ^ 2 / 2) * (1 - Real.exp (-w)) *
          ((2 / a + 8 / a ^ 2) * Real.exp (a * w / 2)) := by gcongr
    _ = τ ^ 2 / 2 * (2 / a + 8 / a ^ 2) * (Real.exp (-a * w) * Real.exp (a * w / 2)) *
          (1 - Real.exp (-w)) := by ring
    _ = τ ^ 2 / 2 * (2 / a + 8 / a ^ 2) * Real.exp (-(a / 2) * w) * (1 - Real.exp (-w)) := by
        rw [h4]

/-- **G3a** (M). Integrability of Gauss' kernel `e^{-a w} (1 - cos(τ w)) / (1 - e^{-w})` on `(0,∞)`. -/
theorem integrableOn_gaussKernel {a : ℝ} (ha : 0 < a) (τ : ℝ) :
    IntegrableOn (fun w : ℝ ↦ Real.exp (-a * w) * (1 - Real.cos (τ * w)) / (1 - Real.exp (-w)))
      (Set.Ioi 0) := by
  have hmeas : Measurable (fun w : ℝ ↦
      Real.exp (-a * w) * (1 - Real.cos (τ * w)) / (1 - Real.exp (-w))) := by fun_prop
  have hdom : IntegrableOn
      (fun w : ℝ ↦ τ ^ 2 / 2 * (2 / a + 8 / a ^ 2) * Real.exp (-(a / 2) * w)) (Set.Ioi 0) :=
    (integrableOn_exp_mul_Ioi (by linarith) 0).const_mul _
  refine Integrable.mono' hdom hmeas.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with w hw
  exact gaussKernel_norm_le ha τ hw

/-- One term of Gauss' integral (helper for G3): for `b > 0`,
`∫₀^∞ e^{-b w} (1 - cos(τ w)) dw = Re (1/b - 1/(b + iτ))`. -/
theorem integral_exp_mul_one_sub_cos_Ioi {b : ℝ} (hb : 0 < b) (τ : ℝ) :
    IntegrableOn (fun w : ℝ ↦ Real.exp (-b * w) * (1 - Real.cos (τ * w))) (Set.Ioi 0) ∧
      ∫ w in Set.Ioi (0 : ℝ), Real.exp (-b * w) * (1 - Real.cos (τ * w)) =
        (1 / (b : ℂ) - 1 / ((b : ℂ) + (τ : ℂ) * I)).re := by
  have h1re : (-(b : ℂ)).re < 0 := by simpa using hb
  have h2re : (-((b : ℂ) + (τ : ℂ) * I)).re < 0 := by simpa using hb
  have hi1 := integrableOn_exp_mul_complex_Ioi h1re 0
  have hi2 := integrableOn_exp_mul_complex_Ioi h2re 0
  have hint : IntegrableOn (fun w : ℝ ↦ Complex.exp (-(b : ℂ) * w) -
      Complex.exp (-((b : ℂ) + (τ : ℂ) * I) * w)) (Set.Ioi 0) := hi1.sub hi2
  have hre : ∀ w : ℝ, (Complex.exp (-(b : ℂ) * w) -
      Complex.exp (-((b : ℂ) + (τ : ℂ) * I) * w)).re =
        Real.exp (-b * w) * (1 - Real.cos (τ * w)) := by
    intro w
    simp [Complex.exp_re]
    ring
  have hval : ∫ w in Set.Ioi (0 : ℝ), (Complex.exp (-(b : ℂ) * w) -
      Complex.exp (-((b : ℂ) + (τ : ℂ) * I) * w)) =
        1 / (b : ℂ) - 1 / ((b : ℂ) + (τ : ℂ) * I) := by
    rw [integral_sub hi1 hi2, integral_exp_mul_complex_Ioi h1re,
      integral_exp_mul_complex_Ioi h2re]
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, neg_div_neg_eq]
  refine ⟨?_, ?_⟩
  · have := hint.re
    refine this.congr ?_
    exact Filter.Eventually.of_forall fun w ↦ hre w
  · have h := integral_re hint
    simp only [RCLike.re_to_complex] at h
    rw [hval] at h
    rw [← h]
    exact integral_congr_ae (Filter.Eventually.of_forall fun w ↦ (hre w).symm)

/-- **G3** (M, from G1+G2). Gauss' integral, in the difference form needed here: for `a > 0`,
`Re ψ(a + iτ) - ψ(a) = ∫₀^∞ e^{-a w} (1 - cos(τ w)) / (1 - e^{-w}) dw`.

Proof sketch: by G2, `ψ(a+iτ) - ψ(a) = ∑ₙ (1/(a+n) - 1/(a+n+iτ))`; each term is
`∫₀^∞ e^{-(a+n)w} (1 - e^{-iτw}) dw`; take real parts (nonnegative integrands) and sum the
geometric series under the integral by monotone convergence. -/
theorem re_digamma_add_mul_I_sub {a : ℝ} (ha : 0 < a) (τ : ℝ) :
    (digamma ((a : ℂ) + (τ : ℂ) * I)).re - (digamma (a : ℂ)).re =
      ∫ w in Set.Ioi (0 : ℝ),
        Real.exp (-a * w) * (1 - Real.cos (τ * w)) / (1 - Real.exp (-w)) := by
  set s : ℂ := (a : ℂ) + (τ : ℂ) * I with hs
  have hsne : ∀ m : ℕ, s ≠ -(m : ℂ) := by
    intro m h
    have h' := congrArg Complex.re h
    simp [hs] at h'
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have hane : ∀ m : ℕ, (a : ℂ) ≠ -(m : ℂ) := by
    intro m h
    have h' := congrArg Complex.re h
    simp at h'
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have hsum : Summable (fun n : ℕ ↦ 1 / ((a : ℂ) + n) - 1 / (s + n)) := by
    refine ((summable_gaussSeries s).sub (summable_gaussSeries (a : ℂ))).congr fun n ↦ ?_
    ring
  have hser : digamma s - digamma (a : ℂ) = ∑' n : ℕ, (1 / ((a : ℂ) + n) - 1 / (s + n)) := by
    rw [digamma_eq_gaussSeries hsne, digamma_eq_gaussSeries hane, add_sub_add_left_eq_sub,
      ← (summable_gaussSeries s).tsum_sub (summable_gaussSeries (a : ℂ))]
    refine tsum_congr fun n ↦ ?_
    ring
  set F : ℕ → ℝ → ℝ := fun n w ↦ Real.exp (-(a + n) * w) * (1 - Real.cos (τ * w)) with hF
  have hb : ∀ n : ℕ, 0 < a + n := fun n ↦ by positivity
  have hFint : ∀ n, Integrable (F n) (volume.restrict (Set.Ioi 0)) := fun n ↦
    (integral_exp_mul_one_sub_cos_Ioi (hb n) τ).1
  have hFval : ∀ n : ℕ, ∫ w in Set.Ioi (0 : ℝ), F n w = (1 / ((a : ℂ) + n) - 1 / (s + n)).re := by
    intro n
    rw [(integral_exp_mul_one_sub_cos_Ioi (hb n) τ).2, hs]
    congr 1
    push_cast
    ring
  have hFnn : ∀ n w, 0 ≤ F n w := fun n w ↦
    mul_nonneg (Real.exp_pos _).le (by linarith [Real.cos_le_one (τ * w)])
  have hFsum : Summable fun n : ℕ ↦ ∫ w in Set.Ioi (0 : ℝ), ‖F n w‖ := by
    have : (fun n : ℕ ↦ ∫ w in Set.Ioi (0 : ℝ), ‖F n w‖) =
        fun n : ℕ ↦ (1 / ((a : ℂ) + n) - 1 / (s + n)).re := by
      funext n
      rw [← hFval n]
      exact integral_congr_ae (Filter.Eventually.of_forall fun w ↦
        Real.norm_of_nonneg (hFnn n w))
    rw [this]
    exact (Complex.hasSum_re hsum.hasSum).summable
  have key := integral_tsum_of_summable_integral_norm hFint hFsum
  calc (digamma s).re - (digamma (a : ℂ)).re
      = (digamma s - digamma (a : ℂ)).re := (Complex.sub_re _ _).symm
    _ = ∑' n : ℕ, (1 / ((a : ℂ) + n) - 1 / (s + n)).re := by rw [hser, Complex.re_tsum hsum]
    _ = ∑' n : ℕ, ∫ w in Set.Ioi (0 : ℝ), F n w := tsum_congr fun n ↦ (hFval n).symm
    _ = ∫ w in Set.Ioi (0 : ℝ), ∑' n : ℕ, F n w := key
    _ = ∫ w in Set.Ioi (0 : ℝ),
          Real.exp (-a * w) * (1 - Real.cos (τ * w)) / (1 - Real.exp (-w)) := by
        refine setIntegral_congr_fun measurableSet_Ioi fun w hw ↦ ?_
        have hw' : (0 : ℝ) < w := hw
        have hr : Real.exp (-w) < 1 := by rw [Real.exp_lt_one_iff]; linarith
        have hterm : ∀ n : ℕ, F n w =
            Real.exp (-a * w) * (1 - Real.cos (τ * w)) * Real.exp (-w) ^ n := by
          intro n
          simp only [hF]
          rw [show -(a + (n : ℝ)) * w = -a * w + (n : ℝ) * (-w) by ring, Real.exp_add,
            Real.exp_natCast_mul]
          ring
        simp only [hterm]
        rw [tsum_mul_left, tsum_geometric_of_lt_one (Real.exp_pos _).le hr, div_eq_mul_inv]

/-- **G4** (S). `ψ(3/4) = -γ + π/2 - 3 log 2`.
From `digamma_one_sub` at `s = 1/4` (`cot (π/4) = 1`), `digamma_two_mul` at `s = 1/4` and
`digamma_one_half`. -/
theorem digamma_three_quarters : digamma ((3 / 4 : ℝ) : ℂ) = (psi34 : ℂ) := by
  have hq (n : ℤ) : (1 / 4 : ℂ) ≠ n := by
    intro h
    have h' : ((1 / 4 : ℝ) : ℂ) = ((n : ℝ) : ℂ) := by push_cast; exact h
    have h4 : (4 * n : ℤ) = 1 := by
      have := ofReal_injective h'
      have h5 : ((4 * n : ℤ) : ℝ) = ((1 : ℤ) : ℝ) := by push_cast; linarith
      exact_mod_cast h5
    omega
  have hd (m : ℕ) : 2 * (1 / 4 : ℂ) ≠ -(m : ℂ) := by
    intro h
    have h' : ((1 / 2 : ℝ) : ℂ) = ((-(m : ℝ) : ℝ) : ℂ) := by push_cast; rw [← h]; norm_num
    have := ofReal_injective h'
    have hm : (0 : ℝ) ≤ m := m.cast_nonneg
    linarith
  have h1 := digamma_one_sub hq
  have h2 := digamma_two_mul hd
  have hcot : Complex.cot ((Real.pi : ℂ) * (1 / 4)) = 1 := by
    have h4 : (Real.pi : ℂ) * (1 / 4) = ((Real.pi / 4 : ℝ) : ℂ) := by push_cast; ring
    rw [h4, Complex.cot_eq_cos_div_sin, ← ofReal_cos, ← ofReal_sin, Real.cos_pi_div_four,
      Real.sin_pi_div_four]
    exact div_self (ofReal_ne_zero.mpr (by positivity))
  have hlog : Complex.log 2 = ((Real.log 2 : ℝ) : ℂ) := by
    rw [ofReal_log (by norm_num)]; norm_num
  rw [hcot] at h1
  rw [show (2 : ℂ) * (1 / 4) = 1 / 2 by norm_num, digamma_one_half,
    show (1 / 4 : ℂ) + 1 / 2 = 1 - 1 / 4 by norm_num, h1, hlog] at h2
  have h34 : ((3 / 4 : ℝ) : ℂ) = 1 - 1 / 4 := by push_cast; norm_num
  rw [h34, h1, psi34]
  push_cast
  linear_combination (-1 : ℂ) * h2

/-- **G5** (S). Logarithmic derivative of the gamma factor of an odd character:
`γ'/γ(s) = ½ ψ((s+1)/2) - ½ log π` on `Re s > 0`. -/
theorem logDeriv_gammaFactor_odd {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ.Odd)
    {s : ℂ} (hs : 0 < s.re) :
    logDeriv χ.gammaFactor s = digamma ((s + 1) / 2) / 2 - (Real.log Real.pi : ℂ) / 2 := by
  have hfun : χ.gammaFactor =
      fun z : ℂ ↦ (Real.pi : ℂ) ^ (-(z + 1) / 2) * Gamma ((z + 1) / 2) := by
    funext z
    rw [hχ.gammaFactor_def, Gammaℝ_def]
  have hpi : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hg (m : ℕ) : (s + 1) / 2 ≠ -(m : ℂ) := by
    intro h
    have h' := congrArg Complex.re h
    have hre : ((s + 1) / 2).re = (s.re + 1) / 2 := by simp
    rw [hre] at h'
    simp only [neg_re, natCast_re] at h'
    have hm : (0 : ℝ) ≤ m := m.cast_nonneg
    linarith
  have hd1 : HasDerivAt (fun z : ℂ ↦ (z + 1) / 2) (1 / 2) s :=
    ((hasDerivAt_id' s).add_const 1).div_const 2
  have hd2 : HasDerivAt (fun z : ℂ ↦ -(z + 1) / 2) (-1 / 2) s :=
    (((hasDerivAt_id' s).add_const 1).neg).div_const 2
  have hpow := hd2.const_cpow (c := (Real.pi : ℂ)) (Or.inl hpi)
  have hpow0 : (Real.pi : ℂ) ^ (-(s + 1) / 2) ≠ 0 := by simp [cpow_eq_zero_iff, hpi]
  have hdG : DifferentiableAt ℂ (fun z : ℂ ↦ Gamma ((z + 1) / 2)) s :=
    (differentiableAt_Gamma _ hg).comp s hd1.differentiableAt
  rw [hfun, logDeriv_fun_mul (f := fun z : ℂ ↦ (Real.pi : ℂ) ^ (-(z + 1) / 2))
      (g := fun z : ℂ ↦ Gamma ((z + 1) / 2)) s hpow0 (Gamma_ne_zero hg) hpow.differentiableAt hdG,
    hd1.logDeriv_Gamma hg, logDeriv_apply, hpow.deriv, ofReal_log Real.pi_pos.le]
  field_simp
  ring

/-- **G6** (S). `ψ` is analytic on the right half-plane.
From `Complex.differentiableAt_Gamma`, `Complex.Gamma_ne_zero_of_re_pos`, `DifferentiableOn.analyticOnNhd`. -/
theorem analyticOnNhd_digamma_re_pos : AnalyticOnNhd ℂ digamma {s : ℂ | 0 < s.re} := by
  have hopen : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hG : AnalyticOnNhd ℂ Gamma {s : ℂ | 0 < s.re} := by
    refine DifferentiableOn.analyticOnNhd (fun s hs ↦ ?_) hopen
    refine (differentiableAt_Gamma s fun m h ↦ ?_).differentiableWithinAt
    have h' := congrArg Complex.re h
    simp only [neg_re, natCast_re] at h'
    have hm : (0 : ℝ) ≤ m := m.cast_nonneg
    have hs' : 0 < s.re := hs
    linarith
  exact hG.deriv.div hG fun s hs ↦ Gamma_ne_zero_of_re_pos hs

/-- **G7** (S). `ψ` is real on the positive real axis (`Complex.Gamma_conj`, or G2). -/
theorem digamma_ofReal_im {x : ℝ} (hx : 0 < x) : (digamma (x : ℂ)).im = 0 := by
  have hfun : (starRingEnd ℂ) ∘ Gamma ∘ (starRingEnd ℂ) = Gamma := by
    funext z
    simp [Gamma_conj]
  have hderiv : (starRingEnd ℂ) (deriv Gamma (x : ℂ)) = deriv Gamma (x : ℂ) := by
    have h := congrFun (deriv_conj_conj (f := Gamma)) (x : ℂ)
    rw [hfun] at h
    simpa using h.symm
  have hG : (starRingEnd ℂ) (Gamma (x : ℂ)) = Gamma (x : ℂ) := by
    rw [← Gamma_conj, conj_ofReal]
  have h1 : (deriv Gamma (x : ℂ)).im = 0 := conj_eq_iff_im.mp hderiv
  have h2 : (Gamma (x : ℂ)).im = 0 := conj_eq_iff_im.mp hG
  -- `hx` is not needed: the identity holds for every real `x` (junk values at the poles included)
  have _ := hx
  rw [digamma_def, logDeriv_apply, div_im, h1, h2]
  simp

end Exp7.EF
