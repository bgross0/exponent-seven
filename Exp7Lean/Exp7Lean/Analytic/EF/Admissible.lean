import Exp7Lean.Analytic.EF.Defs

/-!
# Explicit formula blueprint: consequences of admissibility

Leaves **A1–A7** of `BLUEPRINT.md`: elementary real analysis for a pair `(f, h)` with
`WeilAdmissible f L h`.  No number theory.
-/

namespace Exp7.EF

open Real MeasureTheory

variable {f h : ℝ → ℝ} {L : ℝ}

/-- **A1** (S). `h` is integrable (`0 ≤ h ≤ C/(1+t²)`, `integrable_inv_one_add_sq`). -/
theorem WeilAdmissible.integrable (hf : WeilAdmissible f L h) : Integrable h := by
  obtain ⟨C, hC⟩ := hf.decay
  refine Integrable.mono' (integrable_inv_one_add_sq.const_mul C) hf.cont.aestronglyMeasurable
    (Filter.Eventually.of_forall fun t => ?_)
  rw [Real.norm_of_nonneg (hf.nonneg t), ← div_eq_mul_inv]
  exact hC t

/-- **A2** (S). `∫ h = 2π` (inversion at `u = 0` and `f 0 = 1`). -/
theorem WeilAdmissible.integral_eq (hf : WeilAdmissible f L h) : ∫ t, h t = 2 * π := by
  have h0 := hf.inv 0
  rw [hf.zero] at h0
  simp only [mul_zero, Real.cos_zero, mul_one] at h0
  have hpi : (2 * π) ≠ 0 := by positivity
  field_simp at h0
  linarith

/-- **A3** (S). `0 ≤ 1 - f u` (since `cos ≤ 1` and `h ≥ 0`). -/
theorem WeilAdmissible.one_sub_nonneg (hf : WeilAdmissible f L h) (u : ℝ) : 0 ≤ 1 - f u := by
  have hint := hf.integrable
  have hcos : Integrable fun t => h t * Real.cos (t * u) := by
    refine Integrable.mono' hint
      (hf.cont.mul (Real.continuous_cos.comp
        (continuous_id.mul continuous_const))).aestronglyMeasurable
      (Filter.Eventually.of_forall fun t => ?_)
    rw [norm_mul, Real.norm_of_nonneg (hf.nonneg t), Real.norm_eq_abs]
    exact mul_le_of_le_one_right (hf.nonneg t) (Real.abs_cos_le_one (t * u))
  have hle : ∫ t, h t * Real.cos (t * u) ≤ ∫ t, h t :=
    integral_mono hcos hint fun t => mul_le_of_le_one_right (hf.nonneg t) (Real.cos_le_one _)
  rw [hf.integral_eq] at hle
  rw [hf.inv u, sub_nonneg]
  have hpi : 0 < 2 * π := by positivity
  calc 1 / (2 * π) * ∫ t, h t * Real.cos (t * u) ≤ 1 / (2 * π) * (2 * π) := by gcongr
    _ = 1 := by field_simp

/-- Helper for A4: `(1 - cos x)(1 + x²) ≤ 4x²`. -/
theorem one_sub_cos_mul_one_add_sq_le (x : ℝ) : (1 - Real.cos x) * (1 + x ^ 2) ≤ 4 * x ^ 2 := by
  have h1 : 1 - x ^ 2 / 2 ≤ Real.cos x := Real.one_sub_sq_div_two_le_cos
  have h2 : -1 ≤ Real.cos x := Real.neg_one_le_cos x
  have h3 : Real.cos x ≤ 1 := Real.cos_le_one x
  have hx : 0 ≤ x ^ 2 := sq_nonneg x
  rcases le_total (x ^ 2) 1 with hx1 | hx1
  · have e1 : (1 - Real.cos x) * (1 + x ^ 2) ≤ x ^ 2 / 2 * (1 + x ^ 2) :=
      mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    have e2 : x ^ 2 / 2 * (1 + x ^ 2) ≤ x ^ 2 / 2 * 2 :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    linarith
  · have e1 : (1 - Real.cos x) * (1 + x ^ 2) ≤ 2 * (1 + x ^ 2) :=
      mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    linarith

/-- **A4** (M). `1 - f u ≤ C |u|`: from `1 - f u = (1/2π) ∫ h(t) (1 - cos(tu)) dt`,
`1 - cos x ≤ min 2 (x²/2)` and `h ≤ C/(1+t²)` (split at `|t| = 1/|u|`). -/
theorem WeilAdmissible.one_sub_le (hf : WeilAdmissible f L h) :
    ∃ C : ℝ, ∀ u, 1 - f u ≤ C * |u| := by
  obtain ⟨C, hC⟩ := hf.decay
  have hC0 : 0 ≤ C := by simpa using (hf.nonneg 0).trans (hC 0)
  refine ⟨2 * C, fun u => ?_⟩
  rcases eq_or_ne u 0 with rfl | hu
  · simp [hf.zero]
  have hint : Integrable h := hf.integrable
  have hcos : Integrable (fun t => h t * Real.cos (t * u)) :=
    hint.mul_bdd (c := 1) (by fun_prop) (.of_forall fun t => by
      simpa using Real.abs_cos_le_one (t * u))
  have hcos1 : Integrable (fun t => h t * (1 - Real.cos (t * u))) :=
    (hint.sub hcos).congr (.of_forall fun t => by simp [mul_sub])
  have hg : Integrable (fun t : ℝ => 4 * C * u ^ 2 * (1 + (u * t) ^ 2)⁻¹) :=
    (integrable_inv_one_add_sq.comp_mul_left' hu).const_mul _
  have key : 1 - f u = 1 / (2 * π) * ∫ t, h t * (1 - Real.cos (t * u)) := by
    have e : ∫ t, h t * (1 - Real.cos (t * u)) = (∫ t, h t) - ∫ t, h t * Real.cos (t * u) := by
      rw [← integral_sub hint hcos]
      congr 1
      ext t
      ring
    have hpi : 1 / (2 * π) * (2 * π) = 1 := by field_simp
    rw [e, hf.inv u, hf.integral_eq, mul_sub, hpi]
  have hle : ∫ t, h t * (1 - Real.cos (t * u)) ≤
      ∫ t : ℝ, 4 * C * u ^ 2 * (1 + (u * t) ^ 2)⁻¹ := by
    refine integral_mono hcos1 hg fun t => ?_
    have h1 : 0 ≤ 1 - Real.cos (t * u) := sub_nonneg.2 (Real.cos_le_one _)
    have h2 := one_sub_cos_mul_one_add_sq_le (t * u)
    have h3 : (1 - Real.cos (t * u)) / (1 + t ^ 2) ≤ 4 * u ^ 2 * (1 + (u * t) ^ 2)⁻¹ := by
      rw [← div_eq_mul_inv, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [sq_nonneg u]
    calc h t * (1 - Real.cos (t * u))
        ≤ C / (1 + t ^ 2) * (1 - Real.cos (t * u)) := mul_le_mul_of_nonneg_right (hC t) h1
      _ = C * ((1 - Real.cos (t * u)) / (1 + t ^ 2)) := by ring
      _ ≤ C * (4 * u ^ 2 * (1 + (u * t) ^ 2)⁻¹) := mul_le_mul_of_nonneg_left h3 hC0
      _ = 4 * C * u ^ 2 * (1 + (u * t) ^ 2)⁻¹ := by ring
  have hval : ∫ t : ℝ, 4 * C * u ^ 2 * (1 + (u * t) ^ 2)⁻¹ = 4 * C * π * |u| := by
    rw [integral_const_mul, Measure.integral_comp_mul_left (fun y : ℝ => (1 + y ^ 2)⁻¹) u,
      integral_univ_inv_one_add_sq, abs_inv, smul_eq_mul]
    have hu' : |u| ≠ 0 := abs_ne_zero.2 hu
    have : u ^ 2 = |u| * |u| := by rw [← sq, sq_abs]
    rw [this]
    field_simp
  rw [key]
  have hpi : 0 < 1 / (2 * π) := by positivity
  calc 1 / (2 * π) * ∫ t, h t * (1 - Real.cos (t * u))
      ≤ 1 / (2 * π) * (4 * C * π * |u|) := by
        rw [← hval]
        exact mul_le_mul_of_nonneg_left hle hpi.le
    _ = 2 * C * |u| := by
        field_simp
        ring

/-- **A5** (S). `f` is continuous (dominated convergence, `continuous_of_dominated`). -/
theorem WeilAdmissible.continuous (hf : WeilAdmissible f L h) : Continuous f := by
  have hfeq : f = fun u => 1 / (2 * π) * ∫ t, h t * Real.cos (t * u) := funext hf.inv
  rw [hfeq]
  refine continuous_const.mul ?_
  refine continuous_of_dominated (bound := h) (fun u => ?_) (fun u => ?_) hf.integrable ?_
  · exact (hf.cont.mul (Real.continuous_cos.comp
      (continuous_id.mul continuous_const))).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun t => ?_
    rw [norm_mul, Real.norm_of_nonneg (hf.nonneg t), Real.norm_eq_abs]
    exact mul_le_of_le_one_right (hf.nonneg t) (Real.abs_cos_le_one (t * u))
  · refine Filter.Eventually.of_forall fun t => ?_
    exact continuous_const.mul (Real.continuous_cos.comp (continuous_const.mul continuous_id))

/-- **A6** (M). The damped archimedean integrand is integrable on `(0,∞)` for `δ ≥ 0`
(near `0`: A4 and `u/(1-e^{-2u})` bounded; near `∞`: `1 - f ≤ 2`, exponential decay). -/
theorem WeilAdmissible.integrableOn_archIntegrand (hf : WeilAdmissible f L h) {δ : ℝ}
    (hδ : 0 ≤ δ) : IntegrableOn (archIntegrand f δ) (Set.Ioi 0) := by
  obtain ⟨C, hC⟩ := hf.one_sub_le
  have hmeas : Measurable (archIntegrand f δ) := by
    have hfm : Measurable f := hf.continuous.measurable
    unfold archIntegrand
    fun_prop
  have hg : IntegrableOn (fun u : ℝ => 2 * C * Real.exp (-(1 / 2) * u)) (Set.Ioi 0) :=
    (integrableOn_exp_mul_Ioi (by norm_num) 0).const_mul _
  refine Integrable.mono' hg hmeas.aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ioi).2 (.of_forall fun u hu => ?_)
  have hu : 0 < u := hu
  have hw0 : 0 ≤ 1 - f u := hf.one_sub_nonneg u
  have hw1 : 1 - f u ≤ C * u := by simpa [abs_of_pos hu] using hC u
  have hC0 : 0 ≤ C := by
    by_contra hneg
    have : C * u < 0 := mul_neg_of_neg_of_pos (not_le.1 hneg) hu
    linarith
  have hD : 0 < 1 - Real.exp (-2 * u) := by
    have : Real.exp (-2 * u) < 1 := Real.exp_lt_one_iff.2 (by linarith)
    linarith
  have hD2 : 2 * u ≤ (1 - Real.exp (-2 * u)) * (1 + 2 * u) := by
    have h1 : 2 * u + 1 ≤ Real.exp (2 * u) := Real.add_one_le_exp _
    have h2 : Real.exp (-2 * u) * Real.exp (2 * u) = 1 := by
      rw [← Real.exp_add]
      simp
    have h3 := mul_nonneg (Real.exp_pos (-2 * u)).le (sub_nonneg.2 h1)
    linarith
  have hE : Real.exp (-(3 / 2 + δ) * u) * (1 + 2 * u) ≤ 2 * Real.exp (-(1 / 2) * u) := by
    have h1 : 1 + 2 * u ≤ 2 * Real.exp u := by linarith [Real.add_one_le_exp u]
    have h2 : Real.exp (-(3 / 2 + δ) * u) ≤ Real.exp (-(3 / 2) * u) :=
      Real.exp_le_exp.2 (by nlinarith)
    have h3 : Real.exp (-(3 / 2) * u) * Real.exp u = Real.exp (-(1 / 2) * u) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc Real.exp (-(3 / 2 + δ) * u) * (1 + 2 * u)
        ≤ Real.exp (-(3 / 2) * u) * (2 * Real.exp u) :=
          mul_le_mul h2 h1 (by linarith) (Real.exp_pos _).le
      _ = 2 * Real.exp (-(1 / 2) * u) := by
          rw [← h3]
          ring
  have hval : archIntegrand f δ u =
      Real.exp (-(3 / 2 + δ) * u) * (2 * (1 - f u) / (1 - Real.exp (-2 * u))) := by
    unfold archIntegrand
    ring
  have hq : 2 * (1 - f u) / (1 - Real.exp (-2 * u)) ≤ C * (1 + 2 * u) := by
    rw [div_le_iff₀ hD]
    have := mul_le_mul_of_nonneg_left hD2 hC0
    linarith
  have hnn : 0 ≤ archIntegrand f δ u := by
    rw [hval]
    exact mul_nonneg (Real.exp_pos _).le (div_nonneg (by linarith) hD.le)
  rw [Real.norm_of_nonneg hnn, hval]
  calc Real.exp (-(3 / 2 + δ) * u) * (2 * (1 - f u) / (1 - Real.exp (-2 * u)))
      ≤ Real.exp (-(3 / 2 + δ) * u) * (C * (1 + 2 * u)) :=
        mul_le_mul_of_nonneg_left hq (Real.exp_pos _).le
    _ = C * (Real.exp (-(3 / 2 + δ) * u) * (1 + 2 * u)) := by ring
    _ ≤ C * (2 * Real.exp (-(1 / 2) * u)) := mul_le_mul_of_nonneg_left hE hC0
    _ = 2 * C * Real.exp (-(1 / 2) * u) := by ring

/-- Helper for A7: `1/((1+t²)(1+(t-γ)²)) ≤ 4/(4+γ²) · (1/(1+t²) + 1/(1+(t-γ)²))`. -/
theorem inv_one_add_sq_mul_inv_le (t γ : ℝ) :
    (1 + t ^ 2)⁻¹ * (1 + (t - γ) ^ 2)⁻¹ ≤
      4 / (4 + γ ^ 2) * ((1 + t ^ 2)⁻¹ + (1 + (t - γ) ^ 2)⁻¹) := by
  have hA : 0 < 1 + t ^ 2 := by positivity
  have hB : 0 < 1 + (t - γ) ^ 2 := by positivity
  have key : 4 + γ ^ 2 ≤ 4 * ((1 + t ^ 2) + (1 + (t - γ) ^ 2)) := by
    nlinarith [sq_nonneg (2 * t - γ)]
  have e : 4 / (4 + γ ^ 2) * ((1 + t ^ 2)⁻¹ + (1 + (t - γ) ^ 2)⁻¹) =
      (4 * ((1 + t ^ 2) + (1 + (t - γ) ^ 2)) / (4 + γ ^ 2)) *
        ((1 + t ^ 2)⁻¹ * (1 + (t - γ) ^ 2)⁻¹) := by
    field_simp
    ring
  rw [e]
  have h1 : 1 ≤ 4 * ((1 + t ^ 2) + (1 + (t - γ) ^ 2)) / (4 + γ ^ 2) := by
    rw [one_le_div (by positivity)]
    exact key
  exact le_mul_of_one_le_left (by positivity) h1

/-- Helper for A7 (real form): if `a ≤ σ` and `σ² + τ² ≤ b²` then
`σ² + (τ + x)² ≥ c (1 + x²)` with `c = a² / (4 (1 + a² + b²))`. -/
theorem sq_add_sq_shift_ge {a b σ τ : ℝ} (ha : 0 < a) (h1 : a ≤ σ)
    (h2 : σ ^ 2 + τ ^ 2 ≤ b ^ 2) (x : ℝ) :
    a ^ 2 / (4 * (1 + a ^ 2 + b ^ 2)) * (1 + x ^ 2) ≤ σ ^ 2 + (τ + x) ^ 2 := by
  have hM : 0 < 4 * (1 + a ^ 2 + b ^ 2) := by positivity
  rw [div_mul_eq_mul_div, div_le_iff₀ hM]
  have hσ : a ^ 2 ≤ σ ^ 2 := by nlinarith
  have hτ : τ ^ 2 ≤ b ^ 2 := by nlinarith [sq_nonneg σ]
  have e1 : x ^ 2 ≤ 2 * (τ + x) ^ 2 + 2 * τ ^ 2 := by nlinarith [sq_nonneg (2 * τ + x)]
  have e2 : a ^ 2 * (1 + 2 * τ ^ 2) ≤ σ ^ 2 * (4 * (1 + a ^ 2 + b ^ 2)) := by
    calc a ^ 2 * (1 + 2 * τ ^ 2) ≤ a ^ 2 * (4 * (1 + a ^ 2 + b ^ 2)) :=
          mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg a]) (sq_nonneg a)
      _ ≤ σ ^ 2 * (4 * (1 + a ^ 2 + b ^ 2)) := mul_le_mul_of_nonneg_right hσ hM.le
  have e3 : a ^ 2 * (2 * (τ + x) ^ 2) ≤ (τ + x) ^ 2 * (4 * (1 + a ^ 2 + b ^ 2)) := by
    have := mul_nonneg (sq_nonneg (τ + x)) (by positivity : (0 : ℝ) ≤ 4 + 2 * a ^ 2 + 4 * b ^ 2)
    linarith
  have e4 := mul_le_mul_of_nonneg_left e1 (sq_nonneg a)
  linarith

/-- Helper for A7: on the box `a ≤ Re δ`, `‖δ‖ ≤ b` one has `‖δ² + x²‖ ≥ c (1 + x²)` with a
constant `c = c(a, b) > 0`, uniformly in real `x`. -/
theorem exists_norm_sq_add_sq_ge {a : ℝ} (ha : 0 < a) (b : ℝ) :
    ∃ c : ℝ, 0 < c ∧ ∀ δ : ℂ, a ≤ δ.re → ‖δ‖ ≤ b → ∀ x : ℝ,
      c * (1 + x ^ 2) ≤ ‖δ ^ 2 + (x : ℂ) ^ 2‖ := by
  refine ⟨a ^ 2 / (4 * (1 + a ^ 2 + b ^ 2)), by positivity, fun δ h1 h2 x => ?_⟩
  have hb : δ.re ^ 2 + δ.im ^ 2 ≤ b ^ 2 := by
    have h3 : ‖δ‖ ^ 2 ≤ b ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h2 2
    rwa [Complex.sq_norm, Complex.normSq_apply, ← sq, ← sq] at h3
  have hfac : δ ^ 2 + (x : ℂ) ^ 2 = (δ + x * Complex.I) * (δ - x * Complex.I) := by
    have hI : Complex.I ^ 2 = -1 := Complex.I_sq
    linear_combination (x : ℂ) ^ 2 * hI
  have n1 : a ^ 2 / (4 * (1 + a ^ 2 + b ^ 2)) * (1 + x ^ 2) ≤ ‖δ + x * Complex.I‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    have := sq_add_sq_shift_ge ha h1 hb x
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]
    nlinarith
  have n2 : a ^ 2 / (4 * (1 + a ^ 2 + b ^ 2)) * (1 + x ^ 2) ≤ ‖δ - x * Complex.I‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    have := sq_add_sq_shift_ge ha h1 hb (-x)
    simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]
    nlinarith
  have hpos : 0 ≤ a ^ 2 / (4 * (1 + a ^ 2 + b ^ 2)) * (1 + x ^ 2) := by positivity
  rw [hfac, norm_mul]
  refine (sq_le_sq₀ hpos (by positivity)).1 ?_
  calc (a ^ 2 / (4 * (1 + a ^ 2 + b ^ 2)) * (1 + x ^ 2)) ^ 2
      = (a ^ 2 / (4 * (1 + a ^ 2 + b ^ 2)) * (1 + x ^ 2)) *
          (a ^ 2 / (4 * (1 + a ^ 2 + b ^ 2)) * (1 + x ^ 2)) := sq _
    _ ≤ ‖δ + x * Complex.I‖ ^ 2 * ‖δ - x * Complex.I‖ ^ 2 :=
        mul_le_mul n1 n2 hpos (sq_nonneg _)
    _ = (‖δ + x * Complex.I‖ * ‖δ - x * Complex.I‖) ^ 2 := by ring

/-- **A7** (M). Uniform Cauchy-kernel bound: for `δ` in a "box" `a ≤ Re δ`, `‖δ‖ ≤ b` of the right
half-plane, `∫ h(t) |δ / (δ² + (t-γ)²)| dt ≤ C/(1+γ²)` uniformly in `γ`.

Proof sketch: `|δ² + x²| = |δ + ix| |δ - ix| ≥ c (1 + x²)` with `c = c(a,b) > 0`, then
`∫ dt / ((1+t²)(1+(t-γ)²)) ≤ 8π/(4+γ²)` (split according to `|t| ≥ |γ|/2` or `|t-γ| ≥ |γ|/2`). -/
theorem WeilAdmissible.exists_poisson_bound (hf : WeilAdmissible f L h) {a b : ℝ} (ha : 0 < a) :
    ∃ C : ℝ, ∀ δ : ℂ, a ≤ δ.re → ‖δ‖ ≤ b → ∀ γ : ℝ,
      Integrable (fun t : ℝ ↦ (h t : ℂ) * (δ / (δ ^ 2 + ((t - γ : ℝ) : ℂ) ^ 2))) ∧
      ∫ t : ℝ, h t * ‖δ / (δ ^ 2 + ((t - γ : ℝ) : ℂ) ^ 2)‖ ≤ C / (1 + γ ^ 2) := by
  obtain ⟨Ch, hCh⟩ := hf.decay
  have hCh0 : 0 ≤ Ch := by simpa using (hf.nonneg 0).trans (hCh 0)
  obtain ⟨c, hc0, hlow⟩ := exists_norm_sq_add_sq_ge ha b
  refine ⟨Ch * (b / c) * (8 * π), fun δ h1 h2 γ => ?_⟩
  have hb0 : 0 ≤ b := (norm_nonneg δ).trans h2
  have hker : ∀ t : ℝ,
      ‖δ / (δ ^ 2 + ((t - γ : ℝ) : ℂ) ^ 2)‖ ≤ b / c * (1 + (t - γ) ^ 2)⁻¹ := by
    intro t
    have hpos : 0 < c * (1 + (t - γ) ^ 2) := by positivity
    rw [norm_div]
    calc ‖δ‖ / ‖δ ^ 2 + ((t - γ : ℝ) : ℂ) ^ 2‖
        ≤ b / (c * (1 + (t - γ) ^ 2)) := div_le_div₀ hb0 h2 hpos (hlow δ h1 h2 (t - γ))
      _ = b / c * (1 + (t - γ) ^ 2)⁻¹ := by
          rw [div_mul_eq_div_div, div_eq_mul_inv (b / c)]
  have hshift : Integrable (fun t : ℝ => (1 + (t - γ) ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.comp_sub_right γ
  have hGint : Integrable (fun t : ℝ =>
      Ch * (b / c) * (4 / (4 + γ ^ 2)) * ((1 + t ^ 2)⁻¹ + (1 + (t - γ) ^ 2)⁻¹)) :=
    (integrable_inv_one_add_sq.add hshift).const_mul _
  have hGval : ∫ t : ℝ, Ch * (b / c) * (4 / (4 + γ ^ 2)) *
      ((1 + t ^ 2)⁻¹ + (1 + (t - γ) ^ 2)⁻¹) = Ch * (b / c) * (4 / (4 + γ ^ 2)) * (2 * π) := by
    rw [integral_const_mul, integral_add integrable_inv_one_add_sq hshift,
      integral_sub_right_eq_self (fun t : ℝ => (1 + t ^ 2)⁻¹) γ, integral_univ_inv_one_add_sq]
    ring
  have hpt : ∀ t, h t * ‖δ / (δ ^ 2 + ((t - γ : ℝ) : ℂ) ^ 2)‖ ≤
      Ch * (b / c) * (4 / (4 + γ ^ 2)) * ((1 + t ^ 2)⁻¹ + (1 + (t - γ) ^ 2)⁻¹) := by
    intro t
    have hK0 : 0 ≤ Ch * (b / c) := by positivity
    calc h t * ‖δ / (δ ^ 2 + ((t - γ : ℝ) : ℂ) ^ 2)‖
        ≤ Ch / (1 + t ^ 2) * (b / c * (1 + (t - γ) ^ 2)⁻¹) :=
          mul_le_mul (hCh t) (hker t) (norm_nonneg _) (by positivity)
      _ = Ch * (b / c) * ((1 + t ^ 2)⁻¹ * (1 + (t - γ) ^ 2)⁻¹) := by ring
      _ ≤ Ch * (b / c) * (4 / (4 + γ ^ 2) * ((1 + t ^ 2)⁻¹ + (1 + (t - γ) ^ 2)⁻¹)) :=
          mul_le_mul_of_nonneg_left (inv_one_add_sq_mul_inv_le t γ) hK0
      _ = Ch * (b / c) * (4 / (4 + γ ^ 2)) * ((1 + t ^ 2)⁻¹ + (1 + (t - γ) ^ 2)⁻¹) := by ring
  have hmh : Measurable h := hf.cont.measurable
  have hmeas : Measurable (fun t : ℝ ↦ (h t : ℂ) * (δ / (δ ^ 2 + ((t - γ : ℝ) : ℂ) ^ 2))) := by
    fun_prop
  refine ⟨?_, ?_⟩
  · refine Integrable.mono' hGint hmeas.aestronglyMeasurable (.of_forall fun t => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hf.nonneg t)]
    exact hpt t
  · have hlast : 4 / (4 + γ ^ 2) * (2 * π) ≤ 8 * π / (1 + γ ^ 2) := by
      have e : 4 / (4 + γ ^ 2) * (2 * π) = 8 * π / (4 + γ ^ 2) := by ring
      rw [e]
      exact div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
    have hK0 : 0 ≤ Ch * (b / c) := by positivity
    calc ∫ t : ℝ, h t * ‖δ / (δ ^ 2 + ((t - γ : ℝ) : ℂ) ^ 2)‖
        ≤ ∫ t : ℝ, Ch * (b / c) * (4 / (4 + γ ^ 2)) *
            ((1 + t ^ 2)⁻¹ + (1 + (t - γ) ^ 2)⁻¹) :=
          integral_mono_of_nonneg
            (.of_forall fun t => mul_nonneg (hf.nonneg t) (norm_nonneg _)) hGint (.of_forall hpt)
      _ = Ch * (b / c) * (4 / (4 + γ ^ 2)) * (2 * π) := hGval
      _ = Ch * (b / c) * (4 / (4 + γ ^ 2) * (2 * π)) := by ring
      _ ≤ Ch * (b / c) * (8 * π / (1 + γ ^ 2)) := mul_le_mul_of_nonneg_left hlast hK0
      _ = Ch * (b / c) * (8 * π) / (1 + γ ^ 2) := by ring

end Exp7.EF
