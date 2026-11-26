import Exp7Lean.Analytic.EF.Admissible
import Exp7Lean.Analytic.EF.Zeros
import Exp7Lean.Analytic.EF.Digamma
import Exp7Lean.Analytic.EF.DirichletSeries

/-!
# Explicit formula blueprint: integrating the pointwise identity against `h(t) dt`

Leaves **I1–I3** of `BLUEPRINT.md`.  Each computes `∫ h(t) · (one term of P0) dt` using only
the inversion formula `(1/2π) ∫ h(t) cos(tu) dt = f(u)` and Fubini/Tonelli.
-/

namespace Exp7.EF

open Real MeasureTheory Complex

variable (q : ℕ) [Fact q.Prime] {f h : ℝ → ℝ} {X : ℕ}

/-- **I1** (M). Prime side. For `δ > 1/2`, `t ↦ h(t) · ∑ₙ Λ(n)χ(n) n^{-1/2-δ} cos(t log n)` is
integrable and its integral is `π · primeTermR q f X δ = 2π ∑_{n<X} Λ(n)χ(n) f(log n) n^{-1/2-δ}`.

Proof sketch: `integral_tsum_of_summable_integral_norm` (D1 and A1), then
`∫ h(t) cos(t log n) dt = 2π f(log n)` (`WeilAdmissible.inv`), and `f(log n) = 0` for `n ≥ X`
(`WeilAdmissible.supp`, monotonicity of `log`; note `Λ 0 = 0`). -/
theorem integral_h_mul_dirichletR (hf : WeilAdmissible f (Real.log X) h) {δ : ℝ}
    (hδ : 1 / 2 < δ) :
    Integrable (fun t ↦ h t * dirichletR q δ t) ∧
      ∫ t, h t * dirichletR q δ t = π * primeTermR q f X δ := by
  -- coefficients `c n = Λ(n) χ(n) n^{-1/2-δ}`, absolutely summable by D1
  set c : ℕ → ℝ := fun n ↦ coeff q n * (n : ℝ) ^ (-(1 / 2 : ℝ) - δ) with hc
  have hcabs : ∀ n, |c n| = |coeff q n| * (n : ℝ) ^ (-(1 / 2 : ℝ) - δ) := fun n ↦ by
    rw [hc, abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)]
  have hsum : Summable (fun n ↦ |c n|) := by
    simpa only [hcabs] using summable_abs_coeff_mul_rpow q hδ
  have hint : Integrable h := hf.integrable
  -- the terms of the series, multiplied by `h`
  set F : ℕ → ℝ → ℝ := fun n t ↦ h t * (c n * Real.cos (t * Real.log n)) with hF
  have hFcont : ∀ n, Continuous (F n) := fun n ↦
    hf.cont.mul (continuous_const.mul
      (Real.continuous_cos.comp (continuous_id.mul continuous_const)))
  have hFbound : ∀ n t, ‖F n t‖ ≤ |c n| * h t := fun n t ↦ by
    simp only [hF, Real.norm_eq_abs, abs_mul, abs_of_nonneg (hf.nonneg t)]
    calc h t * (|c n| * |Real.cos (t * Real.log n)|) ≤ h t * (|c n| * 1) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (abs_nonneg _)) (hf.nonneg t)
      _ = |c n| * h t := by ring
  have hFint : ∀ n, Integrable (F n) := fun n ↦
    (hint.const_mul |c n|).mono' (hFcont n).aestronglyMeasurable
      (Filter.Eventually.of_forall (hFbound n))
  have hFsum : Summable (fun n ↦ ∫ t, ‖F n t‖) := by
    refine Summable.of_nonneg_of_le (fun n ↦ integral_nonneg fun t ↦ norm_nonneg _)
      (fun n ↦ ?_) (hsum.mul_right (2 * π))
    calc ∫ t, ‖F n t‖ ≤ ∫ t, |c n| * h t :=
          integral_mono (hFint n).norm (hint.const_mul _) (hFbound n)
      _ = |c n| * (2 * π) := by rw [integral_const_mul, hf.integral_eq]
  have hpt : ∀ t, h t * dirichletR q δ t = ∑' n, F n t := fun t ↦ by
    simp only [hF, dirichletR, hc]
    rw [tsum_mul_left]
  -- integrability: `dirichletR` is continuous and bounded by `∑ |c n|`
  have hDcont : Continuous (dirichletR q δ) :=
    continuous_tsum (u := fun n ↦ |c n|)
      (fun n ↦ continuous_const.mul
        (Real.continuous_cos.comp (continuous_id.mul continuous_const)))
      hsum (fun n t ↦ by
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _))
  have hDbound : ∀ t, |dirichletR q δ t| ≤ ∑' n, |c n| := fun t ↦ by
    rw [← Real.norm_eq_abs]
    refine tsum_of_norm_bounded hsum.hasSum (fun n ↦ ?_)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
  have hI : Integrable (fun t ↦ h t * dirichletR q δ t) := by
    refine (hint.mul_const (∑' n, |c n|)).mono'
      (hf.cont.mul hDcont).aestronglyMeasurable (Filter.Eventually.of_forall fun t ↦ ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hf.nonneg t)]
    exact mul_le_mul_of_nonneg_left (hDbound t) (hf.nonneg t)
  refine ⟨hI, ?_⟩
  -- each term: `∫ h(t) c_n cos(t log n) dt = c_n · 2π f(log n)`
  have hterm : ∀ n, ∫ t, F n t = c n * (2 * π * f (Real.log n)) := fun n ↦ by
    have h1 : ∫ t, F n t = c n * ∫ t, h t * Real.cos (t * Real.log n) := by
      rw [← integral_const_mul]
      exact integral_congr_ae (Filter.Eventually.of_forall fun t ↦ by simp only [hF]; ring)
    have h2 : ∫ t, h t * Real.cos (t * Real.log n) = 2 * π * f (Real.log n) := by
      rw [hf.inv (Real.log n), ← mul_assoc, mul_one_div_cancel (by positivity), one_mul]
    rw [h1, h2]
  -- terms with `n ≥ X` vanish
  have hvanish : ∀ n ∉ Finset.range X, c n * (2 * π * f (Real.log n)) = 0 := fun n hn ↦ by
    rw [Finset.mem_range, not_lt] at hn
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · simp [hc, coeff]
    · have hle : Real.log X ≤ Real.log n := by
        rcases Nat.eq_zero_or_pos X with rfl | hX
        · simpa using Real.log_natCast_nonneg n
        · exact Real.log_le_log (by exact_mod_cast hX) (by exact_mod_cast hn)
      rw [hf.supp _ hle]
      ring
  calc ∫ t, h t * dirichletR q δ t = ∫ t, ∑' n, F n t := by simp only [hpt]
    _ = ∑' n, ∫ t, F n t := (integral_tsum_of_summable_integral_norm hFint hFsum).symm
    _ = ∑' n, c n * (2 * π * f (Real.log n)) := by simp only [hterm]
    _ = ∑ n ∈ Finset.range X, c n * (2 * π * f (Real.log n)) := tsum_eq_sum hvanish
    _ = π * primeTermR q f X δ := by
      rw [primeTermR, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun n _ ↦ ?_
      simp only [hc]
      ring

/-- Helper for **I2**: `t ↦ h(t) cos(tu)` is integrable (dominated by `h`). -/
theorem archPair_integrable_mul_cos {L : ℝ} (hf : WeilAdmissible f L h) (u : ℝ) :
    Integrable (fun t : ℝ ↦ h t * Real.cos (t * u)) := by
  refine hf.integrable.mono' ?_ (Filter.Eventually.of_forall fun t ↦ ?_)
  · exact (hf.cont.mul (by fun_prop)).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hf.nonneg t)]
    exact mul_le_of_le_one_right (hf.nonneg t) (Real.abs_cos_le_one _)

/-- Helper for **I2**: `∫ h(t) (1 - cos(tu)) dt = 2π (1 - f u)` (A2 and inversion). -/
theorem archPair_integral_mul_one_sub_cos {L : ℝ} (hf : WeilAdmissible f L h) (u : ℝ) :
    ∫ t : ℝ, h t * (1 - Real.cos (t * u)) = 2 * π * (1 - f u) := by
  have h1 := archPair_integrable_mul_cos hf u
  have h2 : ∫ t : ℝ, h t * Real.cos (t * u) = 2 * π * f u := by
    have hpi : (2 * π : ℝ) ≠ 0 := by positivity
    rw [hf.inv u, ← mul_assoc, mul_one_div_cancel hpi, one_mul]
  calc ∫ t : ℝ, h t * (1 - Real.cos (t * u))
      = ∫ t : ℝ, (h t - h t * Real.cos (t * u)) := by
        congr 1
        ext t
        ring
    _ = (∫ t : ℝ, h t) - ∫ t : ℝ, h t * Real.cos (t * u) := integral_sub hf.integrable h1
    _ = 2 * π * (1 - f u) := by
        rw [hf.integral_eq, h2]
        ring

/-- Helper for **I2**: Gauss' integral G3 at `a = 3/4 + δ/2`, `τ = t/2`, after the substitution
`w = 2u`. -/
theorem archPair_re_digamma_eq {δ : ℝ} (hδ : 0 ≤ δ) (t : ℝ) :
    (digamma (((3 / 4 + δ / 2 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * I)).re
      = (digamma ((3 / 4 + δ / 2 : ℝ) : ℂ)).re +
        ∫ u in Set.Ioi (0 : ℝ),
          2 * Real.exp (-(3 / 2 + δ) * u) / (1 - Real.exp (-2 * u)) * (1 - Real.cos (t * u)) := by
  have ha : (0 : ℝ) < 3 / 4 + δ / 2 := by positivity
  have h3 := re_digamma_add_mul_I_sub ha (t / 2)
  have hsub := integral_comp_mul_left_Ioi
    (fun w : ℝ ↦ Real.exp (-(3 / 4 + δ / 2) * w) * (1 - Real.cos (t / 2 * w)) /
      (1 - Real.exp (-w))) (0 : ℝ) (b := 2) (by norm_num)
  rw [mul_zero, smul_eq_mul] at hsub
  have hEq : ∫ u in Set.Ioi (0 : ℝ),
        2 * Real.exp (-(3 / 2 + δ) * u) / (1 - Real.exp (-2 * u)) * (1 - Real.cos (t * u))
      = 2 * ∫ u in Set.Ioi (0 : ℝ),
          Real.exp (-(3 / 4 + δ / 2) * (2 * u)) * (1 - Real.cos (t / 2 * (2 * u))) /
            (1 - Real.exp (-(2 * u))) := by
    rw [← integral_const_mul]
    congr 1
    ext u
    have e1 : -(3 / 4 + δ / 2) * (2 * u) = -(3 / 2 + δ) * u := by ring
    have e2 : t / 2 * (2 * u) = t * u := by ring
    have e3 : -(2 * u) = -2 * u := by ring
    rw [e1, e2, e3]
    ring
  rw [hEq, hsub, ← h3]
  ring

/-- **I2** (L). Archimedean side. For `δ ≥ 0`, `t ↦ h(t) · Re ψ(3/4 + δ/2 + it/2)` is integrable
and its integral is `2π · archTermR f δ`.

Proof sketch: G3 with `a = 3/4 + δ/2`, `τ = t/2` writes
`Re ψ(a + it/2) = ψ(a) + ∫₀^∞ e^{-a w}(1 - cos(t w/2))/(1 - e^{-w}) dw` with a nonnegative
integrand; Tonelli (`integral_integral_swap` after `lintegral`-finiteness, or
`MeasureTheory.integral_prod` + `Integrable` from nonnegativity) and
`∫ h(t)(1 - cos(tu)) dt = 2π (1 - f u)` (A2 + `inv`); substitute `w = 2u`
(`integral_comp_mul_left_Ioi`). Finiteness is A6. -/
theorem integral_h_mul_re_digamma {L : ℝ} (hf : WeilAdmissible f L h) {δ : ℝ} (hδ : 0 ≤ δ) :
    Integrable (fun t : ℝ ↦
        h t * (digamma (((3 / 4 + δ / 2 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * I)).re) ∧
      ∫ t : ℝ, h t * (digamma (((3 / 4 + δ / 2 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * I)).re
        = 2 * π * archTermR f δ := by
  classical
  -- the kernel and the two-variable integrand
  let K : ℝ → ℝ := fun u ↦ 2 * Real.exp (-(3 / 2 + δ) * u) / (1 - Real.exp (-2 * u))
  let F : ℝ → ℝ → ℝ := fun t u ↦ h t * (K u * (1 - Real.cos (t * u)))
  let ν : Measure ℝ := volume.restrict (Set.Ioi 0)
  have hKnn : ∀ u ∈ Set.Ioi (0 : ℝ), 0 ≤ K u := by
    intro u hu
    have hu' : (0 : ℝ) < u := hu
    have h1 : Real.exp (-2 * u) < 1 := by
      rw [Real.exp_lt_one_iff]
      linarith
    exact div_nonneg (by positivity) (by linarith)
  have hFnn : ∀ t, ∀ u ∈ Set.Ioi (0 : ℝ), 0 ≤ F t u := by
    intro t u hu
    exact mul_nonneg (hf.nonneg t)
      (mul_nonneg (hKnn u hu) (by linarith [Real.cos_le_one (t * u)]))
  have hFmeas : Measurable (Function.uncurry F) := by
    have hh : Measurable h := hf.cont.measurable
    show Measurable fun p : ℝ × ℝ ↦
      h p.1 * (2 * Real.exp (-(3 / 2 + δ) * p.2) / (1 - Real.exp (-2 * p.2)) *
        (1 - Real.cos (p.1 * p.2)))
    fun_prop
  -- Tonelli: the integrand is integrable on the product
  have hFint : Integrable (Function.uncurry F) ((volume : Measure ℝ).prod ν) := by
    rw [integrable_prod_iff' hFmeas.aestronglyMeasurable]
    constructor
    · refine Filter.Eventually.of_forall fun u ↦ ?_
      have h1 := (hf.integrable.sub (archPair_integrable_mul_cos hf u)).const_mul (K u)
      refine h1.congr (Filter.Eventually.of_forall fun t ↦ ?_)
      show K u * (h t - h t * Real.cos (t * u)) = h t * (K u * (1 - Real.cos (t * u)))
      ring
    · have hA : Integrable (fun u ↦ 2 * π * archIntegrand f δ u) ν :=
        (hf.integrableOn_archIntegrand hδ).const_mul (2 * π)
      refine hA.congr ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      have hn : ∀ t, ‖Function.uncurry F (t, u)‖ = K u * (h t * (1 - Real.cos (t * u))) := by
        intro t
        rw [Function.uncurry_apply_pair, Real.norm_eq_abs, abs_of_nonneg (hFnn t u hu)]
        show h t * (K u * (1 - Real.cos (t * u))) = K u * (h t * (1 - Real.cos (t * u)))
        ring
      simp_rw [hn]
      rw [integral_const_mul, archPair_integral_mul_one_sub_cos hf u]
      show 2 * π * (2 * Real.exp (-(3 / 2 + δ) * u) / (1 - Real.exp (-2 * u)) * (1 - f u))
        = 2 * Real.exp (-(3 / 2 + δ) * u) / (1 - Real.exp (-2 * u)) * (2 * π * (1 - f u))
      ring
  -- pointwise identity from Gauss' integral
  have hfun : (fun t : ℝ ↦
        h t * (digamma (((3 / 4 + δ / 2 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * I)).re)
      = fun t : ℝ ↦ h t * (digamma ((3 / 4 + δ / 2 : ℝ) : ℂ)).re + ∫ u, F t u ∂ν := by
    funext t
    rw [archPair_re_digamma_eq hδ t, mul_add]
    congr 1
    show h t * ∫ u in Set.Ioi (0 : ℝ), K u * (1 - Real.cos (t * u))
      = ∫ u in Set.Ioi (0 : ℝ), h t * (K u * (1 - Real.cos (t * u)))
    rw [integral_const_mul]
  have hI0 : Integrable (fun t : ℝ ↦ h t * (digamma ((3 / 4 + δ / 2 : ℝ) : ℂ)).re) :=
    hf.integrable.mul_const _
  have hI1 : Integrable (fun t : ℝ ↦ ∫ u, F t u ∂ν) := hFint.integral_prod_left
  have hswap : ∫ t : ℝ, ∫ u, F t u ∂ν = 2 * π * ∫ u in Set.Ioi (0 : ℝ), archIntegrand f δ u := by
    rw [integral_integral_swap hFint, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun u _ ↦ ?_
    show ∫ t : ℝ, h t * (K u * (1 - Real.cos (t * u))) = 2 * π * archIntegrand f δ u
    have hc : ∀ t : ℝ, h t * (K u * (1 - Real.cos (t * u)))
        = K u * (h t * (1 - Real.cos (t * u))) := fun t ↦ by ring
    simp_rw [hc]
    rw [integral_const_mul, archPair_integral_mul_one_sub_cos hf u]
    show 2 * Real.exp (-(3 / 2 + δ) * u) / (1 - Real.exp (-2 * u)) * (2 * π * (1 - f u))
      = 2 * π * (2 * Real.exp (-(3 / 2 + δ) * u) / (1 - Real.exp (-2 * u)) * (1 - f u))
    ring
  rw [hfun]
  refine ⟨hI0.add hI1, ?_⟩
  rw [integral_add hI0 hI1, integral_mul_const, hf.integral_eq, hswap, archTermR]
  ring

/-- Helper for **I3**: Tonelli for a countable family of nonnegative integrable real functions
whose integrals are summable. The pointwise sum is integrable and can be integrated termwise. -/
theorem i3_integrable_tsum_of_nonneg {ι : Type*} [Countable ι] {G : ι → ℝ → ℝ}
    (hG_int : ∀ i, Integrable (G i)) (hG_nonneg : ∀ i t, 0 ≤ G i t)
    (hG_sum : Summable fun i ↦ ∫ t, G i t) :
    Integrable (fun t ↦ ∑' i, G i t) ∧ ∫ t, ∑' i, G i t = ∑' i, ∫ t, G i t := by
  have hnorm : (fun i ↦ ∫ t, ‖G i t‖) = fun i ↦ ∫ t, G i t := by
    funext i
    exact integral_congr_ae
      (Filter.Eventually.of_forall fun t ↦ Real.norm_of_nonneg (hG_nonneg i t))
  refine ⟨?_, (integral_tsum_of_summable_integral_norm hG_int (hnorm ▸ hG_sum)).symm⟩
  have hmeas : ∀ i, AEMeasurable (fun t ↦ ENNReal.ofReal (G i t)) :=
    fun i ↦ (hG_int i).aestronglyMeasurable.aemeasurable.ennreal_ofReal
  have hfin : ∫⁻ t, ∑' i, ENNReal.ofReal (G i t) ≠ ⊤ := by
    rw [lintegral_tsum hmeas]
    have hi : ∀ i, ∫⁻ t, ENNReal.ofReal (G i t) = ENNReal.ofReal (∫ t, G i t) := fun i ↦
      (ofReal_integral_eq_lintegral_ofReal (hG_int i)
        (Filter.Eventually.of_forall (hG_nonneg i))).symm
    simp_rw [hi]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun i ↦ integral_nonneg (hG_nonneg i)) hG_sum]
    exact ENNReal.ofReal_ne_top
  have hint := integrable_toReal_of_lintegral_ne_top (AEMeasurable.tsum hmeas) hfin
  refine hint.congr (Filter.Eventually.of_forall fun t ↦ ?_)
  simp only
  rw [ENNReal.tsum_toReal_eq (fun i ↦ ENNReal.ofReal_ne_top)]
  exact tsum_congr fun i ↦ ENNReal.toReal_ofReal (hG_nonneg i t)

/-- Helper for **I3**: the real form of A7 at a real damping parameter `δ > 0`. -/
theorem i3_poisson_bound {L : ℝ} (hf : WeilAdmissible f L h) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, ∀ γ : ℝ, Integrable (fun t : ℝ ↦ h t * poissonKer δ (t - γ)) ∧
      ∫ t : ℝ, h t * poissonKer δ (t - γ) ≤ C / (1 + γ ^ 2) := by
  obtain ⟨C, hC⟩ := hf.exists_poisson_bound (a := δ) (b := δ) hδ
  refine ⟨C, fun γ ↦ ?_⟩
  have key : ∀ t : ℝ, (δ : ℂ) / ((δ : ℂ) ^ 2 + ((t - γ : ℝ) : ℂ) ^ 2)
      = ((poissonKer δ (t - γ) : ℝ) : ℂ) := by
    intro t
    simp [poissonKer]
  have hpos : ∀ t : ℝ, 0 ≤ poissonKer δ (t - γ) := fun t ↦ by
    unfold poissonKer; positivity
  obtain ⟨hint, hle⟩ := hC (δ : ℂ) (by simp) (by simp [abs_of_pos hδ]) γ
  constructor
  · have hre := hint.re
    refine hre.congr (Filter.Eventually.of_forall fun t ↦ ?_)
    simp only [key]
    rw [← Complex.ofReal_mul]
    exact Complex.ofReal_re _
  · have heq : ∀ t : ℝ, h t * poissonKer δ (t - γ)
        = h t * ‖(δ : ℂ) / ((δ : ℂ) ^ 2 + ((t - γ : ℝ) : ℂ) ^ 2)‖ := fun t ↦ by
      rw [key, Complex.norm_real, Real.norm_of_nonneg (hpos t)]
    simp_rw [heq]
    exact hle

/-- **I3** (M). Zero side. For `δ > 0`, `t ↦ h(t) · ∑_ρ m(ρ) δ/(δ²+(t-Im ρ)²)` is integrable with
integral `π · zeroSideR q h δ`.

Proof sketch: all terms are nonnegative; Tonelli for `∑' ρ : ℂ` (restrict to the countable support
of `mult q`, `Summable.countable_support` applied to L2c; `lintegral_tsum` or
`integral_tsum`), finiteness from A7 (`δ` real) and L2c. -/
theorem integral_h_mul_zerosKer {L : ℝ} (hq : q % 4 = 3) (hf : WeilAdmissible f L h) {δ : ℝ}
    (hδ : 0 < δ) :
    Integrable (fun t ↦ h t * zerosKer q δ t) ∧
      ∫ t, h t * zerosKer q δ t = π * zeroSideR q h δ := by
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
  obtain ⟨C, hC⟩ := i3_poisson_bound hf hδ
  -- the family of nonnegative terms
  let G : S → ℝ → ℝ := fun ρ t ↦ h t * ((mult q ρ : ℝ) * poissonKer δ (t - (ρ : ℂ).im))
  have hG_int : ∀ ρ, Integrable (G ρ) := fun ρ ↦ by
    have hc := ((hC (ρ : ℂ).im).1).const_mul (mult q ρ : ℝ)
    refine hc.congr (Filter.Eventually.of_forall fun t ↦ ?_)
    simp only [G]
    ring
  have hG_nonneg : ∀ ρ t, 0 ≤ G ρ t := fun ρ t ↦
    mul_nonneg (hf.nonneg t) (mul_nonneg (Nat.cast_nonneg _) (by unfold poissonKer; positivity))
  have hG_eq : ∀ ρ : S, ∫ t, G ρ t
      = (mult q ρ : ℝ) * ∫ t, h t * poissonKer δ (t - (ρ : ℂ).im) := fun ρ ↦ by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t ↦ ?_)
    simp only [G]
    ring
  have hG_sum : Summable fun ρ : S ↦ ∫ t, G ρ t := by
    have hbig : Summable fun ρ : S ↦ C * ((mult q ρ : ℝ) / (1 + (ρ : ℂ).im ^ 2)) :=
      (hL2c.mul_left C).comp_injective Subtype.coe_injective
    refine Summable.of_nonneg_of_le (fun ρ ↦ integral_nonneg (hG_nonneg ρ)) (fun ρ ↦ ?_) hbig
    rw [hG_eq]
    calc (mult q ρ : ℝ) * ∫ t, h t * poissonKer δ (t - (ρ : ℂ).im)
        ≤ (mult q ρ : ℝ) * (C / (1 + (ρ : ℂ).im ^ 2)) :=
          mul_le_mul_of_nonneg_left (hC _).2 (Nat.cast_nonneg _)
      _ = C * ((mult q ρ : ℝ) / (1 + (ρ : ℂ).im ^ 2)) := by ring
  obtain ⟨hint, hval⟩ := i3_integrable_tsum_of_nonneg hG_int hG_nonneg hG_sum
  have hfun : (fun t ↦ h t * zerosKer q δ t) = fun t ↦ ∑' ρ : S, G ρ t := by
    funext t
    unfold zerosKer
    have hsub : Function.support (fun ρ : ℂ ↦ (mult q ρ : ℝ) * poissonKer δ (t - ρ.im)) ⊆ S := by
      intro ρ hρ
      by_contra hn
      exact hρ (by simp [hzero ρ hn])
    rw [← tsum_subtype_eq_of_support_subset hsub, ← tsum_mul_left]
  rw [hfun]
  refine ⟨hint, ?_⟩
  rw [hval]
  unfold zeroSideR
  have hsub : Function.support
      (fun ρ : ℂ ↦ (mult q ρ : ℝ) * (1 / π * ∫ t : ℝ, h t * poissonKer δ (t - ρ.im))) ⊆ S := by
    intro ρ hρ
    by_contra hn
    exact hρ (by simp [hzero ρ hn])
  rw [← tsum_subtype_eq_of_support_subset hsub, ← tsum_mul_left]
  refine tsum_congr fun ρ ↦ ?_
  rw [hG_eq]
  field_simp

end Exp7.EF
