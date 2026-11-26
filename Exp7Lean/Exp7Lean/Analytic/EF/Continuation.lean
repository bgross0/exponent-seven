import Exp7Lean.Analytic.EF.DampedFormula

/-!
# Explicit formula blueprint: analytic continuation in the damping parameter

Leaves **K2–K5**, proved nodes **K1, K6, C2–C4** of `BLUEPRINT.md`.

Both sides of the damped explicit formula are restrictions to `δ ∈ (0,∞)` of functions holomorphic
on `Re δ > 0`; they agree for `δ > 1/2` (C1), hence for all `δ > 0` (identity theorem).  The zero
side is `≥ 0` for every `δ > 0`, and the arithmetic side is continuous at `δ = 0⁺`, where it equals
`log(q/π) + ψ(3/4) + J_f - primeSum q f X`.
-/

namespace Exp7.EF

open Real MeasureTheory Complex Filter Topology

variable (q : ℕ) [Fact q.Prime] {f h : ℝ → ℝ} {X : ℕ}

/-- **K1** (proved). The complex zero side restricted to real `δ` is the real zero side. -/
theorem zeroSide_ofReal (δ : ℝ) : zeroSide q h (δ : ℂ) = (zeroSideR q h δ : ℂ) := by
  unfold zeroSide zeroSideR
  rw [Complex.ofReal_tsum]
  refine tsum_congr fun ρ ↦ ?_
  have hker : ∀ t : ℝ, (h t : ℂ) * ((δ : ℂ) / ((δ : ℂ) ^ 2 + ((t - ρ.im : ℝ) : ℂ) ^ 2))
      = ((h t * poissonKer δ (t - ρ.im) : ℝ) : ℂ) := by
    intro t
    unfold poissonKer
    push_cast
    ring
  simp_rw [hker]
  rw [integral_complex_ofReal]
  push_cast
  ring

/-- **K2** (M). The complex arithmetic side restricted to real `δ ≥ 0` is the real arithmetic side
(G7 for `ψ`, `integral_ofReal`, `Complex.ofReal_cpow`). -/
theorem arithSide_ofReal {δ : ℝ} (hδ : 0 ≤ δ) :
    arithSide q f X (δ : ℂ) = (arithSideR q f X δ : ℂ) := by
  -- the digamma term: `ψ` is real on the positive real axis (G7)
  have hdig : digamma (3 / 4 + (δ : ℂ) / 2) = ((digamma ((3 / 4 + δ / 2 : ℝ) : ℂ)).re : ℂ) := by
    have hpos : (0 : ℝ) < 3 / 4 + δ / 2 := by linarith
    have hcast : (3 / 4 + (δ : ℂ) / 2) = ((3 / 4 + δ / 2 : ℝ) : ℂ) := by push_cast; ring
    rw [hcast]
    refine Complex.ext ?_ ?_
    · rw [Complex.ofReal_re]
    · rw [digamma_ofReal_im hpos, Complex.ofReal_im]
  -- the archimedean integral: the integrand is pointwise the cast of the real integrand
  have hint : ∫ u in Set.Ioi (0 : ℝ),
      2 * Complex.exp (-(3 / 2 + (δ : ℂ)) * u) / (1 - Complex.exp (-2 * u)) * ((1 - f u : ℝ) : ℂ)
      = ((∫ u in Set.Ioi (0 : ℝ), archIntegrand f δ u : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine integral_congr_ae (Eventually.of_forall fun u ↦ ?_)
    simp only [archIntegrand]
    push_cast
    ring
  -- the prime term: `n ≥ 0`, so the complex power is the cast of the real power
  have hprime : primeTerm q f X (δ : ℂ) = (primeTermR q f X δ : ℂ) := by
    unfold primeTerm primeTermR
    rw [Complex.ofReal_mul, Complex.ofReal_sum]
    congr 1
    refine Finset.sum_congr rfl fun n _ ↦ ?_
    rw [Complex.ofReal_mul (coeff q n * f (Real.log n)),
      Complex.ofReal_cpow (Nat.cast_nonneg n)]
    push_cast
    ring
  unfold arithSide arithSideR archTerm archTermR
  rw [hdig, hint, hprime]
  push_cast
  ring

/-- Helper for **K3**. For `a ≤ Re δ` (`a > 0`) and real `x`, `a² ≤ ‖δ² + x²‖`
(`δ² + x² = (δ + ix)(δ - ix)` and both factors have real part `Re δ`). -/
private lemma sq_le_norm_sq_add_sq {a : ℝ} (ha : 0 < a) {δ : ℂ} (hδ : a ≤ δ.re) (x : ℝ) :
    a ^ 2 ≤ ‖δ ^ 2 + (x : ℂ) ^ 2‖ := by
  have hfac : δ ^ 2 + (x : ℂ) ^ 2 = (δ + x * I) * (δ - x * I) := by
    linear_combination ((x : ℂ) ^ 2) * Complex.I_sq
  have h1 : a ≤ ‖δ + x * I‖ := by
    have h := Complex.abs_re_le_norm (δ + x * I)
    have h' : (δ + x * I).re = δ.re := by simp
    rw [h'] at h
    exact hδ.trans ((le_abs_self _).trans h)
  have h2 : a ≤ ‖δ - x * I‖ := by
    have h := Complex.abs_re_le_norm (δ - x * I)
    have h' : (δ - x * I).re = δ.re := by simp
    rw [h'] at h
    exact hδ.trans ((le_abs_self _).trans h)
  rw [hfac, norm_mul, pow_two]
  exact mul_le_mul h1 h2 ha.le (ha.le.trans h1)

/-- Helper for **K3**. Each Poisson integral `δ ↦ ∫ h(t) δ/(δ² + (t-γ)²) dt` is holomorphic on the
open box `a < Re δ`, `‖δ‖ < b` (differentiation under the integral sign; the `δ`-derivative of the
kernel is bounded on the box by `1/a² + 2b²/a⁴`, and `h` is integrable). -/
private lemma differentiableOn_poisson_integral {L : ℝ} (hf : WeilAdmissible f L h) {a b : ℝ}
    (ha : 0 < a) (γ : ℝ) :
    DifferentiableOn ℂ
      (fun δ : ℂ ↦ ∫ t : ℝ, (h t : ℂ) * (δ / (δ ^ 2 + ((t - γ : ℝ) : ℂ) ^ 2)))
      {δ : ℂ | a < δ.re ∧ ‖δ‖ < b} := by
  obtain ⟨C, hC⟩ := hf.exists_poisson_bound (a := a) (b := b) ha
  have hUo : IsOpen {δ : ℂ | a < δ.re ∧ ‖δ‖ < b} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt continuous_norm continuous_const)
  intro δ₀ hδ₀
  refine DifferentiableAt.differentiableWithinAt ?_
  have hm : Measurable h := hf.cont.measurable
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := (volume : Measure ℝ))
    (F := fun (δ : ℂ) (t : ℝ) ↦ (h t : ℂ) * (δ / (δ ^ 2 + ((t - γ : ℝ) : ℂ) ^ 2)))
    (F' := fun (δ : ℂ) (t : ℝ) ↦ (h t : ℂ) *
      ((1 * (δ ^ 2 + ((t - γ : ℝ) : ℂ) ^ 2) - δ * (2 * δ)) /
        (δ ^ 2 + ((t - γ : ℝ) : ℂ) ^ 2) ^ 2))
    (x₀ := δ₀) (bound := fun t ↦ h t * (1 / a ^ 2 + 2 * b ^ 2 / (a ^ 2) ^ 2))
    (s := {δ : ℂ | a < δ.re ∧ ‖δ‖ < b}) (hUo.mem_nhds hδ₀) ?_ ?_ ?_ ?_ ?_ ?_
  · exact key.2.differentiableAt
  · filter_upwards [hUo.mem_nhds hδ₀] with δ hδ
    exact (hC δ hδ.1.le hδ.2.le γ).1.aestronglyMeasurable
  · exact (hC δ₀ hδ₀.1.le hδ₀.2.le γ).1
  · exact (by fun_prop : Measurable fun t : ℝ ↦ (h t : ℂ) *
      ((1 * (δ₀ ^ 2 + ((t - γ : ℝ) : ℂ) ^ 2) - δ₀ * (2 * δ₀)) /
        (δ₀ ^ 2 + ((t - γ : ℝ) : ℂ) ^ 2) ^ 2)).aestronglyMeasurable
  · refine Eventually.of_forall fun t δ hδ ↦ ?_
    have hD : a ^ 2 ≤ ‖δ ^ 2 + ((t - γ : ℝ) : ℂ) ^ 2‖ := sq_le_norm_sq_add_sq ha hδ.1.le _
    have ha2 : 0 < a ^ 2 := by positivity
    have hDpos : 0 < ‖δ ^ 2 + ((t - γ : ℝ) : ℂ) ^ 2‖ := ha2.trans_le hD
    have hb : ‖δ‖ ^ 2 ≤ b ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hδ.2.le 2
    have hnum : ‖1 * (δ ^ 2 + ((t - γ : ℝ) : ℂ) ^ 2) - δ * (2 * δ)‖
        ≤ ‖δ ^ 2 + ((t - γ : ℝ) : ℂ) ^ 2‖ + 2 * b ^ 2 := by
      refine (norm_sub_le _ _).trans ?_
      have h2 : ‖δ * (2 * δ)‖ = 2 * ‖δ‖ ^ 2 := by
        rw [norm_mul, norm_mul, Complex.norm_ofNat]; ring
      rw [one_mul, h2]
      linarith
    have hker : ‖(1 * (δ ^ 2 + ((t - γ : ℝ) : ℂ) ^ 2) - δ * (2 * δ)) /
        (δ ^ 2 + ((t - γ : ℝ) : ℂ) ^ 2) ^ 2‖ ≤ 1 / a ^ 2 + 2 * b ^ 2 / (a ^ 2) ^ 2 := by
      rw [norm_div, norm_pow]
      calc ‖1 * (δ ^ 2 + ((t - γ : ℝ) : ℂ) ^ 2) - δ * (2 * δ)‖ /
            ‖δ ^ 2 + ((t - γ : ℝ) : ℂ) ^ 2‖ ^ 2
          ≤ (‖δ ^ 2 + ((t - γ : ℝ) : ℂ) ^ 2‖ + 2 * b ^ 2) /
            ‖δ ^ 2 + ((t - γ : ℝ) : ℂ) ^ 2‖ ^ 2 := by gcongr
        _ = 1 / ‖δ ^ 2 + ((t - γ : ℝ) : ℂ) ^ 2‖ +
            2 * b ^ 2 / ‖δ ^ 2 + ((t - γ : ℝ) : ℂ) ^ 2‖ ^ 2 := by
          field_simp
        _ ≤ 1 / a ^ 2 + 2 * b ^ 2 / (a ^ 2) ^ 2 := by gcongr
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hf.nonneg t)]
    exact mul_le_mul_of_nonneg_left hker (hf.nonneg t)
  · exact hf.integrable.mul_const _
  · refine Eventually.of_forall fun t δ hδ ↦ ?_
    have hD : a ^ 2 ≤ ‖δ ^ 2 + ((t - γ : ℝ) : ℂ) ^ 2‖ := sq_le_norm_sq_add_sq ha hδ.1.le _
    have hne : δ ^ 2 + ((t - γ : ℝ) : ℂ) ^ 2 ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hD
      have : 0 < a ^ 2 := by positivity
      linarith
    have hd : HasDerivAt (fun y : ℂ ↦ y ^ 2 + ((t - γ : ℝ) : ℂ) ^ 2) (2 * δ) δ := by
      simpa using ((hasDerivAt_id δ).pow 2).add_const (((t - γ : ℝ) : ℂ) ^ 2)
    exact (((hasDerivAt_id δ).fun_div hd hne).const_mul (h t : ℂ))

/-- **K3** (L). The zero side is holomorphic on `Re δ > 0`.

Proof sketch: locally (on boxes `a < Re δ`, `‖δ‖ < b`) each term is holomorphic in `δ`
(`hasDerivAt_integral_of_dominated_loc_of_deriv_le`, or Morera/`DifferentiableOn` of parametric
integrals; domination by A7) and bounded by `m(ρ) · C/(1 + (Im ρ)²)` (A7), which is summable (L2c);
conclude with `differentiableOn_tsum_of_summable_norm`. -/
theorem differentiableOn_zeroSide {L : ℝ} (hq : q % 4 = 3) (hf : WeilAdmissible f L h) :
    DifferentiableOn ℂ (zeroSide q h) rightHalfPlane := by
  intro δ₀ hδ₀
  have hre : 0 < δ₀.re := hδ₀
  -- work on the open box `a < Re δ`, `‖δ‖ < b` around `δ₀`
  obtain ⟨a, ha, haδ⟩ : ∃ a : ℝ, 0 < a ∧ a < δ₀.re := ⟨δ₀.re / 2, by linarith, by linarith⟩
  obtain ⟨b, hbδ⟩ : ∃ b : ℝ, ‖δ₀‖ < b := ⟨‖δ₀‖ + 1, by linarith⟩
  have hUo : IsOpen {δ : ℂ | a < δ.re ∧ ‖δ‖ < b} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt continuous_norm continuous_const)
  have hmem : δ₀ ∈ {δ : ℂ | a < δ.re ∧ ‖δ‖ < b} := ⟨haδ, hbδ⟩
  obtain ⟨C, hC⟩ := hf.exists_poisson_bound (a := a) (b := b) ha
  have hsum : Summable (fun ρ : ℂ ↦ 1 / π * C * ((mult q ρ : ℝ) / (1 + ρ.im ^ 2))) :=
    (summable_mult_div q hq).mul_left _
  have hD : DifferentiableOn ℂ (fun w : ℂ ↦ ∑' ρ : ℂ, (mult q ρ : ℂ) *
      (1 / π * ∫ t : ℝ, (h t : ℂ) * (w / (w ^ 2 + ((t - ρ.im : ℝ) : ℂ) ^ 2))))
      {δ : ℂ | a < δ.re ∧ ‖δ‖ < b} := by
    refine differentiableOn_tsum_of_summable_norm hsum (fun ρ ↦ ?_) hUo (fun ρ w hw ↦ ?_)
    · exact ((differentiableOn_poisson_integral hf ha ρ.im).const_mul _).const_mul _
    · obtain ⟨-, hle⟩ := hC w hw.1.le hw.2.le ρ.im
      have h1 : ‖∫ t : ℝ, (h t : ℂ) * (w / (w ^ 2 + ((t - ρ.im : ℝ) : ℂ) ^ 2))‖
          ≤ C / (1 + ρ.im ^ 2) := by
        refine (norm_integral_le_integral_norm _).trans (le_trans (le_of_eq ?_) hle)
        refine integral_congr_ae (Eventually.of_forall fun t ↦ ?_)
        simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hf.nonneg t)]
      have hπ : ‖(1 / π : ℂ)‖ = 1 / π := by
        rw [norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
      rw [norm_mul, norm_mul, Complex.norm_natCast, hπ]
      have hm0 : (0 : ℝ) ≤ (mult q ρ : ℝ) := Nat.cast_nonneg _
      have hπ0 : (0 : ℝ) ≤ 1 / π := by positivity
      calc (mult q ρ : ℝ) * (1 / π *
            ‖∫ t : ℝ, (h t : ℂ) * (w / (w ^ 2 + ((t - ρ.im : ℝ) : ℂ) ^ 2))‖)
          ≤ (mult q ρ : ℝ) * (1 / π * (C / (1 + ρ.im ^ 2))) := by gcongr
        _ = 1 / π * C * ((mult q ρ : ℝ) / (1 + ρ.im ^ 2)) := by ring
  exact (hD.differentiableAt (hUo.mem_nhds hmem)).differentiableWithinAt

/-- Helper for **K4**. The complex archimedean integrand is `e^{-δu}` times the real integrand at
`δ = 0`. -/
private theorem archKernel_eq (f : ℝ → ℝ) (δ : ℂ) (u : ℝ) :
    2 * Complex.exp (-(3 / 2 + δ) * u) / (1 - Complex.exp (-2 * u)) * ((1 - f u : ℝ) : ℂ)
      = Complex.exp (-δ * u) * ((archIntegrand f 0 u : ℝ) : ℂ) := by
  unfold archIntegrand
  have h1 : Complex.exp (-(3 / 2 + δ) * u)
      = Complex.exp (-δ * u) * Complex.exp (-(3 / 2 + (0 : ℝ)) * u) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [h1]
  push_cast
  ring

/-- Helper for **K4** (holomorphy of a Laplace transform). For `g` integrable on `(0,∞)`,
`δ ↦ ∫₀^∞ e^{-δu} g(u) du` is complex-differentiable at every `δ₀` with `Re δ₀ > 0`. -/
private theorem differentiableAt_laplace {g : ℝ → ℝ} (hg : IntegrableOn g (Set.Ioi 0)) {δ₀ : ℂ}
    (hδ₀ : 0 < δ₀.re) :
    DifferentiableAt ℂ
      (fun δ : ℂ ↦ ∫ u in Set.Ioi (0 : ℝ), Complex.exp (-δ * u) * ((g u : ℝ) : ℂ)) δ₀ := by
  set a : ℝ := δ₀.re / 2 with ha
  have ha0 : 0 < a := by positivity
  have hgC : AEStronglyMeasurable (fun u : ℝ ↦ ((g u : ℝ) : ℂ)) (volume.restrict (Set.Ioi 0)) :=
    hg.ofReal.aestronglyMeasurable
  have hnorm : ∀ (δ : ℂ) (u : ℝ), ‖Complex.exp (-δ * u)‖ = Real.exp (-(δ.re * u)) := by
    intro δ u
    rw [Complex.norm_exp]
    congr 1
    simp
  have hmeas : ∀ δ : ℂ, AEStronglyMeasurable
      (fun u : ℝ ↦ Complex.exp (-δ * u) * ((g u : ℝ) : ℂ)) (volume.restrict (Set.Ioi 0)) := by
    intro δ
    have hc : Continuous (fun u : ℝ ↦ Complex.exp (-δ * u)) := by fun_prop
    exact hc.aestronglyMeasurable.mul hgC
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Set.Ioi (0 : ℝ)))
    (F := fun (δ : ℂ) (u : ℝ) ↦ Complex.exp (-δ * u) * ((g u : ℝ) : ℂ))
    (F' := fun (δ : ℂ) (u : ℝ) ↦ -(u : ℂ) * Complex.exp (-δ * u) * ((g u : ℝ) : ℂ))
    (x₀ := δ₀) (s := Metric.ball δ₀ a) (bound := fun u ↦ 1 / a * ‖g u‖)
    (Metric.ball_mem_nhds δ₀ ha0) (Eventually.of_forall hmeas) ?_ ?_ ?_ ?_ ?_
  · exact key.2.differentiableAt
  · -- integrability at `δ₀`
    refine hg.norm.mono' (hmeas δ₀) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun u hu ↦ ?_)
    have hu0 : (0 : ℝ) < u := hu
    rw [norm_mul, hnorm, Complex.norm_real]
    have h1 : Real.exp (-(δ₀.re * u)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    exact mul_le_of_le_one_left (norm_nonneg _) h1
  · -- measurability of the derivative at `δ₀`
    have hc : Continuous (fun u : ℝ ↦ -(u : ℂ) * Complex.exp (-δ₀ * u)) := by fun_prop
    exact hc.aestronglyMeasurable.mul hgC
  · -- domination of the derivative on the ball
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun u hu δ hδ ↦ ?_)
    have hu0 : (0 : ℝ) < u := hu
    have hre : a < δ.re := by
      have h1 : |(δ - δ₀).re| ≤ ‖δ - δ₀‖ := Complex.abs_re_le_norm _
      have h2 : ‖δ - δ₀‖ < a := by simpa [dist_eq_norm] using hδ
      have h3 := (abs_lt.mp (lt_of_le_of_lt h1 h2)).1
      rw [Complex.sub_re] at h3
      linarith
    rw [norm_mul, norm_mul, norm_neg, Complex.norm_real, hnorm, Real.norm_of_nonneg hu0.le,
      Complex.norm_real]
    have h1 : Real.exp (-(δ.re * u)) ≤ Real.exp (-(a * u)) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have h2 : a * u * Real.exp (-(a * u)) ≤ 1 :=
      (Real.mul_exp_neg_le_exp_neg_one (a * u)).trans (Real.exp_le_one_iff.mpr (by norm_num))
    have h3 : u * Real.exp (-(δ.re * u)) ≤ 1 / a := by
      rw [le_div_iff₀ ha0]
      calc u * Real.exp (-(δ.re * u)) * a ≤ u * Real.exp (-(a * u)) * a :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hu0.le) ha0.le
        _ = a * u * Real.exp (-(a * u)) := by ring
        _ ≤ 1 := h2
    exact mul_le_mul_of_nonneg_right h3 (norm_nonneg (g u))
  · -- the bound is integrable
    exact hg.norm.const_mul _
  · -- pointwise derivative
    refine Eventually.of_forall fun u δ _ ↦ ?_
    have h1 : HasDerivAt (fun δ : ℂ ↦ -δ * (u : ℂ)) (-(u : ℂ)) δ := by
      simpa using ((hasDerivAt_id δ).neg.mul_const (u : ℂ))
    have h2 := (h1.cexp).mul_const ((g u : ℝ) : ℂ)
    convert h2 using 1
    ring

/-- **K4** (M). The arithmetic side is holomorphic on `Re δ > 0`: `ψ(3/4 + δ/2)` by G6, the
archimedean integral by differentiation under the integral sign (domination as in A6), and the
prime term is a finite sum of entire functions `n^{-1/2-δ}` (the `n = 0` term has coefficient
`Λ 0 = 0`). -/
theorem differentiableOn_arithSide {L : ℝ} (hf : WeilAdmissible f L h) :
    DifferentiableOn ℂ (arithSide q f X) rightHalfPlane := by
  intro δ₀ hδ₀
  have hδ₀' : 0 < δ₀.re := hδ₀
  refine DifferentiableAt.differentiableWithinAt ?_
  have hdig : DifferentiableAt ℂ (fun δ : ℂ ↦ Complex.digamma (3 / 4 + δ / 2)) δ₀ := by
    have hre : (0 : ℝ) < (3 / 4 + δ₀ / 2 : ℂ).re := by
      have h34 : ((3 / 4 : ℂ)).re = 3 / 4 := by norm_num
      have h2 : (δ₀ / 2 : ℂ).re = δ₀.re / 2 := by simp
      rw [Complex.add_re, h34, h2]
      linarith
    have h1 : DifferentiableAt ℂ Complex.digamma (3 / 4 + δ₀ / 2) :=
      (analyticOnNhd_digamma_re_pos _ hre).differentiableAt
    have h2 : DifferentiableAt ℂ (fun δ : ℂ ↦ (3 / 4 + δ / 2 : ℂ)) δ₀ := by fun_prop
    exact h1.comp δ₀ h2
  have hint : DifferentiableAt ℂ (fun δ : ℂ ↦ ∫ u in Set.Ioi (0 : ℝ),
      2 * Complex.exp (-(3 / 2 + δ) * u) / (1 - Complex.exp (-2 * u)) * ((1 - f u : ℝ) : ℂ))
      δ₀ := by
    have hL := differentiableAt_laplace (hf.integrableOn_archIntegrand le_rfl) hδ₀'
    have hEq : (fun δ : ℂ ↦ ∫ u in Set.Ioi (0 : ℝ),
        2 * Complex.exp (-(3 / 2 + δ) * u) / (1 - Complex.exp (-2 * u)) * ((1 - f u : ℝ) : ℂ))
        = fun δ : ℂ ↦ ∫ u in Set.Ioi (0 : ℝ),
          Complex.exp (-δ * u) * ((archIntegrand f 0 u : ℝ) : ℂ) := by
      funext δ
      exact integral_congr_ae (Eventually.of_forall fun u ↦ archKernel_eq f δ u)
    rw [hEq]
    exact hL
  have hprime : DifferentiableAt ℂ (primeTerm q f X) δ₀ := by
    have hterm : ∀ n ∈ Finset.range X, DifferentiableAt ℂ (fun δ : ℂ ↦
        ((coeff q n * f (Real.log n) : ℝ) : ℂ) * (n : ℂ) ^ (-(1 / 2 : ℂ) - δ)) δ₀ := by
      intro n _
      have hexp : DifferentiableAt ℂ (fun δ : ℂ ↦ (-(1 / 2 : ℂ) - δ)) δ₀ := by fun_prop
      refine (hexp.const_cpow (Or.inr ?_)).const_mul _
      intro h0
      have h1 := congrArg Complex.re h0
      have h12 : ((1 / 2 : ℂ)).re = 1 / 2 := by norm_num
      rw [Complex.sub_re, Complex.neg_re, h12, Complex.zero_re] at h1
      linarith
    have hsum := DifferentiableAt.fun_sum hterm
    exact hsum.const_mul 2
  have hall : DifferentiableAt ℂ (fun δ : ℂ ↦ ((Real.log (q / π) : ℝ) : ℂ)
      + (Complex.digamma (3 / 4 + δ / 2) + ∫ u in Set.Ioi (0 : ℝ),
        2 * Complex.exp (-(3 / 2 + δ) * u) / (1 - Complex.exp (-2 * u)) * ((1 - f u : ℝ) : ℂ))
      - primeTerm q f X δ) δ₀ :=
    ((differentiableAt_const _).add (hdig.add hint)).sub hprime
  exact hall

/-- Helper for K5: the damped archimedean integrand is the undamped one times `e^{-δu}`. -/
private lemma archIntegrand_eq_exp_mul (f : ℝ → ℝ) (δ u : ℝ) :
    archIntegrand f δ u = Real.exp (-δ * u) * archIntegrand f 0 u := by
  unfold archIntegrand
  rw [show -(3 / 2 + δ) * u = -δ * u + -(3 / 2 + 0) * u by ring, Real.exp_add]
  ring

/-- Helper for K5: continuity of `δ ↦ Re ψ(3/4 + δ/2)` at `δ = 0` (from G6). -/
private lemma tendsto_re_digamma_zero :
    Tendsto (fun δ : ℝ ↦ (digamma ((3 / 4 + δ / 2 : ℝ) : ℂ)).re) (𝓝 0)
      (𝓝 (digamma ((3 / 4 + (0 : ℝ) / 2 : ℝ) : ℂ)).re) := by
  have hmem : ((3 / 4 + (0 : ℝ) / 2 : ℝ) : ℂ) ∈ {s : ℂ | 0 < s.re} := by
    rw [Set.mem_ofPred_eq, Complex.ofReal_re]
    norm_num
  have hc : ContinuousAt digamma ((3 / 4 + (0 : ℝ) / 2 : ℝ) : ℂ) :=
    (analyticOnNhd_digamma_re_pos _ hmem).continuousAt
  have hg : Continuous fun δ : ℝ ↦ ((3 / 4 + δ / 2 : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (by fun_prop)
  have h1 : Tendsto (fun δ : ℝ ↦ digamma ((3 / 4 + δ / 2 : ℝ) : ℂ)) (𝓝 0)
      (𝓝 (digamma ((3 / 4 + (0 : ℝ) / 2 : ℝ) : ℂ))) :=
    hc.tendsto.comp (hg.tendsto 0)
  exact (Complex.continuous_re.tendsto _).comp h1

/-- Helper for K5: dominated convergence for the archimedean integral, with dominating function
`|archIntegrand f 0|` (A6). -/
private lemma tendsto_integral_archIntegrand {L : ℝ} (hf : WeilAdmissible f L h) :
    Tendsto (fun δ : ℝ ↦ ∫ u in Set.Ioi (0 : ℝ), archIntegrand f δ u) (𝓝[>] 0)
      (𝓝 (∫ u in Set.Ioi (0 : ℝ), archIntegrand f 0 u)) := by
  have h0 : IntegrableOn (archIntegrand f 0) (Set.Ioi 0) :=
    hf.integrableOn_archIntegrand le_rfl
  refine tendsto_integral_filter_of_dominated_convergence (fun u ↦ ‖archIntegrand f 0 u‖)
    ?_ ?_ h0.norm ?_
  · filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact (hf.integrableOn_archIntegrand (le_of_lt hδ)).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with δ hδ
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hδ0 : (0 : ℝ) < δ := hδ
    have hu0 : (0 : ℝ) < u := hu
    rw [archIntegrand_eq_exp_mul, norm_mul, Real.norm_eq_abs (Real.exp _), Real.abs_exp]
    have hle : Real.exp (-δ * u) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      nlinarith [mul_pos hδ0 hu0]
    exact mul_le_of_le_one_left (norm_nonneg _) hle
  · refine Eventually.of_forall fun u ↦ ?_
    have hcont : Continuous fun δ : ℝ ↦ archIntegrand f δ u := by
      unfold archIntegrand
      fun_prop
    exact (hcont.tendsto 0).mono_left nhdsWithin_le_nhds

/-- Helper for K5: continuity of the (finite) damped prime sum at `δ = 0`.  Every exponent
`-1/2 - δ` is nonzero near `δ = 0`, so even the `n = 0` term is continuous there. -/
private lemma tendsto_primeTermR_zero :
    Tendsto (primeTermR q f X) (𝓝 0) (𝓝 (primeTermR q f X 0)) := by
  unfold primeTermR
  refine Tendsto.const_mul 2 (tendsto_finsetSum _ fun n _ ↦ Tendsto.const_mul _ ?_)
  have hne : -(1 / 2 : ℝ) - 0 ≠ 0 := by norm_num
  have hc : ContinuousAt (fun y : ℝ ↦ (n : ℝ) ^ y) (-(1 / 2 : ℝ) - 0) :=
    Real.continuousAt_const_rpow' hne
  have hg : Continuous fun δ : ℝ ↦ -(1 / 2 : ℝ) - δ := by fun_prop
  exact hc.tendsto.comp (hg.tendsto 0)

/-- **K5** (M). Right-continuity of the arithmetic side at `δ = 0` (continuity of `ψ` at `3/4`,
dominated convergence with dominating function `archIntegrand f 0` from A6, continuity of
`δ ↦ n^{-1/2-δ}` for `n ≥ 1`). -/
theorem tendsto_arithSideR {L : ℝ} (hf : WeilAdmissible f L h) :
    Tendsto (arithSideR q f X) (𝓝[>] 0) (𝓝 (arithSideR q f X 0)) := by
  have hψ := tendsto_re_digamma_zero.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
  have hI := tendsto_integral_archIntegrand hf
  have hP := (tendsto_primeTermR_zero q (f := f) (X := X)).mono_left
    (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
  have key := (tendsto_const_nhds (x := Real.log (q / π))).add (hψ.add hI) |>.sub hP
  exact key

/-- **K6** (proved from G4). At `δ = 0` the arithmetic side is the right-hand side of the target
inequality minus the prime sum.  This is the formal check that the normalisations of the blueprint
(`archIntegrand`, `primeTermR`, `ψ(3/4)`) match `Jterm`, `primeSum`, `psi34` of `Statement.lean`. -/
theorem arithSideR_zero :
    arithSideR q f X 0 = Real.log (q / π) + psi34 + Jterm f - primeSum q f X := by
  have hd : (digamma ((3 / 4 + (0 : ℝ) / 2 : ℝ) : ℂ)).re = psi34 := by
    have h34 : (3 / 4 + (0 : ℝ) / 2 : ℝ) = (3 / 4 : ℝ) := by norm_num
    rw [h34, digamma_three_quarters, Complex.ofReal_re]
  have hJ : ∫ u in Set.Ioi (0 : ℝ), archIntegrand f 0 u = Jterm f := by
    unfold Jterm archIntegrand
    simp only [add_zero]
  have hP : primeTermR q f X 0 = primeSum q f X := by
    unfold primeTermR primeSum coeff
    congr 1
    refine Finset.sum_congr rfl fun n _ ↦ ?_
    rw [sub_zero, Real.rpow_neg (Nat.cast_nonneg n), ← Real.sqrt_eq_rpow]
    ring
  unfold arithSideR archTermR
  rw [hd, hJ, hP]
  ring

/-- **C2** (proved). The zero side is nonnegative for real `δ ≥ 0`. -/
theorem zeroSideR_nonneg {L : ℝ} (hf : WeilAdmissible f L h) {δ : ℝ} (hδ : 0 ≤ δ) :
    0 ≤ zeroSideR q h δ := by
  unfold zeroSideR
  refine tsum_nonneg fun ρ ↦ mul_nonneg (Nat.cast_nonneg _)
    (mul_nonneg (by positivity) (integral_nonneg fun t ↦ mul_nonneg (hf.nonneg t) ?_))
  unfold poissonKer
  positivity

/-- **C3** (proved from C1, K1–K4 by the identity theorem). The damped explicit formula for every
`δ > 0`, under GRH. -/
theorem zeroSideR_eq_arithSideR (hq : q % 4 = 3) (hGRH : GRHFor q)
    (hf : WeilAdmissible f (Real.log X) h) {δ : ℝ} (hδ : 0 < δ) :
    zeroSideR q h δ = arithSideR q f X δ := by
  have hU : IsOpen rightHalfPlane := isOpen_lt continuous_const Complex.continuous_re
  have hconn : IsPreconnected rightHalfPlane := (convex_halfSpace_re_gt 0).isPreconnected
  have hZ : AnalyticOnNhd ℂ (zeroSide q h) rightHalfPlane :=
    (differentiableOn_zeroSide q hq hf).analyticOnNhd hU
  have hA : AnalyticOnNhd ℂ (arithSide q f X) rightHalfPlane :=
    (differentiableOn_arithSide q hf).analyticOnNhd hU
  -- the two sides agree on the real points `1 + 1/(n+1)`, which accumulate at `1`
  have hfreq : ∃ᶠ z in 𝓝[≠] (1 : ℂ), zeroSide q h z = arithSide q f X z := by
    let u : ℕ → ℂ := fun n ↦ ((1 + 1 / ((n : ℝ) + 1) : ℝ) : ℂ)
    have hu : Tendsto u atTop (𝓝[≠] (1 : ℂ)) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun n ↦ ?_⟩
      · have h1 : Tendsto (fun n : ℕ ↦ (1 + 1 / ((n : ℝ) + 1) : ℝ)) atTop (𝓝 (1 + 0)) :=
          tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat
        have h2 : Tendsto (fun n : ℕ ↦ ((1 + 1 / ((n : ℝ) + 1) : ℝ) : ℂ)) atTop
            (𝓝 ((1 + 0 : ℝ) : ℂ)) := (Complex.continuous_ofReal.tendsto (1 + 0 : ℝ)).comp h1
        simpa [u] using h2
      · have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
        simp only [u, Set.mem_compl_iff, Set.mem_singleton_iff]
        intro hEq
        have : (1 + 1 / ((n : ℝ) + 1) : ℝ) = 1 := by exact_mod_cast hEq
        linarith
    refine hu.frequently (Frequently.of_forall fun n ↦ ?_)
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    have hgt : (1 / 2 : ℝ) < 1 + 1 / ((n : ℝ) + 1) := by linarith
    simp only [u]
    rw [zeroSide_ofReal, arithSide_ofReal q (by linarith),
      zeroSideR_eq_arithSideR_of_half_lt q hq hGRH hf hgt]
  have hEq := hZ.eqOn_of_preconnected_of_frequently_eq hA hconn
    (show (1 : ℂ) ∈ rightHalfPlane by simp [rightHalfPlane]) hfreq
  have h1 := hEq (show (δ : ℂ) ∈ rightHalfPlane by simpa [rightHalfPlane] using hδ)
  rw [zeroSide_ofReal, arithSide_ofReal q hδ.le] at h1
  exact_mod_cast h1

/-- **C4** (proved from C2, C3, K5, K6). The explicit-formula inequality for an admissible test
function: under GRH for `chi q`,
`2 ∑_{n<X} Λ(n) χ(n) f(log n)/√n ≤ log(q/π) + ψ(3/4) + J_f`. -/
theorem primeSum_le_of_weilAdmissible (hq : q % 4 = 3) (hGRH : GRHFor q)
    (hf : WeilAdmissible f (Real.log X) h) :
    primeSum q f X ≤ Real.log (q / π) + psi34 + Jterm f := by
  have h0 : 0 ≤ arithSideR q f X 0 := by
    refine ge_of_tendsto (tendsto_arithSideR q hf) ?_
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    rw [← zeroSideR_eq_arithSideR q hq hGRH hf hδ]
    exact zeroSideR_nonneg q hf (le_of_lt hδ)
  rw [arithSideR_zero] at h0
  linarith

end Exp7.EF
