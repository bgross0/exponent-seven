import Exp7Lean.Analytic.EF.Admissible
import Exp7Lean.Analytic.JBound

/-!
# Explicit formula blueprint: the test function `autocorr (stepFn L v)`

Leaves **T1–T9** and the proved node **T10** of `BLUEPRINT.md`: the normalised autocorrelation of a
step function is `WeilAdmissible`, with `h(t) = |ĝ(t)|² / ∫ g²`, `ĝ(t) = ∫ g(x) e^{itx} dx`.
Pure real/Fourier analysis; no number theory.

Sanity check of the normalisation (`v = [1]`): `g = 1_{[0,L)}`, `f(u) = (1 - |u|/L)₊`,
`ĝ(t) = (e^{itL} - 1)/(it)`, `h(t) = 4 sin²(tL/2)/(L t²)`, and indeed
`(1/2π) ∫ h(t) cos(tu) dt = (1 - |u|/L)₊`.
-/

namespace Exp7.EF

open Real MeasureTheory Complex

variable {L : ℝ} {v : List ℝ}

/-- Fourier transform `ĝ(t) = ∫ g(x) e^{itx} dx` of the step function `g = stepFn L v`. -/
noncomputable def ftStep (L : ℝ) (v : List ℝ) (t : ℝ) : ℂ :=
  ∫ x : ℝ, (stepFn L v x : ℂ) * Complex.exp (((t * x : ℝ) : ℂ) * I)

/-- `h(t) = |ĝ(t)|² / ∫ g²`, the Fourier transform of `autocorr (stepFn L v)`. -/
noncomputable def hStep (L : ℝ) (v : List ℝ) (t : ℝ) : ℝ :=
  ‖ftStep L v t‖ ^ 2 / ∫ x, stepFn L v x ^ 2

/-- **T1** (proved). `stepFn L v` vanishes outside `[0, L)`. -/
theorem stepFn_eq_zero (x : ℝ) (hx : x < 0 ∨ L ≤ x) : stepFn L v x = 0 := by
  unfold stepFn
  split_ifs with h
  · exfalso
    rcases hx with h' | h' <;> linarith [h.1, h.2]
  · rfl

/-- **T2** (S). `stepFn L v` is measurable (`Measurable.ite`, `Nat.floor` measurable,
`measurable_from_nat`/countable codomain). -/
theorem measurable_stepFn : Measurable (stepFn L v) := by
  change Measurable fun t : ℝ ↦ if 0 ≤ t ∧ t < L then v.getD ⌊t * v.length / L⌋₊ 0 else 0
  refine Measurable.ite measurableSet_Ico ?_ measurable_const
  exact (measurable_from_nat (f := fun n : ℕ ↦ v.getD n 0)).comp
    (Nat.measurable_floor.comp ((measurable_id.mul_const _).div_const _))

/-- **T3** (S). `stepFn L v` is bounded (by the largest `|vᵢ|`). -/
theorem abs_stepFn_le : ∃ C : ℝ, ∀ x, |stepFn L v x| ≤ C := by
  refine ⟨∑ k ∈ Finset.range v.length, |v.getD k 0|, fun x ↦ ?_⟩
  have hC : 0 ≤ ∑ k ∈ Finset.range v.length, |v.getD k 0| :=
    Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
  unfold stepFn
  split_ifs
  · by_cases hn : ⌊x * v.length / L⌋₊ < v.length
    · exact Finset.single_le_sum (f := fun k ↦ |v.getD k 0|) (fun _ _ ↦ abs_nonneg _)
        (Finset.mem_range.mpr hn)
    · rw [List.getD_eq_default _ _ (not_lt.mp hn), abs_zero]
      exact hC
  · rw [abs_zero]
    exact hC

/-- **T4** (M). `∫ g² > 0` when `L > 0` and some entry of `v` is nonzero
(`g² = vⱼ² > 0` on a cell `[jL/n, (j+1)L/n)` of positive length). -/
theorem integral_stepFn_sq_pos (hL : 0 < L) (hv : ∃ t ∈ v, t ≠ 0) :
    0 < ∫ x, stepFn L v x ^ 2 := by
  have hm : 0 < v.length := length_pos_of_exists_ne_zero hv
  rw [integral_stepFn_sq hL hm]
  exact mul_pos (div_pos hL (by exact_mod_cast hm)) (sumSq_pos hv)

/-- Helper for T5/T9a. A step function is a finite linear combination of indicators of bounded
half-open intervals (no hypothesis on `L` or `v`: in the degenerate cases it is `0`). -/
theorem exists_stepFn_eq_sum_indicator (L : ℝ) (v : List ℝ) :
    ∃ (m : ℕ) (c a b : ℕ → ℝ), (∀ j, a j ≤ b j) ∧ ∀ x, stepFn L v x =
      ∑ j ∈ Finset.range m, c j * (Set.Ico (a j) (b j)).indicator (fun _ ↦ (1 : ℝ)) x := by
  by_cases hdeg : 0 < L ∧ 0 < v.length
  · obtain ⟨hL, hm⟩ := hdeg
    have hm' : (0 : ℝ) < v.length := by exact_mod_cast hm
    have hw : 0 < L / v.length := div_pos hL hm'
    refine ⟨v.length, fun j ↦ v.getD j 0, fun j ↦ j * (L / v.length),
      fun j ↦ (j + 1) * (L / v.length), fun j ↦ by nlinarith, fun x ↦ ?_⟩
    by_cases hx : 0 ≤ x
    · obtain ⟨i, h1, h2⟩ : ∃ i : ℕ, i * (L / v.length) ≤ x ∧ x < (i + 1) * (L / v.length) := by
        have h0 : 0 ≤ x / (L / v.length) := div_nonneg hx hw.le
        refine ⟨⌊x / (L / v.length)⌋₊, ?_, ?_⟩
        · have := Nat.floor_le h0
          rwa [le_div_iff₀ hw] at this
        · have := Nat.lt_floor_add_one (x / (L / v.length))
          rwa [div_lt_iff₀ hw] at this
      rw [stepFn_cell hL hm i h1 h2]
      have hind : ∀ j : ℕ, (Set.Ico (j * (L / v.length)) ((j + 1) * (L / v.length))).indicator
          (fun _ ↦ (1 : ℝ)) x = if j = i then 1 else 0 := by
        intro j
        by_cases hji : j = i
        · rw [ite_eq_left hji, hji, Set.indicator_of_mem (show x ∈ Set.Ico _ _ from ⟨h1, h2⟩)]
        · rw [ite_eq_right hji, Set.indicator_of_notMem]
          rintro ⟨h3, h4⟩
          apply hji
          have h5 : (j : ℝ) < i + 1 := lt_of_mul_lt_mul_right (h3.trans_lt h2) hw.le
          have h6 : (i : ℝ) < j + 1 := lt_of_mul_lt_mul_right (h1.trans_lt h4) hw.le
          have h7 : j < i + 1 := by exact_mod_cast h5
          have h8 : i < j + 1 := by exact_mod_cast h6
          omega
      simp only [hind, mul_ite, mul_one, mul_zero]
      rw [Finset.sum_ite_eq']
      split_ifs with hmem
      · rfl
      · rw [List.getD_eq_default]
        simpa using hmem
    · rw [stepFn_of_not_mem (fun h ↦ hx h.1)]
      symm
      refine Finset.sum_eq_zero fun j _ ↦ ?_
      rw [Set.indicator_of_notMem, mul_zero]
      rintro ⟨h3, -⟩
      exact hx (le_trans (by positivity) h3)
  · refine ⟨0, fun _ ↦ 0, fun _ ↦ 0, fun _ ↦ 0, fun _ ↦ le_rfl, fun x ↦ ?_⟩
    rw [Finset.sum_range_zero]
    unfold stepFn
    split_ifs with h
    · have hL : 0 < L := lt_of_le_of_lt h.1 h.2
      have hlen : v.length = 0 := by
        by_contra hne
        exact hdeg ⟨hL, Nat.pos_of_ne_zero hne⟩
      rw [List.getD_eq_default _ _ (by omega)]
    · rfl

/-- Helper for T5. The two bounds `|∫_a^b e^{itx} dx| ≤ b - a` and `|t| |∫_a^b e^{itx} dx| ≤ 2`. -/
theorem norm_integral_Ico_exp_le (t a b : ℝ) (hab : a ≤ b) :
    ‖∫ x in Set.Ico a b, Complex.exp (((t * x : ℝ) : ℂ) * I)‖ ≤ b - a ∧
      |t| * ‖∫ x in Set.Ico a b, Complex.exp (((t * x : ℝ) : ℂ) * I)‖ ≤ 2 := by
  constructor
  · have h := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Set.Ico a b) (C := 1)
      (f := fun x : ℝ ↦ Complex.exp (((t * x : ℝ) : ℂ) * I)) measure_Ico_lt_top
      (fun x _ ↦ (Complex.norm_exp_ofReal_mul_I _).le)
    rwa [Real.volume_real_Ico_of_le hab, one_mul] at h
  · by_cases ht : t = 0
    · simp [ht]
    · have hc : (t : ℂ) * I ≠ 0 := mul_ne_zero (by exact_mod_cast ht) Complex.I_ne_zero
      have e : ∫ x in Set.Ico a b, Complex.exp (((t * x : ℝ) : ℂ) * I) =
          (Complex.exp (t * I * b) - Complex.exp (t * I * a)) / (t * I) := by
        rw [integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab,
          ← integral_exp_mul_complex hc]
        refine intervalIntegral.integral_congr fun x _ ↦ ?_
        simp only [Complex.ofReal_mul]
        ring_nf
      have e1 : ∀ y : ℝ, ‖Complex.exp (t * I * y)‖ = 1 := by
        intro y
        rw [show (t : ℂ) * I * y = ((t * y : ℝ) : ℂ) * I by push_cast; ring,
          Complex.norm_exp_ofReal_mul_I]
      have hnorm : ‖(t : ℂ) * I‖ = |t| := by
        rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
      rw [e, norm_div, hnorm, mul_div_cancel₀ _ (abs_ne_zero.mpr ht)]
      calc ‖Complex.exp (t * I * b) - Complex.exp (t * I * a)‖
          ≤ ‖Complex.exp (t * I * b)‖ + ‖Complex.exp (t * I * a)‖ := norm_sub_le _ _
        _ = 2 := by rw [e1, e1]; norm_num

/-- **T5** (M). Decay of `h`: `|ĝ(t)| ≤ min (C₀) (C₁/|t|)`, hence `h(t) ≤ C/(1+t²)`.
Either compute `ĝ(t) = ∑ⱼ vⱼ (e^{it(j+1)L/n} - e^{itjL/n})/(it)` or integrate by parts cellwise. -/
theorem hStep_decay (hL : 0 < L) : ∃ C : ℝ, ∀ t, hStep L v t ≤ C / (1 + t ^ 2) := by
  obtain ⟨m, c, a, b, hab, hg⟩ := exists_stepFn_eq_sum_indicator L v
  have hft : ∀ t, ftStep L v t = ∑ j ∈ Finset.range m,
      (c j : ℂ) * ∫ x in Set.Ico (a j) (b j), Complex.exp (((t * x : ℝ) : ℂ) * I) := by
    intro t
    unfold ftStep
    have e : ∀ x : ℝ, (stepFn L v x : ℂ) * Complex.exp (((t * x : ℝ) : ℂ) * I) =
        ∑ j ∈ Finset.range m, (c j : ℂ) * (Set.Ico (a j) (b j)).indicator
          (fun x : ℝ ↦ Complex.exp (((t * x : ℝ) : ℂ) * I)) x := by
      intro x
      rw [hg x, Complex.ofReal_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      by_cases hx : x ∈ Set.Ico (a j) (b j)
      · simp [Set.indicator_of_mem hx]
      · simp [Set.indicator_of_notMem hx]
    simp_rw [e]
    rw [integral_finsetSum]
    · refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [integral_const_mul, integral_indicator measurableSet_Ico]
    · intro j _
      refine Integrable.const_mul ?_ _
      rw [integrable_indicator_iff measurableSet_Ico]
      exact (Continuous.continuousOn (by fun_prop)).integrableOn_Icc.mono_set
        Set.Ico_subset_Icc_self
  have h0 : ∀ t, ‖ftStep L v t‖ ≤ ∑ j ∈ Finset.range m, |c j| * (b j - a j) := by
    intro t
    rw [hft t]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ ↦ ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (norm_integral_Ico_exp_le t _ _ (hab j)).1 (abs_nonneg _)
  have h1 : ∀ t, |t| * ‖ftStep L v t‖ ≤ ∑ j ∈ Finset.range m, |c j| * 2 := by
    intro t
    rw [hft t]
    refine (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (abs_nonneg t)).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ ↦ ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_left_comm]
    exact mul_le_mul_of_nonneg_left (norm_integral_Ico_exp_le t _ _ (hab j)).2 (abs_nonneg _)
  refine ⟨((∑ j ∈ Finset.range m, |c j| * (b j - a j)) ^ 2 +
    (∑ j ∈ Finset.range m, |c j| * 2) ^ 2) / ∫ x, stepFn L v x ^ 2, fun t ↦ ?_⟩
  have hI : 0 ≤ ∫ x, stepFn L v x ^ 2 := integral_nonneg fun _ ↦ sq_nonneg _
  have hsq : ‖ftStep L v t‖ ^ 2 * (1 + t ^ 2) ≤
      (∑ j ∈ Finset.range m, |c j| * (b j - a j)) ^ 2 +
        (∑ j ∈ Finset.range m, |c j| * 2) ^ 2 := by
    have h2 := pow_le_pow_left₀ (norm_nonneg _) (h0 t) 2
    have h3 := pow_le_pow_left₀ (mul_nonneg (abs_nonneg t) (norm_nonneg _)) (h1 t) 2
    rw [mul_pow, sq_abs] at h3
    nlinarith
  unfold hStep
  rw [div_right_comm]
  exact div_le_div_of_nonneg_right ((le_div_iff₀ (by positivity)).mpr hsq) hI

/-- Helper for **T6**: `ĝ = ftStep L v` is continuous (dominated convergence, with the integrable
bound `|g|`; `g` is bounded, measurable and supported in `[0, L)`). -/
theorem continuous_ftStep : Continuous (ftStep L v) := by
  obtain ⟨C, hC⟩ := abs_stepFn_le (L := L) (v := v)
  have hint : Integrable (stepFn L v) := by
    have h1 : IntegrableOn (stepFn L v) (Set.Ico 0 L) :=
      Measure.integrableOn_of_bounded (M := C) measure_Ico_lt_top.ne
        measurable_stepFn.aestronglyMeasurable
        (ae_of_all _ fun x ↦ by simpa [Real.norm_eq_abs] using hC x)
    refine (integrableOn_iff_integrable_of_support_subset fun x hx ↦ ?_).mp h1
    by_contra hmem
    refine hx (stepFn_eq_zero x ?_)
    by_contra hcon
    push Not at hcon
    exact hmem ⟨hcon.1, hcon.2⟩
  change Continuous fun t : ℝ ↦
    ∫ x : ℝ, (stepFn L v x : ℂ) * Complex.exp (((t * x : ℝ) : ℂ) * I)
  refine continuous_of_dominated (bound := fun x ↦ |stepFn L v x|) (fun t ↦ ?_) (fun t ↦ ?_)
    hint.abs ?_
  · exact ((Complex.measurable_ofReal.comp measurable_stepFn).mul
      (Complex.measurable_exp.comp ((Complex.measurable_ofReal.comp
        (measurable_const.mul measurable_id)).mul_const I))).aestronglyMeasurable
  · refine ae_of_all _ fun x ↦ ?_
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  · refine ae_of_all _ fun x ↦ ?_
    fun_prop

/-- **T6** (S). `h` is continuous (`ĝ` is continuous: `continuous_of_dominated`). -/
theorem continuous_hStep : Continuous (hStep L v) := by
  change Continuous fun t : ℝ ↦ ‖ftStep L v t‖ ^ 2 / ∫ x, stepFn L v x ^ 2
  exact (continuous_ftStep.norm.pow 2).div_const _

/-- **T7** (proved from T4). `autocorr g 0 = 1`. -/
theorem autocorr_stepFn_zero (hL : 0 < L) (hv : ∃ t ∈ v, t ≠ 0) :
    autocorr (stepFn L v) 0 = 1 := by
  have hpos := integral_stepFn_sq_pos hL hv
  have h2 : (fun x ↦ stepFn L v x * stepFn L v (x + 0)) = fun x ↦ stepFn L v x ^ 2 := by
    funext x
    rw [add_zero]
    ring
  rw [autocorr, h2, div_self hpos.ne']

/-- **T8** (proved from T1). `autocorr g u = 0` for `u ≥ L`. -/
theorem autocorr_stepFn_eq_zero (u : ℝ) (hu : L ≤ u) : autocorr (stepFn L v) u = 0 := by
  have h0 : ∀ x, stepFn L v x * stepFn L v (x + u) = 0 := by
    intro x
    by_cases hx : 0 ≤ x
    · rw [stepFn_eq_zero (x + u) (Or.inr (by linarith)), mul_zero]
    · rw [stepFn_eq_zero x (Or.inl (not_le.mp hx)), zero_mul]
  simp [autocorr, h0]

/-- Helper for T9a. The product of an interval indicator and a shifted interval indicator is the
indicator of an interval. -/
theorem indicator_Ico_mul_shift (a b c d u x : ℝ) :
    (Set.Ico a b).indicator (fun _ ↦ (1 : ℝ)) x * (Set.Ico c d).indicator (fun _ ↦ (1 : ℝ)) (x + u) =
      (Set.Ico (max a (c - u)) (min b (d - u))).indicator (fun _ ↦ (1 : ℝ)) x := by
  have key : x ∈ Set.Ico (max a (c - u)) (min b (d - u)) ↔
      x ∈ Set.Ico a b ∧ x + u ∈ Set.Ico c d := by
    simp only [Set.mem_Ico, max_le_iff, lt_min_iff, sub_le_iff_le_add, lt_sub_iff_add_lt]
    tauto
  by_cases h1 : x ∈ Set.Ico a b
  · by_cases h2 : x + u ∈ Set.Ico c d
    · rw [Set.indicator_of_mem h1, Set.indicator_of_mem h2,
        Set.indicator_of_mem (key.mpr ⟨h1, h2⟩), mul_one]
    · rw [Set.indicator_of_notMem h2, Set.indicator_of_notMem (fun h ↦ h2 (key.mp h).2), mul_zero]
  · rw [Set.indicator_of_notMem h1, Set.indicator_of_notMem (fun h ↦ h1 (key.mp h).1), zero_mul]

/-- Helper for T9a. The indicator of a bounded interval is integrable. -/
theorem integrable_indicator_Ico_one (p q : ℝ) :
    Integrable ((Set.Ico p q).indicator (fun _ : ℝ ↦ (1 : ℝ))) := by
  rw [integrable_indicator_iff measurableSet_Ico]
  exact integrableOn_const measure_Ico_lt_top.ne

/-- **T9a** (M). The correlation `c(u) = ∫ g(x) g(x+u) dx` is continuous and integrable
(continuity of translation in `L¹` for a bounded compactly supported `g`; `c` is supported in
`[-L, L]`). -/
theorem continuous_integrable_corr :
    Continuous (fun u : ℝ ↦ ∫ x, stepFn L v x * stepFn L v (x + u)) ∧
      Integrable (fun u : ℝ ↦ ∫ x, stepFn L v x * stepFn L v (x + u)) := by
  obtain ⟨m, c, a, b, -, hg⟩ := exists_stepFn_eq_sum_indicator L v
  have hc : ∀ u, ∫ x, stepFn L v x * stepFn L v (x + u) =
      ∑ j ∈ Finset.range m, ∑ k ∈ Finset.range m,
        c j * c k * max (min (b j) (b k - u) - max (a j) (a k - u)) 0 := by
    intro u
    have e : ∀ x, stepFn L v x * stepFn L v (x + u) =
        ∑ j ∈ Finset.range m, ∑ k ∈ Finset.range m, c j * c k *
          ((Set.Ico (a j) (b j)).indicator (fun _ ↦ (1 : ℝ)) x *
            (Set.Ico (a k) (b k)).indicator (fun _ ↦ (1 : ℝ)) (x + u)) := by
      intro x
      rw [hg x, hg (x + u), Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun k _ ↦ ?_
      ring
    simp_rw [e, indicator_Ico_mul_shift]
    rw [integral_finsetSum _ (fun j _ ↦ integrable_finsetSum _ fun k _ ↦
      (integrable_indicator_Ico_one _ _).const_mul _)]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [integral_finsetSum _ (fun k _ ↦ (integrable_indicator_Ico_one _ _).const_mul _)]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [integral_const_mul, integral_indicator_const _ measurableSet_Ico, Real.volume_real_Ico,
      smul_eq_mul, mul_one]
  have hcont : Continuous (fun u : ℝ ↦ ∫ x, stepFn L v x * stepFn L v (x + u)) := by
    simp_rw [hc]
    exact continuous_finsetSum _ fun j _ ↦ continuous_finsetSum _ fun k _ ↦
      continuous_const.mul (((continuous_const.min (continuous_const.sub continuous_id)).sub
        (continuous_const.max (continuous_const.sub continuous_id))).max continuous_const)
  refine ⟨hcont, hcont.integrable_of_hasCompactSupport
    (HasCompactSupport.intro (isCompact_Icc (a := -|L|) (b := |L|)) fun u hu ↦ ?_)⟩
  have h0 : ∀ x, stepFn L v x * stepFn L v (x + u) = 0 := by
    intro x
    by_cases hx : 0 ≤ x ∧ x < L
    · rw [Set.mem_Icc, not_and_or, not_le, not_le] at hu
      rw [stepFn_eq_zero (x + u) ?_, mul_zero]
      rcases hu with hu | hu
      · left
        linarith [le_abs_self L]
      · right
        linarith [le_abs_self L]
    · rw [stepFn_of_not_mem hx, zero_mul]
  simp [h0]

/-- `stepFn L v` is integrable (bounded, measurable, supported in `[0, L)`). -/
theorem T9.integrable_stepFn : Integrable (stepFn L v) := by
  obtain ⟨C, hC⟩ := abs_stepFn_le (L := L) (v := v)
  have h1 : IntegrableOn (stepFn L v) (Set.Ico 0 L) :=
    Measure.integrableOn_of_bounded (M := C) measure_Ico_lt_top.ne
      measurable_stepFn.aestronglyMeasurable (Filter.Eventually.of_forall fun x ↦ by
        rw [Real.norm_eq_abs]; exact hC x)
  refine (integrableOn_iff_integrable_of_support_subset ?_).mp h1
  intro x hx
  by_contra hx'
  rw [Set.mem_Ico, not_and_or, not_le, not_lt] at hx'
  exact hx (stepFn_eq_zero x hx')

/-- The integrand of `ftStep` is integrable. -/
theorem T9.integrable_stepFn_mul_exp (t : ℝ) :
    Integrable (fun x : ℝ ↦ (stepFn L v x : ℂ) * Complex.exp (((t * x : ℝ) : ℂ) * I)) := by
  refine (T9.integrable_stepFn (L := L) (v := v)).norm.mono' ?_
    (Filter.Eventually.of_forall fun x ↦ ?_)
  · exact (Complex.measurable_ofReal.comp measurable_stepFn).aestronglyMeasurable.mul
      (by fun_prop : Continuous fun x : ℝ ↦
        Complex.exp (((t * x : ℝ) : ℂ) * I)).aestronglyMeasurable
  · rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real]

/-- **T9b** (M). Fourier transform of the correlation: `∫ c(u) e^{itu} du = |ĝ(t)|²`
(Fubini and the substitution `y = x + u`; alternatively `Real.fourier_mul_convolution_eq` from
`Mathlib/Analysis/Fourier/Convolution.lean`). -/
theorem integral_corr_mul_exp (t : ℝ) :
    ∫ u : ℝ, ((∫ x, stepFn L v x * stepFn L v (x + u) : ℝ) : ℂ) *
        Complex.exp (((t * u : ℝ) : ℂ) * I) = ((‖ftStep L v t‖ ^ 2 : ℝ) : ℂ) := by
  set g := stepFn L v with hg
  set a : ℝ → ℂ := fun x ↦ (g x : ℂ) * Complex.exp (((t * x : ℝ) : ℂ) * I) with ha
  set b : ℝ → ℂ := fun x ↦ (starRingEnd ℂ) (a x) with hb
  have ha_int : Integrable a := T9.integrable_stepFn_mul_exp t
  have hb_int : Integrable b :=
    ha_int.norm.mono' (Complex.continuous_conj.comp_aestronglyMeasurable
      ha_int.aestronglyMeasurable) (Filter.Eventually.of_forall fun x ↦ by simp [hb])
  have hpt : ∀ u x : ℝ, ((g x * g (x + u) : ℝ) : ℂ) * Complex.exp (((t * u : ℝ) : ℂ) * I) =
      b x * a (x + u) := by
    intro u x
    have hexp : Complex.exp (((t * u : ℝ) : ℂ) * I) =
        (starRingEnd ℂ) (Complex.exp (((t * x : ℝ) : ℂ) * I)) *
          Complex.exp (((t * (x + u) : ℝ) : ℂ) * I) := by
      rw [← Complex.exp_conj, ← Complex.exp_add]
      congr 1
      simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
      push_cast
      ring
    simp only [ha, hb, map_mul, Complex.conj_ofReal]
    rw [hexp]
    push_cast
    ring
  have hint : Integrable (Function.uncurry fun x u : ℝ ↦ b x * a (x + u))
      ((volume : Measure ℝ).prod (volume : Measure ℝ)) := by
    have h0 : Integrable (fun z : ℝ × ℝ ↦ b z.1 * a z.2)
        ((volume : Measure ℝ).prod (volume : Measure ℝ)) := hb_int.mul_prod ha_int
    exact (measurePreserving_prod_add (volume : Measure ℝ)
      (volume : Measure ℝ)).integrable_comp_of_integrable h0
  calc ∫ u : ℝ, ((∫ x, g x * g (x + u) : ℝ) : ℂ) * Complex.exp (((t * u : ℝ) : ℂ) * I)
      = ∫ u : ℝ, ∫ x : ℝ, b x * a (x + u) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun u ↦ ?_)
        simp only
        rw [← integral_complex_ofReal, ← integral_mul_const]
        simp_rw [hpt]
    _ = ∫ x : ℝ, ∫ u : ℝ, b x * a (x + u) := (integral_integral_swap hint).symm
    _ = ∫ x : ℝ, b x * ∫ u : ℝ, a u := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
        simp only
        rw [integral_const_mul, integral_add_left_eq_self]
    _ = (∫ x : ℝ, b x) * ∫ u : ℝ, a u := integral_mul_const _ _
    _ = (starRingEnd ℂ) (ftStep L v t) * ftStep L v t := by
        rw [hb, integral_conj]
        rfl
    _ = ((‖ftStep L v t‖ ^ 2 : ℝ) : ℂ) := by
        rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]

/-- `hStep L v` is integrable (continuous, nonnegative, `≤ C/(1+t²)`). -/
theorem T9.integrable_hStep (hL : 0 < L) : Integrable (hStep L v) := by
  obtain ⟨C, hC⟩ := hStep_decay (v := v) hL
  have hnn : ∀ t, 0 ≤ hStep L v t := fun _ ↦
    div_nonneg (sq_nonneg _) (integral_nonneg fun _ ↦ sq_nonneg _)
  refine (integrable_inv_one_add_sq.const_mul C).mono' continuous_hStep.aestronglyMeasurable
    (Filter.Eventually.of_forall fun t ↦ ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (hnn t), ← div_eq_mul_inv]
  exact hC t

open scoped FourierTransform in
/-- Complex form of the inversion formula for the correlation `c(u) = ∫ g(x) g(x+u) dx`:
`c(u) = ∫ e^{2πiξu} · (∫g²) · h(-2πξ) dξ`. -/
theorem T9.corr_eq_integral_exp_mul_hStep (hL : 0 < L) (hv : ∃ t ∈ v, t ≠ 0) (u : ℝ) :
    ((∫ x, stepFn L v x * stepFn L v (x + u) : ℝ) : ℂ) =
      ∫ ξ : ℝ, Complex.exp (((2 * π * ξ * u : ℝ) : ℂ) * I) *
        (((∫ x, stepFn L v x ^ 2) * hStep L v (-(2 * π) * ξ) : ℝ) : ℂ) := by
  have hG : 0 < ∫ x, stepFn L v x ^ 2 := integral_stepFn_sq_pos hL hv
  set G := ∫ x, stepFn L v x ^ 2 with hGdef
  set cC : ℝ → ℂ := fun u ↦ ((∫ x, stepFn L v x * stepFn L v (x + u) : ℝ) : ℂ) with hcC
  have hcont : Continuous cC :=
    Complex.continuous_ofReal.comp (continuous_integrable_corr (L := L) (v := v)).1
  have hcint : Integrable cC := (continuous_integrable_corr (L := L) (v := v)).2.ofReal
  have hF : 𝓕 cC = fun ξ : ℝ ↦ ((G * hStep L v (-(2 * π) * ξ) : ℝ) : ℂ) := by
    funext ξ
    rw [Real.fourier_real_eq_integral_exp_smul]
    have h1 : ∀ w : ℝ, Complex.exp (((-2 * π * w * ξ : ℝ) : ℂ) * I) • cC w =
        ((∫ x, stepFn L v x * stepFn L v (x + w) : ℝ) : ℂ) *
          Complex.exp (((-(2 * π) * ξ * w : ℝ) : ℂ) * I) := by
      intro w
      rw [smul_eq_mul, mul_comm, show -2 * π * w * ξ = -(2 * π) * ξ * w by ring]
    simp_rw [h1]
    rw [integral_corr_mul_exp]
    congr 1
    rw [hStep, ← hGdef, mul_div_cancel₀ _ hG.ne']
  have hFint : Integrable (𝓕 cC) := by
    rw [hF]
    exact (((T9.integrable_hStep hL).comp_mul_left' (R := -(2 * π))
      (neg_ne_zero.mpr (by positivity))).const_mul G).ofReal
  have hinv := congr_fun (hcont.fourierInv_fourier_eq hcint hFint) u
  rw [Real.fourierInv_eq', hF] at hinv
  refine hinv.symm.trans ?_
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ ↦ ?_)
  simp only [smul_eq_mul]
  congr 3
  simp [mul_comm, mul_assoc, mul_left_comm]

/-- **T9** (L, from T5, T9a, T9b). Fourier inversion for the autocorrelation:
`autocorr g u = (1/2π) ∫ h(t) cos(tu) dt`.

Proof sketch: `Continuous.fourierInv_fourier_eq` (`Mathlib/Analysis/Fourier/Inversion.lean`) applied
to `c`, whose Mathlib-normalised transform `𝓕 c (ξ) = ∫ c(u) e^{-2πiuξ} du = |ĝ(-2πξ)|²` is integrable
by T5; change variables `t = 2πξ` and take real parts; divide by `∫ g²`. -/
theorem autocorr_stepFn_inv (hL : 0 < L) (hv : ∃ t ∈ v, t ≠ 0) (u : ℝ) :
    autocorr (stepFn L v) u = 1 / (2 * π) * ∫ t, hStep L v t * Real.cos (t * u) := by
  have hG : 0 < ∫ x, stepFn L v x ^ 2 := integral_stepFn_sq_pos hL hv
  have hc := T9.corr_eq_integral_exp_mul_hStep hL hv u
  set G := ∫ x, stepFn L v x ^ 2 with hGdef
  have hr : Integrable (fun ξ : ℝ ↦ G * hStep L v (-(2 * π) * ξ)) :=
    ((T9.integrable_hStep hL).comp_mul_left' (R := -(2 * π))
      (neg_ne_zero.mpr (by positivity))).const_mul G
  have hFint : Integrable (fun ξ : ℝ ↦ Complex.exp (((2 * π * ξ * u : ℝ) : ℂ) * I) *
      ((G * hStep L v (-(2 * π) * ξ) : ℝ) : ℂ)) := by
    refine hr.norm.mono' ?_ (Filter.Eventually.of_forall fun ξ ↦ ?_)
    · exact (by fun_prop : Continuous fun ξ : ℝ ↦
        Complex.exp (((2 * π * ξ * u : ℝ) : ℂ) * I)).aestronglyMeasurable.mul
          hr.ofReal.aestronglyMeasurable
    · rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_real]
  have hre : (∫ x, stepFn L v x * stepFn L v (x + u)) =
      ∫ ξ : ℝ, (fun t : ℝ ↦ G * (hStep L v t * Real.cos (t * u))) (-(2 * π) * ξ) := by
    have h1 := congr_arg Complex.re hc
    rw [Complex.ofReal_re] at h1
    have h2 : (∫ ξ : ℝ, Complex.exp (((2 * π * ξ * u : ℝ) : ℂ) * I) *
        ((G * hStep L v (-(2 * π) * ξ) : ℝ) : ℂ)).re =
        ∫ ξ : ℝ, (Complex.exp (((2 * π * ξ * u : ℝ) : ℂ) * I) *
          ((G * hStep L v (-(2 * π) * ξ) : ℝ) : ℂ)).re := (integral_re hFint).symm
    rw [h1, h2]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ξ ↦ ?_)
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero, Complex.exp_ofReal_mul_I_re]
    rw [show -(2 * π) * ξ * u = -(2 * π * ξ * u) by ring, Real.cos_neg]
    ring
  have h3 : (∫ x, stepFn L v x * stepFn L v (x + u)) =
      |(-(2 * π))⁻¹| • ∫ t : ℝ, G * (hStep L v t * Real.cos (t * u)) :=
    hre.trans (Measure.integral_comp_mul_left
      (fun t : ℝ ↦ G * (hStep L v t * Real.cos (t * u))) (-(2 * π)))
  rw [autocorr, ← hGdef, h3, integral_const_mul, smul_eq_mul, inv_neg,
    abs_neg, abs_of_pos (by positivity : (0 : ℝ) < (2 * π)⁻¹)]
  generalize (∫ t : ℝ, hStep L v t * Real.cos (t * u)) = J
  field_simp

/-- **T10** (proved from T4–T9). The normalised autocorrelation of a nonzero step function on
`[0, L)` is an admissible test function. -/
theorem weilAdmissible_autocorr_stepFn (hL : 0 < L) (hv : ∃ t ∈ v, t ≠ 0) :
    WeilAdmissible (autocorr (stepFn L v)) L (hStep L v) where
  cont := continuous_hStep
  nonneg _ := div_nonneg (sq_nonneg _) (integral_nonneg fun _ ↦ sq_nonneg _)
  decay := hStep_decay hL
  inv := autocorr_stepFn_inv hL hv
  zero := autocorr_stepFn_zero hL hv
  supp := autocorr_stepFn_eq_zero

end Exp7.EF
