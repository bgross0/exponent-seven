import Exp7Lean.Analytic.Autocorr

/-!
Exponent 7, analytic side: an explicit upper bound for the archimedean term `Jterm f`,
`f = autocorr (stepFn L v)`.  This is the quantity `J⁺` computed by `rigorous_margin` in
`kernel_verify.py`.

With `a(u) = aKer u = 2 e^{-3u/2} / (1 - e^{-2u})`, `w = L / v.length`, `step = w / 16`:

    Jterm f ≤ (1 - corr v 1)
            + ∑_{1 ≤ j < m} ∑_{i < 16}
                step · a(step (16 j + i)) · (1 - (c_j + (c_{j+1} - c_j)(2i+1)/32))
            + 4 / (3 e^{3L/2} (1 - e^{-2L})).

Main results: `integrableOn_Jint`, `Jterm_le`, `Jterm_le_Jplus`, `Jterm_log_le`.
-/

namespace Exp7

open Real MeasureTheory Set

/-! ### The weight `a(u) = 2 e^{-3u/2} / (1 - e^{-2u})` -/

/-- The archimedean weight `a(u) = 2 e^{-3u/2} / (1 - e^{-2u}) = e^{-u/2} / sinh u`. -/
noncomputable def aKer (u : ℝ) : ℝ := 2 * exp (-(3 / 2) * u) / (1 - exp (-2 * u))

theorem Jterm_eq_integral_aKer (f : ℝ → ℝ) :
    Jterm f = ∫ u in Ioi (0 : ℝ), aKer u * (1 - f u) := rfl

theorem one_sub_exp_neg_two_mul_pos {u : ℝ} (hu : 0 < u) : 0 < 1 - exp (-2 * u) := by
  have : exp (-2 * u) < 1 := exp_lt_one_iff.mpr (by linarith)
  linarith

theorem aKer_pos {u : ℝ} (hu : 0 < u) : 0 < aKer u :=
  div_pos (by positivity) (one_sub_exp_neg_two_mul_pos hu)

/-- `a` is decreasing on `(0, ∞)`. -/
theorem aKer_anti {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) : aKer y ≤ aKer x := by
  unfold aKer
  refine div_le_div₀ (by positivity) ?_ (one_sub_exp_neg_two_mul_pos hx) ?_
  · have : exp (-(3 / 2) * y) ≤ exp (-(3 / 2) * x) := exp_le_exp.mpr (by linarith)
    linarith
  · have : exp (-2 * y) ≤ exp (-2 * x) := exp_le_exp.mpr (by linarith)
    linarith

/-- `u · a(u) ≤ 1` on `(0, ∞)`. -/
theorem aKer_mul_self_le_one {u : ℝ} (hu : 0 < u) : aKer u * u ≤ 1 := by
  unfold aKer
  have hd := one_sub_exp_neg_two_mul_pos hu
  rw [div_mul_eq_mul_div, div_le_one hd]
  have hs : u ≤ sinh u := self_le_sinh_iff.mpr hu.le
  rw [sinh_eq] at hs
  have hp : 0 < exp (-u) := exp_pos _
  have hq : exp (-(u / 2)) ≤ 1 := exp_le_one_iff.mpr (by linarith)
  have hq0 : 0 < exp (-(u / 2)) := exp_pos _
  have hrp : exp u * exp (-u) = 1 := by rw [← exp_add]; simp
  have e1 : exp (-(3 / 2) * u) = exp (-u) * exp (-(u / 2)) := by
    rw [← exp_add]; congr 1; ring
  have e2 : exp (-2 * u) = exp (-u) * exp (-u) := by rw [← exp_add]; congr 1; ring
  rw [e1, e2]
  have h1 : 2 * u * exp (-u) ≤ 1 - exp (-u) * exp (-u) := by
    nlinarith [mul_le_mul_of_nonneg_right hs hp.le]
  have h2 : 2 * u * exp (-u) * exp (-(u / 2)) ≤ 2 * u * exp (-u) := by
    have : 0 ≤ 2 * u * exp (-u) := by positivity
    nlinarith
  linarith

/-- `a(u) ≤ 1 / u` on `(0, ∞)`. -/
theorem aKer_le_inv {u : ℝ} (hu : 0 < u) : aKer u ≤ 1 / u := by
  rw [le_div_iff₀ hu]
  exact aKer_mul_self_le_one hu

theorem continuousOn_aKer : ContinuousOn aKer (Ioi 0) := by
  have h1 : Continuous fun u : ℝ => 2 * exp (-(3 / 2) * u) := by fun_prop
  have h2 : Continuous fun u : ℝ => 1 - exp (-2 * u) := by fun_prop
  exact h1.continuousOn.div h2.continuousOn
    (fun u hu => (one_sub_exp_neg_two_mul_pos hu).ne')

theorem measurable_aKer : Measurable aKer := by
  have : aKer = fun u => 2 * exp (-(3 / 2) * u) / (1 - exp (-2 * u)) := rfl
  rw [this]
  fun_prop

/-- `a(log X · c) = 2 X^{-3c/2} / (1 - X^{-2c})`, for numerical evaluation. -/
theorem aKer_log_mul {X : ℝ} (hX : 0 < X) (c : ℝ) :
    aKer (log X * c) = 2 * X ^ (-(3 / 2) * c) / (1 - X ^ (-2 * c)) := by
  unfold aKer
  rw [rpow_def_of_pos hX, rpow_def_of_pos hX]
  congr 3 <;> ring

/-! ### The integrand -/

variable {L : ℝ} {v : List ℝ}

/-- The integrand of `Jterm (autocorr (stepFn L v))`. -/
noncomputable def Jint (L : ℝ) (v : List ℝ) (u : ℝ) : ℝ :=
  aKer u * (1 - autocorr (stepFn L v) u)

theorem Jterm_eq_integral_Jint (L : ℝ) (v : List ℝ) :
    Jterm (autocorr (stepFn L v)) = ∫ u in Ioi (0 : ℝ), Jint L v u := rfl

theorem Jint_of_mem_cell (hL : 0 < L) (hv : ∃ t ∈ v, t ≠ 0) (j : ℕ) {u : ℝ}
    (h1 : j * (L / v.length) ≤ u) (h2 : u ≤ (j + 1) * (L / v.length)) :
    Jint L v u =
      aKer u * (1 - (corr v j + (u / (L / v.length) - j) * (corr v (j + 1) - corr v j))) := by
  unfold Jint
  rw [autocorr_stepFn_of_mem_cell hL hv j h1 h2]

/-- First cell `(0, w]`: integrable, with integral at most `1 - corr v 1`. -/
theorem Jint_first_cell (hL : 0 < L) (hv : ∃ t ∈ v, t ≠ 0) :
    IntervalIntegrable (Jint L v) volume 0 (L / v.length) ∧
      ∫ u in (0 : ℝ)..(L / v.length), Jint L v u ≤ 1 - corr v 1 := by
  have hm := length_pos_of_exists_ne_zero hv
  have hm' : (0 : ℝ) < v.length := by exact_mod_cast hm
  have hw0 : 0 < L / v.length := div_pos hL hm'
  have hc1 : 0 ≤ 1 - corr v 1 := by linarith [(abs_le.mp (abs_corr_le_one hv 1)).2]
  have hG : ∀ u ∈ Ioc 0 (L / (v.length : ℝ)),
      Jint L v u = aKer u * (u / (L / v.length) * (1 - corr v 1)) := by
    intro u hu
    rw [Jint_of_mem_cell hL hv 0 (by simpa using hu.1.le) (by simpa using hu.2), corr_zero hv]
    simp only [Nat.cast_zero, sub_zero, zero_add]
    ring
  have hbd : ∀ u ∈ Ioc 0 (L / (v.length : ℝ)),
      aKer u * (u / (L / v.length) * (1 - corr v 1)) ≤ (1 - corr v 1) / (L / v.length) ∧
        0 ≤ aKer u * (u / (L / v.length) * (1 - corr v 1)) := by
    intro u hu
    have h1 := aKer_mul_self_le_one hu.1
    have h0 := (aKer_pos hu.1).le
    constructor
    · have : aKer u * (u / (L / v.length) * (1 - corr v 1)) =
          (aKer u * u) * ((1 - corr v 1) / (L / v.length)) := by ring
      rw [this]
      exact mul_le_of_le_one_left (div_nonneg hc1 hw0.le) h1
    · exact mul_nonneg h0 (mul_nonneg (div_nonneg hu.1.le hw0.le) hc1)
  have hGint : IntegrableOn (fun u => aKer u * (u / (L / v.length) * (1 - corr v 1)))
      (Ioc 0 (L / (v.length : ℝ))) := by
    refine Measure.integrableOn_of_bounded (M := (1 - corr v 1) / (L / v.length))
      measure_Ioc_lt_top.ne ?_ ?_
    · exact (measurable_aKer.mul (by fun_prop)).aestronglyMeasurable
    · exact ae_restrict_of_forall_mem measurableSet_Ioc (fun u hu => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hbd u hu).2]; exact (hbd u hu).1)
  have hint : IntervalIntegrable (Jint L v) volume 0 (L / v.length) := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hw0.le]
    exact hGint.congr_fun (fun u hu => (hG u hu).symm) measurableSet_Ioc
  refine ⟨hint, ?_⟩
  calc ∫ u in (0 : ℝ)..(L / v.length), Jint L v u
      ≤ ∫ _ in (0 : ℝ)..(L / v.length), (1 - corr v 1) / (L / v.length) :=
        intervalIntegral.integral_mono_on_of_le_Ioo hw0.le hint intervalIntegrable_const
          (fun u hu => by
            have hu' : u ∈ Ioc 0 (L / (v.length : ℝ)) := ⟨hu.1, hu.2.le⟩
            rw [hG u hu']; exact (hbd u hu').1)
    _ = 1 - corr v 1 := by
        rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero, mul_div_cancel₀ _ hw0.ne']

/-- On a subinterval of a cell `[j w, (j + 1) w]`, `j ≥ 1`, the integrand is integrable. -/
theorem intervalIntegrable_Jint_of_subset_cell (hL : 0 < L) (hv : ∃ t ∈ v, t ≠ 0) {j : ℕ}
    (hj : 1 ≤ j) {a b : ℝ} (ha : j * (L / v.length) ≤ a) (hab : a ≤ b)
    (hb : b ≤ (j + 1) * (L / v.length)) : IntervalIntegrable (Jint L v) volume a b := by
  have hm := length_pos_of_exists_ne_zero hv
  have hm' : (0 : ℝ) < v.length := by exact_mod_cast hm
  have hw0 : 0 < L / v.length := div_pos hL hm'
  have hj' : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have ha0 : 0 < a := lt_of_lt_of_le (by nlinarith) ha
  have hcont : ContinuousOn (fun u => aKer u *
      (1 - (corr v j + (u / (L / v.length) - j) * (corr v (j + 1) - corr v j)))) (Icc a b) :=
    (continuousOn_aKer.mono (fun u (hu : u ∈ Icc a b) => lt_of_lt_of_le ha0 hu.1)).mul
      (by fun_prop)
  refine (hcont.intervalIntegrable_of_Icc hab).congr_uIoo ?_
  rw [uIoo_of_le hab]
  intro u hu
  exact (Jint_of_mem_cell hL hv j (ha.trans hu.1.le) (hu.2.le.trans hb)).symm

theorem integral_affine (α β a b : ℝ) :
    ∫ u in a..b, (α + β * u) = α * (b - a) + β * ((b ^ 2 - a ^ 2) / 2) := by
  rw [intervalIntegral.integral_add intervalIntegrable_const
      ((by fun_prop : Continuous fun u : ℝ => β * u).intervalIntegrable _ _),
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul, integral_id,
    smul_eq_mul]
  ring

/-- One of the 16 subcells of a cell `j ≥ 1`: `a` is decreasing and `1 - f ≥ 0` is affine. -/
theorem Jint_subcell_bound (hL : 0 < L) (hv : ∃ t ∈ v, t ≠ 0) {j : ℕ} (hj : 1 ≤ j) {i : ℕ}
    (hi : i < 16) :
    ∫ u in (j * (L / v.length) + i * (L / v.length / 16))..(j * (L / v.length) +
        (i + 1 : ℕ) * (L / v.length / 16)), Jint L v u ≤
      (L / v.length / 16) * aKer ((L / v.length / 16) * (j * 16 + i)) *
        (1 - (corr v j + (corr v (j + 1) - corr v j) * ((2 * i + 1) / 32))) := by
  have hm := length_pos_of_exists_ne_zero hv
  have hm' : (0 : ℝ) < v.length := by exact_mod_cast hm
  have hw0 : 0 < L / v.length := div_pos hL hm'
  have hj' : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hi' : (i : ℝ) + 1 ≤ 16 := by exact_mod_cast hi
  have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  set w := L / (v.length : ℝ) with hw
  set a := j * w + i * (w / 16) with ha
  set b := j * w + (i + 1 : ℕ) * (w / 16) with hb
  have hja : j * w ≤ a := by rw [ha]; nlinarith
  have hab : a ≤ b := by rw [ha, hb]; push_cast; nlinarith
  have hbj : b ≤ (j + 1) * w := by rw [hb]; push_cast; nlinarith
  have ha0 : 0 < a := lt_of_lt_of_le (by nlinarith) hja
  have hint := intervalIntegrable_Jint_of_subset_cell hL hv hj hja hab hbj
  have earg : w / 16 * (j * 16 + i) = a := by rw [ha]; ring
  rw [earg]
  have hmono : ∀ u ∈ Icc a b, Jint L v u ≤
      aKer a * (1 - corr v j + j * (corr v (j + 1) - corr v j)) +
        -(aKer a * (corr v (j + 1) - corr v j) / w) * u := by
    intro u hu
    have h1 : j * w ≤ u := hja.trans hu.1
    have h2 : u ≤ (j + 1) * w := hu.2.trans hbj
    have hnn := one_sub_autocorr_stepFn_nonneg hL hv (ha0.le.trans hu.1)
    rw [autocorr_stepFn_of_mem_cell hL hv j h1 h2] at hnn
    rw [Jint_of_mem_cell hL hv j h1 h2]
    have hk := aKer_anti ha0 hu.1
    calc aKer u * (1 - (corr v j + (u / w - j) * (corr v (j + 1) - corr v j)))
        ≤ aKer a * (1 - (corr v j + (u / w - j) * (corr v (j + 1) - corr v j))) :=
          mul_le_mul_of_nonneg_right hk hnn
      _ = _ := by field_simp; ring
  calc ∫ u in a..b, Jint L v u
      ≤ ∫ u in a..b, (aKer a * (1 - corr v j + j * (corr v (j + 1) - corr v j)) +
          -(aKer a * (corr v (j + 1) - corr v j) / w) * u) :=
        intervalIntegral.integral_mono_on hab hint
          (Continuous.intervalIntegrable (by fun_prop) _ _) hmono
    _ = _ := by
        rw [integral_affine, ha, hb]
        push_cast
        field_simp
        ring

/-- Tail `(L, ∞)`: there `f = 0` and `a(u) ≤ 2 e^{-3u/2} / (1 - e^{-2L})`. -/
theorem Jint_tail (hL : 0 < L) (hv : ∃ t ∈ v, t ≠ 0) :
    IntegrableOn (Jint L v) (Ioi L) ∧
      ∫ u in Ioi L, Jint L v u ≤ 4 / (3 * exp (3 * L / 2) * (1 - exp (-2 * L))) := by
  have hd := one_sub_exp_neg_two_mul_pos hL
  have hEq : EqOn (Jint L v) aKer (Ioi L) := by
    intro u hu
    unfold Jint
    rw [autocorr_stepFn_of_le hL hv (le_of_lt hu)]
    ring
  have hTint : IntegrableOn (fun u : ℝ => 2 * exp (-(3 / 2) * u) / (1 - exp (-2 * L)))
      (Ioi L) :=
    ((integrableOn_exp_mul_Ioi (a := -(3 / 2)) (by norm_num) L).const_mul 2).div_const _
  have hle : ∀ u ∈ Ioi L, aKer u ≤ 2 * exp (-(3 / 2) * u) / (1 - exp (-2 * L)) := by
    intro u hu
    have hu' : L < u := hu
    unfold aKer
    apply div_le_div_of_nonneg_left (by positivity) hd
    have : exp (-2 * u) ≤ exp (-2 * L) := exp_le_exp.mpr (by linarith)
    linarith
  have haInt : IntegrableOn aKer (Ioi L) := by
    refine Integrable.mono' hTint measurable_aKer.aestronglyMeasurable ?_
    exact ae_restrict_of_forall_mem measurableSet_Ioi (fun u hu => by
      rw [Real.norm_eq_abs, abs_of_pos (aKer_pos (hL.trans hu))]; exact hle u hu)
  have hJint : IntegrableOn (Jint L v) (Ioi L) := haInt.congr_fun hEq.symm measurableSet_Ioi
  refine ⟨hJint, ?_⟩
  calc ∫ u in Ioi L, Jint L v u = ∫ u in Ioi L, aKer u :=
        setIntegral_congr_fun measurableSet_Ioi hEq
    _ ≤ ∫ u in Ioi L, 2 * exp (-(3 / 2) * u) / (1 - exp (-2 * L)) :=
        setIntegral_mono_on haInt hTint measurableSet_Ioi hle
    _ = 4 / (3 * exp (3 * L / 2) * (1 - exp (-2 * L))) := by
        rw [integral_div, integral_const_mul, integral_exp_mul_Ioi (by norm_num) L]
        have : exp (-(3 / 2) * L) = (exp (3 * L / 2))⁻¹ := by
          rw [← exp_neg]; congr 1; ring
        rw [this]
        have := exp_pos (3 * L / 2)
        field_simp
        ring

/-! ### Assembly -/

/-- The data of the decomposition `(0, ∞) = (0, w] ∪ (w, L] ∪ (L, ∞)`. -/
theorem Jint_decomposition (hL : 0 < L) (hv : ∃ t ∈ v, t ≠ 0) :
    IntegrableOn (Jint L v) (Ioi 0) ∧
      Jterm (autocorr (stepFn L v)) =
        (∫ u in (0 : ℝ)..(L / v.length), Jint L v u) +
          (∑ j ∈ Finset.Ico 1 v.length,
            ∫ u in (j * (L / v.length))..((j + 1 : ℕ) * (L / v.length)), Jint L v u) +
          ∫ u in Ioi L, Jint L v u := by
  have hm := length_pos_of_exists_ne_zero hv
  have hm' : (0 : ℝ) < v.length := by exact_mod_cast hm
  have hw0 : 0 < L / v.length := div_pos hL hm'
  have hmw : (v.length : ℝ) * (L / v.length) = L := by field_simp
  obtain ⟨hint0, -⟩ := Jint_first_cell hL hv
  obtain ⟨hintT, -⟩ := Jint_tail hL hv
  have hm1 : 1 ≤ v.length := hm
  have hcell : ∀ j ∈ Set.Ico 1 v.length, IntervalIntegrable (Jint L v) volume
      ((j : ℝ) * (L / v.length)) (((j + 1 : ℕ) : ℝ) * (L / v.length)) := fun j hj =>
    intervalIntegrable_Jint_of_subset_cell hL hv hj.1 le_rfl
      (by push_cast; nlinarith) (by push_cast; exact le_rfl)
  have hmid := intervalIntegral.sum_integral_adjacent_intervals_Ico
    (a := fun k : ℕ => (k : ℝ) * (L / v.length)) (f := Jint L v) (μ := volume) hm1 hcell
  have hintmid := IntervalIntegrable.trans_iterate_Ico
    (a := fun k : ℕ => (k : ℝ) * (L / v.length)) hm1 hcell
  simp only [Nat.cast_one, one_mul, hmw] at hmid hintmid
  have hint0L : IntervalIntegrable (Jint L v) volume 0 L := hint0.trans hintmid
  have hIoc : IntegrableOn (Jint L v) (Ioc 0 L) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hL.le).mp hint0L
  refine ⟨?_, ?_⟩
  · rw [← Ioc_union_Ioi_eq_Ioi hL.le]
    exact hIoc.union hintT
  · rw [Jterm_eq_integral_Jint, ← Ioc_union_Ioi_eq_Ioi hL.le,
      setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi hIoc hintT,
      ← intervalIntegral.integral_of_le hL.le,
      ← intervalIntegral.integral_add_adjacent_intervals hint0 hintmid, hmid]

/-- Integrability of the integrand of `Jterm (autocorr (stepFn L v))` on `(0, ∞)`. -/
theorem integrableOn_Jint (hL : 0 < L) (hv : ∃ t ∈ v, t ≠ 0) :
    IntegrableOn (fun u => 2 * exp (-(3 / 2) * u) / (1 - exp (-2 * u)) *
      (1 - autocorr (stepFn L v) u)) (Ioi 0) :=
  (Jint_decomposition hL hv).1

/-- A whole cell `j ≥ 1`, cut into 16 subcells. -/
theorem Jint_cell_bound (hL : 0 < L) (hv : ∃ t ∈ v, t ≠ 0) {j : ℕ} (hj : 1 ≤ j) :
    ∫ u in (j * (L / v.length))..((j + 1 : ℕ) * (L / v.length)), Jint L v u ≤
      ∑ i ∈ Finset.range 16,
        (L / v.length / 16) * aKer ((L / v.length / 16) * (j * 16 + i)) *
          (1 - (corr v j + (corr v (j + 1) - corr v j) * ((2 * i + 1) / 32))) := by
  have hm := length_pos_of_exists_ne_zero hv
  have hm' : (0 : ℝ) < v.length := by exact_mod_cast hm
  have hw0 : 0 < L / v.length := div_pos hL hm'
  have hj' : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hsub := intervalIntegral.sum_integral_adjacent_intervals
    (a := fun i : ℕ => (j : ℝ) * (L / v.length) + i * (L / v.length / 16))
    (f := Jint L v) (μ := volume) (n := 16) (fun i hi => by
      have hi' : (i : ℝ) + 1 ≤ 16 := by exact_mod_cast hi
      have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
      exact intervalIntegrable_Jint_of_subset_cell hL hv hj
        (by nlinarith) (by push_cast; nlinarith) (by push_cast; nlinarith))
  have e16 : (j : ℝ) * (L / v.length) + ((16 : ℕ) : ℝ) * (L / v.length / 16) =
      ((j + 1 : ℕ) : ℝ) * (L / v.length) := by push_cast; ring
  simp only [Nat.cast_zero, zero_mul, add_zero] at hsub
  rw [e16] at hsub
  rw [← hsub]
  exact Finset.sum_le_sum (fun i hi => Jint_subcell_bound hL hv hj (Finset.mem_range.mp hi))

/-- **The explicit upper bound `J⁺`** of `kernel_verify.py` (`rigorous_margin`). -/
theorem Jterm_le (hL : 0 < L) (hv : ∃ t ∈ v, t ≠ 0) :
    Jterm (autocorr (stepFn L v)) ≤
      (1 - corr v 1) +
        ∑ j ∈ Finset.Ico 1 v.length, ∑ i ∈ Finset.range 16,
          (L / v.length / 16) * aKer ((L / v.length / 16) * (j * 16 + i)) *
            (1 - (corr v j + (corr v (j + 1) - corr v j) * ((2 * i + 1) / 32))) +
        4 / (3 * exp (3 * L / 2) * (1 - exp (-2 * L))) := by
  rw [(Jint_decomposition hL hv).2]
  have h0 := (Jint_first_cell hL hv).2
  have hT := (Jint_tail hL hv).2
  have hmid := Finset.sum_le_sum
    (fun j hj => Jint_cell_bound hL hv (Finset.mem_Ico.mp hj).1 :
      ∀ j ∈ Finset.Ico 1 v.length, _ ≤ _)
  linarith

/-- The upper bound `J⁺`, as a definition. -/
noncomputable def Jplus (L : ℝ) (v : List ℝ) : ℝ :=
  (1 - corr v 1) +
    ∑ j ∈ Finset.Ico 1 v.length, ∑ i ∈ Finset.range 16,
      (L / v.length / 16) * aKer ((L / v.length / 16) * (j * 16 + i)) *
        (1 - (corr v j + (corr v (j + 1) - corr v j) * ((2 * i + 1) / 32))) +
    4 / (3 * exp (3 * L / 2) * (1 - exp (-2 * L)))

theorem Jterm_le_Jplus (hL : 0 < L) (hv : ∃ t ∈ v, t ≠ 0) :
    Jterm (autocorr (stepFn L v)) ≤ Jplus L v :=
  Jterm_le hL hv

/-! ### Specialisation to `L = log X` -/

theorem exp_three_mul_log_div_two {X : ℝ} (hX : 0 < X) : exp (3 * log X / 2) = X * √X := by
  have hs : √X = exp (log X / 2) := by
    rw [sqrt_eq_iff_mul_self_eq_of_pos (exp_pos _), ← exp_add, add_halves, exp_log hX]
  calc exp (3 * log X / 2) = exp (log X + log X / 2) := by congr 1; ring
    _ = exp (log X) * exp (log X / 2) := exp_add _ _
    _ = X * √X := by rw [exp_log hX, hs]

theorem exp_neg_two_mul_log {X : ℝ} (hX : 0 < X) : exp (-2 * log X) = 1 / (X * X) := by
  calc exp (-2 * log X) = exp (-(log X + log X)) := by congr 1; ring
    _ = (exp (log X) * exp (log X))⁻¹ := by rw [exp_neg, exp_add]
    _ = 1 / (X * X) := by rw [exp_log hX, one_div]

/-- The bound for `L = log X`, in the shape evaluated by `rigorous_margin`: the tail is
`4 / (3 X √X (1 - 1/X²))`. -/
theorem Jterm_log_le {X : ℕ} (hX : 2 ≤ X) (hv : ∃ t ∈ v, t ≠ 0) :
    Jterm (autocorr (stepFn (log X) v)) ≤
      (1 - corr v 1) +
        ∑ j ∈ Finset.Ico 1 v.length, ∑ i ∈ Finset.range 16,
          (log X / v.length / 16) * aKer ((log X / v.length / 16) * (j * 16 + i)) *
            (1 - (corr v j + (corr v (j + 1) - corr v j) * ((2 * i + 1) / 32))) +
        4 / (3 * X * √(X : ℝ) * (1 - 1 / ((X : ℝ) * X))) := by
  have hX1 : (1 : ℝ) < X := by exact_mod_cast hX
  have hX0 : (0 : ℝ) < X := by linarith
  have h := Jterm_le (L := log X) (v := v) (log_pos hX1) hv
  rw [exp_three_mul_log_div_two hX0, exp_neg_two_mul_log hX0, ← mul_assoc] at h
  exact h

/-- The closed form of `f (log n)` used by `f_at` in `kernel_verify.py`: the cell index `k` of
`log n` is certified by the integer inequalities `X^k ≤ n^m ≤ X^(k+1)`, `m = v.length`. -/
theorem autocorr_stepFn_log {X n k : ℕ} (hX : 2 ≤ X) (hn : 1 ≤ n) (hv : ∃ t ∈ v, t ≠ 0)
    (h1 : X ^ k ≤ n ^ v.length) (h2 : n ^ v.length ≤ X ^ (k + 1)) :
    autocorr (stepFn (log X) v) (log n) =
      corr v k + (log n / (log X / v.length) - k) * (corr v (k + 1) - corr v k) := by
  have hX1 : (1 : ℝ) < X := by exact_mod_cast hX
  have hX0 : (0 : ℝ) < X := by linarith
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hm := length_pos_of_exists_ne_zero hv
  have hm' : (0 : ℝ) < v.length := by exact_mod_cast hm
  have hlX := log_pos hX1
  have e1 : (k : ℝ) * log X ≤ v.length * log n := by
    rw [← log_pow, ← log_pow]
    exact log_le_log (by positivity) (by exact_mod_cast h1)
  have e2 : (v.length : ℝ) * log n ≤ (k + 1 : ℕ) * log X := by
    rw [← log_pow, ← log_pow]
    exact log_le_log (by positivity) (by exact_mod_cast h2)
  push_cast at e2
  refine autocorr_stepFn_of_mem_cell hlX hv k ?_ ?_
  · rw [← mul_div_assoc, div_le_iff₀ hm']
    linarith
  · rw [← mul_div_assoc, le_div_iff₀ hm']
    linarith

end Exp7
