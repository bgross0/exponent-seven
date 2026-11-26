import Exp7Lean.Analytic.Statement

/-!
Exponent 7, analytic side: the autocorrelation of a step function in closed form.

For `L > 0`, a list `v` of length `m ≥ 1` with a nonzero entry, cell width `w = L / m` and
`f = autocorr (stepFn L v)`:

* `autocorr_stepFn_closed_form`: `f ((j + θ) w) = (1 - θ) corr v j + θ corr v (j + 1)` for
  `j : ℕ`, `θ ∈ [0, 1]`;
* `autocorr_stepFn_of_mem_cell`: the same, written for `u ∈ [j w, (j + 1) w]`;
* `autocorr_stepFn_zero`, `autocorr_stepFn_nat_mul`, `autocorr_stepFn_of_le`: `f 0 = 1`,
  `f (j w) = corr v j`, `f u = 0` for `u ≥ L`;
* `abs_corr_le_one`, `abs_autocorr_stepFn_le_one`, `one_sub_autocorr_stepFn_nonneg`:
  `|corr v j| ≤ 1`, and `|f u| ≤ 1`, `0 ≤ 1 - f u` for `u ≥ 0`.
-/

namespace Exp7

open Real MeasureTheory Set

/-- The discrete normalised autocorrelation of the list `v` at lag `j`
(it is `0` for `j ≥ v.length`). -/
noncomputable def corr (v : List ℝ) (j : ℕ) : ℝ :=
  (∑ k ∈ Finset.range (v.length - j), v.getD k 0 * v.getD (k + j) 0) /
    ∑ k ∈ Finset.range v.length, (v.getD k 0) ^ 2

variable {L : ℝ} {v : List ℝ}

/-! ### Elementary facts about `v` and `corr` -/

theorem length_pos_of_exists_ne_zero (hv : ∃ t ∈ v, t ≠ 0) : 0 < v.length := by
  obtain ⟨t, ht, -⟩ := hv
  exact List.length_pos_of_mem ht

theorem sumSq_pos (hv : ∃ t ∈ v, t ≠ 0) :
    0 < ∑ k ∈ Finset.range v.length, (v.getD k 0) ^ 2 := by
  obtain ⟨t, ht, ht0⟩ := hv
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem ht
  have h1 : 0 < (v.getD k 0) ^ 2 := by
    rw [List.getD_eq_getElem _ _ hk]; positivity
  exact lt_of_lt_of_le h1
    (Finset.single_le_sum (f := fun k => (v.getD k 0) ^ 2) (fun i _ => sq_nonneg _)
      (Finset.mem_range.mpr hk))

theorem corr_zero (hv : ∃ t ∈ v, t ≠ 0) : corr v 0 = 1 := by
  unfold corr
  have hpos := sumSq_pos hv
  have : ∑ k ∈ Finset.range (v.length - 0), v.getD k 0 * v.getD (k + 0) 0 =
      ∑ k ∈ Finset.range v.length, (v.getD k 0) ^ 2 := by
    simp [sq]
  rw [this, div_self hpos.ne']

theorem corr_of_length_le {j : ℕ} (hj : v.length ≤ j) : corr v j = 0 := by
  unfold corr
  rw [Nat.sub_eq_zero_of_le hj]
  simp

theorem sum_range_shift_eq (v : List ℝ) (j : ℕ) :
    ∑ k ∈ Finset.range v.length, v.getD k 0 * v.getD (k + j) 0 =
      ∑ k ∈ Finset.range (v.length - j), v.getD k 0 * v.getD (k + j) 0 := by
  symm
  apply Finset.sum_subset
  · intro k hk
    simp only [Finset.mem_range] at hk ⊢
    omega
  · intro k hk hk'
    simp only [Finset.mem_range] at hk hk'
    rw [List.getD_eq_default (n := k + j) _ _ (by omega), mul_zero]

theorem abs_corr_le_one (hv : ∃ t ∈ v, t ≠ 0) (j : ℕ) : |corr v j| ≤ 1 := by
  unfold corr
  have hpos := sumSq_pos hv
  rw [abs_div, abs_of_pos hpos, div_le_one hpos]
  have hA : ∑ k ∈ Finset.range (v.length - j), (v.getD k 0) ^ 2 ≤
      ∑ k ∈ Finset.range v.length, (v.getD k 0) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg
      (by intro k hk; simp only [Finset.mem_range] at hk ⊢; omega) (fun _ _ _ => sq_nonneg _)
  have hB : ∑ k ∈ Finset.range (v.length - j), (v.getD (k + j) 0) ^ 2 ≤
      ∑ k ∈ Finset.range v.length, (v.getD k 0) ^ 2 := by
    have : ∑ k ∈ Finset.range (v.length - j), (v.getD (k + j) 0) ^ 2 =
        ∑ k ∈ Finset.Ico j v.length, (v.getD k 0) ^ 2 := by
      rw [Finset.sum_Ico_eq_sum_range]
      exact Finset.sum_congr rfl (fun k _ => by rw [add_comm])
    rw [this]
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (by intro k hk; simp only [Finset.mem_Ico, Finset.mem_range] at hk ⊢; omega)
      (fun _ _ _ => sq_nonneg _)
  have hC : |∑ k ∈ Finset.range (v.length - j), v.getD k 0 * v.getD (k + j) 0| ≤
      ∑ k ∈ Finset.range (v.length - j), ((v.getD k 0) ^ 2 + (v.getD (k + j) 0) ^ 2) / 2 := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    rw [abs_le]
    constructor <;>
      nlinarith [sq_nonneg (v.getD k 0 - v.getD (k + j) 0),
        sq_nonneg (v.getD k 0 + v.getD (k + j) 0)]
  rw [← Finset.sum_div, Finset.sum_add_distrib] at hC
  linarith

/-! ### The step function on a cell -/

theorem stepFn_of_not_mem {t : ℝ} (ht : ¬(0 ≤ t ∧ t < L)) : stepFn L v t = 0 := ite_eq_right ht

/-- On the `i`-th cell `[i w, (i + 1) w)` the step function is `v.getD i 0`; this holds for every
`i : ℕ` (beyond `v.length` both sides vanish). -/
theorem stepFn_cell (hL : 0 < L) (hm : 0 < v.length) (i : ℕ) {s : ℝ}
    (h1 : i * (L / v.length) ≤ s) (h2 : s < (i + 1) * (L / v.length)) :
    stepFn L v s = v.getD i 0 := by
  have hm' : (0 : ℝ) < v.length := by exact_mod_cast hm
  have hw : 0 < L / v.length := div_pos hL hm'
  have hs0 : 0 ≤ s := le_trans (by positivity) h1
  have hmw : (v.length : ℝ) * (L / v.length) = L := by field_simp
  unfold stepFn
  by_cases hi : i < v.length
  · have hi' : (i : ℝ) + 1 ≤ v.length := by exact_mod_cast hi
    have hsL : s < L := by
      calc s < (i + 1) * (L / v.length) := h2
        _ ≤ v.length * (L / v.length) := by gcongr
        _ = L := hmw
    rw [ite_eq_left ⟨hs0, hsL⟩]
    congr 1
    rw [Nat.floor_eq_iff (by positivity)]
    constructor
    · rw [le_div_iff₀ hL]
      calc (i : ℝ) * L = i * (L / v.length) * v.length := by field_simp
        _ ≤ s * v.length := by gcongr
    · rw [div_lt_iff₀ hL]
      calc s * v.length < (i + 1) * (L / v.length) * v.length := by gcongr
        _ = (i + 1) * L := by field_simp
  · push Not at hi
    have hi' : (v.length : ℝ) ≤ i := by exact_mod_cast hi
    have hsL : L ≤ s := by
      calc L = v.length * (L / v.length) := hmw.symm
        _ ≤ i * (L / v.length) := by gcongr
        _ ≤ s := h1
    rw [ite_eq_right (fun h => absurd h.2 (not_lt.mpr hsL)), List.getD_eq_default _ _ hi]

/-! ### The correlation integral -/

/-- The contribution of the `k`-th cell to `∫ g(t) g(t + u) dt` at `u = (j + θ) w`. -/
theorem cell_integral (hL : 0 < L) (hm : 0 < v.length) (k j : ℕ) {θ : ℝ}
    (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    IntervalIntegrable (fun t => stepFn L v t * stepFn L v (t + (j + θ) * (L / v.length))) volume
        (k * (L / v.length)) ((k + 1 : ℕ) * (L / v.length)) ∧
    ∫ t in (k * (L / v.length))..((k + 1 : ℕ) * (L / v.length)),
        stepFn L v t * stepFn L v (t + (j + θ) * (L / v.length)) =
      (L / v.length) * ((1 - θ) * (v.getD k 0 * v.getD (k + j) 0) +
        θ * (v.getD k 0 * v.getD (k + (j + 1)) 0)) := by
  have hm' : (0 : ℝ) < v.length := by exact_mod_cast hm
  have hw0 : 0 < L / v.length := div_pos hL hm'
  set w := L / (v.length : ℝ) with hw
  have hθw : 0 ≤ θ * w := by positivity
  have hθw' : 0 ≤ (1 - θ) * w := mul_nonneg (by linarith) hw0.le
  set c := (k + 1 - θ) * w with hc
  have hkc : k * w ≤ c := by rw [hc]; linarith
  have hck : c ≤ (k + 1 : ℕ) * w := by rw [hc]; push_cast; linarith
  have e1 : EqOn (fun t => stepFn L v t * stepFn L v (t + (j + θ) * w))
      (fun _ => v.getD k 0 * v.getD (k + j) 0) (Ioo (k * w) c) := by
    intro t ht
    have ht2 := ht.2
    rw [hc] at ht2
    simp only
    rw [stepFn_cell hL hm k ht.1.le (by linarith),
      stepFn_cell hL hm (k + j) (by push_cast; linarith [ht.1]) (by push_cast; linarith)]
  have e2 : EqOn (fun t => stepFn L v t * stepFn L v (t + (j + θ) * w))
      (fun _ => v.getD k 0 * v.getD (k + (j + 1)) 0) (Ioo c ((k + 1 : ℕ) * w)) := by
    intro t ht
    have ht1 := ht.1
    have ht2 := ht.2
    rw [hc] at ht1
    push_cast at ht2
    simp only
    rw [stepFn_cell hL hm k (by linarith) (by linarith),
      stepFn_cell hL hm (k + (j + 1)) (by push_cast; linarith) (by push_cast; linarith)]
  have i1 : IntervalIntegrable (fun t => stepFn L v t * stepFn L v (t + (j + θ) * w)) volume
      (k * w) c :=
    (intervalIntegrable_const (c := v.getD k 0 * v.getD (k + j) 0)).congr_uIoo
      (by rw [uIoo_of_le hkc]; exact e1.symm)
  have i2 : IntervalIntegrable (fun t => stepFn L v t * stepFn L v (t + (j + θ) * w)) volume
      c ((k + 1 : ℕ) * w) :=
    (intervalIntegrable_const (c := v.getD k 0 * v.getD (k + (j + 1)) 0)).congr_uIoo
      (by rw [uIoo_of_le hck]; exact e2.symm)
  refine ⟨i1.trans i2, ?_⟩
  rw [← intervalIntegral.integral_add_adjacent_intervals i1 i2,
    intervalIntegral.integral_congr_Ioo_of_le hkc e1,
    intervalIntegral.integral_congr_Ioo_of_le hck e2,
    intervalIntegral.integral_const, intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  rw [hc]
  push_cast
  ring

/-- `∫ g(t) g(t + u) dt` at `u = (j + θ) w`, `θ ∈ [0, 1]`. -/
theorem integral_stepFn_mul_shift (hL : 0 < L) (hm : 0 < v.length) (j : ℕ) {θ : ℝ}
    (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    ∫ t, stepFn L v t * stepFn L v (t + (j + θ) * (L / v.length)) =
      (L / v.length) *
        ((1 - θ) * (∑ k ∈ Finset.range (v.length - j), v.getD k 0 * v.getD (k + j) 0) +
          θ * (∑ k ∈ Finset.range (v.length - (j + 1)),
            v.getD k 0 * v.getD (k + (j + 1)) 0)) := by
  have hm' : (0 : ℝ) < v.length := by exact_mod_cast hm
  have hmw : (v.length : ℝ) * (L / v.length) = L := by field_simp
  have hsupp : ∀ t, t ∉ Ico 0 L →
      stepFn L v t * stepFn L v (t + (j + θ) * (L / v.length)) = 0 := by
    intro t ht
    rw [stepFn_of_not_mem (fun h => ht h), zero_mul]
  have hsum := intervalIntegral.sum_integral_adjacent_intervals
    (a := fun k : ℕ => (k : ℝ) * (L / v.length))
    (f := fun t => stepFn L v t * stepFn L v (t + (j + θ) * (L / v.length)))
    (μ := volume) (n := v.length) (fun k _ => (cell_integral hL hm k j h0 h1).1)
  simp only [Nat.cast_zero, zero_mul, hmw] at hsum
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hsupp, integral_Ico_eq_integral_Ioo,
    ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hL.le, ← hsum,
    Finset.sum_congr rfl (fun k _ => (cell_integral hL hm k j h0 h1).2),
    ← sum_range_shift_eq v j, ← sum_range_shift_eq v (j + 1)]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]

/-- `∫ g² = w · ∑ v_k²`. -/
theorem integral_stepFn_sq (hL : 0 < L) (hm : 0 < v.length) :
    ∫ t, stepFn L v t ^ 2 = (L / v.length) * ∑ k ∈ Finset.range v.length, (v.getD k 0) ^ 2 := by
  have h := integral_stepFn_mul_shift (v := v) hL hm 0 (θ := 0) le_rfl zero_le_one
  simp only [Nat.cast_zero, add_zero, zero_mul, sub_zero, one_mul, Nat.sub_zero] at h
  simp only [sq]
  rw [h]

/-! ### Closed form of the autocorrelation -/

/-- **Closed form.** With `w = L / v.length`, `f = autocorr (stepFn L v)` is the piecewise linear
interpolation of `corr v` on the grid `w ℕ`. -/
theorem autocorr_stepFn_closed_form (hL : 0 < L) (hv : ∃ t ∈ v, t ≠ 0) (j : ℕ) {θ : ℝ}
    (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    autocorr (stepFn L v) ((j + θ) * (L / v.length)) =
      (1 - θ) * corr v j + θ * corr v (j + 1) := by
  have hm := length_pos_of_exists_ne_zero hv
  have hm' : (0 : ℝ) < v.length := by exact_mod_cast hm
  have hw0 : 0 < L / v.length := div_pos hL hm'
  have hpos := sumSq_pos hv
  unfold autocorr corr
  rw [integral_stepFn_mul_shift hL hm j h0 h1, integral_stepFn_sq hL hm]
  field_simp

/-- The closed form, for `u` in the `j`-th cell `[j w, (j + 1) w]` (both endpoints allowed). -/
theorem autocorr_stepFn_of_mem_cell (hL : 0 < L) (hv : ∃ t ∈ v, t ≠ 0) (j : ℕ) {u : ℝ}
    (h1 : j * (L / v.length) ≤ u) (h2 : u ≤ (j + 1) * (L / v.length)) :
    autocorr (stepFn L v) u =
      corr v j + (u / (L / v.length) - j) * (corr v (j + 1) - corr v j) := by
  have hm := length_pos_of_exists_ne_zero hv
  have hm' : (0 : ℝ) < v.length := by exact_mod_cast hm
  have hw0 : 0 < L / v.length := div_pos hL hm'
  have h := autocorr_stepFn_closed_form hL hv j (θ := u / (L / v.length) - j)
    (by rw [sub_nonneg, le_div_iff₀ hw0]; exact h1)
    (by rw [sub_le_iff_le_add, div_le_iff₀ hw0]; linarith)
  have e : ((j : ℝ) + (u / (L / v.length) - j)) * (L / v.length) = u := by
    rw [add_sub_cancel, div_mul_cancel₀ _ hw0.ne']
  rw [e] at h
  rw [h]
  ring

/-- Every `u ≥ 0` is `(j + θ) w` with `j : ℕ` and `θ ∈ [0, 1]`. -/
theorem exists_cell {w u : ℝ} (hw : 0 < w) (hu : 0 ≤ u) :
    ∃ (j : ℕ) (θ : ℝ), 0 ≤ θ ∧ θ ≤ 1 ∧ u = (j + θ) * w := by
  have h0 : 0 ≤ u / w := div_nonneg hu hw.le
  refine ⟨⌊u / w⌋₊, u / w - ⌊u / w⌋₊, sub_nonneg.mpr (Nat.floor_le h0), ?_, ?_⟩
  · have := Nat.lt_floor_add_one (u / w)
    linarith
  · rw [add_sub_cancel, div_mul_cancel₀ _ hw.ne']

theorem autocorr_stepFn_zero (hL : 0 < L) (hv : ∃ t ∈ v, t ≠ 0) :
    autocorr (stepFn L v) 0 = 1 := by
  have h := autocorr_stepFn_closed_form hL hv 0 (θ := 0) le_rfl zero_le_one
  simpa [corr_zero hv] using h

theorem autocorr_stepFn_nat_mul (hL : 0 < L) (hv : ∃ t ∈ v, t ≠ 0) (j : ℕ) :
    autocorr (stepFn L v) (j * (L / v.length)) = corr v j := by
  have h := autocorr_stepFn_closed_form hL hv j (θ := 0) le_rfl zero_le_one
  simpa using h

/-- `f` vanishes on `[L, ∞)`. -/
theorem autocorr_stepFn_of_le (hL : 0 < L) (hv : ∃ t ∈ v, t ≠ 0) {u : ℝ} (hu : L ≤ u) :
    autocorr (stepFn L v) u = 0 := by
  have hm := length_pos_of_exists_ne_zero hv
  have hm' : (0 : ℝ) < v.length := by exact_mod_cast hm
  have hw0 : 0 < L / v.length := div_pos hL hm'
  have hmw : (v.length : ℝ) * (L / v.length) = L := by field_simp
  obtain ⟨j, θ, h0, h1, rfl⟩ := exists_cell hw0 (hL.le.trans hu)
  have hj : v.length ≤ j ∨ (j + 1 = v.length ∧ θ = 1) := by
    by_contra hcon
    push Not at hcon
    obtain ⟨hlt, hne⟩ := hcon
    have hj1 : (j : ℝ) + 1 ≤ v.length := by exact_mod_cast hlt
    have hθ : θ < 1 ∨ (j : ℝ) + 2 ≤ v.length := by
      by_cases hj2 : j + 1 = v.length
      · exact Or.inl (lt_of_le_of_ne h1 (hne hj2))
      · right
        have : j + 2 ≤ v.length := by omega
        exact_mod_cast this
    have : ((j : ℝ) + θ) * (L / v.length) < v.length * (L / v.length) := by
      apply mul_lt_mul_of_pos_right _ hw0
      rcases hθ with h | h <;> linarith
    linarith
  rw [autocorr_stepFn_closed_form hL hv j h0 h1]
  rcases hj with hj | ⟨hj, rfl⟩
  · rw [corr_of_length_le hj, corr_of_length_le (by omega)]
    ring
  · rw [corr_of_length_le hj.ge]
    ring

/-! ### Bounds -/

/-- `|f u| ≤ 1` for `u ≥ 0`. -/
theorem abs_autocorr_stepFn_le_one (hL : 0 < L) (hv : ∃ t ∈ v, t ≠ 0) {u : ℝ} (hu : 0 ≤ u) :
    |autocorr (stepFn L v) u| ≤ 1 := by
  have hm := length_pos_of_exists_ne_zero hv
  have hm' : (0 : ℝ) < v.length := by exact_mod_cast hm
  have hw0 : 0 < L / v.length := div_pos hL hm'
  obtain ⟨j, θ, h0, h1, rfl⟩ := exists_cell hw0 hu
  rw [autocorr_stepFn_closed_form hL hv j h0 h1]
  have a1 := abs_le.mp (abs_corr_le_one hv j)
  have a2 := abs_le.mp (abs_corr_le_one hv (j + 1))
  have h1' : 0 ≤ 1 - θ := by linarith
  rw [abs_le]
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left a1.1 h1', mul_le_mul_of_nonneg_left a2.1 h0]
  · nlinarith [mul_le_mul_of_nonneg_left a1.2 h1', mul_le_mul_of_nonneg_left a2.2 h0]

/-- The autocorrelation is even (for any `g`). -/
theorem autocorr_neg (g : ℝ → ℝ) (u : ℝ) : autocorr g (-u) = autocorr g u := by
  unfold autocorr
  congr 1
  rw [← integral_add_right_eq_self (fun t => g t * g (t + -u)) u]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only [add_neg_cancel_right]
  ring

/-- `|f u| ≤ 1` for every real `u`. -/
theorem abs_autocorr_stepFn_le_one' (hL : 0 < L) (hv : ∃ t ∈ v, t ≠ 0) (u : ℝ) :
    |autocorr (stepFn L v) u| ≤ 1 := by
  rcases le_total 0 u with hu | hu
  · exact abs_autocorr_stepFn_le_one hL hv hu
  · rw [← autocorr_neg]
    exact abs_autocorr_stepFn_le_one hL hv (neg_nonneg.mpr hu)

theorem autocorr_stepFn_le_one (hL : 0 < L) (hv : ∃ t ∈ v, t ≠ 0) {u : ℝ} (hu : 0 ≤ u) :
    autocorr (stepFn L v) u ≤ 1 :=
  (abs_le.mp (abs_autocorr_stepFn_le_one hL hv hu)).2

/-- `0 ≤ 1 - f u` for `u ≥ 0`. -/
theorem one_sub_autocorr_stepFn_nonneg (hL : 0 < L) (hv : ∃ t ∈ v, t ≠ 0) {u : ℝ}
    (hu : 0 ≤ u) : 0 ≤ 1 - autocorr (stepFn L v) u :=
  sub_nonneg.mpr (autocorr_stepFn_le_one hL hv hu)

end Exp7
