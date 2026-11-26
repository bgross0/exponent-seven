import Exp7Lean.Numerics.LogSeries

/-!
# Sharp bounds for the Euler–Mascheroni constant (DeTemple's inequality)

With `a_n = H_n - log (n + 1/2)` we prove, for every `n ≥ 1`,

    a_n - 1 / (24 n^2)  ≤  γ  ≤  a_n - 1 / (24 (n+1)^2).

The two bounds differ by about `1 / (12 n^3)`; Mathlib's own sequences `eulerMascheroniSeq`,
`eulerMascheroniSeq'` only give `1/n`.

Proof.  `a_n - a_{n+1} = log(n+3/2) - log(n+1/2) - 1/(n+1) = 2 x^3 · atanhTail (x^2) 1` with
`x = 1/(2n+2)`, and `1/3 ≤ atanhTail w 1 ≤ 1/(3(1-w))`.  Hence `n ↦ a_n - 1/(24 n^2)` is
increasing and `n ↦ a_n - 1/(24 (n+1)^2)` is decreasing; and `a_n → γ` because
`H_n - log(n+1) ≤ a_n ≤ H_n - log n`.
-/

namespace Exp7.Num

open Real Filter Topology

/-- `a_n = H_n - log (n + 1/2)`. -/
noncomputable def gamSeq (n : ℕ) : ℝ := (harmonic n : ℝ) - log ((n : ℝ) + 1 / 2)

theorem gamSeq_tendsto : Tendsto gamSeq atTop (𝓝 eulerMascheroniConstant) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_harmonic_sub_log_add_one
    tendsto_harmonic_sub_log ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have : log ((n : ℝ) + 1 / 2) ≤ log ((n : ℝ) + 1) := log_le_log (by positivity) (by linarith)
    unfold gamSeq; linarith
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have : log (n : ℝ) ≤ log ((n : ℝ) + 1 / 2) := log_le_log hn0 (by linarith)
    unfold gamSeq; linarith

theorem atanhTail_one_ge {w : ℝ} (h0 : 0 ≤ w) (h1 : w < 1) : 1 / 3 ≤ atanhTail w 1 := by
  rw [atanhTail_succ h0 h1 1]
  have := mul_nonneg h0 (atanhTail_nonneg h0 2)
  norm_num at this ⊢
  linarith

theorem atanhTail_one_le {w : ℝ} (h0 : 0 ≤ w) (h1 : w < 1) : atanhTail w 1 ≤ 1 / (3 * (1 - w)) := by
  have := atanhTail_le h0 h1 1
  norm_num at this ⊢
  exact this

/-- `a_n - a_{n+1} = 2 x^3 · atanhTail (x^2) 1`, `x = 1/(2n+2)`. -/
theorem gamSeq_sub_succ (n : ℕ) :
    gamSeq n - gamSeq (n + 1)
      = 2 * (1 / (2 * (n : ℝ) + 2)) ^ 3 * atanhTail ((1 / (2 * (n : ℝ) + 2)) ^ 2) 1 := by
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hb : (0 : ℝ) < (n : ℝ) + 1 / 2 := by positivity
  have hab : (n : ℝ) + 1 / 2 ≤ (n : ℝ) + 1 + 1 / 2 := by linarith
  have hlog := log_sub_log_eq hb hab
  have hz : ((n : ℝ) + 1 + 1 / 2 - ((n : ℝ) + 1 / 2)) / ((n : ℝ) + 1 + 1 / 2 + ((n : ℝ) + 1 / 2))
      = 1 / (2 * (n : ℝ) + 2) := by
    congr 1 <;> ring
  rw [hz] at hlog
  have hx0 : (0 : ℝ) ≤ 1 / (2 * (n : ℝ) + 2) := by positivity
  have hx1 : 1 / (2 * (n : ℝ) + 2) < 1 := by
    rw [div_lt_one (by positivity)]; linarith
  have hw0 : (0 : ℝ) ≤ (1 / (2 * (n : ℝ) + 2)) ^ 2 := by positivity
  have hw1 : (1 / (2 * (n : ℝ) + 2)) ^ 2 < 1 := by nlinarith
  rw [atanhTail_succ hw0 hw1 0] at hlog
  have hH : ((harmonic (n + 1) : ℚ) : ℝ) = (harmonic n : ℝ) + 1 / ((n : ℝ) + 1) := by
    rw [harmonic_succ]; push_cast; ring
  unfold gamSeq
  rw [hH]
  push_cast
  have h2 : (1 : ℝ) / ((n : ℝ) + 1) = 2 * (1 / (2 * (n : ℝ) + 2)) := by
    field_simp
  have e : (harmonic n : ℝ) - log ((n : ℝ) + 1 / 2)
      - ((harmonic n : ℝ) + 1 / ((n : ℝ) + 1) - log ((n : ℝ) + 1 + 1 / 2))
      = (log ((n : ℝ) + 1 + 1 / 2) - log ((n : ℝ) + 1 / 2)) - 1 / ((n : ℝ) + 1) := by ring
  rw [e, hlog, h2]
  simp only [Nat.cast_zero, mul_zero, zero_add, div_one]
  ring

/-- Lower DeTemple bound. -/
theorem gamSeq_sub_le_gamma {n : ℕ} (hn : 1 ≤ n) :
    gamSeq n - 1 / (24 * (n : ℝ) ^ 2) ≤ eulerMascheroniConstant := by
  -- `u m = a_m - 1/(24 m^2)` is increasing for `m ≥ 1`
  have step : ∀ m : ℕ, 1 ≤ m →
      gamSeq m - 1 / (24 * (m : ℝ) ^ 2) ≤ gamSeq (m + 1) - 1 / (24 * ((m + 1 : ℕ) : ℝ) ^ 2) := by
    intro m hm
    have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have hd := gamSeq_sub_succ m
    set x : ℝ := 1 / (2 * (m : ℝ) + 2) with hx
    have hx0 : 0 < x := by rw [hx]; positivity
    have hx1 : x < 1 := by rw [hx, div_lt_one (by positivity)]; linarith
    have hw0 : (0 : ℝ) ≤ x ^ 2 := by positivity
    have hw1 : x ^ 2 < 1 := by nlinarith
    have hT := atanhTail_one_le hw0 hw1
    have hδ : gamSeq m - gamSeq (m + 1) ≤ 2 * x ^ 3 * (1 / (3 * (1 - x ^ 2))) := by
      rw [hd]; gcongr
    have key : 2 * x ^ 3 * (1 / (3 * (1 - x ^ 2)))
        ≤ 1 / (24 * (m : ℝ) ^ 2) - 1 / (24 * ((m : ℝ) + 1) ^ 2) := by
      have hx2 : 1 - x ^ 2 = (2 * (m : ℝ) + 1) * (2 * (m : ℝ) + 3) / (2 * (m : ℝ) + 2) ^ 2 := by
        rw [hx]; field_simp; ring
      have e1 : 2 * x ^ 3 * (1 / (3 * (1 - x ^ 2)))
          = 1 / (3 * ((m : ℝ) + 1) * (2 * (m : ℝ) + 1) * (2 * (m : ℝ) + 3)) := by
        rw [hx2, hx]; field_simp
      have e2 : 1 / (24 * (m : ℝ) ^ 2) - 1 / (24 * ((m : ℝ) + 1) ^ 2)
          = (2 * (m : ℝ) + 1) / (24 * (m : ℝ) ^ 2 * ((m : ℝ) + 1) ^ 2) := by
        field_simp; ring
      rw [e1, e2, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [pow_pos (by linarith : (0 : ℝ) < m) 3, pow_pos (by linarith : (0 : ℝ) < m) 2,
        pow_pos (by linarith : (0 : ℝ) < m) 4]
    push_cast
    linarith
  have mono : ∀ m : ℕ, n ≤ m →
      gamSeq n - 1 / (24 * (n : ℝ) ^ 2) ≤ gamSeq m - 1 / (24 * (m : ℝ) ^ 2) := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base => exact le_rfl
    | succ m hm ih => exact ih.trans (step m (hn.trans hm))
  refine ge_of_tendsto gamSeq_tendsto ?_
  filter_upwards [eventually_ge_atTop n] with m hm
  have : (0 : ℝ) ≤ 1 / (24 * (m : ℝ) ^ 2) := by positivity
  linarith [mono m hm]

/-- Upper DeTemple bound. -/
theorem gamma_le_gamSeq_sub (n : ℕ) :
    eulerMascheroniConstant ≤ gamSeq n - 1 / (24 * ((n : ℝ) + 1) ^ 2) := by
  -- `v m = a_m - 1/(24 (m+1)^2)` is decreasing
  have step : ∀ m : ℕ, gamSeq (m + 1) - 1 / (24 * (((m + 1 : ℕ) : ℝ) + 1) ^ 2)
      ≤ gamSeq m - 1 / (24 * ((m : ℝ) + 1) ^ 2) := by
    intro m
    have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    have hd := gamSeq_sub_succ m
    set x : ℝ := 1 / (2 * (m : ℝ) + 2) with hx
    have hx0 : 0 < x := by rw [hx]; positivity
    have hx1 : x < 1 := by rw [hx, div_lt_one (by positivity)]; linarith
    have hw0 : (0 : ℝ) ≤ x ^ 2 := by positivity
    have hw1 : x ^ 2 < 1 := by nlinarith
    have hT := atanhTail_one_ge hw0 hw1
    have hδ : 2 * x ^ 3 * (1 / 3) ≤ gamSeq m - gamSeq (m + 1) := by
      rw [hd]; gcongr
    have key : 1 / (24 * ((m : ℝ) + 1) ^ 2) - 1 / (24 * ((m : ℝ) + 2) ^ 2)
        ≤ 2 * x ^ 3 * (1 / 3) := by
      have e1 : 2 * x ^ 3 * (1 / 3) = 1 / (12 * ((m : ℝ) + 1) ^ 3) := by
        rw [hx]; field_simp; ring
      have e2 : 1 / (24 * ((m : ℝ) + 1) ^ 2) - 1 / (24 * ((m : ℝ) + 2) ^ 2)
          = (2 * (m : ℝ) + 3) / (24 * ((m : ℝ) + 1) ^ 2 * ((m : ℝ) + 2) ^ 2) := by
        field_simp; ring
      rw [e1, e2, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [pow_nonneg hm0 2, pow_nonneg hm0 3, pow_nonneg hm0 4]
    have e3 : (((m + 1 : ℕ) : ℝ) + 1) = (m : ℝ) + 2 := by push_cast; ring
    rw [e3]
    linarith
  have anti : ∀ m : ℕ, n ≤ m →
      gamSeq m - 1 / (24 * ((m : ℝ) + 1) ^ 2) ≤ gamSeq n - 1 / (24 * ((n : ℝ) + 1) ^ 2) := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base => exact le_rfl
    | succ m hm ih => exact (step m).trans ih
  have hlim : Tendsto (fun m : ℕ => gamSeq m - 1 / ((m : ℝ) + 1)) atTop
      (𝓝 (eulerMascheroniConstant - 0)) :=
    gamSeq_tendsto.sub tendsto_one_div_add_atTop_nhds_zero_nat
  rw [sub_zero] at hlim
  refine le_of_tendsto hlim ?_
  filter_upwards [eventually_ge_atTop n] with m hm
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have : 1 / (24 * ((m : ℝ) + 1) ^ 2) ≤ 1 / ((m : ℝ) + 1) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  linarith [anti m hm]

end Exp7.Num
