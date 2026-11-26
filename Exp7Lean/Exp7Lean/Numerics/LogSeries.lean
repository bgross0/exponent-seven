import Mathlib

/-!
# Real-analysis input for the verified logarithm

For `0 ≤ w < 1` and `k : ℕ` put

    atanhTail w k = ∑_{j ≥ 0} w^j / (2 (k + j) + 1).

Then `log a - log b = 2 z · atanhTail (z^2) 0` with `z = (a - b)/(a + b)` (`0 < b ≤ a`), and the
tails satisfy the Horner recursion `atanhTail w k = 1/(2k+1) + w · atanhTail w (k+1)` together
with the two-sided bound `0 ≤ atanhTail w k ≤ 1 / ((2k+1)(1-w))`.  These three facts are all
the fixed-point evaluator in `FixedLog.lean` needs.
-/

namespace Exp7.Num

open Real

/-- `∑_{j ≥ 0} w^j / (2 (k + j) + 1)`. -/
noncomputable def atanhTail (w : ℝ) (k : ℕ) : ℝ := ∑' j : ℕ, w ^ j / (2 * ((k : ℝ) + j) + 1)

theorem atanhTail_summable {w : ℝ} (h0 : 0 ≤ w) (h1 : w < 1) (k : ℕ) :
    Summable (fun j : ℕ => w ^ j / (2 * ((k : ℝ) + j) + 1)) := by
  refine Summable.of_nonneg_of_le (fun j => by positivity) (fun j => ?_)
    (summable_geometric_of_lt_one h0 h1)
  apply div_le_self (by positivity)
  have : (0 : ℝ) ≤ (k : ℝ) + j := by positivity
  linarith

theorem atanhTail_nonneg {w : ℝ} (h0 : 0 ≤ w) (k : ℕ) : 0 ≤ atanhTail w k :=
  tsum_nonneg fun j => by positivity

/-- Horner recursion for the tails. -/
theorem atanhTail_succ {w : ℝ} (h0 : 0 ≤ w) (h1 : w < 1) (k : ℕ) :
    atanhTail w k = 1 / (2 * (k : ℝ) + 1) + w * atanhTail w (k + 1) := by
  unfold atanhTail
  rw [(atanhTail_summable h0 h1 k).tsum_eq_zero_add, ← tsum_mul_left]
  congr 1
  · simp
  · refine tsum_congr fun j => ?_
    push_cast
    rw [pow_succ]
    have : (2 * ((k : ℝ) + 1 + j) + 1) = (2 * ((k : ℝ) + (j + 1)) + 1) := by ring
    rw [this]
    ring

/-- Geometric majorant of the tails. -/
theorem atanhTail_le {w : ℝ} (h0 : 0 ≤ w) (h1 : w < 1) (k : ℕ) :
    atanhTail w k ≤ 1 / ((2 * (k : ℝ) + 1) * (1 - w)) := by
  have hk : (0 : ℝ) < 2 * (k : ℝ) + 1 := by positivity
  have hs : Summable (fun j : ℕ => w ^ j / (2 * (k : ℝ) + 1)) :=
    (summable_geometric_of_lt_one h0 h1).div_const _
  have h : atanhTail w k ≤ ∑' j : ℕ, w ^ j / (2 * (k : ℝ) + 1) := by
    refine (atanhTail_summable h0 h1 k).tsum_le_tsum (fun j => ?_) hs
    apply div_le_div_of_nonneg_left (by positivity) hk
    have : (0 : ℝ) ≤ (j : ℝ) := by positivity
    linarith
  rw [tsum_div_const, tsum_geometric_of_lt_one h0 h1] at h
  calc atanhTail w k ≤ (1 - w)⁻¹ / (2 * (k : ℝ) + 1) := h
    _ = 1 / ((2 * (k : ℝ) + 1) * (1 - w)) := by
        have : (0 : ℝ) < 1 - w := by linarith
        field_simp

/-- `log(1+z) - log(1-z) = 2 z ∑ z^{2j}/(2j+1)`. -/
theorem log_sub_log_eq_atanhTail {z : ℝ} (h0 : 0 ≤ z) (h1 : z < 1) :
    log (1 + z) - log (1 - z) = 2 * z * atanhTail (z ^ 2) 0 := by
  have h := (hasSum_log_sub_log_of_abs_lt_one (x := z) (by rw [abs_of_nonneg h0]; exact h1)).tsum_eq
  rw [← h]
  unfold atanhTail
  rw [← tsum_mul_left]
  refine tsum_congr fun j => ?_
  simp only [Nat.cast_zero, zero_add]
  rw [pow_succ, pow_mul]
  ring

/-- The series for `log a - log b`, `0 < b ≤ a`. -/
theorem log_sub_log_eq {a b : ℝ} (hb : 0 < b) (hab : b ≤ a) :
    log a - log b = 2 * ((a - b) / (a + b)) * atanhTail (((a - b) / (a + b)) ^ 2) 0 := by
  have ha : 0 < a := lt_of_lt_of_le hb hab
  have hs : 0 < a + b := by linarith
  have hz0 : 0 ≤ (a - b) / (a + b) := div_nonneg (by linarith) hs.le
  have hz1 : (a - b) / (a + b) < 1 := by rw [div_lt_one hs]; linarith
  rw [← log_sub_log_eq_atanhTail hz0 hz1]
  have e1 : 1 + (a - b) / (a + b) = 2 * a / (a + b) := by field_simp; ring
  have e2 : 1 - (a - b) / (a + b) = 2 * b / (a + b) := by field_simp; ring
  rw [e1, e2, log_div (by positivity) hs.ne', log_div (by positivity) hs.ne',
    log_mul (by norm_num) ha.ne', log_mul (by norm_num) hb.ne']
  ring

/-- `0 ≤ z^2 < 1` for `z = (a-b)/(a+b)`. -/
theorem ratio_sq_bounds {a b : ℝ} (hb : 0 < b) (hab : b ≤ a) :
    0 ≤ ((a - b) / (a + b)) ^ 2 ∧ ((a - b) / (a + b)) ^ 2 < 1 := by
  have hs : 0 < a + b := by linarith
  have hz0 : 0 ≤ (a - b) / (a + b) := div_nonneg (by linarith) hs.le
  have hz1 : (a - b) / (a + b) < 1 := by rw [div_lt_one hs]; linarith
  exact ⟨by positivity, by nlinarith⟩

end Exp7.Num
