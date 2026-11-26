import Exp7Lean.Main

/-!
Exponent 7: the range `q ≥ 10^32`, and the classification.

`above_bound` is proved here from Mathlib's bounds on `e` and `log 2`; nothing about it is assumed.
The published results used for Corollary B enter as the fields of `Published`.
-/

namespace Exp7

open Real

lemma exp73_lt : exp 73 < 10 ^ 32 := by
  have h := Real.exp_one_lt_d9
  have h0 : 0 ≤ exp 1 := (exp_pos 1).le
  have e : exp 73 = exp 1 ^ 73 := by rw [← Real.exp_nat_mul]; norm_num
  rw [e]
  calc exp 1 ^ 73 < (2.7182818286 : ℝ) ^ 73 := by gcongr
    _ < 10 ^ 32 := by norm_num

lemma exp5_gt : (143493 / 1000 : ℝ) < exp 5 := by
  have h := Real.exp_one_gt_d9
  have e : exp 5 = exp 1 ^ 5 := by rw [← Real.exp_nat_mul]; norm_num
  rw [e]
  calc (143493 / 1000 : ℝ) < 2.7182818283 ^ 5 := by norm_num
    _ < exp 1 ^ 5 := by gcongr

lemma log4_lt : log 4 < 13863 / 10000 := by
  have h := Real.log_two_lt_d9
  have e : log 4 = 2 * log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  rw [e]; linarith

/-- For `D ≥ 10^32`, `4 (1.881 log D + 6.18)^14 < D`. -/
theorem above_bound {D : ℝ} (hD : 10 ^ 32 ≤ D) :
    4 * (1881 / 1000 * log D + 309 / 50) ^ 14 < D := by
  have hDpos : 0 < D := lt_of_lt_of_le (by norm_num) hD
  have ht73 : 73 < log D := by
    rw [Real.lt_log_iff_exp_lt hDpos]; exact lt_of_lt_of_le exp73_lt hD
  set t := log D with ht
  set s := 1881 / 1000 * t + 309 / 50 with hs
  have hs0 : (0 : ℝ) < 143493 / 1000 := by norm_num
  have hsge : 143493 / 1000 ≤ s := by rw [hs]; linarith
  have hspos : 0 < s := by linarith
  have hlog : log s - log (143493 / 1000) ≤ s / (143493 / 1000) - 1 := by
    rw [← Real.log_div hspos.ne' hs0.ne']
    exact Real.log_le_sub_one_of_pos (div_pos hspos hs0)
  have hlog0 : log (143493 / 1000) < 5 := by
    rw [Real.log_lt_iff_lt_exp hs0]; exact exp5_gt
  have e : s / (143493 / 1000) - 1 = 1881 / 143493 * (t - 73) := by rw [hs]; field_simp; ring
  have h1 : 14 * (s / (143493 / 1000) - 1) ≤ t - 73 := by rw [e]; nlinarith
  have key : log 4 + 14 * log s < t := by linarith [log4_lt]
  have hpos : 0 < 4 * s ^ 14 := by positivity
  rw [← Real.log_lt_log_iff hpos hDpos, Real.log_mul (by norm_num) (by positivity),
    Real.log_pow]
  push_cast
  linarith

/-- The published results used for Corollary B. -/
structure Published (IsExp7 : ℕ → Prop) : Prop where
  /-- Elsenhans–Klüners–Nicolae, Theorem 3 (from Bach–Sorenson, assuming ERH): for `|D| > e^25`
  some prime `p ≤ (1.881 log|D| + 6.18)^2` splits. -/
  ekn3 : ∀ q : ℕ, q.Prime → q % 4 = 3 → exp 25 < (q : ℝ) →
    ∃ p : ℕ, p.Prime ∧ Splits q p ∧ (p : ℝ) ≤ (1881 / 1000 * log q + 309 / 50) ^ 2
  /-- Elsenhans–Klüners–Nicolae, Theorem 1 and Table 1: below `3.1·10^20` the primes `q ≡ 3 (mod 4)`
  with class group of exponent 7 are exactly the 33 listed in `known`. -/
  ekn1 : ∀ q : ℕ, q.Prime → q % 4 = 3 → q ≤ QLOW → (IsExp7 q ↔ q ∈ known)

/-- No `q ≥ 10^32` has exponent 7. -/
theorem not_exp7_above {IsExp7 : ℕ → Prop} (H : Inputs IsExp7) (P : Published IsExp7) {q : ℕ}
    (hq : q.Prime) (h4 : q % 4 = 3) (htop : QTOP ≤ q) : ¬ IsExp7 q := by
  intro hE
  have hqR : (10 : ℝ) ^ 32 ≤ q := by exact_mod_cast htop
  have h25 : exp 25 < (q : ℝ) := by
    have : exp 25 ≤ exp 73 := Real.exp_le_exp.mpr (by norm_num)
    linarith [exp73_lt]
  obtain ⟨p, hp, hs, hpb⟩ := P.ekn3 q hq h4 h25
  set s := 1881 / 1000 * log (q : ℝ) + 309 / 50 with hsdef
  have hbound : 4 * s ^ 14 < (q : ℝ) := above_bound hqR
  have hs1 : 1 ≤ s := by
    have : 0 ≤ log (q : ℝ) := Real.log_nonneg (by linarith)
    linarith
  have hpR : (p : ℝ) ^ 7 ≤ s ^ 14 := by
    calc (p : ℝ) ^ 7 ≤ (s ^ 2) ^ 7 := by gcongr
      _ = s ^ 14 := by ring
  have hpq : p ≠ q := by
    intro h
    have : (q : ℝ) ≤ s ^ 2 := by rw [← h]; exact hpb
    have : s ^ 2 ≤ s ^ 14 := pow_le_pow_right₀ hs1 (by norm_num)
    linarith
  have hle : q ≤ 4 * p ^ 7 := le_of_splits H hq h4 hE hp hpq hs
  have hleR : (q : ℝ) ≤ 4 * (p : ℝ) ^ 7 := by exact_mod_cast hle
  linarith

lemma known_lt : ∀ q ∈ known, q < QLOW := by decide

/-- **Corollary B** (field version, from the inputs and the published results): for a prime
`q ≡ 3 (mod 4)`, the class group of `ℚ(√-q)` has exponent 7 if and only if `q` is one of the 33
listed primes. -/
theorem classification {IsExp7 : ℕ → Prop} (H : Inputs IsExp7) (P : Published IsExp7) {q : ℕ}
    (hq : q.Prime) (h4 : q % 4 = 3) : IsExp7 q ↔ q ∈ known := by
  by_cases hlow : q ≤ QLOW
  · exact P.ekn1 q hq h4 hlow
  · have hk : q ∉ known := fun h => by have := known_lt q h; omega
    simp only [hk, iff_false]
    by_cases htop : q ≤ QTOP
    · exact theoremA H hq h4 (by omega) htop
    · exact not_exp7_above H P hq h4 (by omega)

end Exp7
