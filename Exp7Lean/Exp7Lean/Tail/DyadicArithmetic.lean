import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Nat.Log

/-!
Kernel-checkable algebra for the Chebyshev tail, using the coarse `J <= 4`
profile. Analytic Abel-summation inequalities are deliberately not asserted
here. The positive parameters r,u,v correspond to 2^(1/2),2^(1/4),2^(1/6).
-/

namespace Exp7.ChebyshevTailArithmetic

noncomputable def error (c u v : ℝ) (n : ℕ) : ℝ :=
  (3 * c * n + 8) * u ^ n +
  48 * v ^ n +
  (11 / 54) * c ^ 2 * (n : ℝ) ^ 3 +
  (55 / 6 + c) * c * (n : ℝ) ^ 2 +
  (11 * c + 12) * n +
  n * (2 * c * n + 8) / u ^ n

lemma linear_succ_le {a b x : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hx : 19 ≤ x) :
    a * (x + 1) + b ≤ (20 / 19) * (a * x + b) := by
  have : 0 ≤ a * (x - 19) := mul_nonneg ha (by linarith)
  nlinarith

lemma self_succ_le {x : ℝ} (hx : 19 ≤ x) : x + 1 ≤ (20 / 19) * x := by
  linarith

lemma self_pow_succ_le {x : ℝ} (hx : 19 ≤ x) (k : ℕ)
    (hk : (20 / 19 : ℝ) ^ k ≤ 7 / 5) :
    (x + 1) ^ k ≤ (7 / 5) * x ^ k := by
  have hx0 : 0 ≤ x := by linarith
  calc
    (x + 1) ^ k ≤ ((20 / 19) * x) ^ k := by
      gcongr
      exact self_succ_le hx
    _ = (20 / 19) ^ k * x ^ k := by rw [mul_pow]
    _ ≤ (7 / 5) * x ^ k := mul_le_mul_of_nonneg_right hk (pow_nonneg hx0 k)

theorem error_growth {c u v : ℝ} (hc : 0 ≤ c)
    (hu1 : 1 ≤ u) (hu2 : u ≤ 6 / 5) (hv0 : 0 ≤ v) (hv2 : v ≤ 6 / 5)
    (n : ℕ) (hn : 19 ≤ n) :
    error c u v (n + 1) ≤ (7 / 5) * error c u v n := by
  have hnR : (19 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hu0 : 0 < u := by linarith
  have hun : 0 < u ^ n := pow_pos hu0 n
  have hvn : 0 ≤ v ^ n := pow_nonneg hv0 n
  have hlin := linear_succ_le (a := 3 * c) (b := 8) (by positivity) (by norm_num) hnR
  have hlin2 := linear_succ_le (a := 2 * c) (b := 8) (by positivity) (by norm_num) hnR
  have hstep := self_succ_le hnR
  have hp2 := self_pow_succ_le hnR 2 (by norm_num)
  have hp3 := self_pow_succ_le hnR 3 (by norm_num)
  have h1 : (3 * c * ((n : ℝ) + 1) + 8) * u ^ (n + 1) ≤
      (7 / 5) * ((3 * c * n + 8) * u ^ n) := by
    rw [pow_succ]
    calc
      (3 * c * ((n : ℝ) + 1) + 8) * (u ^ n * u) ≤
          ((20 / 19) * (3 * c * n + 8)) * (u ^ n * (6 / 5)) := by gcongr
      _ ≤ (7 / 5) * ((3 * c * n + 8) * u ^ n) := by
        have : 0 ≤ (3 * c * n + 8) * u ^ n := by positivity
        nlinarith only [this]
  have h2 : 48 * v ^ (n + 1) ≤ (7 / 5) * (48 * v ^ n) := by
    rw [pow_succ]
    have := mul_nonneg hvn (sub_nonneg.mpr hv2)
    nlinarith only [hvn, this]
  have h3 : (11 / 54 : ℝ) * c ^ 2 * ((n : ℝ) + 1) ^ 3 ≤
      (7 / 5) * ((11 / 54) * c ^ 2 * (n : ℝ) ^ 3) := by
    have := mul_le_mul_of_nonneg_left hp3 (by positivity : 0 ≤ (11 / 54 : ℝ) * c ^ 2)
    nlinarith only [this]
  have h4 : (55 / 6 + c) * c * ((n : ℝ) + 1) ^ 2 ≤
      (7 / 5) * ((55 / 6 + c) * c * (n : ℝ) ^ 2) := by
    have := mul_le_mul_of_nonneg_left hp2 (by positivity : 0 ≤ (55 / 6 + c) * c)
    nlinarith only [this]
  have h5 : (11 * c + 12) * ((n : ℝ) + 1) ≤
      (7 / 5) * ((11 * c + 12) * n) := by
    have h := mul_le_mul_of_nonneg_left hstep (by positivity : 0 ≤ 11 * c + 12)
    have : 0 ≤ (11 * c + 12) * n := by positivity
    nlinarith only [h, this]
  have hden : u ^ n ≤ u ^ (n + 1) := by
    rw [pow_succ]
    nlinarith only [mul_nonneg hun.le (sub_nonneg.mpr hu1)]
  have h6 : ((n : ℝ) + 1) * (2 * c * ((n : ℝ) + 1) + 8) / u ^ (n + 1) ≤
      (7 / 5) * (n * (2 * c * n + 8) / u ^ n) := by
    calc
      ((n : ℝ) + 1) * (2 * c * ((n : ℝ) + 1) + 8) / u ^ (n + 1) ≤
          ((20 / 19) * n) * ((20 / 19) * (2 * c * n + 8)) / u ^ n := by
        gcongr
      _ ≤ (7 / 5) * (n * (2 * c * n + 8) / u ^ n) := by
        calc
          ((20 / 19) * n) * ((20 / 19) * (2 * c * n + 8)) / u ^ n =
              (20 / 19 : ℝ) ^ 2 * (n * (2 * c * n + 8) / u ^ n) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
  unfold error
  push_cast
  nlinarith only [h1, h2, h3, h4, h5, h6]

theorem base_case {c r u v : ℝ}
    (hc0 : 0 ≤ c) (hc : c ≤ 7 / 10)
    (hu : 16 ≤ u ^ 19) (hu' : u ^ 19 ≤ 27)
    (_hv0 : 0 ≤ v ^ 19) (hv : v ^ 19 ≤ 9)
    (hr : (512 : ℝ) * (7 / 5) ≤ r ^ 19) :
    error c u v 19 < 8 * r ^ 19 := by
  have hu0 : 0 < u ^ 19 := by linarith
  unfold error
  simp only [Nat.cast_ofNat]
  calc
    (3 * c * 19 + 8) * u ^ 19 + 48 * v ^ 19 +
        (11 / 54) * c ^ 2 * (19 : ℝ) ^ 3 +
        (55 / 6 + c) * c * (19 : ℝ) ^ 2 +
        (11 * c + 12) * 19 + 19 * (2 * c * 19 + 8) / u ^ 19 ≤
      (3 * (7 / 10) * 19 + 8) * 27 + 48 * 9 +
        (11 / 54) * (7 / 10) ^ 2 * (19 : ℝ) ^ 3 +
        (55 / 6 + (7 / 10)) * (7 / 10) * (19 : ℝ) ^ 2 +
        (11 * (7 / 10) + 12) * 19 + 19 * (2 * (7 / 10) * 19 + 8) / 16 := by gcongr
    _ < 8 * ((512 : ℝ) * (7 / 5)) := by norm_num
    _ ≤ 8 * r ^ 19 := by gcongr

theorem comparison_induction {A B : ℕ → ℝ} {k : ℝ} (hk : 0 < k)
    (hbase : B 19 < A 19)
    (hA : ∀ n, 19 ≤ n → k * A n ≤ A (n + 1))
    (hB : ∀ n, 19 ≤ n → B (n + 1) ≤ k * B n) :
    ∀ n, 19 ≤ n → B n < A n := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => exact hbase
  | succ n hn ih =>
    exact lt_of_le_of_lt (hB n hn)
      (lt_of_lt_of_le (mul_lt_mul_of_pos_left ih hk) (hA n hn))

theorem dyadic_comparison {c r u v : ℝ}
    (hc0 : 0 ≤ c) (hc : c ≤ 7 / 10)
    (hr : 7 / 5 ≤ r)
    (hu1 : 1 ≤ u) (hu2 : u ≤ 6 / 5)
    (hv0 : 0 ≤ v) (hv2 : v ≤ 6 / 5)
    (hu19 : 16 ≤ u ^ 19) (hu19' : u ^ 19 ≤ 27)
    (hv19 : v ^ 19 ≤ 9)
    (hr19 : (512 : ℝ) * (7 / 5) ≤ r ^ 19) :
    ∀ n, 19 ≤ n → error c u v n < 8 * r ^ n := by
  apply comparison_induction (k := (7 / 5 : ℝ)) (by norm_num)
  · exact base_case hc0 hc hu19 hu19' (pow_nonneg hv0 19) hv19 hr19
  · intro n _
    have hr0 : 0 ≤ r := by linarith
    rw [pow_succ]
    nlinarith only [mul_nonneg (pow_nonneg hr0 n) (sub_nonneg.mpr hr)]
  · exact error_growth hc0 hu1 hu2 hv0 hv2

lemma le_of_pow_le {x y : ℝ} (_hx : 0 ≤ x) (hy : 0 ≤ y)
    {k : ℕ} (hk : k ≠ 0) (h : x ^ k ≤ y ^ k) : x ≤ y := by
  by_contra hxy
  have hxy' : y < x := lt_of_not_ge hxy
  exact (not_lt_of_ge h) (pow_lt_pow_left₀ hxy' hy hk)

theorem canonical_comparison (n : ℕ) (hn : 19 ≤ n) :
    error (Real.log 2) ((2 : ℝ) ^ (1 / 4 : ℝ)) ((2 : ℝ) ^ (1 / 6 : ℝ)) n <
      8 * ((2 : ℝ) ^ (1 / 2 : ℝ)) ^ n := by
  let r : ℝ := (2 : ℝ) ^ (1 / 2 : ℝ)
  let u : ℝ := (2 : ℝ) ^ (1 / 4 : ℝ)
  let v : ℝ := (2 : ℝ) ^ (1 / 6 : ℝ)
  have hr0 : 0 ≤ r := Real.rpow_nonneg (by norm_num) _
  have hu0 : 0 ≤ u := Real.rpow_nonneg (by norm_num) _
  have hv0 : 0 ≤ v := Real.rpow_nonneg (by norm_num) _
  have hr2 : r ^ 2 = 2 := by
    dsimp [r]
    convert Real.rpow_inv_natCast_pow (x := (2 : ℝ)) (n := 2) (by norm_num) (by norm_num) using 1; norm_num
  have hu4 : u ^ 4 = 2 := by
    dsimp [u]
    convert Real.rpow_inv_natCast_pow (x := (2 : ℝ)) (n := 4) (by norm_num) (by norm_num) using 1; norm_num
  have hv6 : v ^ 6 = 2 := by
    dsimp [v]
    convert Real.rpow_inv_natCast_pow (x := (2 : ℝ)) (n := 6) (by norm_num) (by norm_num) using 1; norm_num
  have hr : 7 / 5 ≤ r := le_of_pow_le (by norm_num) hr0 (k := 2) (by norm_num) (by rw [hr2]; norm_num)
  have hu1 : 1 ≤ u := le_of_pow_le (by norm_num) hu0 (k := 4) (by norm_num) (by rw [hu4]; norm_num)
  have hu2 : u ≤ 6 / 5 := le_of_pow_le hu0 (by norm_num) (k := 4) (by norm_num) (by rw [hu4]; norm_num)
  have hv2 : v ≤ 6 / 5 := le_of_pow_le hv0 (by norm_num) (k := 6) (by norm_num) (by rw [hv6]; norm_num)
  have hu76 : (u ^ 19) ^ 4 = (2 : ℝ) ^ 19 := by
    calc (u ^ 19) ^ 4 = (u ^ 4) ^ 19 := by ring
         _ = _ := by rw [hu4]
  have hv114 : (v ^ 19) ^ 6 = (2 : ℝ) ^ 19 := by
    calc (v ^ 19) ^ 6 = (v ^ 6) ^ 19 := by ring
         _ = _ := by rw [hv6]
  have hu19 : 16 ≤ u ^ 19 := le_of_pow_le (by norm_num) (pow_nonneg hu0 19)
    (k := 4) (by norm_num) (by rw [hu76]; norm_num)
  have hu19' : u ^ 19 ≤ 27 := le_of_pow_le (pow_nonneg hu0 19) (by norm_num)
    (k := 4) (by norm_num) (by rw [hu76]; norm_num)
  have hv19 : v ^ 19 ≤ 9 := le_of_pow_le (pow_nonneg hv0 19) (by norm_num)
    (k := 6) (by norm_num) (by rw [hv114]; norm_num)
  have hr19eq : r ^ 19 = 512 * r := by
    calc r ^ 19 = (r ^ 2) ^ 9 * r := by ring
         _ = _ := by rw [hr2]; norm_num
  have hr19 : (512 : ℝ) * (7 / 5) ≤ r ^ 19 := by rw [hr19eq]; linarith
  have hc0 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hc : Real.log 2 ≤ 7 / 10 := by linarith [Real.log_two_lt_d9]
  exact dyadic_comparison hc0 hc hr hu1 hu2 hv0 hv2 hu19 hu19' hv19 hr19 n hn

noncomputable def haarLowerBound (n : ℕ) : ℝ :=
  let c := Real.log 2
  let r := (2 : ℝ) ^ (1 / 2 : ℝ)
  let u := (2 : ℝ) ^ (1 / 4 : ℝ)
  let v := (2 : ℝ) ^ (1 / 6 : ℝ)
  8 * r ^ n / n - (3 * c + 8 / n) * u ^ n - 48 * v ^ n / n -
    (11 / 54) * c ^ 2 * (n : ℝ) ^ 2 - (13 / 6 + c) * c * n -
    (2 * c + 8) - (2 * c * n + 8) / u ^ n

theorem haarLowerBound_gt (n : ℕ) (hn : 19 ≤ n) :
    (7 * (n : ℝ) + 9) * Real.log 2 + 4 < haarLowerBound n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 19) hn)
  have hu : 0 < ((2 : ℝ) ^ (1 / 4 : ℝ)) ^ n :=
    pow_pos (Real.rpow_pos_of_pos (by norm_num) _) n
  have h := sub_pos.mpr (canonical_comparison n hn)
  have heq : 8 * ((2 : ℝ) ^ (1 / 2 : ℝ)) ^ n -
      error (Real.log 2) ((2 : ℝ) ^ (1 / 4 : ℝ)) ((2 : ℝ) ^ (1 / 6 : ℝ)) n =
      n * (haarLowerBound n - ((7 * (n : ℝ) + 9) * Real.log 2 + 4)) := by
    unfold error haarLowerBound
    dsimp only
    field_simp
    ring
  rw [heq] at h
  exact sub_pos.mp ((mul_pos_iff_of_pos_left hn0).mp h)

theorem exists_dyadic_index {q : ℕ} (hq : 2 ^ 135 < q) :
    ∃ n : ℕ, 19 ≤ n ∧ 4 * (2 ^ n) ^ 7 < q ∧ q ≤ 2 ^ (7 * n + 9) := by
  have ht : (1 : ℕ) < 2 ^ 135 := by norm_num
  have hq0 : q - 1 ≠ 0 := by omega
  have hlarge : 2 ^ 135 ≤ q - 1 := by omega
  let k := Nat.log 2 (q - 1)
  have hk : 135 ≤ k := Nat.le_log_of_pow_le (by norm_num) hlarge
  have hlo : 2 ^ k ≤ q - 1 := Nat.pow_log_le_self 2 hq0
  have hhi : q - 1 < 2 ^ (k + 1) := Nat.lt_pow_succ_log_self (by norm_num) (q - 1)
  let n := (k - 2) / 7
  have hn : 19 ≤ n := by dsimp [n]; omega
  have hnk : 7 * n + 2 ≤ k := by dsimp [n]; omega
  have hkn : k + 1 ≤ 7 * n + 9 := by dsimp [n]; omega
  have heq : 4 * (2 ^ n) ^ 7 = 2 ^ (7 * n + 2) := by
    rw [pow_add, Nat.mul_comm 7 n, pow_mul]
    norm_num
    ring
  refine ⟨n, hn, ?_, ?_⟩
  · rw [heq]
    have hp := Nat.pow_le_pow_right (by norm_num : 0 < 2) hnk
    omega
  · have hp := Nat.pow_le_pow_right (by norm_num : 0 < 2) hkn
    omega

theorem exists_dyadic_index_of_mod_four {q : ℕ}
    (hq : 2 ^ 135 ≤ q) (h4 : q % 4 = 3) :
    ∃ n : ℕ, 19 ≤ n ∧ 4 * (2 ^ n) ^ 7 < q ∧ q ≤ 2 ^ (7 * n + 9) := by
  apply exists_dyadic_index
  have hne : q ≠ 2 ^ 135 := by
    intro h
    rw [h] at h4
    norm_num at h4
  omega

#print axioms haarLowerBound_gt
#print axioms exists_dyadic_index_of_mod_four

end Exp7.ChebyshevTailArithmetic
