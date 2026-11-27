import Exp7Lean.Tail.EvenLoss
import Exp7Lean.Tail.OddLoss
import Exp7Lean.Tail.PositivePrimes
import Exp7Lean.Tail.DyadicArithmetic

/-! # The three weighted sums clear the dyadic threshold -/

namespace Exp7.ChebyshevTail

open Finset
open scoped ArithmeticFunction.vonMangoldt

/-- The contribution of primes above √X less the two upper bounds on losses,
written as finite sums at their actual cutoffs. -/
noncomputable def weightedPrimeBalance (X : ℝ) :=
  let A := Real.sqrt X
  let Y := X ^ (1 / 3 : ℝ)
  2 * (∑ p ∈ Ioc ⌊A⌋₊ ⌊X⌋₊ with p.Prime, logWeight (Real.log X) p * Real.log p) -
    2 * (∑ n ∈ Ioc 0 ⌊Y⌋₊, logWeight (Real.log Y) n * Λ n) -
    ∑ d ∈ Ioc 0 ⌊A⌋₊, Λ d / d

private theorem dyadic_rpow (n : ℕ) (s : ℝ) :
    ((2 : ℝ) ^ n) ^ s = ((2 : ℝ) ^ s) ^ n := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), mul_comm,
    Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast]

/-- The strict threshold holds for the finite prime sums at every dyadic
index from 19 onward. -/
theorem weightedPrimeBalance_gt (n : ℕ) (hn : 19 ≤ n) :
    (7 * (n : ℝ) + 9) * Real.log 2 + 4 < weightedPrimeBalance (2 ^ n) := by
  let X : ℝ := 2 ^ n
  let c := Real.log 2
  let A := Real.sqrt X
  let U := Real.sqrt A
  let Y := X ^ (1 / 3 : ℝ)
  have hX : 16 ≤ X := by
    calc
      (16 : ℝ) = 2 ^ 4 := by norm_num
      _ ≤ X := pow_le_pow_right₀ (by norm_num) (by omega : 4 ≤ n)
  have hXpos : 0 < X := by linarith
  have hA : 4 ≤ A := (Real.le_sqrt (by norm_num) hXpos.le).mpr (by linarith)
  have hU : 0 < U := Real.sqrt_pos.mpr (by linarith)
  have hY : 1 < Y := Real.one_lt_rpow (by linarith) (by norm_num)
  have hc : 0 < c := Real.log_pos (by norm_num)
  have hn' : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hL : Real.log X = n * c := Real.log_pow _ _
  have hlogA : Real.log A = n * c / 2 := (Real.log_sqrt hXpos.le).trans (by rw [hL])
  have hlogY : Real.log Y = n * c / 3 := by rw [Real.log_rpow hXpos, hL]; ring
  have hfour : Real.log 4 = 2 * c := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    change _ = 2 * Real.log 2
    ring
  have hAs : A = ((2 : ℝ) ^ (1 / 2 : ℝ)) ^ n :=
    (Real.sqrt_eq_rpow X).trans (dyadic_rpow _ _)
  have hUs : U = ((2 : ℝ) ^ (1 / 4 : ℝ)) ^ n := by
    change Real.sqrt (Real.sqrt X) = _
    rw [Real.sqrt_eq_rpow (Real.sqrt X), Real.sqrt_eq_rpow X, ← Real.rpow_mul hXpos.le,
      show (1 / 2 : ℝ) * (1 / 2) = 1 / 4 by norm_num, dyadic_rpow]
  have hYs : Real.sqrt Y = ((2 : ℝ) ^ (1 / 6 : ℝ)) ^ n := by
    change Real.sqrt (X ^ (1 / 3 : ℝ)) = _
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hXpos.le,
      show (1 / 3 : ℝ) * (1 / 2) = 1 / 6 by norm_num, dyadic_rpow]
  have hp := positive_primes_ge (X := X) hA
  have ho := odd_loss_le hY
  have he := even_loss_le (show 1 ≤ A by linarith)
  change _ < weightedPrimeBalance X
  apply (Exp7.ChebyshevTailArithmetic.haarLowerBound_gt n hn).trans_le
  unfold weightedPrimeBalance
  dsimp only at hp ⊢
  calc
    _ = (8 * c * A / Real.log X - c * (3 + 8 / Real.log X) * U -
          Real.log X ^ 2 / 6 - 3 * Real.log X / 2 - (2 * Real.log X + 8) / U) -
        2 * (4 * Real.log 4 * Real.sqrt Y / Real.log Y +
          Real.log Y ^ 2 / 6 + Real.log Y) - (Real.log 4 * (1 + Real.log A) + 8) := by
      unfold Exp7.ChebyshevTailArithmetic.haarLowerBound
      dsimp only
      rw [← hAs, ← hUs, ← hYs, hL, hlogY, hlogA, hfour]
      change 8 * A / n - (3 * c + 8 / n) * U - 48 * Real.sqrt Y / n -
        (11/54) * c ^ 2 * (n : ℝ) ^ 2 - (13/6 + c) * c * n - (2*c + 8) -
        (2*c*n+8)/U = _
      field_simp
      ring
    _ ≤ _ := by linarith

/-- Every conductor above the certified bridge admits a legal dyadic cutoff at
which the weighted prime balance exceeds the explicit-formula budget. -/
theorem exists_cutoff_above_bridge {q : ℕ} (hq : 2 ^ 135 < q) :
    ∃ n : ℕ, 19 ≤ n ∧ 4 * (2 ^ n) ^ 7 < q ∧
      Real.log q + 4 < weightedPrimeBalance ((2 : ℝ) ^ n) := by
  obtain ⟨n, hn, hlo, hhi⟩ := Exp7.ChebyshevTailArithmetic.exists_dyadic_index hq
  refine ⟨n, hn, hlo, ?_⟩
  have hqpos : 0 < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
  have hl := Real.log_le_log hqpos (show (q : ℝ) ≤ (2 : ℝ) ^ (7 * n + 9) by exact_mod_cast hhi)
  rw [Real.log_pow] at hl
  push_cast at hl
  linarith [weightedPrimeBalance_gt n hn]

end Exp7.ChebyshevTail
