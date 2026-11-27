import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.Complex.ExponentialBounds

/-! # The even prime-power loss in the dyadic Haar bound

Counting the multiples of each divisor converts the floor-weighted Mangoldt
sum into the sum of logarithms. Removing the floors costs at most ψ(N).
-/

namespace Exp7.ChebyshevTail

open Finset
open scoped ArithmeticFunction.vonMangoldt

private theorem sum_floor_mul_mangoldt (N : ℕ) :
    ∑ d ∈ Ioc 0 N, (↑(N / d) : ℝ) * Λ d = ∑ n ∈ Ioc 0 N, Real.log n := by
  classical
  calc
    _ = ∑ d ∈ Ioc 0 N, ∑ n ∈ Ioc 0 N, if d ∣ n then Λ d else 0 := by
      refine sum_congr rfl fun d _ ↦ ?_
      rw [← sum_filter, sum_const, nsmul_eq_mul, Nat.Ioc_filter_dvd_card_eq_div]
    _ = ∑ n ∈ Ioc 0 N, ∑ d ∈ Ioc 0 N with d ∣ n, Λ d := by
      rw [sum_comm]
      simp only [sum_filter]
    _ = _ := by
      refine sum_congr rfl fun n hn ↦ ?_
      have hn' := mem_Ioc.mp hn
      have hdiv : ((Ioc 0 N).filter fun d ↦ d ∣ n) = n.divisors := by
        ext d
        simp only [mem_filter, mem_Ioc, Nat.mem_divisors]
        exact ⟨fun h ↦ ⟨h.2, hn'.1.ne'⟩, fun h ↦
          ⟨⟨Nat.pos_of_dvd_of_pos h.1 hn'.1, (Nat.le_of_dvd hn'.1 h.1).trans hn'.2⟩, h.1⟩⟩
      rw [hdiv, ArithmeticFunction.vonMangoldt_sum]

/-- An explicit, finite upper bound for the weighted Mangoldt sum, valid at real cutoffs. -/
theorem mangoldt_div_sum_le {M : ℝ} (hM : 1 ≤ M) :
    ∑ d ∈ Ioc 0 ⌊M⌋₊, Λ d / d ≤ Real.log M + Real.log 4 + 4 := by
  let N := ⌊M⌋₊
  have hN : 0 < N := Nat.floor_pos.mpr hM
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  have hround (d : ℕ) (hd : d ∈ Ioc 0 N) :
      (N : ℝ) * (Λ d / d) ≤ (↑(N / d) : ℝ) * Λ d + Λ d := by
    have hd' := (mem_Ioc.mp hd).1
    have hdR : (0 : ℝ) < d := by exact_mod_cast hd'
    have h : (N : ℝ) ≤ d * ((↑(N / d) : ℝ) + 1) := by
      exact_mod_cast (Nat.lt_mul_div_succ N hd').le
    calc
      _ = ((N : ℝ) / d) * Λ d := by ring
      _ ≤ ((↑(N / d) : ℝ) + 1) * Λ d := by
        exact mul_le_mul_of_nonneg_right ((div_le_iff₀ hdR).mpr (by linarith))
          ArithmeticFunction.vonMangoldt_nonneg
      _ = _ := by ring
  have hsum := sum_le_sum hround
  rw [← mul_sum, sum_add_distrib, sum_floor_mul_mangoldt] at hsum
  have hpsi := Chebyshev.psi_le_const_mul_self hNr.le
  simp only [Chebyshev.psi, Nat.floor_natCast] at hpsi
  have hlog : (∑ n ∈ Ioc 0 N, Real.log n) ≤ N * Real.log M := by
    calc
      _ ≤ ∑ _n ∈ Ioc 0 N, Real.log M := by
        refine sum_le_sum fun n hn ↦ Real.log_le_log ?_ ?_
        · exact_mod_cast (mem_Ioc.mp hn).1
        · exact (Nat.cast_le.mpr (mem_Ioc.mp hn).2).trans (Nat.floor_le (by linarith))
      _ = _ := by simp
  change (∑ d ∈ Ioc 0 N, Λ d / d) ≤ _
  apply le_of_mul_le_mul_left (a := (N : ℝ)) _ hNr
  linarith

/-- The even-power loss budget used in the uniform Haar comparison. -/
theorem even_loss_le {M : ℝ} (hM : 1 ≤ M) :
    ∑ d ∈ Ioc 0 ⌊M⌋₊, Λ d / d ≤ Real.log 4 * (1 + Real.log M) + 8 := by
  have hfour : 1 ≤ Real.log 4 := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    linarith [Real.log_two_gt_d9]
  have hprod := mul_le_mul_of_nonneg_right hfour (Real.log_nonneg hM)
  linarith [mangoldt_div_sum_le hM]

end Exp7.ChebyshevTail
