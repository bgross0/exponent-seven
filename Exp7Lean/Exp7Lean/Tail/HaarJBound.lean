import Exp7Lean.Analytic.JBound

/-!
Coarse archimedean bound for the two-cell Haar function.

For L >= 1 the first-cell bound is 3/2, the 16 middle subcells contribute
at most 3/2, and the existing tail expression is at most 4/5.
-/

namespace Exp7

open Real

private theorem haar_corr_one : corr ([1, -1] : List ℝ) 1 = -(1 / 2 : ℝ) := by
  norm_num [corr, Finset.sum_range_succ, List.getD]

private theorem haar_corr_two : corr ([1, -1] : List ℝ) 2 = 0 := by
  exact corr_of_length_le (by decide)

/-- The existing finite upper bound for the Haar test function is at most 4
once the support length is at least 1. -/
theorem Jplus_haar_le_four {L : ℝ} (hL : 1 ≤ L) :
    Jplus L ([1, -1] : List ℝ) ≤ 4 := by
  have hL0 : 0 < L := by linarith
  let step : ℝ := L / 2 / 16
  have hs : 0 < step := by dsimp [step]; positivity
  let term : ℕ → ℝ := fun i =>
    step * aKer (step * (16 + (i : ℝ))) *
      (1 - (-(1 / 2 : ℝ) + ((0 : ℝ) - -(1 / 2 : ℝ)) *
        ((2 * (i : ℝ) + 1) / 32)))
  have hterm : ∀ i : ℕ, i < 16 → term i ≤ 3 / 32 := by
    intro i hi
    have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
    have hi15 : (i : ℝ) ≤ 15 := by
      exact_mod_cast (show i ≤ 15 by omega)
    let u : ℝ := step * (16 + (i : ℝ))
    have hu : 0 < u := by dsimp [u]; positivity
    have hu16 : 16 * step ≤ u := by
      dsimp [u]
      nlinarith [mul_nonneg hs.le hi0]
    have ha0 : 0 ≤ aKer u := (aKer_pos hu).le
    have hscaled : 16 * (step * aKer u) ≤ 1 := by
      calc
        16 * (step * aKer u) = aKer u * (16 * step) := by ring
        _ ≤ aKer u * u := mul_le_mul_of_nonneg_left hu16 ha0
        _ ≤ 1 := aKer_mul_self_le_one hu
    have hstep : step * aKer u ≤ (1 / 16 : ℝ) := by linarith
    have hf : 0 ≤ 1 - (-(1 / 2 : ℝ) + ((0 : ℝ) - -(1 / 2 : ℝ)) *
          ((2 * (i : ℝ) + 1) / 32)) ∧
        1 - (-(1 / 2 : ℝ) + ((0 : ℝ) - -(1 / 2 : ℝ)) *
          ((2 * (i : ℝ) + 1) / 32)) ≤ 3 / 2 := by
      constructor <;> nlinarith
    dsimp only [term]
    calc
      step * aKer (step * (16 + (i : ℝ))) *
          (1 - (-(1 / 2 : ℝ) + ((0 : ℝ) - -(1 / 2 : ℝ)) *
            ((2 * (i : ℝ) + 1) / 32))) ≤ (1 / 16 : ℝ) * (3 / 2) :=
        mul_le_mul hstep hf.2 hf.1 (by norm_num)
      _ = 3 / 32 := by norm_num
  have hmid : (∑ i ∈ Finset.range 16, term i) ≤ (3 / 2 : ℝ) := by
    calc
      (∑ i ∈ Finset.range 16, term i) ≤
          ∑ _i ∈ Finset.range 16, (3 / 32 : ℝ) :=
        Finset.sum_le_sum fun i hi => hterm i (Finset.mem_range.mp hi)
      _ = 3 / 2 := by norm_num
  have hea : (5 / 2 : ℝ) ≤ exp (3 * L / 2) := by
    have := add_one_le_exp (3 * L / 2)
    linarith
  have heb : (3 : ℝ) ≤ exp (2 * L) := by
    have := add_one_le_exp (2 * L)
    linarith
  have hprod : exp (-2 * L) * exp (2 * L) = 1 := by
    rw [← exp_add, show -2 * L + 2 * L = 0 by ring, exp_zero]
  have heneg : exp (-2 * L) ≤ (1 / 3 : ℝ) := by
    have hm := mul_le_mul_of_nonneg_left heb (exp_pos (-2 * L)).le
    rw [hprod] at hm
    linarith
  have hfactor : (2 / 3 : ℝ) ≤ 1 - exp (-2 * L) := by linarith
  have hden : (5 : ℝ) ≤ 3 * exp (3 * L / 2) * (1 - exp (-2 * L)) := by
    have hm := mul_le_mul hea hfactor (by norm_num : (0 : ℝ) ≤ 2 / 3)
      (exp_pos (3 * L / 2)).le
    nlinarith
  have hden0 : 0 < 3 * exp (3 * L / 2) * (1 - exp (-2 * L)) := by linarith
  have htail : 4 / (3 * exp (3 * L / 2) * (1 - exp (-2 * L))) ≤ (4 / 5 : ℝ) := by
    apply (div_le_iff₀ hden0).2
    nlinarith
  have hcalc : (1 - -(1 / 2 : ℝ)) + (∑ i ∈ Finset.range 16, term i) +
      4 / (3 * exp (3 * L / 2) * (1 - exp (-2 * L))) ≤ 4 := by
    linarith
  have hico : Finset.Ico 1 (2 : ℕ) = {1} := by decide
  dsimp only [term, step] at hcalc
  simpa only [Jplus, List.length_cons, List.length_nil, Nat.reduceAdd,
    hico, Finset.sum_singleton, haar_corr_one, haar_corr_two,
    Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, one_mul] using hcalc

/-- Coarse J bound sufficient for the dyadic Chebyshev tail and its finite
bridge row. It follows from the project's existing Jplus theorem. -/
theorem Jterm_haar_le_four {L : ℝ} (hL : 1 ≤ L) :
    Jterm (autocorr (stepFn L ([1, -1] : List ℝ))) ≤ 4 := by
  have hL0 : 0 < L := by linarith
  have hv : ∃ t ∈ ([1, -1] : List ℝ), t ≠ 0 := by
    refine ⟨1, by simp, by norm_num⟩
  exact (Jterm_le_Jplus hL0 hv).trans (Jplus_haar_le_four hL)

end Exp7

#print axioms Exp7.Jplus_haar_le_four
#print axioms Exp7.Jterm_haar_le_four
