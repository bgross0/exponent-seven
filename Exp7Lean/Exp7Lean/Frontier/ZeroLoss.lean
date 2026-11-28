import Exp7Lean.Frontier.ZeroMass

/-!
# Summing low and high zero losses without GRH

The bounds are on actual completed-L-function zeros, with multiplicities.
The test-function estimates remain explicit hypotheses. In particular this
module does not assert that the smoothed Haar kernel satisfies those estimates.
-/

namespace Exp7.Frontier

open Exp7.EF

/-- The quartic tail comparison, including its boundary. -/
theorem quartic_tail_weight {T t : ℝ} (hT : 0 < T) (ht : T ≤ |t|) :
    1 / t ^ 4 ≤ (((T + 1) ^ 2 + T ^ 2) / T ^ 4) /
      ((T + 1) ^ 2 + t ^ 2) := by
  have hs : T ^ 2 ≤ t ^ 2 := by nlinarith [sq_abs t]
  have ht2 : 0 < t ^ 2 := lt_of_lt_of_le (sq_pos_of_pos hT) hs
  have ht4 : 0 < t ^ 4 := by nlinarith [sq_pos_of_pos ht2]
  have hT4 : 0 < T ^ 4 := by positivity
  have h4 : T ^ 4 ≤ t ^ 4 := by nlinarith [sq_nonneg (t ^ 2 - T ^ 2)]
  have hcross : T ^ 4 * t ^ 2 ≤ t ^ 4 * T ^ 2 := by
    nlinarith [mul_nonneg (mul_nonneg ht2.le (sq_nonneg T)) (sub_nonneg.mpr hs)]
  have hpoly : T ^ 4 * ((T + 1) ^ 2 + t ^ 2) ≤
      ((T + 1) ^ 2 + T ^ 2) * t ^ 4 := by
    nlinarith [mul_nonneg (sq_nonneg (T + 1)) (sub_nonneg.mpr h4)]
  apply (le_div_iff₀ (by positivity : 0 < (T + 1) ^ 2 + t ^ 2)).2
  rw [one_div_mul_eq_div, div_le_div_iff₀ ht4 hT4]
  nlinarith [hpoly]

variable (q : ℕ) [Fact q.Prime]

/-- The aggregate quartic high-zero loss. The real parts of high zeros are unrestricted. -/
theorem high_zero_loss_le (hq : q % 4 = 3) {T C : ℝ} (hT : 0 < T) (hC : 0 ≤ C)
    (F : ℂ → ℝ)
    (hF : ∀ ρ, mult q ρ ≠ 0 → T < |ρ.im| → |F ρ| ≤ C / ρ.im ^ 4) :
    Summable (fun ρ : ℂ ↦ if T < |ρ.im| then (mult q ρ : ℝ) * |F ρ| else 0) ∧
      (∑' ρ : ℂ, if T < |ρ.im| then (mult q ρ : ℝ) * |F ρ| else 0) ≤
        (C * (((T + 1) ^ 2 + T ^ 2) / T ^ 4)) *
          (logDerivativeMass q (T + 1) / T) := by
  classical
  let K := C * (((T + 1) ^ 2 + T ^ 2) / T ^ 4)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hsum := (summable_shifted_weight q hq hT).mul_left K
  have hbound : ∀ ρ : ℂ,
      (if T < |ρ.im| then (mult q ρ : ℝ) * |F ρ| else 0) ≤
        K * ((mult q ρ : ℝ) / ((T + 1) ^ 2 + ρ.im ^ 2)) := by
    intro ρ
    split_ifs with ht
    · by_cases hm : mult q ρ = 0
      · simp [hm]
      have h := (hF ρ hm ht).trans (by
        have hb := mul_le_mul_of_nonneg_left (quartic_tail_weight hT ht.le) hC
        convert hb using 1; ring)
      have hm' := mul_le_mul_of_nonneg_left h (Nat.cast_nonneg (mult q ρ) : (0 : ℝ) ≤ _)
      dsimp [K] at *
      convert hm' using 1; ring
    · positivity
  have hsmall := Summable.of_nonneg_of_le (fun ρ ↦ by split_ifs <;> positivity) hbound hsum
  refine ⟨hsmall, ?_⟩
  calc _ ≤ ∑' ρ : ℂ, K * ((mult q ρ : ℝ) / ((T + 1) ^ 2 + ρ.im ^ 2)) :=
      Summable.tsum_le_tsum hbound hsmall hsum
    _ = K * ∑' ρ : ℂ, (mult q ρ : ℝ) / ((T + 1) ^ 2 + ρ.im ^ 2) := tsum_mul_left
    _ ≤ K * (logDerivativeMass q (T + 1) / T) :=
      mul_le_mul_of_nonneg_left (shifted_mass_le q hq hT) hK

/-- Sum a low-zero lower bound and an unrestricted quartic high-zero bound.
Absolute convergence of the chosen test function is an explicit input. -/
theorem zero_sum_lower_bound (hq : q % 4 = 3) {T A C : ℝ}
    (hT : 0 < T) (hA : 0 ≤ A) (hC : 0 ≤ C) (F : ℂ → ℝ)
    (hsum : Summable (fun ρ : ℂ ↦ (mult q ρ : ℝ) * F ρ))
    (hlow : ∀ ρ, mult q ρ ≠ 0 → |ρ.im| ≤ T → -A / (1 + ρ.im ^ 2) ≤ F ρ)
    (hhigh : ∀ ρ, mult q ρ ≠ 0 → T < |ρ.im| → |F ρ| ≤ C / ρ.im ^ 4) :
    -(A * (2 * logDerivativeMass q 2) +
      (C * (((T + 1) ^ 2 + T ^ 2) / T ^ 4)) *
        (logDerivativeMass q (T + 1) / T)) ≤
      ∑' ρ : ℂ, (mult q ρ : ℝ) * F ρ := by
  classical
  let hi : ℂ → ℝ := fun ρ ↦ if T < |ρ.im| then (mult q ρ : ℝ) * |F ρ| else 0
  obtain ⟨hhi, hhi_bound⟩ := high_zero_loss_le q hq hT hC F hhigh
  have hlo := (summable_mult_div q hq).mul_left A
  have hpoint : ∀ ρ : ℂ, -(A * ((mult q ρ : ℝ) / (1 + ρ.im ^ 2)) + hi ρ) ≤
      (mult q ρ : ℝ) * F ρ := by
    intro ρ
    by_cases hm : mult q ρ = 0
    · simp [hm, hi]
    have hm0 : (0 : ℝ) ≤ (mult q ρ : ℝ) := Nat.cast_nonneg _
    have hlo0 : 0 ≤ A * ((mult q ρ : ℝ) / (1 + ρ.im ^ 2)) := by positivity
    by_cases ht : T < |ρ.im|
    · dsimp [hi]
      rw [ite_eq_left ht]
      have habs := mul_le_mul_of_nonneg_left (neg_abs_le (F ρ)) hm0
      nlinarith
    · dsimp [hi]
      rw [ite_eq_right ht]
      have hl := mul_le_mul_of_nonneg_left (hlow ρ hm (not_lt.mp ht)) hm0
      convert hl using 1; ring
  have hcomp := Summable.tsum_le_tsum hpoint (hlo.add hhi).neg hsum
  have hlow_bound := mul_le_mul_of_nonneg_left (standard_mass_le q hq) hA
  rw [tsum_neg, hlo.tsum_add hhi, tsum_mul_left] at hcomp
  linarith

end Exp7.Frontier
