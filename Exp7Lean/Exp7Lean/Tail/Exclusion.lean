import Exp7Lean.Tail.HaarInert
import Exp7Lean.Tail.HaarJBound
import Exp7Lean.Rows.Bridge30000

/-! # The dyadic tail and classification at all discriminants -/

namespace Exp7.ChebyshevTail

open Real

/-- Above the finite bridge, the norm bound and the explicit formula give
incompatible bounds for the two-cell Haar row. -/
theorem excludes_above_bridge (hGRH : GRHPrimeConductor) {q : ℕ} (hq : q.Prime)
    (h4 : q % 4 = 3) (hlarge : 2 ^ 135 < q) : ¬ IsExp7 q := by
  obtain ⟨n, hn, hnorm, hbalance⟩ := exists_cutoff_above_bridge hlarge
  let X := 2 ^ n
  have hX : 2 ≤ X := by
    calc
      2 = (2 : ℕ) ^ 1 := by simp
      _ ≤ X := Nat.pow_le_pow_right (by decide) (by omega)
  have hXq : X < q := by
    have := Nat.le_self_pow (by decide : 7 ≠ 0) X
    change 4 * X ^ 7 < q at hnorm
    omega
  have hcast : (X : ℝ) = 2 ^ n := by simp [X]
  rw [← hcast] at hbalance
  have hsum := hbalance.trans_le (weightedPrimeBalance_le_inertSum hX)
  have hlen : 1 ≤ log (X : ℝ) := by
    rw [hcast, log_pow]
    have hn' : (19 : ℝ) ≤ n := by exact_mod_cast hn
    have hc := log_pos (by norm_num : (1 : ℝ) < 2)
    nlinarith [Real.log_two_gt_d9, mul_nonneg (sub_nonneg.mpr hn') hc.le]
  have hJ := Jterm_haar_le_four hlen
  have hpi := log_nonneg (show 1 ≤ π by linarith [Real.pi_gt_three])
  have hpsi : psi34 ≤ 0 := by
    unfold psi34
    linarith [Real.one_half_lt_eulerMascheroniConstant, Real.pi_lt_four, Real.log_two_gt_d9]
  have hmargin : 0 < rowMargin q X [1, -1] := by
    unfold rowMargin
    linarith
  obtain ⟨p, hp, hpX, hs⟩ := split_prime_of_row EF.explicitFormulaBound hGRH q X [1, -1]
    hX ⟨1, by simp, one_ne_zero⟩ hmargin q hq h4 hXq le_rfl
  intro hE
  obtain ⟨x, y, hy, _, he⟩ := normEq_classGroup q hq h4 hE p hp (hpX.trans hXq).ne hs
  have hqle : q ≤ q * y ^ 2 := Nat.le_mul_of_pos_right _ (by positivity)
  have hp7 := Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left hpX.le 7)
  change 4 * X ^ 7 < q at hnorm
  omega

/-- The finite row and the dyadic argument exclude every prime conductor at
or above the original search ceiling. -/
theorem excludes_from_search_ceiling (hGRH : GRHPrimeConductor) {q : ℕ}
    (hq : q.Prime) (h4 : q % 4 = 3) (hlo : QTOP ≤ q) : ¬ IsExp7 q := by
  rcases le_or_gt q (2 ^ 135) with h | h
  · exact Rows.Bridge30000.excludes hGRH hq h4 hlo h
  · exact excludes_above_bridge hGRH hq h4 h

/-- Classification of prime conductors, with no size hypothesis. -/
theorem classification_prime (hGRH : GRHPrimeConductor) (hS : SearchHigh) (hSL : SearchLow)
    {q : ℕ} (hq : q.Prime) (h4 : q % 4 = 3) : IsExp7 q ↔ q ∈ known := by
  rcases le_or_gt q QTOP with h | h
  · exact theoremD_rows hGRH hS hSL hq h4 h
  · exact ⟨fun hE ↦ (excludes_from_search_ceiling hGRH hq h4 h.le hE).elim,
      isExp7_of_known_all q⟩

/-- Classification at all negative fundamental discriminants. -/
theorem classification_fundamental (hGRH : GRHPrimeConductor) (hS : SearchHigh) (hSL : SearchLow)
    (a b : ℤ) (hfund : Int.IsFundamentalDiscr (QuadraticAlgebra.discr a b))
    (hneg : QuadraticAlgebra.discr a b < 0) [IsDomain (QuadraticAlgebra ℤ a b)] :
    Monoid.exponent (ClassGroup (QuadraticAlgebra ℤ a b)) = 7 ↔
      ∃ q ∈ known, QuadraticAlgebra.discr a b = -(q : ℤ) := by
  constructor
  · intro hE
    obtain ⟨q, hq, h4, hd⟩ := prime_discr_of_exponent_seven' a b hfund hneg hE
    exact ⟨q, (classification_prime hGRH hS hSL hq h4).mp
      ((isExp7_iff_exponent hq h4 hd).mpr hE), hd⟩
  · rintro ⟨q, hk, hd⟩
    exact exponent_seven_of_mem_known hk hd

end Exp7.ChebyshevTail
