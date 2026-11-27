import Exp7Lean.Step1

/-!
Unconditional consequences of the existing class-group norm equation.

`NormWitness` packages exactly the conclusion of `normEq_classGroup`; it does not
replace `IsExp7` or introduce an analytic hypothesis. The arithmetic lemmas can
also be used on candidate solutions before a class-group interpretation is known.
-/

namespace Exp7

/-- A natural-number norm witness, retaining the primitivity supplied by Step 1. -/
structure NormWitness (q p x y : ℕ) : Prop where
  y_pos : 1 ≤ y
  primitive : p ≠ 2 → ¬ p ∣ y
  equation : 4 * p ^ 7 = x ^ 2 + q * y ^ 2

/-- Step 1 supplies a witness for every unramified split prime. -/
theorem IsExp7.exists_normWitness {q p : ℕ} (hE : IsExp7 q)
    (hp : p.Prime) (hpq : p ≠ q) (hs : Splits q p) :
    ∃ x y, NormWitness q p x y := by
  have hdata := hE
  obtain ⟨hq, h4, _⟩ := hdata
  obtain ⟨x, y, hy, hprim, heq⟩ := normEq_classGroup q hq h4 hE p hp hpq hs
  exact ⟨x, y, hy, hprim, heq⟩

namespace NormWitness

variable {q p x y : ℕ} (h : NormWitness q p x y)

include h

theorem conductor_le : q ≤ 4 * p ^ 7 := by
  have := Nat.le_mul_of_pos_right q (show 0 < y ^ 2 by have := h.y_pos; positivity)
  have := h.equation
  omega

theorem y_sq_le (hq : 0 < q) : y ^ 2 ≤ (4 * p ^ 7) / q := by
  apply (Nat.le_div_iff_mul_le hq).mpr
  have := h.equation
  nlinarith

/-- A lower bound on the conductor gives a uniform finite range for `y`. -/
theorem y_sq_le_of_lower {Q : ℕ} (hQ : 0 < Q) (hQq : Q ≤ q) :
    y ^ 2 ≤ (4 * p ^ 7) / Q := by
  apply (Nat.le_div_iff_mul_le hQ).mpr
  have hmul := Nat.mul_le_mul_right (y ^ 2) hQq
  have := h.equation
  nlinarith

theorem x_sq_lt (hq : 0 < q) : x ^ 2 < 4 * p ^ 7 := by
  have hy := h.y_pos
  have hpos : 0 < q * y ^ 2 := by positivity
  have := h.equation
  omega

/-- Avoid truncated subtraction when exposing the square obstruction. -/
theorem residual_eq : 4 * p ^ 7 - q * y ^ 2 = x ^ 2 := by
  have := h.equation
  omega

theorem residual_isSquare : IsSquare (4 * p ^ 7 - q * y ^ 2) := by
  rw [h.residual_eq]
  exact ⟨x, by ring⟩

/-- If `4p^7 < 4q`, only the first `y` slice can contain a witness. -/
theorem y_eq_one (hsmall : 4 * p ^ 7 < 4 * q) : y = 1 := by
  have hy := h.y_pos
  have he := h.equation
  by_contra hne
  have hyge : 2 ≤ y := by omega
  have hy2 : 4 ≤ y ^ 2 := by nlinarith
  have hmul := Nat.mul_le_mul_left q hy2
  nlinarith

/-- In the first slice, the remaining obstruction is one exact square. -/
theorem first_slice (hsmall : 4 * p ^ 7 < 4 * q) : q + x ^ 2 = 4 * p ^ 7 := by
  have he := h.equation
  rw [h.y_eq_one hsmall] at he
  nlinarith

/-- For an odd unramified prime, primitivity also excludes `p | x`. -/
theorem not_dvd_x (hp : p.Prime) (hp2 : p ≠ 2) (hq : q.Prime) (hpq : p ≠ q) :
    ¬ p ∣ x := by
  intro hx
  have hleft : p ∣ 4 * p ^ 7 := dvd_mul_of_dvd_right (dvd_pow_self p (by norm_num)) 4
  have hx2 : p ∣ x ^ 2 := dvd_pow hx (by norm_num)
  have hqy : p ∣ q * y ^ 2 := by
    rw [h.equation] at hleft
    exact (Nat.dvd_add_right hx2).mp hleft
  rcases hp.dvd_mul.mp hqy with hpq' | hpy
  · exact hpq ((Nat.prime_dvd_prime_iff_eq hp hq).mp hpq')
  · exact h.primitive hp2 (hp.dvd_of_dvd_pow hpy)

end NormWitness

/-- A split prime gives an unconditional conductor bound, without `Inputs`. -/
theorem IsExp7.le_of_split {q p : ℕ} (hE : IsExp7 q) (hp : p.Prime)
    (hpq : p ≠ q) (hs : Splits q p) : q ≤ 4 * p ^ 7 := by
  obtain ⟨x, y, h⟩ := hE.exists_normWitness hp hpq hs
  exact h.conductor_le

/-- A split prime below the norm threshold excludes exponent seven. -/
theorem not_isExp7_of_small_split {q p : ℕ} (hp : p.Prime) (hpq : p ≠ q)
    (hs : Splits q p) (hsmall : 4 * p ^ 7 < q) : ¬ IsExp7 q := by
  intro hE
  exact (not_le.mpr hsmall) (hE.le_of_split hp hpq hs)

/-- The conductor exceeds every proposed cutoff below the norm threshold. -/
theorem cutoff_lt_conductor {q X : ℕ} (hX : 4 * X ^ 7 < q) : X < q := by
  have hpow : X ≤ X ^ 7 := Nat.le_self_pow (by norm_num) X
  omega

/-- A cutoff can be chosen independently of any analytic certificate. -/
theorem IsExp7.no_split_le {q X : ℕ} (hE : IsExp7 q) (hX : 4 * X ^ 7 < q)
    {p : ℕ} (hp : p.Prime) (hpX : p ≤ X) : ¬ Splits q p := by
  intro hs
  have hpq : p ≠ q := by have := cutoff_lt_conductor hX; omega
  have hpow := Nat.pow_le_pow_left hpX 7
  have := hE.le_of_split hp hpq hs
  omega

/-- Above 512, the prime 2 is inert and the prime conductor is 3 modulo 8. -/
theorem IsExp7.mod_eight_of_large {q : ℕ} (hE : IsExp7 q) (hq : 512 < q) :
    q % 8 = 3 := by
  have hn := hE.no_split_le (X := 2) (by norm_num; exact hq) Nat.prime_two le_rfl
  rw [splits_two_iff] at hn
  obtain ⟨_, h4, _⟩ := hE
  omega

end Exp7
