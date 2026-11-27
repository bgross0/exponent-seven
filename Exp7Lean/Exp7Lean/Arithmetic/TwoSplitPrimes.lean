import Exp7Lean.Arithmetic.NormBounds

/-!
Two split primes give compatible norm equations for the same conductor.

The elimination and composition identities are unconditional. Distinct primes
and the primitivity from Step 1 make the determinant nonzero. The final criterion
allows a future Diophantine argument to exclude exponent seven by excluding
these paired witnesses. It does not assert that such an exclusion is known.
-/

namespace Exp7
namespace NormWitness

variable {q p r x y u v : ℕ} (h : NormWitness q p x y) (k : NormWitness q r u v)

include h k

/-- Eliminate the common conductor without subtraction in the naturals. -/
theorem eliminate_conductor :
    4 * p ^ 7 * v ^ 2 + u ^ 2 * y ^ 2 =
      4 * r ^ 7 * y ^ 2 + x ^ 2 * v ^ 2 := by
  rw [h.equation, k.equation]
  ring

omit k in
/-- Distinct primes cannot give proportional primitive norm witnesses. -/
theorem weighted_powers_ne (hp : p.Prime) (hr : r.Prime) (hpr : p ≠ r) (hp2 : p ≠ 2) :
    p ^ 7 * v ^ 2 ≠ r ^ 7 * y ^ 2 := by
  intro heq
  have hd : p ∣ p ^ 7 * v ^ 2 := dvd_mul_of_dvd_left (dvd_pow_self p (by norm_num)) _
  rw [heq] at hd
  rcases hp.dvd_mul.mp hd with hpr' | hpy
  · exact hpr ((Nat.prime_dvd_prime_iff_eq hp hr).mp (hp.dvd_of_dvd_pow hpr'))
  · exact h.primitive hp2 (hp.dvd_of_dvd_pow hpy)

theorem cross_products_ne (hp : p.Prime) (hr : r.Prime) (hpr : p ≠ r) (hp2 : p ≠ 2) :
    x * v ≠ u * y := by
  intro heq
  have hs : x ^ 2 * v ^ 2 = u ^ 2 * y ^ 2 := by nlinarith [congrArg (fun n : ℕ => n ^ 2) heq]
  have helim := h.eliminate_conductor k
  apply h.weighted_powers_ne (v := v) hp hr hpr hp2
  nlinarith

/-- The determinant is taken in the integers, so its sign is preserved. -/
theorem determinant_ne_zero (hp : p.Prime) (hr : r.Prime) (hpr : p ≠ r) (hp2 : p ≠ 2) :
    (x : ℤ) * v - (u : ℤ) * y ≠ 0 := by
  intro heq
  have heq' : (x : ℤ) * v = (u : ℤ) * y := sub_eq_zero.mp heq
  exact h.cross_products_ne k hp hr hpr hp2 (by exact_mod_cast heq')

/-- An integral nonzero determinant has square at least one. -/
theorem one_le_determinant_sq (hp : p.Prime) (hr : r.Prime) (hpr : p ≠ r) (hp2 : p ≠ 2) :
    (1 : ℤ) ≤ ((x : ℤ) * v - (u : ℤ) * y) ^ 2 := by
  have hn := h.determinant_ne_zero k hp hr hpr hp2
  have hp' : 0 < ((x : ℤ) * v - (u : ℤ) * y) ^ 2 := sq_pos_of_ne_zero hn
  omega

/-- Factoring the elimination identity exposes the signed determinant. -/
theorem determinant_factorization :
    ((x : ℤ) * v - (u : ℤ) * y) * ((x : ℤ) * v + (u : ℤ) * y) =
      4 * ((p : ℤ) ^ 7 * v ^ 2 - (r : ℤ) ^ 7 * y ^ 2) := by
  have he : 4 * (p : ℤ) ^ 7 * v ^ 2 + (u : ℤ) ^ 2 * y ^ 2 =
      4 * (r : ℤ) ^ 7 * y ^ 2 + (x : ℤ) ^ 2 * v ^ 2 := by
    exact_mod_cast h.eliminate_conductor k
  linear_combination -he

/-- Multiplication of the two norm forms, with one factor conjugated. -/
theorem composition_identity :
    ((x : ℤ) * u + (q : ℤ) * y * v) ^ 2 +
      (q : ℤ) * ((x : ℤ) * v - (u : ℤ) * y) ^ 2 = 16 * ((p : ℤ) * r) ^ 7 := by
  have he : 4 * (p : ℤ) ^ 7 = (x : ℤ) ^ 2 + (q : ℤ) * y ^ 2 := by
    exact_mod_cast h.equation
  have ke : 4 * (r : ℤ) ^ 7 = (u : ℤ) ^ 2 + (q : ℤ) * v ^ 2 := by
    exact_mod_cast k.equation
  calc
    _ = ((x : ℤ) ^ 2 + (q : ℤ) * y ^ 2) *
        ((u : ℤ) ^ 2 + (q : ℤ) * v ^ 2) := by ring
    _ = 16 * ((p : ℤ) * r) ^ 7 := by rw [← he, ← ke]; ring

end NormWitness

/-- Package the necessary paired equations and their nondegeneracy for downstream arguments. -/
theorem IsExp7.exists_paired_normWitness {q p r : ℕ} (hE : IsExp7 q)
    (hp : p.Prime) (hr : r.Prime) (hpq : p ≠ q) (hrq : r ≠ q)
    (hpr : p ≠ r) (hp2 : p ≠ 2) (hps : Splits q p) (hrs : Splits q r) :
    ∃ x y u v, NormWitness q p x y ∧ NormWitness q r u v ∧
      x * v ≠ u * y ∧
      4 * p ^ 7 * v ^ 2 + u ^ 2 * y ^ 2 =
        4 * r ^ 7 * y ^ 2 + x ^ 2 * v ^ 2 := by
  obtain ⟨x, y, h⟩ := hE.exists_normWitness hp hpq hps
  obtain ⟨u, v, k⟩ := hE.exists_normWitness hr hrq hrs
  exact ⟨x, y, u, v, h, k, h.cross_products_ne k hp hr hpr hp2, h.eliminate_conductor k⟩

/-- A concrete downstream target: rule out every nondegenerate pair of norm witnesses. -/
theorem not_isExp7_of_no_paired_normWitness {q p r : ℕ}
    (hp : p.Prime) (hr : r.Prime) (hpq : p ≠ q) (hrq : r ≠ q)
    (hpr : p ≠ r) (hp2 : p ≠ 2) (hps : Splits q p) (hrs : Splits q r)
    (hno : ∀ x y u v, NormWitness q p x y → NormWitness q r u v →
      x * v ≠ u * y → False) : ¬ IsExp7 q := by
  intro hE
  obtain ⟨x, y, u, v, h, k, hn, _⟩ :=
    hE.exists_paired_normWitness hp hr hpq hrq hpr hp2 hps hrs
  exact hno x y u v h k hn

end Exp7
