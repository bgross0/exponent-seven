import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Exact cyclic order-seven period certificates

This module proves algebraic certificates for the two explicitly supplied
cyclic coefficient vectors.  The order is the order of the chosen generator
of the cyclic group, not the sorted order of the supersingular j-invariants.

* E389: `(-1, 0, -1, 1, 0, 0, 1)`.
* E433: `(1, 1, -1, 0, 0, 0, -1)`.

The Bezout identities below prove that the nontrivial-character evaluations
are nonzero in every field of characteristic different from seven.  They
also prove the stronger unit statement in any commutative ring where seven
is a unit, once the argument is a root of the seventh cyclotomic polynomial.

These are complete algebraic proofs about the supplied polynomials.  This
module does not identify these vectors with CM evaluations, construct CM
points or toric periods, or prove a special-value formula.  Such arithmetic
identifications are separate obligations.
-/

namespace BSDCMPeriods

open scoped BigOperators

/-- Coefficients indexed in cyclic generator order. -/
def values389 : Fin 7 → ℤ := ![-1, 0, -1, 1, 0, 0, 1]

/-- Coefficients indexed in cyclic generator order. -/
def values433 : Fin 7 → ℤ := ![1, 1, -1, 0, 0, 0, -1]

section Ring

variable {R : Type*} [CommRing R]

/-- The seventh cyclotomic polynomial, written as its evaluation function. -/
def phi7 (z : R) : R := 1 + z + z ^ 2 + z ^ 3 + z ^ 4 + z ^ 5 + z ^ 6

/-- Evaluation of the corrected cyclic E389 vector. -/
def period389 (z : R) : R := -1 - z ^ 2 + z ^ 3 + z ^ 6

/-- Evaluation of the cyclic E433 vector. -/
def period433 (z : R) : R := 1 + z - z ^ 2 - z ^ 6

/-- Character evaluation of a supplied integral vector on a cyclic group. -/
def cyclicPeriod (v : Fin 7 → ℤ) (z : R) : R :=
  ∑ j : Fin 7, (v j : R) * z ^ (j : ℕ)

theorem cyclicPeriod_values389 (z : R) : cyclicPeriod values389 z = period389 z := by
  norm_num [cyclicPeriod, values389, Fin.sum_univ_succ, period389]
  ring

theorem cyclicPeriod_values433 (z : R) : cyclicPeriod values433 z = period433 z := by
  norm_num [cyclicPeriod, values433, Fin.sum_univ_succ, period433]
  ring

def bezout389A (z : R) : R := z ^ 5 + 4 * z ^ 4 + 2 * z ^ 3 +
  2 * z ^ 2 + 4 * z + 1

def bezout389B (z : R) : R := -z ^ 5 - 3 * z ^ 4 + 2 * z ^ 3 -
  z ^ 2 - 4 * z + 8

def bezout433A (z : R) : R := -3 * z ^ 5 - 2 * z ^ 4 - 4 * z ^ 3 -
  2 * z ^ 2 - 3 * z

def bezout433B (z : R) : R := -3 * z ^ 5 + z ^ 4 - 2 * z ^ 3 +
  2 * z ^ 2 - 4 * z + 7

/-- Integral Bezout certificate; the constant is seven. -/
theorem bezout389 (z : R) :
    bezout389A z * period389 z + bezout389B z * phi7 z = 7 := by
  unfold bezout389A period389 bezout389B phi7
  ring

/-- Integral Bezout certificate; the constant is seven. -/
theorem bezout433 (z : R) :
    bezout433A z * period433 z + bezout433B z * phi7 z = 7 := by
  unfold bezout433A period433 bezout433B phi7
  ring

theorem seventh_root_factorization (z : R) :
    (z - 1) * phi7 z = z ^ 7 - 1 := by
  unfold phi7
  ring

/-- The trivial-character evaluation vanishes exactly. -/
theorem period389_one : period389 (1 : R) = 0 := by
  norm_num [period389]

/-- The trivial-character evaluation vanishes exactly. -/
theorem period433_one : period433 (1 : R) = 0 := by
  norm_num [period433]

/-- The certificate proves an integral unit, not merely field nonvanishing. -/
theorem period389_isUnit_of_phi7 (z : R) (hz : phi7 z = 0)
    (h7 : IsUnit (7 : R)) : IsUnit (period389 z) := by
  have h := bezout389 z
  simp only [hz, mul_zero, add_zero] at h
  exact isUnit_of_mul_isUnit_right (h ▸ h7)

/-- The certificate proves an integral unit, not merely field nonvanishing. -/
theorem period433_isUnit_of_phi7 (z : R) (hz : phi7 z = 0)
    (h7 : IsUnit (7 : R)) : IsUnit (period433 z) := by
  have h := bezout433 z
  simp only [hz, mul_zero, add_zero] at h
  exact isUnit_of_mul_isUnit_right (h ▸ h7)

/-- No field or integrality assumptions are needed for this implication. -/
theorem period389_ne_zero_of_phi7 (z : R) (hz : phi7 z = 0)
    (h7 : (7 : R) ≠ 0) : period389 z ≠ 0 := by
  intro hp
  have h := bezout389 z
  simp only [hz, hp, mul_zero, add_zero] at h
  exact h7 h.symm

/-- No field or integrality assumptions are needed for this implication. -/
theorem period433_ne_zero_of_phi7 (z : R) (hz : phi7 z = 0)
    (h7 : (7 : R) ≠ 0) : period433 z ≠ 0 := by
  intro hp
  have h := bezout433 z
  simp only [hz, hp, mul_zero, add_zero] at h
  exact h7 h.symm

/-- The product of the six cyclic character evaluations.  Under an arithmetic
identification with conjugates in the seventh cyclotomic field, this is the
field norm.  The definition itself needs no number-field infrastructure. -/
def conjugateProduct (P : R → R) (z : R) : R :=
  P z * P (z ^ 2) * P (z ^ 3) * P (z ^ 4) * P (z ^ 5) * P (z ^ 6)

/-- An exact group-ring identity, valid even for the trivial seventh root. -/
theorem period389_conjugateProduct_identity (z : R) (hz : z ^ 7 = 1) :
    conjugateProduct period389 z = 49 - 7 * phi7 z := by
  have hpow (n : ℕ) : z ^ n = z ^ (n % 7) := pow_eq_pow_mod n hz
  calc
    conjugateProduct period389 z =
        (z ^ 6 + z ^ 3 - z ^ 2 - 1) *
        (z ^ 6 + z ^ 5 - z ^ 4 - 1) *
        (-z ^ 6 + z ^ 4 + z ^ 2 - 1) *
        (z ^ 5 + z ^ 3 - z - 1) *
        (-z ^ 3 + z ^ 2 + z - 1) *
        (-z ^ 5 + z ^ 4 + z - 1) := by
      norm_num [conjugateProduct, period389, ← pow_mul,
        hpow 8, hpow 9, hpow 10, hpow 12, hpow 15, hpow 18,
        hpow 24, hpow 30, hpow 36]
      ring
    _ = 49 - 7 * phi7 z := by
      unfold phi7
      ring_nf
      norm_num [hpow 7, hpow 8, hpow 9, hpow 10, hpow 11, hpow 12,
        hpow 13, hpow 14, hpow 15, hpow 16, hpow 17, hpow 18,
        hpow 19, hpow 20, hpow 21, hpow 22, hpow 23, hpow 24,
        hpow 25, hpow 26, hpow 27, hpow 28, hpow 29, hpow 30,
        hpow 31]
      ring

/-- An exact group-ring identity, valid even for the trivial seventh root. -/
theorem period433_conjugateProduct_identity (z : R) (hz : z ^ 7 = 1) :
    conjugateProduct period433 z = 49 - 7 * phi7 z := by
  have hpow (n : ℕ) : z ^ n = z ^ (n % 7) := pow_eq_pow_mod n hz
  calc
    conjugateProduct period433 z =
        (-z ^ 6 - z ^ 2 + z + 1) *
        (-z ^ 5 - z ^ 4 + z ^ 2 + 1) *
        (-z ^ 6 - z ^ 4 + z ^ 3 + 1) *
        (z ^ 4 - z ^ 3 - z + 1) *
        (z ^ 5 - z ^ 3 - z ^ 2 + 1) *
        (z ^ 6 - z ^ 5 - z + 1) := by
      norm_num [conjugateProduct, period433, ← pow_mul,
        hpow 8, hpow 10, hpow 12, hpow 18, hpow 24, hpow 30, hpow 36]
      ring
    _ = 49 - 7 * phi7 z := by
      unfold phi7
      ring_nf
      norm_num [hpow 7, hpow 8, hpow 9, hpow 10, hpow 11, hpow 12,
        hpow 13, hpow 14, hpow 15, hpow 16, hpow 17, hpow 18,
        hpow 19, hpow 20, hpow 21, hpow 22, hpow 23, hpow 24,
        hpow 25, hpow 26, hpow 27, hpow 28, hpow 29, hpow 30,
        hpow 31, hpow 32]
      ring

/-- Exact norm certificate expressed as the product of six conjugate values. -/
theorem period389_conjugateProduct_eq_49 (z : R) (hz : phi7 z = 0) :
    conjugateProduct period389 z = 49 := by
  have hroot : z ^ 7 = 1 := by
    have h := seventh_root_factorization z
    rw [hz, mul_zero] at h
    exact sub_eq_zero.mp h.symm
  rw [period389_conjugateProduct_identity z hroot, hz]
  ring

/-- Exact norm certificate expressed as the product of six conjugate values. -/
theorem period433_conjugateProduct_eq_49 (z : R) (hz : phi7 z = 0) :
    conjugateProduct period433 z = 49 := by
  have hroot : z ^ 7 = 1 := by
    have h := seventh_root_factorization z
    rw [hz, mul_zero] at h
    exact sub_eq_zero.mp h.symm
  rw [period433_conjugateProduct_identity z hroot, hz]
  ring

end Ring

section Domain

variable {R : Type*} [CommRing R] [IsDomain R]

/-- A nontrivial seventh root is a root of the displayed cyclotomic polynomial. -/
theorem phi7_eq_zero_of_seventh_root (z : R) (hz : z ^ 7 = 1)
    (hne : z ≠ 1) : phi7 z = 0 := by
  have h := seventh_root_factorization z
  rw [hz, sub_self] at h
  exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hne)

theorem period389_ne_zero_of_seventh_root (z : R) (hz : z ^ 7 = 1)
    (hne : z ≠ 1) (h7 : (7 : R) ≠ 0) : period389 z ≠ 0 :=
  period389_ne_zero_of_phi7 z (phi7_eq_zero_of_seventh_root z hz hne) h7

theorem period433_ne_zero_of_seventh_root (z : R) (hz : z ^ 7 = 1)
    (hne : z ≠ 1) (h7 : (7 : R) ≠ 0) : period433 z ≠ 0 :=
  period433_ne_zero_of_phi7 z (phi7_eq_zero_of_seventh_root z hz hne) h7

/-- All six nontrivial characters of a cyclic group of order seven. -/
theorem period389_pow_ne_zero (z : R) (hz : IsPrimitiveRoot z 7)
    (j : ℕ) (hj0 : j ≠ 0) (hj7 : j < 7) (h7 : (7 : R) ≠ 0) :
    period389 (z ^ j) ≠ 0 := by
  apply period389_ne_zero_of_seventh_root (z ^ j) _
    (hz.pow_ne_one_of_pos_of_lt hj0 hj7) h7
  rw [← pow_mul, Nat.mul_comm, pow_mul, hz.pow_eq_one, one_pow]

/-- All six nontrivial characters of a cyclic group of order seven. -/
theorem period433_pow_ne_zero (z : R) (hz : IsPrimitiveRoot z 7)
    (j : ℕ) (hj0 : j ≠ 0) (hj7 : j < 7) (h7 : (7 : R) ≠ 0) :
    period433 (z ^ j) ≠ 0 := by
  apply period433_ne_zero_of_seventh_root (z ^ j) _
    (hz.pow_ne_one_of_pos_of_lt hj0 hj7) h7
  rw [← pow_mul, Nat.mul_comm, pow_mul, hz.pow_eq_one, one_pow]

/-- All six evaluations are integral units when seven is an integral unit. -/
theorem period389_pow_isUnit (z : R) (hz : IsPrimitiveRoot z 7)
    (j : ℕ) (hj0 : j ≠ 0) (hj7 : j < 7) (h7 : IsUnit (7 : R)) :
    IsUnit (period389 (z ^ j)) := by
  apply period389_isUnit_of_phi7 _ _ h7
  apply phi7_eq_zero_of_seventh_root _ _ (hz.pow_ne_one_of_pos_of_lt hj0 hj7)
  rw [← pow_mul, Nat.mul_comm, pow_mul, hz.pow_eq_one, one_pow]

/-- All six evaluations are integral units when seven is an integral unit. -/
theorem period433_pow_isUnit (z : R) (hz : IsPrimitiveRoot z 7)
    (j : ℕ) (hj0 : j ≠ 0) (hj7 : j < 7) (h7 : IsUnit (7 : R)) :
    IsUnit (period433 (z ^ j)) := by
  apply period433_isUnit_of_phi7 _ _ h7
  apply phi7_eq_zero_of_seventh_root _ _ (hz.pow_ne_one_of_pos_of_lt hj0 hj7)
  rw [← pow_mul, Nat.mul_comm, pow_mul, hz.pow_eq_one, one_pow]

theorem period389_primitive_conjugateProduct_eq_49 (z : R)
    (hz : IsPrimitiveRoot z 7) : conjugateProduct period389 z = 49 :=
  period389_conjugateProduct_eq_49 z
    (phi7_eq_zero_of_seventh_root z hz.pow_eq_one (hz.ne_one (by norm_num)))

theorem period433_primitive_conjugateProduct_eq_49 (z : R)
    (hz : IsPrimitiveRoot z 7) : conjugateProduct period433 z = 49 :=
  period433_conjugateProduct_eq_49 z
    (phi7_eq_zero_of_seventh_root z hz.pow_eq_one (hz.ne_one (by norm_num)))

end Domain

end BSDCMPeriods
