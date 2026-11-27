import Exp7Lean.ClassGroup.Criterion

/-!
The forward norm equation from principality of one ideal power. Unlike Step 1's
class-group-exponent hypothesis, this applies to an individual ideal class.
The norm calculation follows Step 1 and works for any odd positive exponent.
-/

namespace Exp7

open QuadraticAlgebra

section

variable {q : ℕ} [hq : Fact q.Prime] [h4 : Fact (q % 4 = 3)]

/-- Principality of an odd power of one split prime ideal supplies a nonrational norm witness.
No assumption is made about the other classes. -/
theorem norm_eq_of_principal_odd_power {p n : ℕ} (hp : p.Prime) (hpq : p ≠ q)
    {t : ℤ} (ht : (p : ℤ) ∣ t ^ 2 - t - aOf q) (hn : Odd n)
    (hprincipal : (idealI q p t ^ n).IsPrincipal) :
    ∃ x y : ℕ, 1 ≤ y ∧ 4 * p ^ n = x ^ 2 + q * y ^ 2 := by
  obtain ⟨α, hα⟩ := hprincipal
  have h4a := four_aOf h4.out
  have hprod := idealI_mul_map hp hpq ht
  have hα' : idealI q p t ^ n = Ideal.span {α} := hα
  have hσ : (idealI q p t).map (starRingEnd (OK q)) ^ n = Ideal.span {star α} := by
    rw [← Ideal.map_pow, hα', Ideal.map_span, Set.image_singleton, starRingEnd_apply]
  have hassoc : Ideal.span {α * star α} = Ideal.span {(p : OK q) ^ n} := by
    rw [← Ideal.span_singleton_mul_span_singleton, ← hα', ← hσ, ← mul_pow, hprod,
      Ideal.span_singleton_pow]
  rw [Ideal.span_singleton_eq_span_singleton] at hassoc
  obtain ⟨u, hu⟩ := hassoc
  set m : ℤ := QuadraticAlgebra.norm α with hm
  have hms : algebraMap ℤ (OK q) m = α * star α := algebraMap_norm_eq_mul_star α
  have hnorm := congrArg QuadraticAlgebra.norm hu
  rw [← hms, map_mul, map_pow, QuadraticAlgebra.norm_algebraMap,
    QuadraticAlgebra.norm_natCast] at hnorm
  have hunit : IsUnit (QuadraticAlgebra.norm (u : OK q)) :=
    QuadraticAlgebra.isUnit_iff_norm_isUnit.mp u.isUnit
  have hmdef : m = α.re * α.re + 1 * α.re * α.im - aOf q * α.im * α.im :=
    QuadraticAlgebra.norm_def α
  have hm4 : 4 * m = (2 * α.re + α.im) ^ 2 + q * α.im ^ 2 := by
    linear_combination 4 * hmdef - α.im ^ 2 * h4a
  have hppos : (0 : ℤ) < (p : ℤ) ^ n := pow_pos (by exact_mod_cast hp.pos) n
  have hmn : 0 ≤ m := by
    nlinarith [sq_nonneg (2 * α.re + α.im), sq_nonneg α.im,
      (Nat.cast_nonneg q : (0 : ℤ) ≤ q)]
  have hmp : m = (p : ℤ) ^ n := by
    rcases Int.isUnit_iff.mp hunit with he | he
    · rw [he, mul_one] at hnorm
      have h0 : (m - (p : ℤ) ^ n) * (m + (p : ℤ) ^ n) = 0 := by
        linear_combination hnorm
      rcases mul_eq_zero.mp h0 with h1 | h1 <;> linarith
    · rw [he] at hnorm
      have hpos : (0 : ℤ) < ((p : ℤ) ^ 2) ^ n :=
        pow_pos (pow_pos (by exact_mod_cast hp.pos) 2) n
      nlinarith [sq_nonneg m]
  have hy : α.im ≠ 0 := by
    intro hy0
    rw [hy0] at hm4
    have hsq : (α.re.natAbs : ℤ) ^ 2 = (p : ℤ) ^ n := by
      rw [Int.natAbs_sq]; linarith
    have hsqN : α.re.natAbs ^ 2 = p ^ n := by exact_mod_cast hsq
    have := Fact.mk hp
    have hval := congrArg (multiplicity p) hsqN
    rw [Nat.multiplicity_pow, Nat.multiplicity_prime_pow] at hval
    obtain ⟨k, hk⟩ := hn
    omega
  refine ⟨(2 * α.re + α.im).natAbs, α.im.natAbs, Int.natAbs_pos.mpr hy, ?_⟩
  have he : ((4 * p ^ n : ℕ) : ℤ) =
      ((((2 * α.re + α.im).natAbs ^ 2 + q * α.im.natAbs ^ 2) : ℕ) : ℤ) := by
    push_cast
    rw [sq_abs, sq_abs, ← hm4, hmp]
  exact_mod_cast he

/-- The same local norm consequence, expressed directly in Mathlib's class group. -/
theorem norm_eq_of_class_pow_eq_one {p n : ℕ} (hp : p.Prime) (hpq : p ≠ q)
    {t : ℤ} (ht : (p : ℤ) ∣ t ^ 2 - t - aOf q) (hn : Odd n)
    (hc : classOf q p hp.ne_zero t ^ n = 1) :
    ∃ x y : ℕ, 1 ≤ y ∧ 4 * p ^ n = x ^ 2 + q * y ^ 2 :=
  norm_eq_of_principal_odd_power hp hpq ht hn ((classOf_pow_eq_one_iff hp.ne_zero t n).mp hc)

end
end Exp7
