/-
Copyright (c) 2026 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Adapted from the integer quadratic algebra and fundamental discriminant proofs in
Mathlib 31ce06eaadf4a200c0e1407c5f10953cf606b8f8.
-/
import Exp7Lean.Step1

/-! # Integral closure for negative fundamental discriminants, including even discriminants -/

namespace Exp7.Compat435

open QuadraticAlgebra
variable {a b : ℤ}

theorem four_mul_norm_eq {R : Type*} [CommRing R] {a b : R} (z : QuadraticAlgebra R a b) :
    4 * norm z = trace z ^ 2 - discr a b * z.im ^ 2 := by
  rw [trace_def, norm_def, discr_def]
  ring

private theorem denominator_primitive {z : QuadraticAlgebra ℚ a b} (hz : IsIntegral ℤ z)
    (hfund : Int.IsFundamentalDiscr (discr a b)) : z.im.den = 1 := by
  obtain ⟨x, hx⟩ := im_den_smul_mem hz
  let d : ℤ := z.im.den
  obtain ⟨t, ht⟩ := trace_mem_range_of_isIntegral hz
  obtain ⟨n, hn⟩ := norm_mem_range_of_isIntegral hz
  have him : (x.im : ℚ) = d • z.im := by simpa [d] using congrArg QuadraticAlgebra.im hx
  have h : discr a b * x.im ^ 2 = d ^ 2 * (t ^ 2 - 4 * n) := by
    apply Int.cast_injective (α := ℚ)
    push_cast
    rw [him, show (t : ℚ) = trace z from ht, show (n : ℚ) = norm z from hn]
    simp only [discr, trace_def, norm_def, zsmul_eq_mul]
    push_cast
    ring
  have hd : IsCoprime d x.im := by
    rw [show x.im = z.im.num by simpa using congrArg QuadraticAlgebra.im hx]
    exact (Rat.isCoprime_num_den z.im).symm
  obtain ⟨e, he⟩ : d ^ 2 ∣ discr a b := hd.pow.dvd_of_dvd_mul_right ⟨_, h⟩
  have hemod : e % 4 = 0 ∨ e % 4 = 1 := by
    obtain hd' | hd' := d.even_or_odd
    · have him : Odd x.im :=
        Int.isCoprime_two_left.mp <| IsCoprime.of_isCoprime_of_dvd_left hd hd'.two_dvd
      have hd₀ : d ≠ 0 := Int.natCast_ne_zero.mpr z.im.den_nz
      rw [he, mul_assoc, mul_right_inj' (Int.pow_ne_zero hd₀)] at h
      replace h := congr_arg (· % 4) h
      rw [Int.mul_emod, Int.sq_emod_four, Int.odd_iff.mp him, mul_one, Int.sub_mul_emod_self_left,
        Int.emod_emod, Int.sq_emod_four] at h
      lia
    · replace he := congr_arg (· % 4) he
      rw [Int.mul_emod, Int.sq_emod_four, Int.odd_iff.mp hd', one_mul, Int.emod_emod] at he
      rw [← he, discr_def, Int.add_mul_emod_self_left, Int.sq_emod_four]
      omega
  obtain ⟨k, hk⟩ := z.im.den.minFac_dvd
  by_contra! hm
  refine (Int.isFundamentalDiscr_iff_forall_prime.mp hfund).2 _
    (Nat.minFac_prime hm) ⟨k ^ 2 * e, ?_, ?_⟩
  · rw [← mul_assoc, ← mul_pow, ← Nat.cast_mul, ← hk, he]
  · rw [Int.mul_emod, Int.sq_emod_four]
    grind

theorem isIntegralClosure_of_fundamental (hfund : Int.IsFundamentalDiscr (discr a b)) :
    IsIntegralClosure (QuadraticAlgebra ℤ a b) ℤ (QuadraticAlgebra ℚ a b) where
  algebraMap_injective := FaithfulSMul.algebraMap_injective _ _
  isIntegral_iff := by
    intro z
    constructor
    · intro hz
      simpa [denominator_primitive hz hfund] using im_den_smul_mem hz
    · rintro ⟨w, rfl⟩
      exact (Algebra.IsIntegral.isIntegral w).algebraMap

end Exp7.Compat435
