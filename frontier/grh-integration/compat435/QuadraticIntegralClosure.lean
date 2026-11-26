import Mathlib

/-!
Lean 4.35 compatibility proof for exponent-seven's prime-discriminant order.
Adapted from Mathlib 31ce06ea, QuadraticAlgebra/Integral.lean and /Int.lean,
Copyright (c) 2026 Xavier Roblot, Apache-2.0.
Only squarefree discriminants are needed here. No assumption is introduced.
-/

namespace Exp7.Compat435
open QuadraticAlgebra

section General
variable {R K : Type*} [CommRing R] [CommRing K] [Algebra R K] {a b : K}
  {z : QuadraticAlgebra K a b}

def starAlgEquiv : QuadraticAlgebra K a b ≃ₐ[K] QuadraticAlgebra K a b where
  __ := starRingAut
  commutes' _ := by ext <;> simp

theorem isIntegral_star_iff :
    IsIntegral R (star z) ↔ IsIntegral R z :=
  isIntegral_algEquiv (starAlgEquiv.restrictScalars R) (x := z)

open Polynomial in
theorem isIntegral_of_trace_mem_range_of_norm_mem_range
    (ht : trace z ∈ Set.range (algebraMap R K))
    (hn : norm z ∈ Set.range (algebraMap R K)) : IsIntegral R z := by
  obtain ⟨t, ht⟩ := ht
  obtain ⟨n, hn⟩ := hn
  refine ⟨X ^ 2 - C t * X + C n, by monicity!, ?_⟩
  simp [IsScalarTower.algebraMap_apply R K (QuadraticAlgebra K a b), ht, hn,
    ← Algebra.smul_def, sq_sub_trace_smul_add_norm_eq_zero]

theorem isIntegral_omega (ha : a ∈ Set.range (algebraMap R K))
    (hb : b ∈ Set.range (algebraMap R K)) :
    IsIntegral R (ω : QuadraticAlgebra K a b) := by
  obtain ⟨a, rfl⟩ := ha
  obtain ⟨b, rfl⟩ := hb
  exact isIntegral_of_trace_mem_range_of_norm_mem_range ⟨b, by simp⟩ ⟨-a, by simp [norm_def]⟩

variable [IsIntegrallyClosedIn R K]

theorem trace_mem_range_of_isIntegral (hz : IsIntegral R z) :
    trace z ∈ Set.range (algebraMap R K) :=
  IsIntegrallyClosedIn.isIntegral_iff.mp <|
    (algebraMap_trace_eq_add_star z ▸ hz.add (isIntegral_star_iff.mpr hz)).tower_bot
      algebraMap_injective

theorem norm_mem_range_of_isIntegral (hz : IsIntegral R z) :
    norm z ∈ Set.range (algebraMap R K) :=
  IsIntegrallyClosedIn.isIntegral_iff.mp <|
    (algebraMap_norm_eq_mul_star z ▸ hz.mul (isIntegral_star_iff.mpr hz)).tower_bot
      algebraMap_injective

theorem re_mem_range_of_im_mem_range (ha : a ∈ Set.range (algebraMap R K))
    (hb : b ∈ Set.range (algebraMap R K)) (h : IsIntegral R z)
    (him : z.im ∈ Set.range (algebraMap R K)) : z.re ∈ Set.range (algebraMap R K) := by
  obtain ⟨m, hm⟩ := him
  have : IsIntegral R (z - m • ω) := h.sub ((isIntegral_omega ha hb).smul _)
  rwa [← re_smul_add_im_smul z, ← hm, algebraMap_smul, add_sub_cancel_right,
    ← Algebra.algebraMap_eq_smul_one, ← IsScalarTower.coe_toAlgHom' R K,
    isIntegral_algHom_iff _ algebraMap_injective, IsIntegrallyClosedIn.isIntegral_iff] at this

end General

variable {a b : ℤ}

theorem im_den_smul_mem {z : QuadraticAlgebra ℚ a b} (hz : IsIntegral ℤ z) :
    (z.im.den : ℤ) • z ∈
      Set.range (algebraMap (QuadraticAlgebra ℤ a b) (QuadraticAlgebra ℚ a b)) := by
  have hi : ((z.im.den : ℤ) • z).im ∈ Set.range (algebraMap ℤ ℚ) := by simp
  obtain ⟨v, hv⟩ := hi
  obtain ⟨u, hu⟩ := re_mem_range_of_im_mem_range
    (R := ℤ) (K := ℚ) ⟨a, rfl⟩ ⟨b, rfl⟩ (hz.zsmul _) ⟨v, hv⟩
  exact ⟨⟨u, v⟩, by ext <;> simp_all⟩

theorem denominator_sq_dvd_discr {z : QuadraticAlgebra ℚ a b} (hz : IsIntegral ℤ z) :
    (z.im.den : ℤ) ^ 2 ∣ discr a b := by
  obtain ⟨x, hx⟩ := im_den_smul_mem hz
  obtain ⟨t, ht⟩ := trace_mem_range_of_isIntegral hz
  obtain ⟨n, hn⟩ := norm_mem_range_of_isIntegral hz
  have him : (x.im : ℚ) = (z.im.den : ℤ) • z.im := by
    simpa using congrArg QuadraticAlgebra.im hx
  have himnum : x.im = z.im.num := by
    simpa using congrArg QuadraticAlgebra.im hx
  have heq : discr a b * x.im ^ 2 = (z.im.den : ℤ) ^ 2 * (t ^ 2 - 4 * n) := by
    apply Int.cast_injective (α := ℚ)
    push_cast
    rw [him]
    have htrace : (t : ℚ) = trace z := ht
    have hnorm : (n : ℚ) = norm z := hn
    rw [htrace, hnorm]
    simp only [discr, trace_def, norm_def, zsmul_eq_mul]
    push_cast
    ring
  have hc : IsCoprime (z.im.den : ℤ) x.im := by
    rw [himnum]
    exact (Rat.isCoprime_num_den z.im).symm
  exact hc.pow.dvd_of_dvd_mul_right ⟨_, heq⟩

theorem isIntegralClosure_of_squarefree_discr (hs : Squarefree (discr a b)) :
    IsIntegralClosure (QuadraticAlgebra ℤ a b) ℤ (QuadraticAlgebra ℚ a b) where
  algebraMap_injective := FaithfulSMul.algebraMap_injective _ _
  isIntegral_iff := by
    intro z
    constructor
    · intro hz
      have hu : IsUnit (z.im.den : ℤ) :=
        hs _ (by simpa [pow_two] using denominator_sq_dvd_discr hz)
      have hd : z.im.den = 1 := by
        have hp := z.im.den_pos
        rcases Int.isUnit_iff.mp hu with h | h <;> omega
      simpa [hd] using im_den_smul_mem hz
    · rintro ⟨w, rfl⟩
      exact (Algebra.IsIntegral.isIntegral w).algebraMap

end Exp7.Compat435

#print axioms Exp7.Compat435.isIntegralClosure_of_squarefree_discr

