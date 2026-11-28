import Exp7Lean.ClassGroup.Criterion
import Exp7Lean.ClassGroup.GenBoundProof
import Exp7Lean.ClassGroup.SeventyOneLocal

/-!
# The actual class group of discriminant -71

The ideal class of `(2, ω)` generates `ClassGroup (OK 71)` and has order seven.
This proof uses the existing sharp generation bound, the norm-24 relation
`Norm (2 + ω) = 24`, and the explicit equality `(2, ω)^7 = (10 + ω)`.
It does not use the exponent-seven classification or the known-field table.

The ring is the existing maximal quadratic order `OK 71`, with
`ω² = ω - 18`. No statement about nonmaximal ring-class Picard groups is
inferred here.
-/

namespace Exp7.K71

open QuadraticAlgebra
open scoped nonZeroDivisors

local instance : Fact (Nat.Prime 71) := ⟨by norm_num⟩
local instance : Fact (71 % 4 = 3) := ⟨by norm_num⟩

/-- The actual ideal class of `(2, ω)` in the maximal order of discriminant -71. -/
noncomputable def twoClass : ClassGroup (OK 71) := classOf 71 2 (by norm_num) 0

/-- The actual ideal class of `(3, ω)` in the same maximal order. -/
noncomputable def threeClass : ClassGroup (OK 71) := classOf 71 3 (by norm_num) 0

private lemma classOf_mod (m : ℕ) (hm : m ≠ 0) (t : ℤ) :
    classOf 71 m hm t = classOf 71 m hm (t % (m : ℤ)) := by
  apply classOf_congr
  have ht : t = t % (m : ℤ) + (t / (m : ℤ)) * m := by
    simpa [mul_comm] using (Int.emod_add_mul_ediv t (m : ℤ)).symm
  conv_lhs => rw [ht]
  exact idealI_shift m (t % (m : ℤ)) (t / (m : ℤ))

private lemma map_star_idealI_eq (m : ℕ) (t : ℤ) :
    (idealI 71 m t).map (starRingEnd (OK 71)) = idealI 71 m (1 - t) := by
  rw [map_star_idealI]
  have he : (1 - ω - (t : OK 71)) = -(ω - ((1 - t : ℤ) : OK 71)) := by
    push_cast
    ring
  apply le_antisymm
  · rw [Ideal.span_le]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact natCast_mem_idealI m (1 - t)
    · rw [he]
      exact (Ideal.neg_mem_iff _).mpr (omega_sub_mem_idealI m (1 - t))
  · apply idealI_le
    · exact Ideal.subset_span (by simp)
    · have he' : (ω - ((1 - t : ℤ) : OK 71)) = -(1 - ω - (t : OK 71)) := by
        push_cast
        ring
      rw [he']
      exact (Ideal.neg_mem_iff _).mpr (Ideal.subset_span (by simp))

private lemma classOf_conjugate {l : ℕ} (hl : l.Prime) (hlq : l ≠ 71) {t : ℤ}
    (ht : (l : ℤ) ∣ t ^ 2 - t - aOf 71) :
    classOf 71 l hl.ne_zero (1 - t) = (classOf 71 l hl.ne_zero t)⁻¹ := by
  have hprod : classOf 71 l hl.ne_zero (1 - t) * classOf 71 l hl.ne_zero t = 1 := by
    rw [mul_comm]
    unfold classOf
    rw [← map_mul, ClassGroup.mk0_eq_one_iff]
    change (idealI 71 l t * idealI 71 l (1 - t)).IsPrincipal
    rw [← map_star_idealI_eq, idealI_mul_map hl hlq ht]
    exact ⟨⟨_, rfl⟩⟩
  exact eq_inv_of_mul_eq_one_left hprod

/-- The norm-two ideal class is killed by seven. -/
theorem twoClass_pow_seven : twoClass ^ 7 = 1 := by
  rw [twoClass, classOf_pow_eq_one_iff, SeventyOneLocal.ideal_two_seventh_power]
  exact ⟨⟨_, rfl⟩⟩

/-- The norm-two ideal class is nontrivial. -/
theorem twoClass_ne_one : twoClass ≠ 1 := by
  exact classOf_ne_one (by norm_num) (by norm_num [aOf]) (by norm_num)

/-- The norm-two ideal class has exact order seven. -/
theorem twoClass_order : orderOf twoClass = 7 := by
  let : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  exact orderOf_eq_prime twoClass_pow_seven twoClass_ne_one

/-- The class of `(3, ω)` is the cube of the class of `(2, ω)`.
The principal ideal `(2 + ω)` of norm 24 supplies the relation. -/
theorem threeClass_eq_twoClass_cube : threeClass = twoClass ^ 3 := by
  have h24 : classOf 71 24 (by norm_num) (-2) = 1 := by
    apply classOf_eq_one
    rw [idealI_norm (by norm_num [aOf])]
    exact ⟨⟨_, rfl⟩⟩
  have h83 : classOf 71 24 (by norm_num) (-2) =
      classOf 71 8 (by norm_num) (-2) * classOf 71 3 (by norm_num) (-2) :=
    classOf_mul (q := 71) (m := 8) (n := 3) (t := -2)
      (by norm_num) (by norm_num) (by norm_num [aOf])
  have h24' : classOf 71 8 (by norm_num) (-2) =
      classOf 71 2 (by norm_num) (-2) * classOf 71 4 (by norm_num) (-2) :=
    classOf_mul (q := 71) (m := 2) (n := 4) (t := -2)
      (by norm_num) (by norm_num) (by norm_num [aOf])
  have h22 : classOf 71 4 (by norm_num) (-2) =
      classOf 71 2 (by norm_num) (-2) * classOf 71 2 (by norm_num) (-2) :=
    classOf_mul (q := 71) (m := 2) (n := 2) (t := -2)
      (by norm_num) (by norm_num) (by norm_num [aOf])
  have h2 : classOf 71 2 (by norm_num) (-2) = twoClass := by
    rw [classOf_mod]
    rfl
  have h3 : classOf 71 3 (by norm_num) (-2) = threeClass⁻¹ := by
    rw [classOf_mod]
    simpa [threeClass] using
      (classOf_conjugate (l := 3) (t := 0) (by norm_num) (by norm_num) (by norm_num [aOf]))
  rw [h83, h24', h22, h2, h3] at h24
  have he : twoClass * (twoClass * twoClass) = threeClass := by
    simpa using eq_inv_of_mul_eq_one_left h24
  simpa [pow_succ, pow_two, mul_assoc] using he.symm

private lemma classOf_two_mem (t : ℤ) :
    classOf 71 2 (by norm_num) t ∈ Subgroup.zpowers twoClass := by
  rw [classOf_mod]
  norm_num only [Nat.cast_ofNat]
  rcases Int.emod_two_eq_zero_or_one t with ht | ht
  · rw [ht]
    exact ⟨1, by simp [twoClass]⟩
  · rw [ht]
    have hc : classOf 71 2 (by norm_num) 1 = twoClass⁻¹ := by
      simpa [twoClass] using
        (classOf_conjugate (l := 2) (t := 0) (by norm_num) (by norm_num) (by norm_num [aOf]))
    rw [hc]
    exact (Subgroup.zpowers twoClass).inv_mem ⟨1, by simp⟩

private lemma classOf_three_mem (t : ℤ) (ht : (3 : ℤ) ∣ t ^ 2 - t - aOf 71) :
    classOf 71 3 (by norm_num) t ∈ Subgroup.zpowers twoClass := by
  have hroot : (t ^ 2 - t + 18) % 3 = 0 := by
    exact Int.emod_eq_zero_of_dvd (by simpa [aOf] using ht)
  have hres : t % 3 = 0 ∨ t % 3 = 1 := by
    have hlo := Int.emod_nonneg t (by norm_num : (3 : ℤ) ≠ 0)
    have hhi := Int.emod_lt_of_pos t (by norm_num : (0 : ℤ) < 3)
    have hne : t % 3 ≠ 2 := by
      intro h2
      norm_num [pow_two, Int.add_emod, Int.sub_emod, Int.mul_emod, h2] at hroot
    omega
  have hmem : threeClass ∈ Subgroup.zpowers twoClass := by
    rw [threeClass_eq_twoClass_cube]
    exact (Subgroup.zpowers twoClass).pow_mem ⟨1, by simp⟩ 3
  rw [classOf_mod]
  norm_num only [Nat.cast_ofNat]
  rcases hres with ht0 | ht1
  · rw [ht0]
    exact hmem
  · rw [ht1]
    have hc : classOf 71 3 (by norm_num) 1 = threeClass⁻¹ := by
      simpa [threeClass] using
        (classOf_conjugate (l := 3) (t := 0) (by norm_num) (by norm_num) (by norm_num [aOf]))
    rw [hc]
    exact (Subgroup.zpowers twoClass).inv_mem hmem

/-- Every actual ideal class is a power of the class of `(2, ω)`. -/
theorem twoClass_generates : Subgroup.zpowers twoClass = ⊤ := by
  have hg : GenBound 71 4 := by
    have hs : Nat.sqrt (71 / 3) = 4 := by norm_num
    simpa only [hs] using genBound_sqrt_div_three 71
  unfold GenBound at hg
  apply top_unique
  rw [← hg]
  rw [Subgroup.closure_le]
  rintro c ⟨l, hl, t, hl4, ht, rfl⟩
  have hl23 : l = 2 ∨ l = 3 := by
    have hlo := hl.two_le
    interval_cases l <;> norm_num at *
  rcases hl23 with rfl | rfl
  · exact classOf_two_mem t
  · exact classOf_three_mem t ht

/-- The actual maximal-order class group has seven elements. -/
theorem class_number_seven : Nat.card (ClassGroup (OK 71)) = 7 := by
  rw [← orderOf_eq_card_of_zpowers_eq_top twoClass_generates]
  exact twoClass_order

/-- The actual maximal-order class group is cyclic. -/
theorem class_group_cyclic : IsCyclic (ClassGroup (OK 71)) :=
  isCyclic_iff_exists_zpowers_eq_top.mpr ⟨twoClass, twoClass_generates⟩

/-- Cyclic coordinates on the actual class group, with the norm-two class
as the specified generator. This does not identify any CM evaluations. -/
noncomputable def cyclicCoordinates :
    Multiplicative (ZMod 7) ≃* ClassGroup (OK 71) :=
  zmodMulEquivOfGenerator (g := twoClass)
    (fun c => twoClass_generates.ge (Subgroup.mem_top c)) class_number_seven

/-- The cyclic coordinate one is the actual ideal class of `(2, ω)`. -/
theorem cyclicCoordinates_one :
    cyclicCoordinates (Multiplicative.ofAdd 1) = twoClass := by
  simp [cyclicCoordinates]

/-- All cyclic coordinates agree with integer powers of the specified class. -/
theorem cyclicCoordinates_intCast (n : ℤ) :
    cyclicCoordinates (Multiplicative.ofAdd (n : ZMod 7)) = twoClass ^ n := by
  simp [cyclicCoordinates]

end Exp7.K71
