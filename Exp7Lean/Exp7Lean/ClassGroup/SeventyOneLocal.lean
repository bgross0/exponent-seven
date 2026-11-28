import Exp7Lean.ClassGroup.Converse

/-!
# The principal seventh-power witness at discriminant -71 and its local images

The definitions below use the actual quadratic integer ring `Exp7.OK 71`.
The two algebra maps to `ZMod 25` send its generator to the two roots 12 and
14 of `X^2-X+18`. They turn the principal-power generator `10+omega` into
the units 22 and 24, whose ratio is 3.

This is a local arithmetic input to a prospective ring-class-group argument.
No identification of a nonmaximal order's Picard group or of its CM action
is assumed or asserted here.
-/

namespace Exp7.SeventyOneLocal

open QuadraticAlgebra

local instance : Fact (Nat.Prime 71) := ⟨by norm_num⟩
local instance : Fact (71 % 4 = 3) := ⟨by norm_num⟩

/-- The explicit generator of the seventh power of `(2, omega)`. -/
def alpha : OK 71 := ⟨10, 1⟩

theorem alpha_eq : alpha = 10 + (ω : OK 71) := by
  ext <;> simp [alpha]

theorem norm_alpha : QuadraticAlgebra.norm alpha = 128 := by
  norm_num [alpha, QuadraticAlgebra.norm_def, aOf]

/-- An equality of actual ideals, with no assumed exponent-seven result. -/
theorem ideal_two_seventh_power :
    idealI 71 2 0 ^ 7 = Ideal.span {alpha} := by
  exact idealI_pow_eq_span (q := 71) (by norm_num) (by norm_num)
    (t := 0) (by norm_num [aOf]) 7
    (u := 10) (y := 1) (by norm_num [aOf]) (by norm_num)

/-- The generating ideal has absolute ideal norm two. -/
theorem ideal_two_absNorm : Ideal.absNorm (idealI 71 2 0) = 2 := by
  apply Nat.pow_left_injective (by norm_num : (7 : ℕ) ≠ 0)
  have h := congrArg (fun I : Ideal (OK 71) => Ideal.absNorm I)
    ideal_two_seventh_power
  rw [map_pow, Ideal.absNorm_span_singleton,
    Algebra.norm_quadraticAlgebra_apply, norm_alpha] at h
  norm_num at h ⊢
  exact h

/-- Evaluation at the first root modulo 25. -/
def split12 : OK 71 →ₐ[ℤ] ZMod 25 :=
  QuadraticAlgebra.lift ⟨12, by norm_num [aOf, zsmul_eq_mul]; decide⟩

/-- Evaluation at the conjugate root modulo 25. -/
def split14 : OK 71 →ₐ[ℤ] ZMod 25 :=
  QuadraticAlgebra.lift ⟨14, by norm_num [aOf, zsmul_eq_mul]; decide⟩

@[simp] theorem split12_omega : split12 ω = 12 := by
  simp [split12, QuadraticAlgebra.lift_apply_apply]

@[simp] theorem split14_omega : split14 ω = 14 := by
  simp [split14, QuadraticAlgebra.lift_apply_apply]

/-- Conjugation exchanges the two actual reduction maps. -/
theorem split12_star (z : OK 71) : split12 (star z) = split14 z := by
  have h : split12.comp (QuadraticAlgebra.starAlgEquiv.toAlgHom) = split14 := by
    apply QuadraticAlgebra.algHom_ext
    norm_num [split12, split14, QuadraticAlgebra.lift_apply_apply,
      QuadraticAlgebra.starAlgEquiv, zsmul_eq_mul]
    decide
  exact congrArg (fun f : OK 71 →ₐ[ℤ] ZMod 25 => f z) h

@[simp] theorem split12_alpha : split12 alpha = 22 := by
  norm_num [split12, alpha, QuadraticAlgebra.lift_apply_apply, zsmul_eq_mul]

@[simp] theorem split14_alpha : split14 alpha = 24 := by
  norm_num [split14, alpha, QuadraticAlgebra.lift_apply_apply, zsmul_eq_mul]

/-- The first local image as a unit, with explicit inverse 8. -/
def alpha12 : (ZMod 25)ˣ := ⟨22, 8, by decide, by decide⟩

/-- The conjugate local image as a unit, with explicit inverse 24. -/
def alpha14 : (ZMod 25)ˣ := ⟨24, 24, by decide, by decide⟩

theorem coe_alpha12 : (alpha12 : ZMod 25) = split12 alpha := by
  simp [alpha12]

theorem coe_alpha14 : (alpha14 : ZMod 25) = split12 (star alpha) := by
  rw [split12_star]
  simp [alpha14]

/-- The quotient of the two images of the principal-power generator. -/
def localRatio : (ZMod 25)ˣ := alpha12 / alpha14

theorem coe_localRatio : (localRatio : ZMod 25) = 3 := by
  decide

/-- The same actual unit reduced modulo 5. -/
def residueRatio : (ZMod 5)ˣ :=
  Units.map (ZMod.castHom (by decide : 5 ∣ 25) (ZMod 5)).toMonoidHom localRatio

theorem coe_residueRatio : (residueRatio : ZMod 5) = 3 := by
  decide

/-- The tame part has the full order of the multiplicative group modulo 5. -/
theorem residueRatio_order : orderOf residueRatio = 4 := by
  apply (orderOf_eq_iff (by norm_num : 0 < 4)).2
  constructor
  · decide
  · intro m hm hpos
    interval_cases m <;> decide

/-- Raising to the tame order leaves a nontrivial first principal-unit digit. -/
theorem localRatio_fourth : ((localRatio ^ 4 : (ZMod 25)ˣ) : ZMod 25) = 1 + 5 := by
  decide

theorem localRatio_fourth_ne_one : localRatio ^ 4 ≠ 1 := by
  decide

/-- The local ratio has the full unit-group order modulo 25. -/
theorem localRatio_order : orderOf localRatio = 20 := by
  apply (orderOf_eq_iff (by norm_num : 0 < 20)).2
  constructor
  · decide
  · intro m hm hpos
    interval_cases m <;> decide

end Exp7.SeventyOneLocal
