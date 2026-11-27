module

public import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# Nonvanishing of the completed L-function and the primitive root number

The pinned Mathlib proves nonvanishing of the ordinary L-function and the functional equation.
These two consequences supply the interface used by the project on Lean 4.35.
-/

public section

namespace DirichletCharacter
variable {N : ℕ} [NeZero N]

/-- Nonvanishing of the completed L-function on the closed right half-plane. -/
theorem completedLFunction_ne_zero_of_one_le_re (χ : DirichletCharacter ℂ N) {s : ℂ}
    (hχs : χ ≠ 1 ∨ s ≠ 1) (hs : 1 ≤ s.re) : completedLFunction χ s ≠ 0 := by
  intro hz
  apply LFunction_ne_zero_of_one_le_re χ hχs hs
  have hs0 : s ≠ 0 := by rintro rfl; norm_num at hs
  rw [LFunction_eq_completed_div_gammaFactor χ s (.inl hs0), hz, zero_div]

/-- The functional equation at −1 expresses the nonzero value at 2 as a multiple
of the primitive character's root number. -/
theorem rootNumber_ne_zero {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) :
    χ.rootNumber ≠ 0 := by
  intro hz
  have h := hχ.completedLFunction_one_sub (-1)
  rw [hz, mul_zero, zero_mul] at h
  apply completedLFunction_ne_zero_of_one_le_re χ (s := 2) (.inr (by norm_num)) (by norm_num)
  convert h using 1
  norm_num

end DirichletCharacter
