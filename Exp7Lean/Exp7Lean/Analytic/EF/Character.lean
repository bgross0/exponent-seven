import Exp7Lean.Analytic.EF.Defs

/-!
# Explicit formula blueprint: the character `chi q`

Nodes **L1a** (proved) and leaves **L1b–L1d** of `BLUEPRINT.md`.  All are short Mathlib-only facts about the quadratic
character modulo a prime `q ≡ 3 (mod 4)`.
-/

namespace Exp7.EF

variable (q : ℕ) [Fact q.Prime]

/-- **L1a** (proved). `chi q` takes the values of the Legendre symbol. -/
theorem chi_apply_natCast (n : ℕ) : chi q (n : ZMod q) = (legendreSym q n : ℂ) := by
  simp [chi, legendreSym]

/-- Helper for L1b–L1d: `q % 4 = 3` forces odd characteristic for `ZMod q`. -/
private theorem ringChar_zmod_ne_two_of_mod_four (hq : q % 4 = 3) : ringChar (ZMod q) ≠ 2 := by
  rw [ZMod.ringChar_zmod_n]
  rintro rfl
  omega

/-- **L1b** (S). `chi q` is not the trivial character (it takes the value `-1`).
Entry points: `quadraticChar_exists_neg_one` (needs `ringChar (ZMod q) ≠ 2`, i.e. `q ≠ 2`,
which follows from `q % 4 = 3`), `ZMod.ringChar_zmod_n`. -/
theorem chi_ne_one (hq : q % 4 = 3) : chi q ≠ 1 := by
  intro h
  obtain ⟨a, ha⟩ := quadraticChar_exists_neg_one' (ringChar_zmod_ne_two_of_mod_four q hq)
  have h1 : chi q (a : ZMod q) = 1 := by rw [h, MulChar.one_apply_coe]
  have h2 : chi q (a : ZMod q) = -1 := by
    simp [chi, ha]
  rw [h2] at h1
  norm_num at h1

/-- **L1c** (M). `chi q` is primitive: its conductor divides the prime `q` and is not `1`.
Entry points: `DirichletCharacter.conductor_dvd_level`, `DirichletCharacter.isPrimitive_def`,
`DirichletCharacter.conductor_eq_one_iff` / `eq_one_iff_conductor_eq_one`, `Nat.Prime.eq_one_or_self_of_dvd`. -/
theorem chi_isPrimitive (hq : q % 4 = 3) : (chi q).IsPrimitive := by
  have : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  rw [DirichletCharacter.isPrimitive_def]
  rcases (Fact.out : q.Prime).eq_one_or_self_of_dvd _
      (DirichletCharacter.conductor_dvd_level (chi q)) with h | h
  · exact absurd (DirichletCharacter.eq_one_iff_conductor_eq_one.mpr h) (chi_ne_one q hq)
  · exact h

/-- **L1d** (S). `chi q` is odd: `χ(-1) = (-1/q) = -1` for `q ≡ 3 (mod 4)`.
Entry points: `quadraticChar_neg_one`, `ZMod.χ₄_nat_three_mod_four`, `ZMod.card`. -/
theorem chi_odd (hq : q % 4 = 3) : (chi q).Odd := by
  have h : quadraticChar (ZMod q) (-1) = -1 := by
    rw [quadraticChar_neg_one (ringChar_zmod_ne_two_of_mod_four q hq), ZMod.card,
      ZMod.χ₄_nat_three_mod_four hq]
  simp [DirichletCharacter.Odd, chi, h]

end Exp7.EF
