import Mathlib.Data.Int.ModEq
import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.Tactic

/-! Exact compression of the square-root congruence from modulus 8*y^2 to period 2*y^2.
All variables are integers. The congruence lemmas include y = 0.
-/

namespace Exp7.RootPeriod

lemma square_mod_two (x : ℤ) : x ^ 2 ≡ x [ZMOD 2] := by
  obtain ⟨k, hk⟩ := Int.two_dvd_mul_add_one x
  apply Int.modEq_iff_dvd.mpr
  refine ⟨x - k, ?_⟩
  calc
    x - x ^ 2 = 2 * x - x * (x + 1) := by ring
    _ = 2 * (x - k) := by rw [hk]; ring

/-- Every root in the original modulus has the parity needed for the smaller period. -/
theorem parity_of_root {x y p : ℤ}
    (h : x ^ 2 + 3 * y ^ 2 ≡ 4 * p ^ 7 [ZMOD 8 * y ^ 2]) :
    x ≡ y [ZMOD 2] := by
  have h2 : x ^ 2 + 3 * y ^ 2 ≡ 4 * p ^ 7 [ZMOD 2] :=
    h.of_dvd ⟨4 * y ^ 2, by ring⟩
  have hleft : x ^ 2 + 3 * y ^ 2 ≡ x + y [ZMOD 2] := by
    apply (square_mod_two x).add
    exact ((square_mod_two y).mul_left 3).trans
      (Int.modEq_iff_dvd.mpr ⟨-y, by ring⟩)
  have hright : 4 * p ^ 7 ≡ 0 [ZMOD 2] :=
    Int.modEq_zero_iff_dvd.mpr ⟨2 * p ^ 7, by ring⟩
  have hz := hleft.symm.trans (h2.trans hright)
  obtain ⟨k, hk⟩ := Int.modEq_iff_dvd.mp hz
  exact Int.modEq_iff_dvd.mpr ⟨y + k, by linarith⟩

/-- A translation by 2*y^2 changes the square by a multiple of 8*y^2. -/
theorem square_shift_dvd {x y : ℤ} (hxy : x ≡ y [ZMOD 2]) (t : ℤ) :
    8 * y ^ 2 ∣ (x + 2 * y ^ 2 * t) ^ 2 - x ^ 2 := by
  obtain ⟨k, hk⟩ := Int.modEq_iff_dvd.mp hxy
  obtain ⟨m, hm⟩ := Int.two_dvd_mul_add_one (y * t)
  refine ⟨m - k * t, ?_⟩
  calc
    (x + 2 * y ^ 2 * t) ^ 2 - x ^ 2 =
        4 * y ^ 2 * ((y * t) * (y * t + 1) - (y - x) * t) := by ring
    _ = (8 * y ^ 2) * (m - k * t) := by rw [hk, hm]; ring

theorem root_shift {x y p : ℤ}
    (h : x ^ 2 + 3 * y ^ 2 ≡ 4 * p ^ 7 [ZMOD 8 * y ^ 2]) (t : ℤ) :
    (x + 2 * y ^ 2 * t) ^ 2 + 3 * y ^ 2 ≡ 4 * p ^ 7 [ZMOD 8 * y ^ 2] :=
  ((Int.modEq_iff_dvd.mpr (square_shift_dvd (parity_of_root h) t)).add_right
    (3 * y ^ 2)).symm.trans h

/-- The full root predicate, without a parity precondition, has period 2*y^2. -/
theorem root_shift_iff (x y p t : ℤ) :
    ((x + 2 * y ^ 2 * t) ^ 2 + 3 * y ^ 2 ≡ 4 * p ^ 7 [ZMOD 8 * y ^ 2]) ↔
      (x ^ 2 + 3 * y ^ 2 ≡ 4 * p ^ 7 [ZMOD 8 * y ^ 2]) := by
  constructor
  · intro h
    have hh := root_shift h (-t)
    convert hh using 1 <;> ring
  · exact fun h => root_shift h t

/-- Reduction modulo the shorter period preserves the original root condition. -/
theorem root_remainder_iff (x y p : ℤ) :
    ((x % (2 * y ^ 2)) ^ 2 + 3 * y ^ 2 ≡ 4 * p ^ 7 [ZMOD 8 * y ^ 2]) ↔
      (x ^ 2 + 3 * y ^ 2 ≡ 4 * p ^ 7 [ZMOD 8 * y ^ 2]) := by
  have h := root_shift_iff (x % (2 * y ^ 2)) y p (x / (2 * y ^ 2))
  have he : x % (2 * y ^ 2) + 2 * y ^ 2 * (x / (2 * y ^ 2)) = x := by
    simpa [mul_comm] using Int.emod_add_ediv_mul x (2 * y ^ 2)
  rw [he] at h
  exact h.symm

/-- Every root has a representative in the compressed range when y is positive. -/
theorem exists_compressed_root {x y p : ℤ} (hy : 0 < y)
    (h : x ^ 2 + 3 * y ^ 2 ≡ 4 * p ^ 7 [ZMOD 8 * y ^ 2]) :
    ∃ r t : ℤ, 0 ≤ r ∧ r < 2 * y ^ 2 ∧ x = r + 2 * y ^ 2 * t ∧
      (r ^ 2 + 3 * y ^ 2 ≡ 4 * p ^ 7 [ZMOD 8 * y ^ 2]) := by
  have hm : (0 : ℤ) < 2 * y ^ 2 := by positivity
  refine ⟨x % (2 * y ^ 2), x / (2 * y ^ 2), Int.emod_nonneg _ hm.ne',
    Int.emod_lt_of_pos _ hm, ?_, (root_remainder_iff x y p).mpr h⟩
  simpa [mul_comm] using (Int.emod_add_ediv_mul x (2 * y ^ 2)).symm

end Exp7.RootPeriod

#print axioms Exp7.RootPeriod.parity_of_root
#print axioms Exp7.RootPeriod.square_shift_dvd
#print axioms Exp7.RootPeriod.root_shift_iff
#print axioms Exp7.RootPeriod.exists_compressed_root

