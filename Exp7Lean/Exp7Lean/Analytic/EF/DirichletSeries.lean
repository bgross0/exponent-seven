import Exp7Lean.Analytic.EF.Character

/-!
# Explicit formula blueprint: the Dirichlet series of `-L'/L`

Leaves **D1, D2** of `BLUEPRINT.md`.  Mathlib provides everything:
`DirichletCharacter.LSeries_twist_vonMangoldt_eq`, `LSeriesSummable_twist_vonMangoldt`,
`DirichletCharacter.LFunction_eq_LSeries`, `deriv_LFunction_eq_deriv_LSeries`,
`ArithmeticFunction.LSeriesSummable_vonMangoldt`.
-/

namespace Exp7.EF

open Complex

variable (q : ℕ) [Fact q.Prime]

/-- `coeff q 0 = 0` because `Λ(0) = 0`. -/
private lemma coeff_zero : coeff q 0 = 0 := by
  simp [coeff]

/-- `|Λ(n) χ(n)| ≤ Λ(n)` since the Legendre symbol takes values in `{-1, 0, 1}`. -/
private lemma abs_coeff_le (n : ℕ) : |coeff q n| ≤ ArithmeticFunction.vonMangoldt n := by
  have hΛ : (0 : ℝ) ≤ ArithmeticFunction.vonMangoldt n := ArithmeticFunction.vonMangoldt_nonneg
  have hχ : |(legendreSym q n : ℝ)| ≤ 1 := by
    have hdef : legendreSym q n = quadraticChar (ZMod q) ((n : ℤ) : ZMod q) := rfl
    rcases quadraticChar_isQuadratic (ZMod q) ((n : ℤ) : ZMod q) with h | h | h <;>
      rw [hdef, h] <;> simp
  calc |coeff q n| = ArithmeticFunction.vonMangoldt n * |(legendreSym q n : ℝ)| := by
        rw [coeff, abs_mul, abs_of_nonneg hΛ]
    _ ≤ ArithmeticFunction.vonMangoldt n * 1 := mul_le_mul_of_nonneg_left hχ hΛ
    _ = ArithmeticFunction.vonMangoldt n := mul_one _

/-- **D1** (S). `∑ₙ Λ(n) n^{-1/2-δ} < ∞` for `δ > 1/2` (hence `∑ₙ |coeff q n| n^{-1/2-δ} < ∞`). -/
theorem summable_abs_coeff_mul_rpow {δ : ℝ} (hδ : 1 / 2 < δ) :
    Summable (fun n : ℕ ↦ |coeff q n| * (n : ℝ) ^ (-(1 / 2 : ℝ) - δ)) := by
  have hs : 1 < (((1 / 2 + δ : ℝ) : ℂ)).re := by
    rw [Complex.ofReal_re]; linarith
  have h := (ArithmeticFunction.LSeriesSummable_vonMangoldt hs).norm
  refine h.of_nonneg_of_le (fun n ↦ by positivity) fun n ↦ ?_
  rw [LSeries.norm_term_eq]
  rcases eq_or_ne n 0 with rfl | hn
  · simp [coeff_zero]
  · have hexp : -(1 / 2 : ℝ) - δ = -(1 / 2 + δ) := by ring
    rw [ite_eq_right hn, Complex.ofReal_re, hexp, Real.rpow_neg (Nat.cast_nonneg n),
      ← div_eq_mul_inv]
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    rw [Complex.norm_real, Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    exact abs_coeff_le q n

/-- Real part of the `n`-th term of the Dirichlet series of `χ·Λ` at `s = 1/2 + δ + it`. -/
private lemma re_term_twist (δ t : ℝ) (n : ℕ) :
    (LSeries.term ((fun n : ℕ ↦ chi q (n : ZMod q)) *
        (fun n : ℕ ↦ (ArithmeticFunction.vonMangoldt n : ℂ)))
        (((1 / 2 + δ : ℝ) : ℂ) + (t : ℂ) * I) n).re =
      coeff q n * (n : ℝ) ^ (-(1 / 2 : ℝ) - δ) * Real.cos (t * Real.log n) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [coeff_zero]
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hcoe : chi q (n : ZMod q) * (ArithmeticFunction.vonMangoldt n : ℂ) =
      ((coeff q n : ℝ) : ℂ) := by
    rw [chi_apply_natCast, coeff]; push_cast; ring
  have hpow : ((n : ℂ) ^ (-(((1 / 2 + δ : ℝ) : ℂ) + (t : ℂ) * I))).re =
      (n : ℝ) ^ (-(1 / 2 : ℝ) - δ) * Real.cos (t * Real.log n) := by
    have key : ∀ x : ℝ, (Complex.exp ((x : ℂ) * (-(((1 / 2 + δ : ℝ) : ℂ) + (t : ℂ) * I)))).re =
        Real.exp (x * (-(1 / 2 : ℝ) - δ)) * Real.cos (t * x) := by
      intro x
      have hre : ((x : ℂ) * (-(((1 / 2 + δ : ℝ) : ℂ) + (t : ℂ) * I))).re =
          x * (-(1 / 2 : ℝ) - δ) := by
        simp only [Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.add_re,
          Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
        ring
      have him : ((x : ℂ) * (-(((1 / 2 + δ : ℝ) : ℂ) + (t : ℂ) * I))).im = -(t * x) := by
        simp only [Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.add_re,
          Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
        ring
      rw [Complex.exp_re, hre, him, Real.cos_neg]
    rw [Complex.cpow_def_of_ne_zero hn0, ← Complex.natCast_log, key,
      Real.rpow_def_of_pos hnpos]
  rw [LSeries.term_of_ne_zero hn, Pi.mul_apply, hcoe, div_eq_mul_inv, ← Complex.cpow_neg,
    Complex.re_ofReal_mul, hpow, mul_assoc]

/-- **D2** (M). For `δ > 1/2`:
`Re (L'/L)(1/2 + δ + it, χ) = -∑ₙ Λ(n) χ(n) n^{-1/2-δ} cos(t log n)`. -/
theorem re_logDeriv_LFunction (δ : ℝ) (hδ : 1 / 2 < δ) (t : ℝ) :
    (logDeriv (chi q).LFunction (((1 / 2 + δ : ℝ) : ℂ) + (t : ℂ) * I)).re = -dirichletR q δ t := by
  have hs : 1 < (((1 / 2 + δ : ℝ) : ℂ) + (t : ℂ) * I).re := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
    linarith
  have h1 : logDeriv (chi q).LFunction (((1 / 2 + δ : ℝ) : ℂ) + (t : ℂ) * I) =
      -LSeries ((fun n : ℕ ↦ chi q (n : ZMod q)) *
        (fun n : ℕ ↦ (ArithmeticFunction.vonMangoldt n : ℂ)))
        (((1 / 2 + δ : ℝ) : ℂ) + (t : ℂ) * I) := by
    rw [logDeriv_apply, (chi q).deriv_LFunction_eq_deriv_LSeries hs,
      (chi q).LFunction_eq_LSeries hs, DirichletCharacter.LSeries_twist_vonMangoldt_eq (chi q) hs,
      neg_div, neg_neg]
  have hsum := DirichletCharacter.LSeriesSummable_twist_vonMangoldt (chi q) hs
  rw [h1, Complex.neg_re, LSeries, Complex.re_tsum hsum, dirichletR]
  exact congrArg Neg.neg (tsum_congr (re_term_twist q δ t))

end Exp7.EF
