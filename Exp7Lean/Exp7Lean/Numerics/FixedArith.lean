import Exp7Lean.Numerics.FixedLog

/-!
# Fast-path arithmetic on non-negative fixed-point numbers

For inner loops (sums with thousands of terms) the signed interval type `FI` is unnecessarily
heavy.  Non-negative quantities are kept as natural numbers at scale `D`, a lower and an upper
bound separately, and combined with the directed operations below (raw `Nat` operations, so the
kernel evaluates each in a few steps).

* `fmulLo`, `fmulHi` : products;
* `fdivLo`, `fdivHi` : quotients by a positive quantity;
* `fpowLo`, `fpowHi` : powers `x^k` by repeated multiplication (e.g. `exp (-k t) = exp (-t) ^ k`).
-/

namespace Exp7.Num

/-- Product rounded down: `a ≤ D x`, `b ≤ D y` give `fmulLo D a b ≤ D (x y)`. -/
def fmulLo (D a b : ℕ) : ℕ := Nat.div (Nat.mul a b) D

/-- Product rounded up. -/
def fmulHi (D a b : ℕ) : ℕ := cdiv (Nat.mul a b) D

theorem fmulLo_eq (D a b : ℕ) : fmulLo D a b = a * b / D := rfl
theorem fmulHi_eq (D a b : ℕ) : fmulHi D a b = cdiv (a * b) D := rfl

theorem fmulLo_le {D : ℕ} (hD : 0 < D) {a b : ℕ} {x y : ℝ} (ha : (a : ℝ) ≤ D * x)
    (hb : (b : ℝ) ≤ D * y) : (fmulLo D a b : ℝ) ≤ D * (x * y) := by
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  rw [fmulLo_eq]
  refine (fdiv_le _ _).trans ?_
  rw [div_le_iff₀ hDr]
  push_cast
  have := mul_le_mul ha hb (Nat.cast_nonneg b) (le_trans (Nat.cast_nonneg a) ha)
  calc (a : ℝ) * b ≤ D * x * (D * y) := this
    _ = D * (x * y) * D := by ring

theorem le_fmulHi {D : ℕ} (hD : 0 < D) {a b : ℕ} {x y : ℝ} (hy : 0 ≤ y) (ha : D * x ≤ (a : ℝ))
    (hb : D * y ≤ (b : ℝ)) : D * (x * y) ≤ (fmulHi D a b : ℝ) := by
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  rw [fmulHi_eq]
  refine le_trans ?_ (div_le_cdiv _ _ hD)
  rw [le_div_iff₀ hDr]
  push_cast
  have := mul_le_mul ha hb (mul_nonneg hDr.le hy) (Nat.cast_nonneg a)
  calc D * (x * y) * D = D * x * (D * y) := by ring
    _ ≤ (a : ℝ) * b := this

/-- Quotient rounded down: `a ≤ D x`, `D y ≤ b`, `0 < y` give `fdivLo D a b ≤ D (x / y)`. -/
def fdivLo (D a b : ℕ) : ℕ := Nat.div (Nat.mul a D) b

/-- Quotient rounded up: `D x ≤ a`, `b ≤ D y`, `0 < b` give `D (x / y) ≤ fdivHi D a b`. -/
def fdivHi (D a b : ℕ) : ℕ := cdiv (Nat.mul a D) b

theorem fdivLo_eq (D a b : ℕ) : fdivLo D a b = a * D / b := rfl
theorem fdivHi_eq (D a b : ℕ) : fdivHi D a b = cdiv (a * D) b := rfl

theorem fdivLo_le {D : ℕ} (hD : 0 < D) {a b : ℕ} {x y : ℝ} (hy : 0 < y) (ha : (a : ℝ) ≤ D * x)
    (hb : D * y ≤ (b : ℝ)) : (fdivLo D a b : ℝ) ≤ D * (x / y) := by
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  have hDy : 0 < (D : ℝ) * y := mul_pos hDr hy
  have hbr : (0 : ℝ) < (b : ℝ) := lt_of_lt_of_le hDy hb
  rw [fdivLo_eq]
  refine (fdiv_le _ _).trans ?_
  push_cast
  calc (a : ℝ) * D / b ≤ (a : ℝ) * D / (D * y) :=
        div_le_div_of_nonneg_left (by positivity) hDy hb
    _ ≤ D * x * D / (D * y) := by gcongr
    _ = D * (x / y) := by field_simp

theorem le_fdivHi {D : ℕ} (hD : 0 < D) {a b : ℕ} {x y : ℝ} (hbpos : 0 < b) (ha : D * x ≤ (a : ℝ))
    (hb : (b : ℝ) ≤ D * y) : D * (x / y) ≤ (fdivHi D a b : ℝ) := by
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  have hbr : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hbpos
  have hDy : 0 < (D : ℝ) * y := lt_of_lt_of_le hbr hb
  have hy : 0 < y := by
    rcases lt_trichotomy y 0 with h1 | h1 | h1
    · exact absurd hDy (not_lt.mpr (mul_nonpos_of_nonneg_of_nonpos hDr.le h1.le))
    · rw [h1, mul_zero] at hDy; exact absurd hDy (lt_irrefl _)
    · exact h1
  rw [fdivHi_eq]
  refine le_trans ?_ (div_le_cdiv _ _ hbpos)
  push_cast
  calc D * (x / y) = D * x * D / (D * y) := by field_simp
    _ ≤ (a : ℝ) * D / (D * y) := by gcongr
    _ ≤ (a : ℝ) * D / b := div_le_div_of_nonneg_left (by positivity) hbr hb

/-- `x^k` rounded down, from a lower bound `r ≤ D x`. -/
def fpowLo (D r k : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) D (fun _ ih => Nat.div (Nat.mul ih r) D) k

/-- `x^k` rounded up, from an upper bound `D x ≤ r`. -/
def fpowHi (D r k : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) D (fun _ ih => cdiv (Nat.mul ih r) D) k

theorem fpowLo_succ (D r k : ℕ) : fpowLo D r (k + 1) = fmulLo D (fpowLo D r k) r := rfl
theorem fpowHi_succ (D r k : ℕ) : fpowHi D r (k + 1) = fmulHi D (fpowHi D r k) r := rfl

theorem fpowLo_le {D : ℕ} (hD : 0 < D) {r : ℕ} {x : ℝ} (hr : (r : ℝ) ≤ D * x) (k : ℕ) :
    (fpowLo D r k : ℝ) ≤ D * x ^ k := by
  induction k with
  | zero => simp [fpowLo]
  | succ k ih =>
    rw [fpowLo_succ, pow_succ]
    exact fmulLo_le hD ih hr

theorem le_fpowHi {D : ℕ} (hD : 0 < D) {r : ℕ} {x : ℝ} (hx : 0 ≤ x) (hr : D * x ≤ (r : ℝ))
    (k : ℕ) : D * x ^ k ≤ (fpowHi D r k : ℝ) := by
  induction k with
  | zero => simp [fpowHi]
  | succ k ih =>
    rw [fpowHi_succ, pow_succ]
    exact le_fmulHi hD hx ih hr

end Exp7.Num
