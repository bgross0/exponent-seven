import Exp7Lean.Numerics.FixedLog

/-!
# A verified fixed-point square root

`sqrtLo D bits fuel n ≤ D * √n ≤ sqrtHi D bits fuel n` for every natural `n` and every choice of
the parameters.  The candidate `⌊D √n⌋` is produced by an (unverified) Newton iteration and then
*certified* by one comparison `s² ≤ n D²` (resp. `n D² ≤ s²`); if the comparison fails a trivially
valid bound is returned, so soundness never depends on the iteration.
-/

namespace Exp7.Num

open Real

/-- `fuel` Newton steps `s ↦ ⌊(s + ⌊m/s⌋)/2⌋` for `√m`, starting from `s`. -/
def newtonSqrt (m s fuel : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) s (fun _ ih => Nat.div (Nat.add ih (Nat.div m ih)) 2) fuel

/-- `s` if it is certified to be a lower bound of `D √n`, else `0`. -/
def sqrtLoS (D n s : ℕ) : ℕ :=
  cond (Nat.ble (Nat.mul s s) (Nat.mul n (Nat.mul D D))) s 0

/-- `s` if it is certified to be an upper bound of `D √n`, else the trivial bound `D (n+1)`. -/
def sqrtHiS (D n s : ℕ) : ℕ :=
  cond (Nat.ble (Nat.mul n (Nat.mul D D)) (Nat.mul s s)) s (Nat.mul D (Nat.succ n))

theorem sqrtLoS_eq (D n s : ℕ) : sqrtLoS D n s = if s * s ≤ n * (D * D) then s else 0 := by
  rw [sqrtLoS, cond_ble]; rfl

theorem sqrtHiS_eq (D n s : ℕ) :
    sqrtHiS D n s = if n * (D * D) ≤ s * s then s else D * (n + 1) := by
  rw [sqrtHiS, cond_ble]; rfl

theorem sqrtLoS_le (D n s : ℕ) : (sqrtLoS D n s : ℝ) ≤ D * √(n : ℝ) := by
  have h0 : (0 : ℝ) ≤ D * √(n : ℝ) := by positivity
  rw [sqrtLoS_eq]
  split_ifs with h
  · have hsq : (s : ℝ) ^ 2 ≤ ((D : ℝ) * √(n : ℝ)) ^ 2 := by
      rw [mul_pow, sq_sqrt (Nat.cast_nonneg n)]
      have : (s : ℝ) * s ≤ (n : ℝ) * ((D : ℝ) * D) := by exact_mod_cast h
      nlinarith
    exact (pow_le_pow_iff_left₀ (Nat.cast_nonneg s) h0 two_ne_zero).mp hsq
  · simpa using h0

theorem le_sqrtHiS (D n s : ℕ) : D * √(n : ℝ) ≤ (sqrtHiS D n s : ℝ) := by
  have h0 : (0 : ℝ) ≤ D * √(n : ℝ) := by positivity
  rw [sqrtHiS_eq]
  split_ifs with h
  · have hsq : ((D : ℝ) * √(n : ℝ)) ^ 2 ≤ (s : ℝ) ^ 2 := by
      rw [mul_pow, sq_sqrt (Nat.cast_nonneg n)]
      have : (n : ℝ) * ((D : ℝ) * D) ≤ (s : ℝ) * s := by exact_mod_cast h
      nlinarith
    exact (pow_le_pow_iff_left₀ h0 (Nat.cast_nonneg s) two_ne_zero).mp hsq
  · push_cast
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg D)
    rw [sqrt_le_left (by positivity)]
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    nlinarith

/-- Newton candidate for `⌊D √n⌋`: start `D · 2^(⌊e/2⌋+1) ≥ D √n` with `e = ⌊log₂ n⌋`. -/
def sqrtCand (D bits fuel n : ℕ) : ℕ :=
  newtonSqrt (Nat.mul n (Nat.mul D D))
    (Nat.mul D (Nat.pow 2 (Nat.succ (Nat.div (expoSearch bits n) 2)))) fuel

/-- Lower bound for `D * √n`. -/
def sqrtLo (D bits fuel n : ℕ) : ℕ := sqrtLoS D n (sqrtCand D bits fuel n)

/-- Upper bound for `D * √n`. -/
def sqrtHi (D bits fuel n : ℕ) : ℕ := sqrtHiS D n (Nat.succ (sqrtCand D bits fuel n))

theorem sqrtLo_le (D bits fuel n : ℕ) : (sqrtLo D bits fuel n : ℝ) ≤ D * √(n : ℝ) :=
  sqrtLoS_le _ _ _

theorem le_sqrtHi (D bits fuel n : ℕ) : D * √(n : ℝ) ≤ (sqrtHi D bits fuel n : ℝ) :=
  le_sqrtHiS _ _ _

/-- The enclosure in the form `lo / D ≤ √n ≤ hi / D`. -/
theorem sqrt_mem {D : ℕ} (hD : 0 < D) (bits fuel n : ℕ) :
    (sqrtLo D bits fuel n : ℝ) / D ≤ √(n : ℝ) ∧ √(n : ℝ) ≤ (sqrtHi D bits fuel n : ℝ) / D := by
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  constructor
  · rw [div_le_iff₀ hDr, mul_comm]; exact sqrtLo_le D bits fuel n
  · rw [le_div_iff₀ hDr, mul_comm]; exact le_sqrtHi D bits fuel n

end Exp7.Num
