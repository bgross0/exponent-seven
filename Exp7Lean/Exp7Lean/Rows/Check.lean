import Exp7Lean.Rows.JPart
import Exp7Lean.Numerics.Constants

/-!
Certificate rows, step 5: the verified row check.

`rowCheck Q X v pack` is a Boolean computed on natural numbers and integers (fixed point, scale
`10^20`, directed rounding).  `rowCheck_sound` shows that `rowCheck Q X v pack = true` implies
`2 ≤ X`, that `v` (cast to `ℝ`) has a nonzero entry, and `0 < rowMargin Q X v` for the real
`rowMargin` of `Analytic/Reduce.lean`.  `pack` is auxiliary data (the autocorrelation numerators
of `v`, base `2^64`, offset `2^62`); it is verified against `v` by `packCheck`.
-/

namespace Exp7.Rows

open Real Exp7.Num

local notation "Dr" => (100000000000000000000 : ℝ)

/-- Directed lower bound for the row margin at scale `10^20`, given a lower prime sum. -/
def marginLower (Q X LX LXhi sq pack : ℕ) (total : ℤ) : ℤ :=
  Int.sub (Int.add total (Int.ofNat 223059076563587229937))
    (Int.ofNat (Nat.add (jHi X LX LXhi sq pack) (logHi P20w Q)))

/-- Positivity of the fixed-point lower bound of the margin. -/
def rowCore (Q X LX LXhi sq pack : ℕ) : Bool :=
  Nat.ble 1 (Int.toNat (marginLower Q X LX LXhi sq pack (totalLo X LX LXhi sq pack)))

/-- The complete check of a certificate row `(Q, X)` with kernel vector `v`. -/
def rowCheck (Q X : ℕ) (v : List ℤ) (pack : ℕ) : Bool :=
  Nat.ble 2 X && (Nat.ble X 6400 && (Nat.ble 1 Q && (packCheck v pack &&
    (Nat.ble 1 (logLo P20 X) && (Nat.ble 1 (sqrtLo20 X) &&
      rowCore Q X (logLo P20 X) (logHi P20 X)
        (Nat.sub (getN pack 0) 4611686018427387904) pack)))))

theorem P20_D' : ((P20.D : ℕ) : ℝ) = Dr := by norm_num [P20]
theorem P20w_D' : ((P20w.D : ℕ) : ℝ) = Dr := by norm_num [P20w]

theorem marginLower_le {Q X LX LXhi sq pack B : ℕ} {v : List ℝ} {total : ℤ}
    (C : RowCtx X LX LXhi sq pack v B) (hQ : 1 ≤ Q) (hs : 0 < sqrtLo20 X)
    (hT : (total : ℝ) ≤ Dr * inertSum (autocorr (stepFn (Real.log X) v)) X) :
    ((marginLower Q X LX LXhi sq pack total : ℤ) : ℝ) ≤ Dr * rowMargin Q X v := by
  have hJ := le_jHi C hs
  have hlQ : Dr * Real.log Q ≤ (logHi P20w Q : ℝ) := by
    have := le_logHi P20w_valid hQ
    rw [P20w_D'] at this
    exact this
  have hc : (223059076563587229937 : ℝ) ≤
      (Real.log π + eulerMascheroniConstant - π / 2 + 3 * Real.log 2) * Dr := by
    have := rowConst_mem.1
    rw [div_le_iff₀ (by norm_num)] at this
    have e20 : (10 : ℝ) ^ 20 = Dr := by norm_num
    rw [e20] at this
    exact this
  change (↑(total + (223059076563587229937 : ℤ) - ↑(jHi X LX LXhi sq pack + logHi P20w Q)) : ℝ) ≤ _
  push_cast
  unfold rowMargin psi34
  linarith

theorem rowCore_sound {Q X LX LXhi sq pack : ℕ} {v : List ℝ} (C : RowCtx X LX LXhi sq pack v)
    (hQ : 1 ≤ Q) (hs : 0 < sqrtLo20 X) (h : rowCore Q X LX LXhi sq pack = true) :
    0 < rowMargin Q X v := by
  have hz : 0 < marginLower Q X LX LXhi sq pack (totalLo X LX LXhi sq pack) := by
    have hh := Nat.le_of_ble_eq_true h
    change 1 ≤ Int.toNat (marginLower Q X LX LXhi sq pack (totalLo X LX LXhi sq pack)) at hh
    omega
  have hzr : (0 : ℝ) < (marginLower Q X LX LXhi sq pack (totalLo X LX LXhi sq pack) : ℤ) := by
    exact_mod_cast hz
  have hpos := lt_of_lt_of_le hzr (marginLower_le C hQ hs (totalLo_le C))
  exact pos_of_mul_pos_right hpos (by norm_num)

/-- **Soundness of the row check.** -/
theorem rowCheck_sound {Q X : ℕ} {v : List ℤ} {pack : ℕ} (h : rowCheck Q X v pack = true) :
    2 ≤ X ∧ (∃ t ∈ v.map (fun z : ℤ => (z : ℝ)), t ≠ 0) ∧
      0 < rowMargin Q X (v.map (fun z : ℤ => (z : ℝ))) := by
  unfold rowCheck at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  have hX : 2 ≤ X := Nat.le_of_ble_eq_true h1
  have hX' : X ≤ 6400 := Nat.le_of_ble_eq_true h2
  have hQ : 1 ≤ Q := Nat.le_of_ble_eq_true h3
  have pk := packOK_of_check h4
  have hlx : 0 < logLo P20 X := Nat.le_of_ble_eq_true h5
  have hs : 0 < sqrtLo20 X := Nat.le_of_ble_eq_true h6
  have C : RowCtx X (logLo P20 X) (logHi P20 X) (Nat.sub (getN pack 0) 4611686018427387904) pack
      (v.map (fun z : ℤ => (z : ℝ))) := by
    refine ⟨hX, hX', pk, hlx, ?_, ?_⟩
    · have := logLo_le P20_valid (n := X) (by omega)
      rw [P20_D'] at this
      exact this
    · have := le_logHi P20_valid (n := X) (by omega)
      rw [P20_D'] at this
      exact this
  exact ⟨hX, pk.ne, rowCore_sound C hQ hs h7⟩

/-- The statement required of one certificate row by `RowMargins`. -/
def RowOK (r : Row) : Prop :=
  2 ≤ r.X ∧ ∃ v : List ℝ, (∃ t ∈ v, t ≠ 0) ∧ 0 < rowMargin r.Q r.X v

theorem rowOK_of_check {Q X : ℕ} {v : List ℤ} {pack : ℕ} (h : rowCheck Q X v pack = true) :
    RowOK ⟨Q, X⟩ := by
  obtain ⟨h1, h2, h3⟩ := rowCheck_sound h
  exact ⟨h1, _, h2, h3⟩

end Exp7.Rows
