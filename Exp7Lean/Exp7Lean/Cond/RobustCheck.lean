import Exp7Lean.Cond.Robust
import Exp7Lean.Cond.Eval
import Exp7Lean.Cond.Table

/-!
Threshold certificates: the verified check.

`robustCheck T Q X v pack` is a Boolean computed on natural numbers and integers (fixed point,
scale `10^20`, directed rounding).  For every prime `l < X` of the certified table
`primeTable8400` it adds

* the lower bound `primeLo` of `primeT f X l (-1)` if `l < T`,
* the smaller of the lower bounds `primeLoP`, `primeLo` of `primeT f X l (±1)` if `T ≤ l`,

and compares with the upper bound `jHi` of the archimedean term and `logHi Q`, exactly as
`rowCheck` (`Rows/Check.lean`) does for the certificate rows.

`robustCheck_sound`: `robustCheck T Q X v pack = true` implies `2 ≤ X`, that `v` (cast to `ℝ`) has
a nonzero entry, and `0 < robustMargin T Q X v` for the real `robustMargin` of `Cond/Robust.lean`.
-/

namespace Exp7.Rows

open Real Exp7.Num

local notation "Dr" => (100000000000000000000 : ℝ)

/-- The contribution of the table entry `(l, L, S)` when no prime below `T` splits. -/
def robustPrime (T X LX LXhi sq pack l L S : ℕ) : ℤ :=
  cond (Nat.ble T l)
    (minZ (primeLoP X LX LXhi sq pack l L S 13 1) (primeLo X LX LXhi sq pack l L S 13 1))
    (primeLo X LX LXhi sq pack l L S 13 1)

/-- The lower bound for `10^20 · robustSum`, folded over the certified table. -/
def robustTotalLo (T X LX LXhi sq pack : ℕ) : ℤ :=
  tableSumZ (fun l L S => robustPrime T X LX LXhi sq pack l L S) X primeTable8400

variable {X LX LXhi sq pack : ℕ} {v : List ℝ}

theorem robustTotalLo_le (C : Ctx X LX LXhi sq pack v) (hX' : X ≤ 8400) (T : ℕ) :
    ((robustTotalLo T X LX LXhi sq pack : ℤ) : ℝ) ≤
      Dr * robustSum T (autocorr (stepFn (Real.log X) v)) X := by
  have e20 : (10 : ℝ) ^ 20 = Dr := by norm_num
  set f := autocorr (stepFn (Real.log X) v) with hf
  unfold robustSum
  rw [Finset.mul_sum, ← primeTable8400_filter hX']
  unfold robustTotalLo
  refine tableSumZ_le_aux _ (fun l => Dr * (if l < T then primeT f X l (-1) else
    min (primeT f X l 1) (primeT f X l (-1)))) X _ primeTable8400_nodup ?_
  intro e he _
  obtain ⟨hp, -, h1, h2, h3, h4⟩ := primeTable8400_spec (p := e.1) (L := e.2.1) (S := e.2.2) he
  rw [e20] at h1 h2 h3 h4
  have hP := primeLoP_le_primeT C (le_trans hX' (by norm_num)) hp h1 h2 h3 h4
  have hM := primeLo_le_primeT C (le_trans hX' (by norm_num)) hp h1 h2 h3 h4
  rw [← hf] at hP hM
  change ((robustPrime T X LX LXhi sq pack e.1 e.2.1 e.2.2 : ℤ) : ℝ) ≤
    Dr * (if e.1 < T then primeT f X e.1 (-1) else min (primeT f X e.1 1) (primeT f X e.1 (-1)))
  unfold robustPrime
  rw [cond_ble]
  split_ifs with a1 a2
  · omega
  · exact minZ_le_min hP hM
  · exact hM
  · omega

/-- Positivity of the fixed-point lower bound of the threshold margin:
`robustTotalLo + const - (jHi + logHi Q) ≥ 1`. -/
def robustCore (T Q X LX LXhi sq pack : ℕ) : Bool :=
  Nat.ble 1 (Int.toNat (Int.sub
    (Int.add (robustTotalLo T X LX LXhi sq pack) (Int.ofNat 223059076563587229937))
    (Int.ofNat (Nat.add (jHi X LX LXhi sq pack) (logHi P20w Q)))))

/-- The complete check of a threshold certificate `(T, Q, X)` with kernel vector `v`. -/
def robustCheck (T Q X : ℕ) (v : List ℤ) (pack : ℕ) : Bool :=
  Nat.ble 2 X && (Nat.ble X 8400 && (Nat.ble 1 Q && (packCheck v pack &&
    (Nat.ble 1 (logLo P20 X) && (Nat.ble 1 (sqrtLo20 X) &&
      robustCore T Q X (logLo P20 X) (logHi P20 X)
        (Nat.sub (getN pack 0) 4611686018427387904) pack)))))

/-- From a lower bound of `10^20 ·` (prime-power side) to positivity of the margin. -/
theorem margin_pos_of_core (C : Ctx X LX LXhi sq pack v) {Q : ℕ} (hQ : 1 ≤ Q)
    (hs : 0 < sqrtLo20 X) {tot : ℤ} {s : ℝ} (hT : (tot : ℝ) ≤ Dr * s)
    (h : Nat.ble 1 (Int.toNat (Int.sub (Int.add tot (Int.ofNat 223059076563587229937))
      (Int.ofNat (Nat.add (jHi X LX LXhi sq pack) (logHi P20w Q))))) = true) :
    0 < s - Jterm (autocorr (stepFn (Real.log X) v)) - Real.log Q + Real.log Real.pi - psi34 := by
  have hJ := le_jHi' C hs
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
  have h1 : 1 ≤ Int.toNat (tot + ((223059076563587229937 : ℕ) : ℤ) -
      ((jHi X LX LXhi sq pack + logHi P20w Q : ℕ) : ℤ)) := Nat.le_of_ble_eq_true h
  have hz : 0 < tot + ((223059076563587229937 : ℕ) : ℤ) -
      ((jHi X LX LXhi sq pack + logHi P20w Q : ℕ) : ℤ) := by
    by_contra hneg
    have := Int.toNat_of_nonpos (not_lt.mp hneg)
    omega
  have hzr : (0 : ℝ) < ((tot + ((223059076563587229937 : ℕ) : ℤ) -
      ((jHi X LX LXhi sq pack + logHi P20w Q : ℕ) : ℤ) : ℤ) : ℝ) := by exact_mod_cast hz
  push_cast at hzr
  have hpos : Dr * 0 < Dr * (s - Jterm (autocorr (stepFn (Real.log X) v)) - Real.log Q +
      Real.log Real.pi - psi34) := by
    unfold psi34
    linarith
  exact lt_of_mul_lt_mul_left hpos (by norm_num)

/-- **Soundness of the threshold check.** -/
theorem robustCheck_sound {T Q X : ℕ} {v : List ℤ} {pack : ℕ}
    (h : robustCheck T Q X v pack = true) :
    2 ≤ X ∧ (∃ t ∈ v.map (fun z : ℤ => (z : ℝ)), t ≠ 0) ∧
      0 < robustMargin T Q X (v.map (fun z : ℤ => (z : ℝ))) := by
  unfold robustCheck at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  have hX : 2 ≤ X := Nat.le_of_ble_eq_true h1
  have hX' : X ≤ 8400 := Nat.le_of_ble_eq_true h2
  have hQ : 1 ≤ Q := Nat.le_of_ble_eq_true h3
  have hlx : 0 < logLo P20 X := Nat.le_of_ble_eq_true h5
  have hs : 0 < sqrtLo20 X := Nat.le_of_ble_eq_true h6
  have C := ctx_of_pack hX h4 hlx
  exact ⟨hX, C.pk.ne, margin_pos_of_core C hQ hs (robustTotalLo_le C hX' T) h7⟩

end Exp7.Rows

namespace Exp7

/-- A threshold certificate: threshold `T`, bound `Q`, cut-off `X`. -/
def RobustOK (T Q X : ℕ) : Prop :=
  2 ≤ X ∧ ∃ v : List ℝ, (∃ t ∈ v, t ≠ 0) ∧ 0 < robustMargin T Q X v

theorem robustOK_of_check {T Q X : ℕ} {v : List ℤ} {pack : ℕ}
    (h : Rows.robustCheck T Q X v pack = true) : RobustOK T Q X := by
  obtain ⟨h1, h2, h3⟩ := Rows.robustCheck_sound h
  exact ⟨h1, _, h2, h3⟩

/-- Under the explicit-formula inequality and GRH, a threshold certificate `(T, Q, X)` shows
that every prime `q ≡ 3 (mod 4)`, `q > X`, without split prime below `T` satisfies `q > Q`. -/
theorem lt_of_robustOK (hEF : ExplicitFormulaBound) (hGRH : GRHPrimeConductor) {T Q X : ℕ}
    (h : RobustOK T Q X) {q : ℕ} (hq : q.Prime) (h4 : q % 4 = 3) (hXq : X < q)
    (hin : ∀ l, l.Prime → l < T → ¬ Splits q l) : Q < q := by
  obtain ⟨hX, v, hv, hm⟩ := h
  exact lt_of_robustMargin hEF hGRH T Q X v hX hv hm q hq h4 hXq hin

end Exp7

#print axioms Exp7.Rows.robustCheck_sound
#print axioms Exp7.lt_of_robustOK
