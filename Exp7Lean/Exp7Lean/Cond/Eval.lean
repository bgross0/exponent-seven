import Exp7Lean.Cond.Reduce
import Exp7Lean.Rows.Check

/-!
Conditional and threshold certificates: the evaluators of the two signs, for any cut-off `X`.

The evaluator of the certificate rows (`Exp7Lean/Rows`) is stated for `X ≤ 6400` (the field `hX'`
of `RowCtx`).  The definitions `termLo`, `primeLo`, `jHi` do not depend on that bound; this file
re-proves their soundness under the context `Ctx` (no bound on `X`), and adds the evaluator
`primeLoP` of the contribution of a prime with `χ(l) = +1`:

* `primeLo_le_primeT`  : `primeLo  … l L S 13 1 ≤ 10^20 · primeT f X l (-1)`,
* `primeLoP_le_primeT` : `primeLoP … l L S 13 1 ≤ 10^20 · primeT f X l 1`     (both for `X ≤ 2^14`),
* `le_jHi'`            : `10^20 · Jterm f ≤ jHi …`.
-/

namespace Exp7.Rows

open Real Exp7.Num

local notation "Dn" => (100000000000000000000 : ℕ)
local notation "Dr" => (100000000000000000000 : ℝ)
local notation "Zn" => (461168601842738790400000000000000000000 : ℕ)

/-- The hypotheses shared by the evaluators (as `RowCtx`, without the bound `X ≤ 6400`). -/
structure Ctx (X LX LXhi sq pack : ℕ) (v : List ℝ) : Prop where
  hX : 2 ≤ X
  pk : PackOK v sq pack
  lxpos : 0 < LX
  lx : (LX : ℝ) ≤ Dr * Real.log X
  lxhi : Dr * Real.log X ≤ (LXhi : ℝ)

variable {X LX LXhi sq pack : ℕ} {v : List ℝ}

/-! ### The value of `f` at a prime power -/

/-- If the cell test succeeds, `fLo` and `fHi` enclose `10^20 (sq f(log p^k) + 2^62)`. -/
theorem cell_value (C : Ctx X LX LXhi sq pack v) {p L k j : ℕ} (hp : p.Prime)
    (h1 : (L : ℝ) ≤ Dr * Real.log p) (h2 : Dr * Real.log p ≤ (L : ℝ) + 16)
    (hc : cellOK X (Nat.pow p k) j = true) :
    (fLo (getN pack j) (getN pack (j + 1)) (hLo LXhi L k j) (hHi LX L k j) : ℝ) ≤
        Dr * sq * autocorr (stepFn (Real.log X) v) (Real.log ((p ^ k : ℕ) : ℝ)) +
          ((Zn : ℕ) : ℝ) ∧
      Dr * sq * autocorr (stepFn (Real.log X) v) (Real.log ((p ^ k : ℕ) : ℝ)) + ((Zn : ℕ) : ℝ) ≤
        (fHi (getN pack j) (getN pack (j + 1)) (hLo LXhi L k j) (hHi LX L k j) : ℝ) := by
  have hX1 : (1 : ℝ) < X := by exact_mod_cast C.hX
  have hlX : 0 < Real.log X := Real.log_pos hX1
  have hp0 : 0 < p := hp.pos
  have hpr : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
  have hlp : 0 ≤ Real.log p := Real.log_nonneg hpr
  have hn : 1 ≤ p ^ k := Nat.one_le_pow _ _ hp0
  have hv := C.pk.ne
  set f := autocorr (stepFn (Real.log X) v) with hf
  unfold cellOK at hc
  rw [Bool.and_eq_true, Bool.and_eq_true] at hc
  obtain ⟨c1, c2, c3⟩ := hc
  have c1' : X ^ j ≤ (p ^ k) ^ 64 := Nat.le_of_ble_eq_true c1
  have c2' : (p ^ k) ^ 64 ≤ X ^ (j + 1) := Nat.le_of_ble_eq_true c2
  have c3' : j ≤ 63 := Nat.le_of_ble_eq_true c3
  have hlen := C.pk.len
  have hX2 := C.hX
  have e64 : ((64 : ℕ) : ℝ) = 64 := by norm_num
  have hval := autocorr_stepFn_log (v := v) C.hX hn hv (by rw [hlen]; exact c1')
    (by rw [hlen]; exact c2')
  rw [hlen, e64] at hval
  have hlogn : Real.log ((p ^ k : ℕ) : ℝ) = k * Real.log p := by
    rw [Nat.cast_pow, Real.log_pow]
  -- the position in the cell
  set θ : ℝ := Real.log ((p ^ k : ℕ) : ℝ) / (Real.log X / 64) - j with hθdef
  have hθ : θ = 64 * (k * Real.log p) / Real.log X - j := by
    rw [hθdef, hlogn]
    field_simp
  obtain ⟨e1, e2⟩ := cell_log_bounds (m := 64) (by omega : 0 < X) hn c1' c2'
  rw [e64] at e1 e2
  have hθ0 : 0 ≤ θ := by
    rw [hθdef, sub_nonneg, le_div_iff₀ (by positivity)]
    linarith
  have hθ1 : θ ≤ 1 := by
    rw [hθdef, sub_le_iff_le_add, div_le_iff₀ (by positivity)]
    linarith
  have hHlo := hLo_le (LXhi := LXhi) (L := L) (k := k) (j := j) hlX h1 C.lxhi hθ hθ0
  have hHhi := le_hHi (LX := LX) (L := L) (k := k) (j := j) hlX hlp C.lxpos h2 C.lx hθ hθ1
  have ha := C.pk.c j (by omega)
  have hb := C.pk.c (j + 1) (by omega)
  -- the shifted value
  have hΦ : (getN pack j : ℝ) * Dr + Dr * θ * ((getN pack (j + 1) : ℝ) - getN pack j) =
      Dr * sq * f (Real.log ((p ^ k : ℕ) : ℝ)) + ((Zn : ℕ) : ℝ) := by
    rw [hf, hval, ha, hb]
    push_cast
    ring
  have hFlo := fLo_le (a := getN pack j) (b := getN pack (j + 1)) hHlo hHhi (hHi_le LX L k j)
  have hFhi := le_fHi (a := getN pack j) (b := getN pack (j + 1)) hHlo hHhi
  rw [hΦ] at hFlo hFhi
  exact ⟨hFlo, hFhi⟩

/-- The trivial bound used when the cell test fails. -/
theorem abs_condTerm_le (C : Ctx X LX LXhi sq pack v) {p : ℕ} (hp : p.Prime) {σ : ℝ}
    (hσ : |σ| = 1) (k : ℕ) :
    |condTerm (autocorr (stepFn (Real.log X) v)) p σ k| ≤ Real.log p := by
  have hX1 : (1 : ℝ) < X := by exact_mod_cast C.hX
  have hlX : 0 < Real.log X := Real.log_pos hX1
  have hpr : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
  have hlp : 0 ≤ Real.log p := Real.log_nonneg hpr
  have hrt1 := sqrt_pow_ge_one (k := k) hp.pos
  have hrt0 : (0 : ℝ) < √((p ^ k : ℕ) : ℝ) := lt_of_lt_of_le one_pos hrt1
  unfold condTerm
  rw [abs_div, abs_mul, abs_mul, abs_pow, hσ, one_pow, mul_one,
    abs_of_nonneg hlp, abs_of_pos hrt0, div_le_iff₀ hrt0]
  have hf1 : |autocorr (stepFn (Real.log X) v) (Real.log ((p ^ k : ℕ) : ℝ))| ≤ 1 :=
    abs_autocorr_stepFn_le_one' hlX C.pk.ne _
  calc Real.log p * |autocorr (stepFn (Real.log X) v) (Real.log ((p ^ k : ℕ) : ℝ))|
      ≤ Real.log p * 1 := mul_le_mul_of_nonneg_left hf1 hlp
    _ ≤ Real.log p * √((p ^ k : ℕ) : ℝ) := mul_le_mul_of_nonneg_left hrt1 hlp

/-! ### One term with `χ(l) = +1` -/

/-- The term for the cell `j`, sign `+1`. -/
def termMainP (LX LXhi sq pack p L S k j : ℕ) : ℤ :=
  (fun a b den =>
      sgnLo (fLo a b (hLo LXhi L k j) (hHi LX L k j)) Zn (wLo L S k) (wHi L S k) den)
    (getN pack j) (getN pack (Nat.succ j))
    (Nat.mul (Nat.mul (Nat.mul (Nat.pow p (Nat.div (Nat.succ k) 2)) sq) Dn) Dn)

/-- Lower bound for `10^20 · 2 log p · f(log p^k) / √(p^k)`. -/
def termLoP (X LX LXhi sq pack p L S k : ℕ) : ℤ :=
  (fun j => cond (cellOK X (Nat.pow p k) j) (termMainP LX LXhi sq pack p L S k j)
      (Int.neg (Int.ofNat (Nat.mul 2 (Nat.add L 16)))))
    (Nat.div (Nat.mul (Nat.mul 64 k) L) LXhi)

theorem termLoP_le (C : Ctx X LX LXhi sq pack v) {p L S k : ℕ} (hp : p.Prime)
    (h1 : (L : ℝ) ≤ Dr * Real.log p) (h2 : Dr * Real.log p ≤ (L : ℝ) + 16)
    (h3 : (S : ℝ) ≤ Dr * √(p : ℝ)) (h4 : Dr * √(p : ℝ) ≤ (S : ℝ) + 1) :
    ((termLoP X LX LXhi sq pack p L S k : ℤ) : ℝ) ≤
      Dr * (2 * condTerm (autocorr (stepFn (Real.log X) v)) p 1 k) := by
  have hp0 : 0 < p := hp.pos
  set f := autocorr (stepFn (Real.log X) v) with hf
  unfold termLoP
  generalize hj : Nat.div (Nat.mul (Nat.mul 64 k) L) LXhi = j
  change ((cond (cellOK X (Nat.pow p k) j) (termMainP LX LXhi sq pack p L S k j)
    (Int.neg (Int.ofNat (Nat.mul 2 (Nat.add L 16)))) : ℤ) : ℝ) ≤ _
  cases hc : cellOK X (Nat.pow p k) j with
  | false =>
    rw [Bool.cond_false]
    change ((-((2 * (L + 16) : ℕ) : ℤ) : ℤ) : ℝ) ≤ _
    have hlow := (abs_le.mp (abs_condTerm_le C hp (σ := 1) abs_one k)).1
    rw [← hf] at hlow
    push_cast
    linarith
  | true =>
    rw [Bool.cond_true]
    obtain ⟨hFlo, -⟩ := cell_value C (L := L) hp h1 h2 hc
    rw [← hf] at hFlo
    have hsq : (0 : ℝ) < sq := by exact_mod_cast C.pk.sqpos
    obtain ⟨hw1, hw2⟩ := weight_bounds (k := k) hp0 h1 h2 h3 h4
    have hden : 0 < p ^ ((k + 1) / 2) * sq * Dn * Dn :=
      Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.pow_pos hp0) C.pk.sqpos) (by norm_num))
        (by norm_num)
    have hPne : ((p : ℝ) ^ ((k + 1) / 2)) ≠ 0 := by positivity
    have hdenr : ((p ^ ((k + 1) / 2) * sq * Dn * Dn : ℕ) : ℝ) =
        (p : ℝ) ^ ((k + 1) / 2) * sq * Dr * Dr := by push_cast; ring
    have et : termMainP LX LXhi sq pack p L S k j =
        sgnLo (fLo (getN pack j) (getN pack (j + 1)) (hLo LXhi L k j) (hHi LX L k j)) Zn
          (wLo L S k) (wHi L S k) (p ^ ((k + 1) / 2) * sq * Dn * Dn) := rfl
    rw [et]
    refine (sgnLo_le hden hFlo (le_refl ((Zn : ℕ) : ℝ)) hw1 hw2).trans (le_of_eq ?_)
    rw [add_sub_cancel_right, hdenr]
    unfold condTerm
    rw [one_pow]
    exact alg_even (by norm_num) hsq.ne' hPne

/-! ### One term with `χ(l) = -1` (the evaluator `termLo` of `Rows/PrimePart.lean`) -/

theorem termLo_le' (C : Ctx X LX LXhi sq pack v) {p L S k : ℕ} (hp : p.Prime)
    (h1 : (L : ℝ) ≤ Dr * Real.log p) (h2 : Dr * Real.log p ≤ (L : ℝ) + 16)
    (h3 : (S : ℝ) ≤ Dr * √(p : ℝ)) (h4 : Dr * √(p : ℝ) ≤ (S : ℝ) + 1) :
    ((termLo X LX LXhi sq pack p L S k : ℤ) : ℝ) ≤
      Dr * (2 * condTerm (autocorr (stepFn (Real.log X) v)) p (-1) k) := by
  have hp0 : 0 < p := hp.pos
  set f := autocorr (stepFn (Real.log X) v) with hf
  unfold termLo
  generalize hj : Nat.div (Nat.mul (Nat.mul 64 k) L) LXhi = j
  change ((cond (cellOK X (Nat.pow p k) j) (termMain LX LXhi sq pack p L S k j)
    (Int.neg (Int.ofNat (Nat.mul 2 (Nat.add L 16)))) : ℤ) : ℝ) ≤ _
  cases hc : cellOK X (Nat.pow p k) j with
  | false =>
    rw [Bool.cond_false]
    change ((-((2 * (L + 16) : ℕ) : ℤ) : ℤ) : ℝ) ≤ _
    have hlow := (abs_le.mp (abs_condTerm_le C hp (σ := -1) (by rw [abs_neg, abs_one]) k)).1
    rw [← hf] at hlow
    push_cast
    linarith
  | true =>
    rw [Bool.cond_true]
    obtain ⟨hFlo, hFhi⟩ := cell_value C (L := L) hp h1 h2 hc
    rw [← hf] at hFlo hFhi
    have hsq : (0 : ℝ) < sq := by exact_mod_cast C.pk.sqpos
    obtain ⟨hw1, hw2⟩ := weight_bounds (k := k) hp0 h1 h2 h3 h4
    have hden : 0 < p ^ ((k + 1) / 2) * sq * Dn * Dn :=
      Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.pow_pos hp0) C.pk.sqpos) (by norm_num))
        (by norm_num)
    have hPne : ((p : ℝ) ^ ((k + 1) / 2)) ≠ 0 := by positivity
    have hdenr : ((p ^ ((k + 1) / 2) * sq * Dn * Dn : ℕ) : ℝ) =
        (p : ℝ) ^ ((k + 1) / 2) * sq * Dr * Dr := by push_cast; ring
    rcases Nat.mod_two_eq_zero_or_one k with hk | hk
    · have et : termMain LX LXhi sq pack p L S k j =
          sgnLo (fLo (getN pack j) (getN pack (j + 1)) (hLo LXhi L k j) (hHi LX L k j)) Zn
            (wLo L S k) (wHi L S k) (p ^ ((k + 1) / 2) * sq * Dn * Dn) := by
        unfold termMain; simp only []; rw [cond_beq]; exact ite_eq_left hk
      rw [et]
      refine (sgnLo_le hden hFlo (le_refl ((Zn : ℕ) : ℝ)) hw1 hw2).trans (le_of_eq ?_)
      rw [add_sub_cancel_right, hdenr]
      unfold condTerm
      rw [(Nat.even_iff.mpr hk).neg_one_pow]
      exact alg_even (by norm_num) hsq.ne' hPne
    · have et : termMain LX LXhi sq pack p L S k j =
          sgnLo Zn (fHi (getN pack j) (getN pack (j + 1)) (hLo LXhi L k j) (hHi LX L k j))
            (wLo L S k) (wHi L S k) (p ^ ((k + 1) / 2) * sq * Dn * Dn) := by
        unfold termMain; simp only []; rw [cond_beq]
        exact ite_eq_right (show ¬ (k % 2 = 0) by omega)
      rw [et]
      refine (sgnLo_le hden (le_refl ((Zn : ℕ) : ℝ)) hFhi hw1 hw2).trans (le_of_eq ?_)
      have hΦ' : ((Zn : ℕ) : ℝ) - (Dr * sq * f (Real.log ((p ^ k : ℕ) : ℝ)) + ((Zn : ℕ) : ℝ)) =
          -(Dr * sq * f (Real.log ((p ^ k : ℕ) : ℝ))) := by ring
      rw [hΦ', hdenr]
      unfold condTerm
      rw [(Nat.odd_iff.mpr hk).neg_one_pow]
      exact alg_odd (by norm_num) hsq.ne' hPne

/-! ### All exponents for one prime -/

/-- `∑ termLoP` over `k, k+1, …` while `p^k < X` (at most `fuel` terms). -/
def primeLoP (X LX LXhi sq pack p L S fuel k : ℕ) : ℤ :=
  Nat.rec (motive := fun _ => ℕ → ℤ) (fun _ => 0)
    (fun _ ih k => cond (Nat.ble X (Nat.pow p k)) 0
      (Int.add (termLoP X LX LXhi sq pack p L S k) (ih (Nat.succ k)))) fuel k

theorem primeLoP_le (C : Ctx X LX LXhi sq pack v) {p L S : ℕ} (hp : p.Prime)
    (h1 : (L : ℝ) ≤ Dr * Real.log p) (h2 : Dr * Real.log p ≤ (L : ℝ) + 16)
    (h3 : (S : ℝ) ≤ Dr * √(p : ℝ)) (h4 : Dr * √(p : ℝ) ≤ (S : ℝ) + 1) (fuel k : ℕ) :
    ((primeLoP X LX LXhi sq pack p L S fuel k : ℤ) : ℝ) ≤
      Dr * ∑ k' ∈ Finset.Ico k (k + fuel),
        if p ^ k' < X then 2 * condTerm (autocorr (stepFn (Real.log X) v)) p 1 k' else 0 := by
  induction fuel generalizing k with
  | zero =>
    change ((0 : ℤ) : ℝ) ≤ _
    simp
  | succ fuel ih =>
    change ((cond (Nat.ble X (p ^ k)) 0
      (termLoP X LX LXhi sq pack p L S k + primeLoP X LX LXhi sq pack p L S fuel (k + 1)) : ℤ) : ℝ)
      ≤ _
    rw [cond_ble]
    split_ifs with hXk
    · rw [Finset.sum_eq_zero]
      · simp
      · intro k' hk'
        have hkk : k ≤ k' := (Finset.mem_Ico.mp hk').1
        have : X ≤ p ^ k' := le_trans hXk (Nat.pow_le_pow_right hp.pos hkk)
        rw [ite_eq_right (not_lt.mpr this)]
    · rw [Finset.sum_eq_sum_Ico_succ_bot (by omega), ite_eq_left (not_le.mp hXk)]
      have ih' := ih (k + 1)
      rw [show k + 1 + fuel = k + (fuel + 1) by omega] at ih'
      have ht := termLoP_le C (k := k) hp h1 h2 h3 h4
      push_cast
      rw [mul_add]
      linarith

theorem primeLo_le' (C : Ctx X LX LXhi sq pack v) {p L S : ℕ} (hp : p.Prime)
    (h1 : (L : ℝ) ≤ Dr * Real.log p) (h2 : Dr * Real.log p ≤ (L : ℝ) + 16)
    (h3 : (S : ℝ) ≤ Dr * √(p : ℝ)) (h4 : Dr * √(p : ℝ) ≤ (S : ℝ) + 1) (fuel k : ℕ) :
    ((primeLo X LX LXhi sq pack p L S fuel k : ℤ) : ℝ) ≤
      Dr * ∑ k' ∈ Finset.Ico k (k + fuel),
        if p ^ k' < X then 2 * condTerm (autocorr (stepFn (Real.log X) v)) p (-1) k' else 0 := by
  induction fuel generalizing k with
  | zero =>
    change ((0 : ℤ) : ℝ) ≤ _
    simp
  | succ fuel ih =>
    change ((cond (Nat.ble X (p ^ k)) 0
      (termLo X LX LXhi sq pack p L S k + primeLo X LX LXhi sq pack p L S fuel (k + 1)) : ℤ) : ℝ)
      ≤ _
    rw [cond_ble]
    split_ifs with hXk
    · rw [Finset.sum_eq_zero]
      · simp
      · intro k' hk'
        have hkk : k ≤ k' := (Finset.mem_Ico.mp hk').1
        have : X ≤ p ^ k' := le_trans hXk (Nat.pow_le_pow_right hp.pos hkk)
        rw [ite_eq_right (not_lt.mpr this)]
    · rw [Finset.sum_eq_sum_Ico_succ_bot (by omega), ite_eq_left (not_le.mp hXk)]
      have ih' := ih (k + 1)
      rw [show k + 1 + fuel = k + (fuel + 1) by omega] at ih'
      have ht := termLo_le' C (k := k) hp h1 h2 h3 h4
      push_cast
      rw [mul_add]
      linarith

/-! ### The two bounds for one prime, in terms of `primeT` -/

theorem two_mul_sum_ite (g : ℕ → ℝ) (s : Finset ℕ) (P : ℕ → Prop) [DecidablePred P] :
    2 * ∑ k ∈ s, (if P k then g k else 0) = ∑ k ∈ s, if P k then 2 * g k else 0 := by
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by split_ifs <;> simp

theorem primeLoP_le_primeT (C : Ctx X LX LXhi sq pack v) (hX14 : X ≤ 16384) {p L S : ℕ}
    (hp : p.Prime)
    (h1 : (L : ℝ) ≤ Dr * Real.log p) (h2 : Dr * Real.log p ≤ (L : ℝ) + 16)
    (h3 : (S : ℝ) ≤ Dr * √(p : ℝ)) (h4 : Dr * √(p : ℝ) ≤ (S : ℝ) + 1) :
    ((primeLoP X LX LXhi sq pack p L S 13 1 : ℤ) : ℝ) ≤
      Dr * primeT (autocorr (stepFn (Real.log X) v)) X p 1 := by
  rw [primeT_eq _ _ hp.two_le (le_trans hX14 (by norm_num) : X ≤ 2 ^ 14), two_mul_sum_ite]
  exact primeLoP_le C hp h1 h2 h3 h4 13 1

theorem primeLo_le_primeT (C : Ctx X LX LXhi sq pack v) (hX14 : X ≤ 16384) {p L S : ℕ}
    (hp : p.Prime)
    (h1 : (L : ℝ) ≤ Dr * Real.log p) (h2 : Dr * Real.log p ≤ (L : ℝ) + 16)
    (h3 : (S : ℝ) ≤ Dr * √(p : ℝ)) (h4 : Dr * √(p : ℝ) ≤ (S : ℝ) + 1) :
    ((primeLo X LX LXhi sq pack p L S 13 1 : ℤ) : ℝ) ≤
      Dr * primeT (autocorr (stepFn (Real.log X) v)) X p (-1) := by
  rw [primeT_eq _ _ hp.two_le (le_trans hX14 (by norm_num) : X ≤ 2 ^ 14), two_mul_sum_ite]
  exact primeLo_le' C hp h1 h2 h3 h4 13 1

/-- The smaller of two integers. -/
def minZ (a b : ℤ) : ℤ := cond (Nat.ble 1 (Int.toNat (Int.sub a b))) b a

theorem minZ_le (a b : ℤ) : minZ a b ≤ a ∧ minZ a b ≤ b := by
  unfold minZ
  rw [cond_ble]
  change (if 1 ≤ (a - b).toNat then b else a) ≤ a ∧ (if 1 ≤ (a - b).toNat then b else a) ≤ b
  split_ifs with h
  · omega
  · omega

/-- The smaller of the two lower bounds is a lower bound of the smaller of the two values. -/
theorem minZ_le_min {a b : ℤ} {x y : ℝ} (ha : (a : ℝ) ≤ Dr * x) (hb : (b : ℝ) ≤ Dr * y) :
    ((minZ a b : ℤ) : ℝ) ≤ Dr * min x y := by
  have hmin := minZ_le a b
  have h1 : ((minZ a b : ℤ) : ℝ) ≤ (a : ℝ) := by exact_mod_cast hmin.1
  have h2 : ((minZ a b : ℤ) : ℝ) ≤ (b : ℝ) := by exact_mod_cast hmin.2
  rw [mul_min_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ Dr)]
  exact le_min (h1.trans ha) (h2.trans hb)

/-! ### The archimedean term -/

theorem le_jHiN' (C : Ctx X LX LXhi sq pack v) (hs : 0 < sqrtLo20 X) (cnt : ℕ)
    (hcnt : cnt ≤ 1008) :
    Dr * ((1 - corr v 1) + ∑ m ∈ Finset.range cnt, jReal (Real.log X) v (16 + m) +
        4 / (3 * X * √(X : ℝ) * (1 - 1 / ((X : ℝ) * X)))) ≤
      (jHiN cnt X LX LXhi sq pack : ℝ) := by
  have hX1 : (1 : ℝ) < X := by exact_mod_cast C.hX
  have hlX : 0 < Real.log X := Real.log_pos hX1
  have hE0 : 0 ≤ Real.exp (-(Real.log X / 2048)) := (Real.exp_pos _).le
  -- `r = exp (-(log X)/2048)`
  have hr : Dr * Real.exp (-(Real.log X / 2048)) ≤ (expNegHi Dn 10 0 (LX / 2048) : ℝ) := by
    have h := le_expNegHi (D := Dn) (by norm_num) 10 0 (x := LX / 2048)
      (t := Real.log X / 2048) (by
        rw [castD]
        refine (fdiv_le _ _).trans ?_
        have := C.lx
        push_cast
        linarith)
    rw [castD] at h
    exact h
  have hr3 : Dr * Real.exp (-(Real.log X / 2048)) ^ 3 ≤
      (fpowHi Dn (expNegHi Dn 10 0 (LX / 2048)) 3 : ℝ) := le_fpowHi' hE0 hr 3
  have hr4 : Dr * Real.exp (-(Real.log X / 2048)) ^ 4 ≤
      (fpowHi Dn (expNegHi Dn 10 0 (LX / 2048)) 4 : ℝ) := le_fpowHi' hE0 hr 4
  have hA0 : Dr * Real.exp (-(Real.log X / 2048)) ^ (3 * 16) ≤
      (fpowHi Dn (fpowHi Dn (expNegHi Dn 10 0 (LX / 2048)) 3) 16 : ℝ) := by
    have h := le_fpowHi' (pow_nonneg hE0 3) hr3 16
    rw [← pow_mul] at h
    exact h
  have hB0 : Dr * Real.exp (-(Real.log X / 2048)) ^ (4 * 16) ≤
      (fpowHi Dn (fpowHi Dn (expNegHi Dn 10 0 (LX / 2048)) 4) 16 : ℝ) := by
    have h := le_fpowHi' (pow_nonneg hE0 4) hr4 16
    rw [← pow_mul] at h
    exact h
  have hstep : Dr * (Real.log X / 64 / 16) ≤ ((cdiv LXhi 1024 : ℕ) : ℝ) := by
    refine le_trans ?_ (div_le_cdiv _ _ (by norm_num))
    have := C.lxhi
    push_cast
    linarith
  have hloop := (jLoop_inv C.pk hlX hstep hr3 hr4 hA0 hB0 cnt hcnt).2.2
  have hfirst := first_le C.pk
  have htail := tail_le C.hX hs
  change _ ≤ ((cdiv ((sq + 4611686018427387904 - getN pack 1) * Dn) sq +
    (jLoop (cdiv LXhi 1024) sq pack (fpowHi Dn (expNegHi Dn 10 0 (LX / 2048)) 3)
      (fpowHi Dn (expNegHi Dn 10 0 (LX / 2048)) 4)
      (fpowHi Dn (fpowHi Dn (expNegHi Dn 10 0 (LX / 2048)) 3) 16)
      (fpowHi Dn (fpowHi Dn (expNegHi Dn 10 0 (LX / 2048)) 4) 16) cnt).2.2 +
    cdiv (4 * X * Dn * Dn) (3 * sqrtLo20 X * (X * X - 1)) : ℕ) : ℝ)
  rw [Nat.cast_add, Nat.cast_add, mul_add, mul_add]
  linarith

theorem le_jHi' (C : Ctx X LX LXhi sq pack v) (hs : 0 < sqrtLo20 X) :
    Dr * Jterm (autocorr (stepFn (Real.log X) v)) ≤ (jHi X LX LXhi sq pack : ℝ) := by
  unfold jHi
  have hJ := Jterm_le_jReal C.hX C.pk.ne C.pk.len
  rw [show (16 * 63 : ℕ) = 1008 from rfl] at hJ
  exact (mul_le_mul_of_nonneg_left hJ (by norm_num)).trans (le_jHiN' C hs 1008 le_rfl)

/-- The context of a checked vector. -/
theorem ctx_of_pack {X : ℕ} {v : List ℤ} {pack : ℕ} (hX : 2 ≤ X)
    (hpk : packCheck v pack = true) (hlx : 0 < logLo P20 X) :
    Ctx X (logLo P20 X) (logHi P20 X) (Nat.sub (getN pack 0) 4611686018427387904) pack
      (v.map (fun z : ℤ => (z : ℝ))) := by
  refine ⟨hX, packOK_of_check hpk, hlx, ?_, ?_⟩
  · have := logLo_le P20_valid (n := X) (by omega)
    rw [P20_D'] at this
    exact this
  · have := le_logHi P20_valid (n := X) (by omega)
    rw [P20_D'] at this
    exact this

end Exp7.Rows

#print axioms Exp7.Rows.primeLoP_le_primeT
#print axioms Exp7.Rows.primeLo_le_primeT
#print axioms Exp7.Rows.le_jHi'
