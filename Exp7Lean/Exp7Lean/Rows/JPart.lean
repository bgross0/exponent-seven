import Exp7Lean.Rows.PrimePart
import Exp7Lean.Numerics.FixedExp
import Exp7Lean.Numerics.Checks

/-!
Certificate rows, step 4: a certified upper bound (fixed point, scale `10^20`) for the archimedean
term `Jterm (autocorr (stepFn (log X) v))`, following `Jterm_log_le`.

The weights `a(u_m) = 2 r^{3m} / (1 - r^{4m})`, `r = X^{-1/2048} = exp (-(log X)/2048)`,
`u_m = m (log X) / 1024`, are obtained from running products rounded up.
-/

namespace Exp7.Rows

open Real Exp7.Num

local notation "Dn" => (100000000000000000000 : ℕ)
local notation "Dr" => (100000000000000000000 : ℝ)

theorem castD : ((Dn : ℕ) : ℝ) = Dr := by norm_num

theorem le_fmulHi' {a b : ℕ} {x y : ℝ} (hy : 0 ≤ y) (ha : Dr * x ≤ (a : ℝ))
    (hb : Dr * y ≤ (b : ℝ)) : Dr * (x * y) ≤ (fmulHi Dn a b : ℝ) := by
  have h := le_fmulHi (D := Dn) (by norm_num) (a := a) (b := b) (x := x) (y := y) hy
    (by rw [castD]; exact ha) (by rw [castD]; exact hb)
  rw [castD] at h
  exact h

theorem le_fpowHi' {r : ℕ} {x : ℝ} (hx : 0 ≤ x) (hr : Dr * x ≤ (r : ℝ)) (k : ℕ) :
    Dr * x ^ k ≤ (fpowHi Dn r k : ℝ) := by
  have h := le_fpowHi (D := Dn) (by norm_num) (r := r) (x := x) hx (by rw [castD]; exact hr) k
  rw [castD] at h
  exact h

/-! ### The real sum, indexed by `m = 16 j + i` -/

/-- The summand of `J⁺` for the subcell `m = 16 j + i`. -/
noncomputable def jReal (lX : ℝ) (v : List ℝ) (m : ℕ) : ℝ :=
  (lX / 64 / 16) * aKer ((lX / 64 / 16) * (m : ℝ)) *
    (1 - (corr v (m / 16) + (corr v (m / 16 + 1) - corr v (m / 16)) *
      ((2 * ((m % 16 : ℕ) : ℝ) + 1) / 32)))

theorem sum_blocks (t : ℕ → ℝ) (J : ℕ) :
    ∑ j ∈ Finset.Ico 1 (J + 1), ∑ i ∈ Finset.range 16, t (j * 16 + i) =
      ∑ m ∈ Finset.range (16 * J), t (16 + m) := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [Finset.sum_Ico_succ_top (by omega), ih, show 16 * (J + 1) = 16 * J + 16 by ring,
      Finset.sum_range_add]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    ring

theorem Jterm_le_jReal {X : ℕ} {v : List ℝ} (hX : 2 ≤ X) (hv : ∃ t ∈ v, t ≠ 0)
    (hlen : v.length = 64) :
    Jterm (autocorr (stepFn (Real.log X) v)) ≤
      (1 - corr v 1) + ∑ m ∈ Finset.range (16 * 63), jReal (Real.log X) v (16 + m) +
        4 / (3 * X * √(X : ℝ) * (1 - 1 / ((X : ℝ) * X))) := by
  have h := Jterm_log_le (v := v) hX hv
  rw [hlen] at h
  simp only [Nat.cast_ofNat] at h
  have key : ∀ j i : ℕ, i < 16 → jReal (Real.log X) v (j * 16 + i) =
      (Real.log X / 64 / 16) * aKer ((Real.log X / 64 / 16) * ((j : ℝ) * 16 + i)) *
        (1 - (corr v j + (corr v (j + 1) - corr v j) * ((2 * (i : ℝ) + 1) / 32))) := by
    intro j i hi
    have e1 : (j * 16 + i) / 16 = j := by omega
    have e2 : (j * 16 + i) % 16 = i := by omega
    unfold jReal
    rw [e1, e2]
    push_cast
    ring
  have e : ∑ m ∈ Finset.range (16 * 63), jReal (Real.log X) v (16 + m) =
      ∑ j ∈ Finset.Ico (1 : ℕ) 64, ∑ i ∈ Finset.range 16,
        (Real.log X / 64 / 16) * aKer ((Real.log X / 64 / 16) * (((j : ℕ) : ℝ) * 16 + i)) *
          (1 - (corr v j + (corr v (j + 1) - corr v j) * ((2 * (i : ℝ) + 1) / 32))) := by
    rw [← sum_blocks]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i hi =>
      key j i (Finset.mem_range.mp hi)
  rw [e]
  exact h

/-! ### One term -/

/-- Upper bound for `10^20 · jReal (log X) v m`, given `A ≥ 10^20 r^{3m}`, `B ≥ 10^20 r^{4m}`. -/
def jTerm (stepHi sq pack A B m : ℕ) : ℕ :=
  cond (Nat.ble Dn B) (Nat.mul 2 Dn)
    ((fun i a b => cdiv (Nat.mul (Nat.mul stepHi (cdiv (Nat.mul (Nat.mul 2 A) Dn) (Nat.sub Dn B)))
        (Nat.sub (Nat.add (Nat.mul 32 sq) 147573952589676412928)
          (Nat.add (Nat.mul (Nat.sub 31 (Nat.mul 2 i)) a) (Nat.mul (Nat.succ (Nat.mul 2 i)) b))))
        (Nat.mul (Nat.mul 32 Dn) sq))
      (Nat.mod m 16) (getN pack (Nat.div m 16)) (getN pack (Nat.succ (Nat.div m 16))))

theorem jTerm_alg {D st aK sq om : ℝ} (hD : D ≠ 0) (hsq : sq ≠ 0) :
    D * (st * aK * om) = (D * st) * (D * aK) * (32 * sq * om) / (32 * D * sq) := by
  field_simp

variable {sq pack : ℕ} {v : List ℝ}

theorem le_jTerm (pk : PackOK v sq pack) {lX : ℝ} (hlX : 0 < lX) {stepHi A B m : ℕ}
    (hm1 : 16 ≤ m) (hm2 : m < 1024) (hstep : Dr * (lX / 64 / 16) ≤ (stepHi : ℝ))
    (hA : Dr * Real.exp (-(lX / 2048)) ^ (3 * m) ≤ (A : ℝ))
    (hB : Dr * Real.exp (-(lX / 2048)) ^ (4 * m) ≤ (B : ℝ)) :
    Dr * jReal lX v m ≤ (jTerm stepHi sq pack A B m : ℝ) := by
  have hmr : (16 : ℝ) ≤ m := by exact_mod_cast hm1
  have hst : 0 < lX / 64 / 16 := by positivity
  have hu : 0 < lX / 64 / 16 * (m : ℝ) := by positivity
  have hj2 : m / 16 ≤ 63 := by omega
  have hi : m % 16 < 16 := Nat.mod_lt _ (by norm_num)
  have ha := pk.c (m / 16) (by omega)
  have hb := pk.c (m / 16 + 1) (by omega)
  have hsq : (0 : ℝ) < sq := by exact_mod_cast pk.sqpos
  have hir : ((m % 16 : ℕ) : ℝ) ≤ 15 := by exact_mod_cast (by omega : m % 16 ≤ 15)
  have hi0 : (0 : ℝ) ≤ ((m % 16 : ℕ) : ℝ) := Nat.cast_nonneg _
  have haK0 : 0 < aKer (lX / 64 / 16 * (m : ℝ)) := aKer_pos hu
  unfold jReal
  generalize hmean : (1 - (corr v (m / 16) + (corr v (m / 16 + 1) - corr v (m / 16)) *
      ((2 * ((m % 16 : ℕ) : ℝ) + 1) / 32))) = om
  unfold jTerm
  rw [cond_ble]
  split_ifs with hDB
  · -- fallback: the term is at most `2`
    have hk1 : lX / 64 / 16 * aKer (lX / 64 / 16 * (m : ℝ)) ≤ 1 := by
      have h1 := aKer_mul_self_le_one hu
      have hm0 : (0 : ℝ) < m := by linarith
      calc lX / 64 / 16 * aKer (lX / 64 / 16 * (m : ℝ))
          = aKer (lX / 64 / 16 * (m : ℝ)) * (lX / 64 / 16 * (m : ℝ)) / m := by field_simp
        _ ≤ 1 / m := div_le_div_of_nonneg_right h1 hm0.le
        _ ≤ 1 := by rw [div_le_one hm0]; linarith
    have hk0 : 0 ≤ lX / 64 / 16 * aKer (lX / 64 / 16 * (m : ℝ)) := mul_nonneg hst.le haK0.le
    have hom : om ≤ 2 := by
      have h1 := (abs_le.mp (abs_corr_le_one pk.ne (m / 16))).1
      have h2 := (abs_le.mp (abs_corr_le_one pk.ne (m / 16 + 1))).1
      have ht0 : (0 : ℝ) ≤ (2 * ((m % 16 : ℕ) : ℝ) + 1) / 32 := by positivity
      have ht1 : (2 * ((m % 16 : ℕ) : ℝ) + 1) / 32 ≤ 1 := by
        rw [div_le_one (by norm_num)]; linarith
      rw [← hmean]
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ corr v (m / 16) + 1)
        (by linarith : (0 : ℝ) ≤ 1 - (2 * ((m % 16 : ℕ) : ℝ) + 1) / 32),
        mul_nonneg (by linarith : (0 : ℝ) ≤ corr v (m / 16 + 1) + 1) ht0]
    change _ ≤ ((2 * Dn : ℕ) : ℝ)
    push_cast
    have h3 : lX / 64 / 16 * aKer (lX / 64 / 16 * (m : ℝ)) * om ≤ 1 * 2 := by
      calc lX / 64 / 16 * aKer (lX / 64 / 16 * (m : ℝ)) * om
          ≤ lX / 64 / 16 * aKer (lX / 64 / 16 * (m : ℝ)) * 2 :=
            mul_le_mul_of_nonneg_left hom hk0
        _ ≤ 1 * 2 := mul_le_mul_of_nonneg_right hk1 (by norm_num)
    linarith
  · have hBD : B ≤ Dn := le_of_lt (not_le.mp hDB)
    have hBD' : 0 < Dn - B := Nat.sub_pos_of_lt (not_le.mp hDB)
    change _ ≤ ((cdiv (stepHi * cdiv (2 * A * Dn) (Dn - B) *
      (32 * sq + 147573952589676412928 -
        ((31 - 2 * (m % 16)) * getN pack (m / 16) +
          (2 * (m % 16) + 1) * getN pack (m / 16 + 1)))) (32 * Dn * sq) : ℕ) : ℝ)
    -- the exponentials
    have he3 : Real.exp (-(3 / 2) * (lX / 64 / 16 * (m : ℝ))) =
        Real.exp (-(lX / 2048)) ^ (3 * m) := by
      rw [← Real.exp_natCast_mul]; congr 1; push_cast; ring
    have he4 : Real.exp (-2 * (lX / 64 / 16 * (m : ℝ))) =
        Real.exp (-(lX / 2048)) ^ (4 * m) := by
      rw [← Real.exp_natCast_mul]; congr 1; push_cast; ring
    have he4lt : 0 < 1 - Real.exp (-(lX / 2048)) ^ (4 * m) := by
      rw [← he4]; exact one_sub_exp_neg_two_mul_pos hu
    have he30 : 0 ≤ Real.exp (-(lX / 2048)) ^ (3 * m) := by positivity
    -- the weight
    have haK : Dr * aKer (lX / 64 / 16 * (m : ℝ)) ≤
        ((cdiv (2 * A * Dn) (Dn - B) : ℕ) : ℝ) := by
      have h := le_fdivHi (D := Dn) (by norm_num) (a := 2 * A) (b := Dn - B)
        (x := 2 * Real.exp (-(lX / 2048)) ^ (3 * m))
        (y := 1 - Real.exp (-(lX / 2048)) ^ (4 * m)) hBD'
        (by rw [castD]; push_cast; linarith)
        (by rw [castD, Nat.cast_sub hBD]; push_cast; linarith)
      rw [castD] at h
      unfold aKer
      rw [he3, he4]
      exact h
    -- the affine factor
    have hom : 32 * (sq : ℝ) * om ≤ ((32 * sq + 147573952589676412928 -
        ((31 - 2 * (m % 16)) * getN pack (m / 16) +
          (2 * (m % 16) + 1) * getN pack (m / 16 + 1)) : ℕ) : ℝ) := by
      refine le_trans (le_of_eq ?_) (cast_sub_ge _ _)
      push_cast [Nat.cast_sub (by omega : 2 * (m % 16) ≤ 31)]
      rw [ha, hb, ← hmean]
      ring
    have hP0 : 0 ≤ Dr * (lX / 64 / 16) * (Dr * aKer (lX / 64 / 16 * (m : ℝ))) := by positivity
    have hP : Dr * (lX / 64 / 16) * (Dr * aKer (lX / 64 / 16 * (m : ℝ))) ≤
        (stepHi : ℝ) * ((cdiv (2 * A * Dn) (Dn - B) : ℕ) : ℝ) :=
      mul_le_mul hstep haK (by positivity) (Nat.cast_nonneg _)
    have hden : 0 < 32 * Dn * sq := Nat.mul_pos (by norm_num) pk.sqpos
    refine le_trans ?_ (div_le_cdiv _ _ hden)
    rw [jTerm_alg (D := Dr) (by norm_num) hsq.ne']
    have hdr : ((32 * Dn * sq : ℕ) : ℝ) = 32 * Dr * sq := by push_cast; ring
    rw [hdr]
    apply div_le_div_of_nonneg_right _ (by positivity)
    push_cast at hom ⊢
    calc Dr * (lX / 64 / 16) * (Dr * aKer (lX / 64 / 16 * (m : ℝ))) * (32 * (sq : ℝ) * om)
        ≤ Dr * (lX / 64 / 16) * (Dr * aKer (lX / 64 / 16 * (m : ℝ))) * _ :=
          mul_le_mul_of_nonneg_left hom hP0
      _ ≤ _ := by
          exact mul_le_mul_of_nonneg_right hP (by positivity)

/-! ### The loop -/

/-- State `(A, B, acc)` after the terms `m = 16, …, 16 + cnt - 1`. -/
def jLoop (stepHi sq pack r3 r4 A0 B0 cnt : ℕ) : ℕ × ℕ × ℕ :=
  Nat.rec (motive := fun _ => ℕ × ℕ × ℕ) (A0, B0, 0)
    (fun i ih => (fmulHi Dn ih.1 r3, fmulHi Dn ih.2.1 r4,
      Nat.add ih.2.2 (jTerm stepHi sq pack ih.1 ih.2.1 (Nat.add 16 i)))) cnt

theorem jLoop_succ (stepHi sq pack r3 r4 A0 B0 cnt : ℕ) :
    jLoop stepHi sq pack r3 r4 A0 B0 (cnt + 1) =
      (fmulHi Dn (jLoop stepHi sq pack r3 r4 A0 B0 cnt).1 r3,
        fmulHi Dn (jLoop stepHi sq pack r3 r4 A0 B0 cnt).2.1 r4,
        (jLoop stepHi sq pack r3 r4 A0 B0 cnt).2.2 +
          jTerm stepHi sq pack (jLoop stepHi sq pack r3 r4 A0 B0 cnt).1
            (jLoop stepHi sq pack r3 r4 A0 B0 cnt).2.1 (16 + cnt)) := rfl

theorem jLoop_inv (pk : PackOK v sq pack) {lX : ℝ} (hlX : 0 < lX) {stepHi r3 r4 A0 B0 : ℕ}
    (hstep : Dr * (lX / 64 / 16) ≤ (stepHi : ℝ))
    (hr3 : Dr * Real.exp (-(lX / 2048)) ^ 3 ≤ (r3 : ℝ))
    (hr4 : Dr * Real.exp (-(lX / 2048)) ^ 4 ≤ (r4 : ℝ))
    (hA0 : Dr * Real.exp (-(lX / 2048)) ^ (3 * 16) ≤ (A0 : ℝ))
    (hB0 : Dr * Real.exp (-(lX / 2048)) ^ (4 * 16) ≤ (B0 : ℝ)) (cnt : ℕ) (hcnt : cnt ≤ 1008) :
    Dr * Real.exp (-(lX / 2048)) ^ (3 * (16 + cnt)) ≤
        ((jLoop stepHi sq pack r3 r4 A0 B0 cnt).1 : ℝ) ∧
      Dr * Real.exp (-(lX / 2048)) ^ (4 * (16 + cnt)) ≤
        ((jLoop stepHi sq pack r3 r4 A0 B0 cnt).2.1 : ℝ) ∧
      Dr * ∑ m ∈ Finset.range cnt, jReal lX v (16 + m) ≤
        ((jLoop stepHi sq pack r3 r4 A0 B0 cnt).2.2 : ℝ) := by
  induction cnt with
  | zero =>
    refine ⟨hA0, hB0, ?_⟩
    change _ ≤ ((0 : ℕ) : ℝ)
    simp
  | succ cnt ih =>
    obtain ⟨iA, iB, iS⟩ := ih (by omega)
    have hE0 : 0 ≤ Real.exp (-(lX / 2048)) := (Real.exp_pos _).le
    rw [jLoop_succ]
    refine ⟨?_, ?_, ?_⟩
    · have h := le_fmulHi' (pow_nonneg hE0 3) iA hr3
      rw [← pow_add] at h
      exact h
    · have h := le_fmulHi' (pow_nonneg hE0 4) iB hr4
      rw [← pow_add] at h
      exact h
    · have ht := le_jTerm pk hlX (m := 16 + cnt) (by omega) (by omega) hstep iA iB
      rw [Finset.sum_range_succ, mul_add]
      push_cast
      exact add_le_add iS ht

/-! ### The upper bound -/

/-- First cell, `cnt` subcells and tail of the upper bound for `10^20 · Jterm`. -/
def jHiN (cnt X LX LXhi sq pack : ℕ) : ℕ :=
  (fun r3 r4 => Nat.add (Nat.add
      (cdiv (Nat.mul (Nat.sub (Nat.add sq 4611686018427387904) (getN pack 1)) Dn) sq)
      (jLoop (cdiv LXhi 1024) sq pack r3 r4 (fpowHi Dn r3 16) (fpowHi Dn r4 16) cnt).2.2)
      (cdiv (Nat.mul (Nat.mul (Nat.mul 4 X) Dn) Dn)
        (Nat.mul (Nat.mul 3 (sqrtLo20 X)) (Nat.sub (Nat.mul X X) 1))))
    (fpowHi Dn (expNegHi Dn 10 0 (Nat.div LX 2048)) 3)
    (fpowHi Dn (expNegHi Dn 10 0 (Nat.div LX 2048)) 4)

/-- Upper bound for `10^20 · Jterm (autocorr (stepFn (log X) v))`. -/
def jHi (X LX LXhi sq pack : ℕ) : ℕ := jHiN 1008 X LX LXhi sq pack

theorem first_le (pk : PackOK v sq pack) :
    Dr * (1 - corr v 1) ≤
      ((cdiv ((sq + 4611686018427387904 - getN pack 1) * Dn) sq : ℕ) : ℝ) := by
  have hsq : (0 : ℝ) < sq := by exact_mod_cast pk.sqpos
  have h1 := pk.c 1 (by norm_num)
  refine le_trans ?_ (div_le_cdiv _ _ pk.sqpos)
  rw [le_div_iff₀ hsq]
  have h2 : (sq : ℝ) * (1 - corr v 1) ≤ ((sq + 4611686018427387904 - getN pack 1 : ℕ) : ℝ) := by
    refine le_trans (le_of_eq ?_) (cast_sub_ge _ _)
    push_cast
    rw [h1]
    ring
  push_cast
  nlinarith

theorem tail_le {X : ℕ} (hX : 2 ≤ X) (hs : 0 < sqrtLo20 X) :
    Dr * (4 / (3 * X * √(X : ℝ) * (1 - 1 / ((X : ℝ) * X)))) ≤
      ((cdiv (4 * X * Dn * Dn) (3 * sqrtLo20 X * (X * X - 1)) : ℕ) : ℝ) := by
  have hXr : (2 : ℝ) ≤ X := by exact_mod_cast hX
  have hX0 : (0 : ℝ) < X := by linarith
  have hrt : (0 : ℝ) < √(X : ℝ) := Real.sqrt_pos.mpr hX0
  have hXX : 1 ≤ X * X := Nat.mul_pos (by omega) (by omega)
  have hXX' : (0 : ℝ) < (X : ℝ) * X - 1 := by nlinarith
  have hsr : (0 : ℝ) < (sqrtLo20 X : ℝ) := by exact_mod_cast hs
  have hsle : (sqrtLo20 X : ℝ) ≤ Dr * √(X : ℝ) := by
    have := sqrtLo_le 100000000000000000000 4 7 X
    rw [castD] at this
    exact this
  have hden : 0 < 3 * sqrtLo20 X * (X * X - 1) :=
    Nat.mul_pos (Nat.mul_pos (by norm_num) hs) (Nat.sub_pos_of_lt (by nlinarith))
  refine le_trans ?_ (div_le_cdiv _ _ hden)
  have e1 : Dr * (4 / (3 * X * √(X : ℝ) * (1 - 1 / ((X : ℝ) * X)))) =
      4 * X * Dr * Dr / (3 * (Dr * √(X : ℝ)) * ((X : ℝ) * X - 1)) := by
    have h1 : (1 : ℝ) - 1 / ((X : ℝ) * X) = ((X : ℝ) * X - 1) / ((X : ℝ) * X) := by
      field_simp
    rw [h1]
    field_simp
  have e2 : ((4 * X * Dn * Dn : ℕ) : ℝ) / ((3 * sqrtLo20 X * (X * X - 1) : ℕ) : ℝ) =
      4 * X * Dr * Dr / (3 * (sqrtLo20 X : ℝ) * ((X : ℝ) * X - 1)) := by
    push_cast [Nat.cast_sub hXX]
    ring
  rw [e1, e2]
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsle (by norm_num)) hXX'.le

variable {X LX LXhi : ℕ}

theorem le_jHiN (C : RowCtx X LX LXhi sq pack v) (hs : 0 < sqrtLo20 X) (cnt : ℕ)
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

theorem le_jHi (C : RowCtx X LX LXhi sq pack v) (hs : 0 < sqrtLo20 X) :
    Dr * Jterm (autocorr (stepFn (Real.log X) v)) ≤ (jHi X LX LXhi sq pack : ℝ) := by
  unfold jHi
  have hJ := Jterm_le_jReal C.hX C.pk.ne C.pk.len
  rw [show (16 * 63 : ℕ) = 1008 from rfl] at hJ
  exact (mul_le_mul_of_nonneg_left hJ (by norm_num)).trans (le_jHiN C hs 1008 le_rfl)

end Exp7.Rows
