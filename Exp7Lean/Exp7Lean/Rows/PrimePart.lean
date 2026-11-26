import Exp7Lean.Rows.InertSum
import Exp7Lean.Rows.Corr
import Exp7Lean.Analytic.JBound
import Exp7Lean.Numerics.BenchTable

/-!
Certificate rows, step 3: a certified lower bound (fixed point, scale `10^20`) for the
prime-power side `inertSum (autocorr (stepFn (log X) v)) X`.

`totalLo X LX LXhi sq pack` folds over the certified table `primeTable6400`; for each prime
`p < X` and each `k ≥ 1` with `p ^ k < X` it adds `termLo`, a lower bound of
`10^20 · 2 (-1)^k log p · f(log p^k) / √(p^k)`.  The cell index `j` of `log p^k` is certified by
the exact integer comparison `X^j ≤ (p^k)^64 ≤ X^(j+1)`.
-/

namespace Exp7.Rows

open Real Exp7.Num

local notation "Dn" => (100000000000000000000 : ℕ)
local notation "Dr" => (100000000000000000000 : ℝ)
local notation "OFFr" => (4611686018427387904 : ℝ)
local notation "Zn" => (461168601842738790400000000000000000000 : ℕ)

/-- The hypotheses shared by the evaluators of one row. -/
structure RowCtx (X LX LXhi sq pack : ℕ) (v : List ℝ) : Prop where
  hX : 2 ≤ X
  hX' : X ≤ 6400
  pk : PackOK v sq pack
  lxpos : 0 < LX
  lx : (LX : ℝ) ≤ Dr * Real.log X
  lxhi : Dr * Real.log X ≤ (LXhi : ℝ)

theorem cond_beq {α : Type} (a b : ℕ) (x y : α) :
    cond (Nat.beq a b) x y = if a = b then x else y := by
  rw [beq_eq_decide]
  by_cases h : a = b <;> simp [h]

theorem cast_sub_le_of {a b : ℕ} {x : ℝ} (h0 : 0 ≤ x) (h : (a : ℝ) - b ≤ x) :
    ((a - b : ℕ) : ℝ) ≤ x := by
  rcases le_total b a with h1 | h1
  · rw [Nat.cast_sub h1]; exact h
  · rw [Nat.sub_eq_zero_of_le h1]; simpa using h0

/-! ### The position inside the cell -/

/-- Lower bound for `10^20 θ`, `θ = 64 k log p / log X - j`. -/
def hLo (LXhi L k j : ℕ) : ℕ :=
  Nat.sub (Nat.div (Nat.mul (Nat.mul (Nat.mul 64 k) L) Dn) LXhi) (Nat.mul j Dn)

/-- Upper bound for `10^20 θ`, clipped at `10^20`. -/
def hHi (LX L k j : ℕ) : ℕ :=
  (fun x => cond (Nat.ble Dn x) Dn x)
    (Nat.sub (cdiv (Nat.mul (Nat.mul (Nat.mul 64 k) (Nat.add L 16)) Dn) LX) (Nat.mul j Dn))

theorem hLo_le {LXhi L k j : ℕ} {lp lX θ : ℝ} (hlX : 0 < lX) (hL : (L : ℝ) ≤ Dr * lp)
    (hLX : Dr * lX ≤ (LXhi : ℝ)) (hθ : θ = 64 * (k * lp) / lX - j) (h0 : 0 ≤ θ) :
    (hLo LXhi L k j : ℝ) ≤ Dr * θ := by
  have hpos : (0 : ℝ) < LXhi := lt_of_lt_of_le (by positivity) hLX
  have hlp : 0 ≤ lp := by
    have : (0 : ℝ) ≤ Dr * lp := le_trans (Nat.cast_nonneg L) hL
    exact nonneg_of_mul_nonneg_right this (by norm_num)
  change ((64 * k * L * Dn / LXhi - j * Dn : ℕ) : ℝ) ≤ _
  apply cast_sub_le_of (by positivity)
  have h1 : ((64 * k * L * Dn / LXhi : ℕ) : ℝ) ≤ ((64 * k * L * Dn : ℕ) : ℝ) / (LXhi : ℝ) :=
    fdiv_le _ _
  have h2 : ((64 * k * L * Dn : ℕ) : ℝ) / (LXhi : ℝ) ≤ Dr * (64 * (k * lp) / lX) := by
    rw [div_le_iff₀ hpos]
    have hq : 0 ≤ Dr * (64 * (k * lp) / lX) := by positivity
    calc ((64 * k * L * Dn : ℕ) : ℝ) = 64 * k * (L : ℝ) * Dr := by push_cast; ring
      _ ≤ 64 * k * (Dr * lp) * Dr := by gcongr
      _ = Dr * (64 * (k * lp) / lX) * (Dr * lX) := by field_simp
      _ ≤ Dr * (64 * (k * lp) / lX) * (LXhi : ℝ) := mul_le_mul_of_nonneg_left hLX hq
  rw [hθ]
  push_cast at h1 h2 ⊢
  linarith

theorem hHi_le (LX L k j : ℕ) : hHi LX L k j ≤ Dn := by
  unfold hHi
  simp only [cond_ble]
  split_ifs with h
  · exact le_rfl
  · exact le_of_lt (not_le.mp h)

theorem le_hHi {LX L k j : ℕ} {lp lX θ : ℝ} (hlX : 0 < lX) (hlp : 0 ≤ lp) (hLXpos : 0 < LX)
    (hL : Dr * lp ≤ (L : ℝ) + 16) (hLX : (LX : ℝ) ≤ Dr * lX)
    (hθ : θ = 64 * (k * lp) / lX - j) (h1 : θ ≤ 1) :
    Dr * θ ≤ (hHi LX L k j : ℝ) := by
  have hpos : (0 : ℝ) < LX := by exact_mod_cast hLXpos
  unfold hHi
  simp only [cond_ble]
  split_ifs with h
  · push_cast
    linarith
  · change _ ≤ ((cdiv (64 * k * (L + 16) * Dn) LX - j * Dn : ℕ) : ℝ)
    refine le_trans ?_ (cast_sub_ge _ _)
    have h2 := div_le_cdiv (64 * k * (L + 16) * Dn) LX hLXpos
    have h3 : Dr * (64 * (k * lp) / lX) ≤ ((64 * k * (L + 16) * Dn : ℕ) : ℝ) / (LX : ℝ) := by
      rw [le_div_iff₀ hpos]
      have hq : 0 ≤ Dr * (64 * (k * lp) / lX) := by positivity
      calc Dr * (64 * (k * lp) / lX) * (LX : ℝ) ≤ Dr * (64 * (k * lp) / lX) * (Dr * lX) :=
            mul_le_mul_of_nonneg_left hLX hq
        _ = 64 * k * (Dr * lp) * Dr := by field_simp
        _ ≤ 64 * k * ((L : ℝ) + 16) * Dr := by gcongr
        _ = ((64 * k * (L + 16) * Dn : ℕ) : ℝ) := by push_cast; ring
    rw [hθ]
    push_cast at h2 h3 ⊢
    linarith

/-! ### The value of `f`, shifted and scaled: `10^20 (sq f + 2^62)` -/

/-- Lower bound for `a D + t (b - a)`, `Hlo ≤ t ≤ Hhi ≤ D`. -/
def fLo (a b Hlo Hhi : ℕ) : ℕ :=
  cond (Nat.ble a b) (Nat.add (Nat.mul a Dn) (Nat.mul Hlo (Nat.sub b a)))
    (Nat.sub (Nat.mul a Dn) (Nat.mul Hhi (Nat.sub a b)))

/-- Upper bound for `a D + t (b - a)`. -/
def fHi (a b Hlo Hhi : ℕ) : ℕ :=
  cond (Nat.ble a b) (Nat.add (Nat.mul a Dn) (Nat.mul Hhi (Nat.sub b a)))
    (Nat.sub (Nat.mul a Dn) (Nat.mul Hlo (Nat.sub a b)))

theorem fLo_le {a b Hlo Hhi : ℕ} {t : ℝ} (h2 : (Hlo : ℝ) ≤ t) (h3 : t ≤ (Hhi : ℝ))
    (h4 : Hhi ≤ Dn) : (fLo a b Hlo Hhi : ℝ) ≤ a * Dr + t * ((b : ℝ) - a) := by
  unfold fLo
  simp only [cond_ble]
  split_ifs with hab
  · change ((a * Dn + Hlo * (b - a) : ℕ) : ℝ) ≤ _
    have hab' : (0 : ℝ) ≤ (b : ℝ) - a := sub_nonneg.mpr (by exact_mod_cast hab)
    push_cast [Nat.cast_sub hab]
    have := mul_le_mul_of_nonneg_right h2 hab'
    linarith
  · have hba : b ≤ a := le_of_lt (not_le.mp hab)
    have hle : Hhi * (a - b) ≤ a * Dn := by
      calc Hhi * (a - b) ≤ Dn * a := Nat.mul_le_mul h4 (Nat.sub_le _ _)
        _ = a * Dn := Nat.mul_comm _ _
    change ((a * Dn - Hhi * (a - b) : ℕ) : ℝ) ≤ _
    have hab' : (0 : ℝ) ≤ (a : ℝ) - b := sub_nonneg.mpr (by exact_mod_cast hba)
    rw [Nat.cast_sub hle]
    push_cast [Nat.cast_sub hba]
    have := mul_le_mul_of_nonneg_right h3 hab'
    linarith

theorem le_fHi {a b Hlo Hhi : ℕ} {t : ℝ} (h2 : (Hlo : ℝ) ≤ t) (h3 : t ≤ (Hhi : ℝ)) :
    a * Dr + t * ((b : ℝ) - a) ≤ (fHi a b Hlo Hhi : ℝ) := by
  unfold fHi
  simp only [cond_ble]
  split_ifs with hab
  · change _ ≤ ((a * Dn + Hhi * (b - a) : ℕ) : ℝ)
    have hab' : (0 : ℝ) ≤ (b : ℝ) - a := sub_nonneg.mpr (by exact_mod_cast hab)
    push_cast [Nat.cast_sub hab]
    have := mul_le_mul_of_nonneg_right h3 hab'
    linarith
  · have hba : b ≤ a := le_of_lt (not_le.mp hab)
    change _ ≤ ((a * Dn - Hlo * (a - b) : ℕ) : ℝ)
    refine le_trans ?_ (cast_sub_ge _ _)
    have hab' : (0 : ℝ) ≤ (a : ℝ) - b := sub_nonneg.mpr (by exact_mod_cast hba)
    push_cast [Nat.cast_sub hba]
    have := mul_le_mul_of_nonneg_right h2 hab'
    linarith

/-! ### The weight `log p / √(p^k)` -/

/-- Lower bound for `10^40 p^⌈k/2⌉ log p / √(p^k)`. -/
def wLo (L S k : ℕ) : ℕ := cond (Nat.beq (Nat.mod k 2) 0) (Nat.mul L Dn) (Nat.mul L S)

/-- Upper bound for `10^40 p^⌈k/2⌉ log p / √(p^k)`. -/
def wHi (L S k : ℕ) : ℕ :=
  cond (Nat.beq (Nat.mod k 2) 0) (Nat.mul (Nat.add L 16) Dn) (Nat.mul (Nat.add L 16) (Nat.succ S))

theorem weight_even {p k : ℕ} (hp : 0 < p) (hk : k % 2 = 0) (x : ℝ) :
    (p : ℝ) ^ ((k + 1) / 2) * (x / √((p ^ k : ℕ) : ℝ)) = x := by
  obtain ⟨q, rfl⟩ : ∃ q, k = 2 * q := ⟨k / 2, by omega⟩
  have hpr : (0 : ℝ) < p := by exact_mod_cast hp
  have e1 : (2 * q + 1) / 2 = q := by omega
  have e2 : √((p ^ (2 * q) : ℕ) : ℝ) = (p : ℝ) ^ q := by
    push_cast
    rw [pow_mul', Real.sqrt_sq (by positivity)]
  rw [e1, e2]
  field_simp

theorem weight_odd {p k : ℕ} (hp : 0 < p) (hk : k % 2 = 1) (x : ℝ) :
    (p : ℝ) ^ ((k + 1) / 2) * (x / √((p ^ k : ℕ) : ℝ)) = x * √(p : ℝ) := by
  obtain ⟨q, rfl⟩ : ∃ q, k = 2 * q + 1 := ⟨k / 2, by omega⟩
  have hpr : (0 : ℝ) < p := by exact_mod_cast hp
  have hs : (0 : ℝ) < √(p : ℝ) := Real.sqrt_pos.mpr hpr
  have e1 : (2 * q + 1 + 1) / 2 = q + 1 := by omega
  have e2 : √((p ^ (2 * q + 1) : ℕ) : ℝ) = (p : ℝ) ^ q * √(p : ℝ) := by
    push_cast
    rw [pow_succ, pow_mul', Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  have e3 : (p : ℝ) = √(p : ℝ) * √(p : ℝ) := (Real.mul_self_sqrt hpr.le).symm
  rw [e1, e2, pow_succ]
  field_simp
  nth_rewrite 1 [e3]
  ring

theorem sqrt_pow_ge_one {p k : ℕ} (hp : 0 < p) : 1 ≤ √((p ^ k : ℕ) : ℝ) := by
  rw [Real.one_le_sqrt]
  exact_mod_cast Nat.one_le_pow _ _ hp

theorem weight_bounds {p L S k : ℕ} (hp : 0 < p) (h1 : (L : ℝ) ≤ Dr * Real.log p)
    (h2 : Dr * Real.log p ≤ (L : ℝ) + 16) (h3 : (S : ℝ) ≤ Dr * √(p : ℝ))
    (h4 : Dr * √(p : ℝ) ≤ (S : ℝ) + 1) :
    (wLo L S k : ℝ) ≤ Dr * Dr * ((p : ℝ) ^ ((k + 1) / 2) * (Real.log p / √((p ^ k : ℕ) : ℝ))) ∧
    Dr * Dr * ((p : ℝ) ^ ((k + 1) / 2) * (Real.log p / √((p ^ k : ℕ) : ℝ))) ≤ (wHi L S k : ℝ) := by
  have hl0 : (0 : ℝ) ≤ Dr * Real.log p := le_trans (Nat.cast_nonneg L) h1
  have hs0 : (0 : ℝ) ≤ Dr * √(p : ℝ) := by positivity
  rcases Nat.mod_two_eq_zero_or_one k with hk | hk
  · rw [weight_even hp hk]
    have ew : wLo L S k = L * Dn := by unfold wLo; rw [cond_beq]; exact ite_eq_left hk
    have ew' : wHi L S k = (L + 16) * Dn := by unfold wHi; rw [cond_beq]; exact ite_eq_left hk
    rw [ew, ew']
    push_cast
    constructor <;> nlinarith
  · rw [weight_odd hp hk]
    have hk0 : ¬ (k % 2 = 0) := by omega
    have ew : wLo L S k = L * S := by unfold wLo; rw [cond_beq]; exact ite_eq_right hk0
    have ew' : wHi L S k = (L + 16) * (S + 1) := by unfold wHi; rw [cond_beq]; exact ite_eq_right hk0
    rw [ew, ew']
    push_cast
    constructor
    · calc (L : ℝ) * S ≤ (Dr * Real.log p) * (Dr * √(p : ℝ)) :=
            mul_le_mul h1 h3 (Nat.cast_nonneg S) hl0
        _ = _ := by ring
    · calc Dr * Dr * (Real.log p * √(p : ℝ)) = (Dr * Real.log p) * (Dr * √(p : ℝ)) := by ring
        _ ≤ ((L : ℝ) + 16) * ((S : ℝ) + 1) := mul_le_mul h2 h4 hs0 (by positivity)

/-! ### Signed lower bounds -/

/-- Lower bound for `2 (A - B) W / den`, where `hi ≤ A`, `B ≤ lo`, `wlo ≤ W ≤ whi`. -/
def sgnLo (hi lo wlo whi den : ℕ) : ℤ :=
  cond (Nat.ble lo hi)
    (Int.ofNat (Nat.div (Nat.mul (Nat.mul 2 (Nat.sub hi lo)) wlo) den))
    (Int.neg (Int.ofNat (cdiv (Nat.mul (Nat.mul 2 (Nat.sub lo hi)) whi) den)))

theorem sgnLo_le {hi lo wlo whi den : ℕ} {A B W : ℝ} (hden : 0 < den) (hA : (hi : ℝ) ≤ A)
    (hB : B ≤ (lo : ℝ)) (hW1 : (wlo : ℝ) ≤ W) (hW2 : W ≤ (whi : ℝ)) :
    ((sgnLo hi lo wlo whi den : ℤ) : ℝ) ≤ 2 * (A - B) * W / den := by
  have hdr : (0 : ℝ) < den := by exact_mod_cast hden
  have hW0 : 0 ≤ W := le_trans (Nat.cast_nonneg wlo) hW1
  unfold sgnLo
  simp only [cond_ble]
  split_ifs with h
  · change (((2 * (hi - lo) * wlo / den : ℕ) : ℤ) : ℝ) ≤ _
    rw [Int.cast_natCast]
    refine (fdiv_le _ _).trans ?_
    apply div_le_div_of_nonneg_right _ hdr.le
    push_cast [Nat.cast_sub h]
    have h0 : (0 : ℝ) ≤ (hi : ℝ) - lo := sub_nonneg.mpr (by exact_mod_cast h)
    have h1 : (hi : ℝ) - lo ≤ A - B := by linarith
    have := mul_le_mul h1 hW1 (Nat.cast_nonneg wlo) (le_trans h0 h1)
    linarith
  · have hlt : hi ≤ lo := le_of_lt (not_le.mp h)
    change ((-((cdiv (2 * (lo - hi) * whi) den : ℕ) : ℤ) : ℤ) : ℝ) ≤ _
    rw [Int.cast_neg, Int.cast_natCast, neg_le]
    refine le_trans ?_ (div_le_cdiv _ _ hden)
    rw [← neg_div]
    apply div_le_div_of_nonneg_right _ hdr.le
    push_cast [Nat.cast_sub hlt]
    have h0 : (0 : ℝ) ≤ (lo : ℝ) - hi := sub_nonneg.mpr (by exact_mod_cast hlt)
    have h1 : B - A ≤ (lo : ℝ) - hi := by linarith
    have h2 : (B - A) * W ≤ ((lo : ℝ) - hi) * W := mul_le_mul_of_nonneg_right h1 hW0
    have h3 : ((lo : ℝ) - hi) * W ≤ ((lo : ℝ) - hi) * whi := mul_le_mul_of_nonneg_left hW2 h0
    linarith

/-! ### One term -/

/-- The exact test `X^j ≤ n^64 ≤ X^(j+1)`, `j ≤ 63`. -/
def cellOK (X n j : ℕ) : Bool :=
  Nat.ble (Nat.pow X j) (Nat.pow n 64) &&
    (Nat.ble (Nat.pow n 64) (Nat.pow X (Nat.succ j)) && Nat.ble j 63)

/-- The term for the cell `j`. -/
def termMain (LX LXhi sq pack p L S k j : ℕ) : ℤ :=
  (fun a b den => cond (Nat.beq (Nat.mod k 2) 0)
      (sgnLo (fLo a b (hLo LXhi L k j) (hHi LX L k j)) Zn (wLo L S k) (wHi L S k) den)
      (sgnLo Zn (fHi a b (hLo LXhi L k j) (hHi LX L k j)) (wLo L S k) (wHi L S k) den))
    (getN pack j) (getN pack (Nat.succ j))
    (Nat.mul (Nat.mul (Nat.mul (Nat.pow p (Nat.div (Nat.succ k) 2)) sq) Dn) Dn)

/-- Lower bound for `10^20 · 2 (-1)^k log p · f(log p^k) / √(p^k)`. -/
def termLo (X LX LXhi sq pack p L S k : ℕ) : ℤ :=
  (fun j => cond (cellOK X (Nat.pow p k) j) (termMain LX LXhi sq pack p L S k j)
      (Int.neg (Int.ofNat (Nat.mul 2 (Nat.add L 16)))))
    (Nat.div (Nat.mul (Nat.mul 64 k) L) LXhi)

theorem cell_log_bounds {X n j m : ℕ} (hX : 0 < X) (hn : 0 < n) (h1 : X ^ j ≤ n ^ m)
    (h2 : n ^ m ≤ X ^ (j + 1)) :
    (j : ℝ) * Real.log X ≤ (m : ℝ) * Real.log n ∧
      (m : ℝ) * Real.log n ≤ ((j : ℝ) + 1) * Real.log X := by
  have hX0 : (0 : ℝ) < X := by exact_mod_cast hX
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  constructor
  · have h : Real.log ((X : ℝ) ^ j) ≤ Real.log ((n : ℝ) ^ m) :=
      Real.log_le_log (pow_pos hX0 _) (by exact_mod_cast h1)
    rw [Real.log_pow, Real.log_pow] at h
    exact h
  · have h : Real.log ((n : ℝ) ^ m) ≤ Real.log ((X : ℝ) ^ (j + 1)) :=
      Real.log_le_log (pow_pos hn0 _) (by exact_mod_cast h2)
    rw [Real.log_pow, Real.log_pow, Nat.cast_add, Nat.cast_one] at h
    exact h

theorem alg_even {D sq P lp F rt : ℝ} (hD : D ≠ 0) (hsq : sq ≠ 0) (hP : P ≠ 0) :
    2 * (D * sq * F) * (D * D * (P * (lp / rt))) / (P * sq * D * D) =
      D * (2 * (lp * 1 * F / rt)) := by
  field_simp

theorem alg_odd {D sq P lp F rt : ℝ} (hD : D ≠ 0) (hsq : sq ≠ 0) (hP : P ≠ 0) :
    2 * (-(D * sq * F)) * (D * D * (P * (lp / rt))) / (P * sq * D * D) =
      D * (2 * (lp * (-1) * F / rt)) := by
  field_simp

variable {X LX LXhi sq pack : ℕ} {v : List ℝ}

theorem termLo_le (C : RowCtx X LX LXhi sq pack v) {p L S k : ℕ} (hp : p.Prime)
    (h1 : (L : ℝ) ≤ Dr * Real.log p) (h2 : Dr * Real.log p ≤ (L : ℝ) + 16)
    (h3 : (S : ℝ) ≤ Dr * √(p : ℝ)) (h4 : Dr * √(p : ℝ) ≤ (S : ℝ) + 1) :
    ((termLo X LX LXhi sq pack p L S k : ℤ) : ℝ) ≤
      Dr * (2 * ppTerm (autocorr (stepFn (Real.log X) v)) p k) := by
  have hX1 : (1 : ℝ) < X := by exact_mod_cast C.hX
  have hlX : 0 < Real.log X := Real.log_pos hX1
  have hp0 : 0 < p := hp.pos
  have hpr : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
  have hlp : 0 ≤ Real.log p := Real.log_nonneg hpr
  have hn : 1 ≤ p ^ k := Nat.one_le_pow _ _ hp0
  have hrt1 := sqrt_pow_ge_one (k := k) hp0
  have hrt0 : (0 : ℝ) < √((p ^ k : ℕ) : ℝ) := lt_of_lt_of_le one_pos hrt1
  have hv := C.pk.ne
  set f := autocorr (stepFn (Real.log X) v) with hf
  unfold termLo
  simp only []
  generalize hj : Nat.div (Nat.mul (Nat.mul 64 k) L) LXhi = j
  cases hc : cellOK X (Nat.pow p k) j with
  | false =>
    rw [Bool.cond_false]
    change ((-((2 * (L + 16) : ℕ) : ℤ) : ℤ) : ℝ) ≤ _
    have habs : |ppTerm f p k| ≤ Real.log p := by
      unfold ppTerm
      rw [abs_div, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, mul_one,
        abs_of_nonneg hlp, abs_of_pos hrt0, div_le_iff₀ hrt0]
      have hf1 : |f (Real.log ((p ^ k : ℕ) : ℝ))| ≤ 1 :=
        abs_autocorr_stepFn_le_one' hlX hv _
      calc Real.log p * |f (Real.log ((p ^ k : ℕ) : ℝ))| ≤ Real.log p * 1 :=
            mul_le_mul_of_nonneg_left hf1 hlp
        _ ≤ Real.log p * √((p ^ k : ℕ) : ℝ) := mul_le_mul_of_nonneg_left hrt1 hlp
    have hlow := (abs_le.mp habs).1
    push_cast
    linarith
  | true =>
    rw [Bool.cond_true]
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
    have hsq : (0 : ℝ) < sq := by exact_mod_cast C.pk.sqpos
    -- the shifted value
    have hΦ : (getN pack j : ℝ) * Dr + Dr * θ * ((getN pack (j + 1) : ℝ) - getN pack j) - Zn =
        Dr * sq * f (Real.log ((p ^ k : ℕ) : ℝ)) := by
      rw [hf, hval, ha, hb]
      push_cast
      ring
    have hFlo := fLo_le (a := getN pack j) (b := getN pack (j + 1)) hHlo hHhi (hHi_le LX L k j)
    have hFhi := le_fHi (a := getN pack j) (b := getN pack (j + 1)) hHlo hHhi
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
      rw [hΦ, hdenr]
      unfold ppTerm
      rw [(Nat.even_iff.mpr hk).neg_one_pow]
      exact alg_even (by norm_num) hsq.ne' hPne
    · have et : termMain LX LXhi sq pack p L S k j =
          sgnLo Zn (fHi (getN pack j) (getN pack (j + 1)) (hLo LXhi L k j) (hHi LX L k j))
            (wLo L S k) (wHi L S k) (p ^ ((k + 1) / 2) * sq * Dn * Dn) := by
        unfold termMain; simp only []; rw [cond_beq]
        exact ite_eq_right (show ¬ (k % 2 = 0) by omega)
      rw [et]
      refine (sgnLo_le hden (le_refl ((Zn : ℕ) : ℝ)) hFhi hw1 hw2).trans (le_of_eq ?_)
      have hΦ' : ((Zn : ℕ) : ℝ) - ((getN pack j : ℝ) * Dr +
          Dr * θ * ((getN pack (j + 1) : ℝ) - getN pack j)) =
          -(Dr * sq * f (Real.log ((p ^ k : ℕ) : ℝ))) := by
        rw [← hΦ]; ring
      rw [hΦ', hdenr]
      unfold ppTerm
      rw [(Nat.odd_iff.mpr hk).neg_one_pow]
      exact alg_odd (by norm_num) hsq.ne' hPne

/-! ### All exponents for one prime -/

/-- `∑ termLo` over `k, k+1, …` while `p^k < X` (at most `fuel` terms). -/
def primeLo (X LX LXhi sq pack p L S fuel k : ℕ) : ℤ :=
  Nat.rec (motive := fun _ => ℕ → ℤ) (fun _ => 0)
    (fun _ ih k => cond (Nat.ble X (Nat.pow p k)) 0
      (Int.add (termLo X LX LXhi sq pack p L S k) (ih (Nat.succ k)))) fuel k

theorem primeLo_le (C : RowCtx X LX LXhi sq pack v) {p L S : ℕ} (hp : p.Prime)
    (h1 : (L : ℝ) ≤ Dr * Real.log p) (h2 : Dr * Real.log p ≤ (L : ℝ) + 16)
    (h3 : (S : ℝ) ≤ Dr * √(p : ℝ)) (h4 : Dr * √(p : ℝ) ≤ (S : ℝ) + 1) (fuel k : ℕ) :
    ((primeLo X LX LXhi sq pack p L S fuel k : ℤ) : ℝ) ≤
      Dr * ∑ k' ∈ Finset.Ico k (k + fuel),
        if p ^ k' < X then 2 * ppTerm (autocorr (stepFn (Real.log X) v)) p k' else 0 := by
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
      have ht := termLo_le C (k := k) hp h1 h2 h3 h4
      push_cast
      rw [mul_add]
      linarith

/-! ### The fold over the table -/

/-- `∑ g p L S` over the entries `(p, L, S)` of `T` with `p < X`, integer valued. -/
def tableSumZ (g : ℕ → ℕ → ℕ → ℤ) (X : ℕ) (T : List (ℕ × ℕ × ℕ)) : ℤ :=
  List.rec (motive := fun _ => ℤ) 0
    (fun e _ ih => cond (Nat.ble (Nat.succ e.1) X) (Int.add (g e.1 e.2.1 e.2.2) ih) ih) T

theorem tableSumZ_cons (g : ℕ → ℕ → ℕ → ℤ) (X : ℕ) (e : ℕ × ℕ × ℕ) (T : List (ℕ × ℕ × ℕ)) :
    tableSumZ g X (e :: T) =
      if e.1 < X then g e.1 e.2.1 e.2.2 + tableSumZ g X T else tableSumZ g X T := by
  change cond (Nat.ble (e.1 + 1) X) (g e.1 e.2.1 e.2.2 + tableSumZ g X T) (tableSumZ g X T) = _
  rw [cond_ble]; rfl

theorem tableSumZ_le_aux (g : ℕ → ℕ → ℕ → ℤ) (F : ℕ → ℝ) (X : ℕ) :
    ∀ T : List (ℕ × ℕ × ℕ), (T.map Prod.fst).Nodup →
      (∀ e ∈ T, e.1 < X → ((g e.1 e.2.1 e.2.2 : ℤ) : ℝ) ≤ F e.1) →
      ((tableSumZ g X T : ℤ) : ℝ) ≤ ∑ p ∈ (T.map Prod.fst).toFinset.filter (· < X), F p := by
  intro T
  induction T with
  | nil => intro _ _; simp [tableSumZ]
  | cons e T ih =>
    intro hN h
    rw [List.map_cons, List.nodup_cons] at hN
    have ih' := ih hN.2 (fun e' he' => h e' (List.mem_cons_of_mem _ he'))
    rw [tableSumZ_cons, List.map_cons, List.toFinset_cons, Finset.filter_insert]
    split_ifs with hlt
    · rw [Finset.sum_insert (by simp [hN.1])]
      have := h e List.mem_cons_self hlt
      push_cast
      linarith
    · exact ih'

/-- The lower bound for the prime-power side, folded over the certified table. -/
def totalLo (X LX LXhi sq pack : ℕ) : ℤ :=
  tableSumZ (fun p L S => primeLo X LX LXhi sq pack p L S 13 1) X primeTable6400

theorem totalLo_le (C : RowCtx X LX LXhi sq pack v) :
    ((totalLo X LX LXhi sq pack : ℤ) : ℝ) ≤
      Dr * inertSum (autocorr (stepFn (Real.log X) v)) X := by
  have e20 : (10 : ℝ) ^ 20 = Dr := by norm_num
  rw [inertSum_eq _ X 14 (le_trans C.hX' (by norm_num))]
  have hsum : Dr * (2 * ∑ p ∈ (Finset.range X).filter Nat.Prime, ∑ k ∈ Finset.Ico 1 14,
        if p ^ k < X then ppTerm (autocorr (stepFn (Real.log X) v)) p k else 0) =
      ∑ p ∈ (Finset.range X).filter Nat.Prime, Dr * ∑ k ∈ Finset.Ico 1 (1 + 13),
        if p ^ k < X then 2 * ppTerm (autocorr (stepFn (Real.log X) v)) p k else 0 := by
    simp only [Finset.mul_sum, mul_ite, mul_zero]
  rw [hsum, ← primeTable6400_filter C.hX']
  unfold totalLo
  apply tableSumZ_le_aux _ _ X _ primeTable6400_nodup
  intro e he _
  obtain ⟨hp, -, h1, h2, h3, h4⟩ := primeTable6400_spec (p := e.1) (L := e.2.1) (S := e.2.2) he
  rw [e20] at h1 h2 h3 h4
  exact primeLo_le C hp h1 h2 h3 h4 13 1

end Exp7.Rows
