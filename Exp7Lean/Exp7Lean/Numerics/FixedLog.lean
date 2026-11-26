import Exp7Lean.Numerics.LogSeries

/-!
# A verified fixed-point logarithm

Real numbers are represented by natural numbers scaled by a fixed denominator `D` (a *scale*,
e.g. `10^20`): `lo` and `hi` enclose `x` when `lo ≤ D * x ≤ hi`.  Rounding is always directed.

All loops are written with the primitive recursor `Nat.rec`, not with structural recursion
compiled through `brecOn`: the kernel unfolds the former about ten times faster.  The bodies use
the raw operations `Nat.add`, `Nat.mul`, `Nat.div`, `Nat.sub`, `Nat.pow`, `Nat.ble` (GMP-accelerated
on literals, and the kernel does not have to unfold any type-class instance: another factor 2-3).
Each definition comes with an `_eq` lemma restating it in ordinary notation; proofs only use
those.  The theorems below are proved once for all arguments; a concrete enclosure is then
obtained by kernel evaluation (`by decide +kernel`).  No `native_decide`.

Main definitions / statements (`D` scale, `N` number of series terms):

* `logRatioLo D N a b ≤ D * (log a - log b) ≤ logRatioHi D N a b` for naturals `0 < b ≤ a`;
* `logLoE D N l2lo e n ≤ D * log n ≤ logHiE D N l2hi e n` for `1 ≤ n`, **any** exponent `e`
  (the reduction `log n = e log 2 ± log(n / 2^e)`), given an enclosure `l2lo, l2hi` of `D * log 2`;
* `Prec`, `Prec.Valid`, `logLo P n`, `logHi P n`: the packaged evaluator.
-/

namespace Exp7.Num

open Real

/-! ### Rounding helpers -/

/-- Ceiling division on `ℕ`. -/
def cdiv (a b : ℕ) : ℕ := Nat.div (Nat.add a (Nat.sub b 1)) b

theorem cdiv_eq (a b : ℕ) : cdiv a b = (a + (b - 1)) / b := rfl

/-- `cond` on `Nat.ble` is `if · ≤ ·`. -/
theorem cond_ble {α : Type} (a b : ℕ) (x y : α) :
    cond (Nat.ble a b) x y = if a ≤ b then x else y := by
  by_cases h : a ≤ b <;> simp [h]

theorem le_cdiv_mul (a b : ℕ) (hb : 0 < b) : a ≤ cdiv a b * b := by
  rw [cdiv_eq]
  have h1 := Nat.div_add_mod (a + (b - 1)) b
  have h2 := Nat.mod_lt (a + (b - 1)) hb
  rw [Nat.mul_comm] at h1
  generalize (a + (b - 1)) / b * b = q at *
  generalize (a + (b - 1)) % b = r at *
  omega

/-- `a / b ≤ ⌈a / b⌉` over the reals. -/
theorem div_le_cdiv (a b : ℕ) (hb : 0 < b) : (a : ℝ) / b ≤ (cdiv a b : ℝ) := by
  rw [div_le_iff₀ (by exact_mod_cast hb)]
  exact_mod_cast le_cdiv_mul a b hb

/-- `⌊a / b⌋ ≤ a / b` over the reals. -/
theorem fdiv_le (a b : ℕ) : ((a / b : ℕ) : ℝ) ≤ (a : ℝ) / b := Nat.cast_div_le

/-- Truncated subtraction only increases. -/
theorem cast_sub_ge (a b : ℕ) : (a : ℝ) - b ≤ ((a - b : ℕ) : ℝ) := by
  rcases le_total b a with h | h
  · rw [Nat.cast_sub h]
  · rw [Nat.sub_eq_zero_of_le h]
    have : (a : ℝ) ≤ b := by exact_mod_cast h
    simp only [Nat.cast_zero]; linarith

/-! ### Horner evaluation of the `atanh` series -/

/-- Lower Horner sum: `atanhLo D w m k ≈ D * ∑_{j<m} (w/D)^j / (2(k+j)+1)`, rounded down. -/
def atanhLo (D w : ℕ) (m : ℕ) : ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ) (fun _ => 0)
    (fun _ ih k => Nat.add (Nat.div D (Nat.add (Nat.mul 2 k) 1))
      (Nat.div (Nat.mul w (ih (Nat.succ k))) D)) m

/-- Upper Horner sum: `m` terms rounded up, closed by the geometric tail bound
`1/((2j+1)(1-w))` at index `j = k + m`. -/
def atanhHi (D w : ℕ) (m : ℕ) : ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ)
    (fun k => cdiv (Nat.mul D D) (Nat.mul (Nat.add (Nat.mul 2 k) 1) (Nat.sub D w)))
    (fun _ ih k => Nat.add (cdiv D (Nat.add (Nat.mul 2 k) 1))
      (cdiv (Nat.mul w (ih (Nat.succ k))) D)) m

theorem atanhLo_zero (D w k : ℕ) : atanhLo D w 0 k = 0 := rfl
theorem atanhLo_succ (D w m k : ℕ) :
    atanhLo D w (m + 1) k = D / (2 * k + 1) + w * atanhLo D w m (k + 1) / D := rfl
theorem atanhHi_zero (D w k : ℕ) :
    atanhHi D w 0 k = cdiv (D * D) ((2 * k + 1) * (D - w)) := rfl
theorem atanhHi_succ (D w m k : ℕ) :
    atanhHi D w (m + 1) k = cdiv D (2 * k + 1) + cdiv (w * atanhHi D w m (k + 1)) D := rfl

theorem atanhLo_le {D : ℕ} (hD : 0 < D) {w : ℝ} (h0 : 0 ≤ w) (h1 : w < 1) {wn : ℕ}
    (hw : (wn : ℝ) ≤ D * w) (m k : ℕ) : (atanhLo D wn m k : ℝ) ≤ D * atanhTail w k := by
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  induction m generalizing k with
  | zero =>
    rw [atanhLo_zero]
    simpa using mul_nonneg hDr.le (atanhTail_nonneg h0 k)
  | succ m ih =>
    rw [atanhLo_succ, atanhTail_succ h0 h1]
    push_cast
    have a1 : ((D / (2 * k + 1) : ℕ) : ℝ) ≤ D * (1 / (2 * (k : ℝ) + 1)) := by
      refine (fdiv_le _ _).trans (le_of_eq ?_)
      push_cast; ring
    have a2 : ((wn * atanhLo D wn m (k + 1) / D : ℕ) : ℝ) ≤ D * (w * atanhTail w (k + 1)) := by
      refine (fdiv_le _ _).trans ?_
      rw [div_le_iff₀ hDr]
      push_cast
      have := mul_le_mul hw (ih (k + 1)) (by positivity) (by positivity)
      calc (wn : ℝ) * (atanhLo D wn m (k + 1) : ℝ) ≤ D * w * (D * atanhTail w (k + 1)) := this
        _ = D * (w * atanhTail w (k + 1)) * D := by ring
    linarith

theorem le_atanhHi {D : ℕ} (hD : 0 < D) {w : ℝ} (h0 : 0 ≤ w) (h1 : w < 1) {wn : ℕ}
    (hw : D * w ≤ (wn : ℝ)) (hwD : wn < D) (m k : ℕ) :
    D * atanhTail w k ≤ (atanhHi D wn m k : ℝ) := by
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  induction m generalizing k with
  | zero =>
    rw [atanhHi_zero]
    have hpos : 0 < (2 * k + 1) * (D - wn) := Nat.mul_pos (by omega) (by omega)
    refine le_trans ?_ (div_le_cdiv _ _ hpos)
    have hk : (0 : ℝ) < 2 * (k : ℝ) + 1 := by positivity
    have hDw : (0 : ℝ) < (D : ℝ) - wn := by
      have : (wn : ℝ) < D := by exact_mod_cast hwD
      linarith
    push_cast [Nat.cast_sub hwD.le]
    rw [le_div_iff₀ (by positivity)]
    have hT := atanhTail_le h0 h1 k
    have hT0 := atanhTail_nonneg h0 k
    have h1w : 0 < 1 - w := by linarith
    rw [le_div_iff₀ (by positivity)] at hT
    -- D * T * ((2k+1) * (D - wn)) ≤ D * T * ((2k+1) * (D - D w)) ≤ D * D
    calc (D : ℝ) * atanhTail w k * ((2 * (k : ℝ) + 1) * ((D : ℝ) - wn))
        ≤ (D : ℝ) * atanhTail w k * ((2 * (k : ℝ) + 1) * ((D : ℝ) - D * w)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply mul_le_mul_of_nonneg_left _ hk.le
          linarith
      _ = D * D * (atanhTail w k * ((2 * (k : ℝ) + 1) * (1 - w))) := by ring
      _ ≤ D * D * 1 := by
          apply mul_le_mul_of_nonneg_left hT (by positivity)
      _ = D * D := by ring
  | succ m ih =>
    rw [atanhHi_succ, atanhTail_succ h0 h1]
    push_cast
    have a1 : D * (1 / (2 * (k : ℝ) + 1)) ≤ (cdiv D (2 * k + 1) : ℝ) := by
      refine le_trans (le_of_eq ?_) (div_le_cdiv _ _ (by omega))
      push_cast; ring
    have a2 : D * (w * atanhTail w (k + 1)) ≤ (cdiv (wn * atanhHi D wn m (k + 1)) D : ℝ) := by
      refine le_trans ?_ (div_le_cdiv _ _ hD)
      rw [le_div_iff₀ hDr]
      push_cast
      have := mul_le_mul hw (ih (k + 1)) (mul_nonneg hDr.le (atanhTail_nonneg h0 _))
        (by positivity)
      calc (D : ℝ) * (w * atanhTail w (k + 1)) * D = D * w * (D * atanhTail w (k + 1)) := by ring
        _ ≤ (wn : ℝ) * (atanhHi D wn m (k + 1) : ℝ) := this
    linarith

/-! ### `log a - log b` for naturals `0 < b ≤ a` -/

/-- Lower bound for `D * (log a - log b)`. -/
def logRatioLo (D N a b : ℕ) : ℕ :=
  Nat.div (Nat.mul (Nat.mul 2 (Nat.sub a b))
    (atanhLo D (Nat.div (Nat.mul (Nat.mul (Nat.sub a b) (Nat.sub a b)) D)
      (Nat.mul (Nat.add a b) (Nat.add a b))) N 0)) (Nat.add a b)

theorem logRatioLo_eq (D N a b : ℕ) : logRatioLo D N a b =
    2 * (a - b) * atanhLo D ((a - b) * (a - b) * D / ((a + b) * (a + b))) N 0 / (a + b) := rfl

/-- Upper bound for `D * (log a - log b)`.  (The `else` branch is a crude but valid fallback,
never taken for moderate ratios `a / b`.) -/
def logRatioHi (D N a b : ℕ) : ℕ :=
  cond (Nat.ble (Nat.succ (cdiv (Nat.mul (Nat.mul (Nat.sub a b) (Nat.sub a b)) D)
      (Nat.mul (Nat.add a b) (Nat.add a b)))) D)
    (cdiv (Nat.mul (Nat.mul 2 (Nat.sub a b))
      (atanhHi D (cdiv (Nat.mul (Nat.mul (Nat.sub a b) (Nat.sub a b)) D)
        (Nat.mul (Nat.add a b) (Nat.add a b))) N 0)) (Nat.add a b))
    (Nat.mul D a)

theorem logRatioHi_eq (D N a b : ℕ) : logRatioHi D N a b =
    if cdiv ((a - b) * (a - b) * D) ((a + b) * (a + b)) + 1 ≤ D then
      cdiv (2 * (a - b) * atanhHi D (cdiv ((a - b) * (a - b) * D) ((a + b) * (a + b))) N 0) (a + b)
    else D * a := by
  rw [logRatioHi, cond_ble]; rfl

theorem logRatioLo_le {D : ℕ} (hD : 0 < D) (N : ℕ) {a b : ℕ} (hb : 0 < b) (hab : b ≤ a) :
    (logRatioLo D N a b : ℝ) ≤ D * (log a - log b) := by
  have hbr : (0 : ℝ) < b := by exact_mod_cast hb
  have habr : (b : ℝ) ≤ a := by exact_mod_cast hab
  have hs : (0 : ℝ) < (a : ℝ) + b := by linarith
  obtain ⟨h0, h1⟩ := ratio_sq_bounds hbr habr
  rw [log_sub_log_eq hbr habr]
  set w : ℝ := (((a : ℝ) - b) / (a + b)) ^ 2 with hwdef
  have hw : (((a - b) * (a - b) * D / ((a + b) * (a + b)) : ℕ) : ℝ) ≤ D * w := by
    refine (fdiv_le _ _).trans (le_of_eq ?_)
    push_cast [Nat.cast_sub hab]
    rw [hwdef]; field_simp
  have hL := atanhLo_le hD h0 h1 hw N 0
  rw [logRatioLo_eq]
  refine (fdiv_le _ _).trans ?_
  rw [div_le_iff₀ (by exact_mod_cast hs)]
  push_cast [Nat.cast_sub hab]
  have hd : (0 : ℝ) ≤ (a : ℝ) - b := by linarith
  calc 2 * ((a : ℝ) - b) * (atanhLo D _ N 0 : ℝ)
      ≤ 2 * ((a : ℝ) - b) * (D * atanhTail w 0) :=
        mul_le_mul_of_nonneg_left hL (by positivity)
    _ = D * (2 * (((a : ℝ) - b) / (a + b)) * atanhTail w 0) * (a + b) := by
        field_simp

theorem le_logRatioHi {D : ℕ} (hD : 0 < D) (N : ℕ) {a b : ℕ} (hb : 0 < b) (hab : b ≤ a) :
    D * (log a - log b) ≤ (logRatioHi D N a b : ℝ) := by
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  have hbr : (0 : ℝ) < b := by exact_mod_cast hb
  have habr : (b : ℝ) ≤ a := by exact_mod_cast hab
  have hs : (0 : ℝ) < (a : ℝ) + b := by linarith
  have hsn : 0 < a + b := by omega
  rw [logRatioHi_eq]
  split_ifs with hlt
  · replace hlt : cdiv ((a - b) * (a - b) * D) ((a + b) * (a + b)) < D := hlt
    obtain ⟨h0, h1⟩ := ratio_sq_bounds hbr habr
    rw [log_sub_log_eq hbr habr]
    set w : ℝ := (((a : ℝ) - b) / (a + b)) ^ 2 with hwdef
    have hw : D * w ≤ (cdiv ((a - b) * (a - b) * D) ((a + b) * (a + b)) : ℝ) := by
      refine le_trans (le_of_eq ?_) (div_le_cdiv _ _ (Nat.mul_pos hsn hsn))
      push_cast [Nat.cast_sub hab]
      rw [hwdef]; field_simp
    have hU := le_atanhHi hD h0 h1 hw hlt N 0
    refine le_trans ?_ (div_le_cdiv _ _ hsn)
    rw [le_div_iff₀ (by exact_mod_cast hs)]
    push_cast [Nat.cast_sub hab]
    have hd : (0 : ℝ) ≤ (a : ℝ) - b := by linarith
    calc D * (2 * (((a : ℝ) - b) / (a + b)) * atanhTail w 0) * ((a : ℝ) + b)
        = 2 * ((a : ℝ) - b) * (D * atanhTail w 0) := by field_simp
      _ ≤ 2 * ((a : ℝ) - b) * (atanhHi D _ N 0 : ℝ) :=
        mul_le_mul_of_nonneg_left hU (by positivity)
  · push_cast
    apply mul_le_mul_of_nonneg_left _ hDr.le
    have h1 : log (a : ℝ) ≤ a :=
      (log_le_sub_one_of_pos (lt_of_lt_of_le hbr habr)).trans (by linarith)
    have h2 : 0 ≤ log (b : ℝ) := log_nonneg (by exact_mod_cast hb)
    linarith

/-! ### `log n` by the reduction `n = 2^e · (n / 2^e)` -/

/-- Lower bound for `D * log n`, using the exponent `e` and a lower bound `l2lo ≤ D log 2`
(and, when `n < 2^e`, an upper bound via `logRatioHi`). -/
def logLoE (D N l2lo e n : ℕ) : ℕ :=
  cond (Nat.ble (Nat.pow 2 e) n)
    (Nat.add (Nat.mul e l2lo) (logRatioLo D N n (Nat.pow 2 e)))
    (Nat.sub (Nat.mul e l2lo) (logRatioHi D N (Nat.pow 2 e) n))

theorem logLoE_eq (D N l2lo e n : ℕ) : logLoE D N l2lo e n =
    if 2 ^ e ≤ n then e * l2lo + logRatioLo D N n (2 ^ e)
    else e * l2lo - logRatioHi D N (2 ^ e) n := by
  rw [logLoE, cond_ble]; rfl

/-- Upper bound for `D * log n`, using the exponent `e` and an upper bound `D log 2 ≤ l2hi`. -/
def logHiE (D N l2hi e n : ℕ) : ℕ :=
  cond (Nat.ble (Nat.pow 2 e) n)
    (Nat.add (Nat.mul e l2hi) (logRatioHi D N n (Nat.pow 2 e)))
    (Nat.sub (Nat.mul e l2hi) (logRatioLo D N (Nat.pow 2 e) n))

theorem logHiE_eq (D N l2hi e n : ℕ) : logHiE D N l2hi e n =
    if 2 ^ e ≤ n then e * l2hi + logRatioHi D N n (2 ^ e)
    else e * l2hi - logRatioLo D N (2 ^ e) n := by
  rw [logHiE, cond_ble]; rfl

theorem log_two_pow (e : ℕ) : log ((2 ^ e : ℕ) : ℝ) = e * log 2 := by
  push_cast; rw [log_pow]

theorem logLoE_le {D : ℕ} (hD : 0 < D) (N : ℕ) {l2lo : ℕ} (h2 : (l2lo : ℝ) ≤ D * log 2)
    (e : ℕ) {n : ℕ} (hn : 1 ≤ n) : (logLoE D N l2lo e n : ℝ) ≤ D * log n := by
  have hP : 0 < 2 ^ e := Nat.pos_of_ne_zero (by positivity)
  have he : (e : ℝ) * (l2lo : ℝ) ≤ D * (e * log 2) := by
    have := mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg e)
    linarith
  rw [logLoE_eq]
  split_ifs with h
  · have hr := logRatioLo_le hD N hP h
    rw [log_two_pow] at hr
    push_cast
    nlinarith
  · have hr := le_logRatioHi hD N (by omega : 0 < n) (le_of_lt (not_le.mp h))
    rw [log_two_pow] at hr
    have hlog : 0 ≤ D * log (n : ℝ) :=
      mul_nonneg (Nat.cast_nonneg D) (log_nonneg (by exact_mod_cast hn))
    rcases le_total (logRatioHi D N (2 ^ e) n) (e * l2lo) with hle | hle
    · rw [Nat.cast_sub hle]; push_cast; nlinarith
    · rw [Nat.sub_eq_zero_of_le hle]; simpa using hlog

theorem le_logHiE {D : ℕ} (hD : 0 < D) (N : ℕ) {l2hi : ℕ} (h2 : D * log 2 ≤ (l2hi : ℝ))
    (e : ℕ) {n : ℕ} (hn : 1 ≤ n) : D * log n ≤ (logHiE D N l2hi e n : ℝ) := by
  have hP : 0 < 2 ^ e := Nat.pos_of_ne_zero (by positivity)
  have he : D * (e * log 2) ≤ (e : ℝ) * (l2hi : ℝ) := by
    have := mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg e)
    linarith
  rw [logHiE_eq]
  split_ifs with h
  · have hr := le_logRatioHi hD N hP h
    rw [log_two_pow] at hr
    push_cast
    nlinarith
  · have hr := logRatioLo_le hD N (by omega : 0 < n) (le_of_lt (not_le.mp h))
    rw [log_two_pow] at hr
    refine le_trans ?_ (cast_sub_ge _ _)
    push_cast
    nlinarith

/-! ### Choice of the exponent (heuristic: soundness never depends on it) -/

/-- Binary search for `⌊log₂ n⌋` among exponents `< 2^bits`.  Only the *accuracy* of the
logarithm depends on this value, never its soundness. -/
def expoSearch (bits n : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ) (fun e => e)
    (fun i ih e => ih (cond (Nat.ble (Nat.pow 2 (Nat.add e (Nat.pow 2 i))) n)
      (Nat.add e (Nat.pow 2 i)) e)) bits 0

/-- Exponent `e` with `n / 2^e ∈ (1/√2, √2]` (for `0 < n < 2^(2^bits)`). -/
def expo (bits n : ℕ) : ℕ :=
  cond (Nat.ble (Nat.mul n n) (Nat.pow 2 (Nat.add (Nat.mul 2 (expoSearch bits n)) 1)))
    (expoSearch bits n) (Nat.succ (expoSearch bits n))

/-! ### Packaged evaluator -/

/-- Precision parameters: scale `D`, number `N` of series terms, exponent search depth `bits`
(inputs up to `2^(2^bits)` are reduced optimally), and an enclosure of `D * log 2`. -/
structure Prec where
  D : ℕ
  N : ℕ
  bits : ℕ
  l2lo : ℕ
  l2hi : ℕ

/-- The parameters are sound: positive scale and a true enclosure of `D * log 2`. -/
structure Prec.Valid (P : Prec) : Prop where
  pos : 0 < P.D
  l2lo : (P.l2lo : ℝ) ≤ P.D * log 2
  l2hi : P.D * log 2 ≤ (P.l2hi : ℝ)

/-- Lower bound for `P.D * log n`. -/
def logLo (P : Prec) (n : ℕ) : ℕ :=
  match P with
  | ⟨D, N, bits, l2lo, _⟩ => logLoE D N l2lo (expo bits n) n

theorem logLo_eq (P : Prec) (n : ℕ) : logLo P n = logLoE P.D P.N P.l2lo (expo P.bits n) n := rfl

/-- Upper bound for `P.D * log n`. -/
def logHi (P : Prec) (n : ℕ) : ℕ :=
  match P with
  | ⟨D, N, bits, _, l2hi⟩ => logHiE D N l2hi (expo bits n) n

theorem logHi_eq (P : Prec) (n : ℕ) : logHi P n = logHiE P.D P.N P.l2hi (expo P.bits n) n := rfl

theorem logLo_le {P : Prec} (hP : P.Valid) {n : ℕ} (hn : 1 ≤ n) :
    (logLo P n : ℝ) ≤ P.D * log n := by
  rw [logLo_eq]; exact logLoE_le hP.pos _ hP.l2lo _ hn

theorem le_logHi {P : Prec} (hP : P.Valid) {n : ℕ} (hn : 1 ≤ n) :
    P.D * log n ≤ (logHi P n : ℝ) := by
  rw [logHi_eq]; exact le_logHiE hP.pos _ hP.l2hi _ hn

/-- The enclosure in the form `lo / D ≤ log n ≤ hi / D`. -/
theorem log_mem {P : Prec} (hP : P.Valid) {n : ℕ} (hn : 1 ≤ n) :
    (logLo P n : ℝ) / P.D ≤ log n ∧ log n ≤ (logHi P n : ℝ) / P.D := by
  have hD : (0 : ℝ) < P.D := by exact_mod_cast hP.pos
  constructor
  · rw [div_le_iff₀ hD, mul_comm]; exact logLo_le hP hn
  · rw [le_div_iff₀ hD, mul_comm]; exact le_logHi hP hn

/-! ### `log 2` from `2 = (16/15)^7 (25/24)^5 (81/80)^3` -/

theorem log_two_eq :
    log 2 = 7 * (log (16 : ℕ) - log (15 : ℕ)) + 5 * (log (25 : ℕ) - log (24 : ℕ))
      + 3 * (log (81 : ℕ) - log (80 : ℕ)) := by
  have h16 : log ((16 : ℕ) : ℝ) = 4 * log 2 := by
    rw [show ((16 : ℕ) : ℝ) = 2 ^ 4 by norm_num, log_pow]; norm_num
  have h15 : log ((15 : ℕ) : ℝ) = log 3 + log 5 := by
    rw [show ((15 : ℕ) : ℝ) = 3 * 5 by norm_num, log_mul (by norm_num) (by norm_num)]
  have h25 : log ((25 : ℕ) : ℝ) = 2 * log 5 := by
    rw [show ((25 : ℕ) : ℝ) = 5 ^ 2 by norm_num, log_pow]; norm_num
  have h24 : log ((24 : ℕ) : ℝ) = 3 * log 2 + log 3 := by
    rw [show ((24 : ℕ) : ℝ) = 2 ^ 3 * 3 by norm_num, log_mul (by norm_num) (by norm_num), log_pow]
    norm_num
  have h81 : log ((81 : ℕ) : ℝ) = 4 * log 3 := by
    rw [show ((81 : ℕ) : ℝ) = 3 ^ 4 by norm_num, log_pow]; norm_num
  have h80 : log ((80 : ℕ) : ℝ) = 4 * log 2 + log 5 := by
    rw [show ((80 : ℕ) : ℝ) = 2 ^ 4 * 5 by norm_num, log_mul (by norm_num) (by norm_num), log_pow]
    norm_num
  rw [h16, h15, h25, h24, h81, h80]; ring

/-- Lower bound for `D * log 2`. -/
def logTwoLo (D N : ℕ) : ℕ :=
  7 * logRatioLo D N 16 15 + 5 * logRatioLo D N 25 24 + 3 * logRatioLo D N 81 80

/-- Upper bound for `D * log 2`. -/
def logTwoHi (D N : ℕ) : ℕ :=
  7 * logRatioHi D N 16 15 + 5 * logRatioHi D N 25 24 + 3 * logRatioHi D N 81 80

theorem logTwoLo_le {D : ℕ} (hD : 0 < D) (N : ℕ) : (logTwoLo D N : ℝ) ≤ D * log 2 := by
  have h1 := logRatioLo_le hD N (a := 16) (b := 15) (by norm_num) (by norm_num)
  have h2 := logRatioLo_le hD N (a := 25) (b := 24) (by norm_num) (by norm_num)
  have h3 := logRatioLo_le hD N (a := 81) (b := 80) (by norm_num) (by norm_num)
  unfold logTwoLo
  rw [log_two_eq]
  push_cast at h1 h2 h3 ⊢
  linarith

theorem le_logTwoHi {D : ℕ} (hD : 0 < D) (N : ℕ) : D * log 2 ≤ (logTwoHi D N : ℝ) := by
  have h1 := le_logRatioHi hD N (a := 16) (b := 15) (by norm_num) (by norm_num)
  have h2 := le_logRatioHi hD N (a := 25) (b := 24) (by norm_num) (by norm_num)
  have h3 := le_logRatioHi hD N (a := 81) (b := 80) (by norm_num) (by norm_num)
  unfold logTwoHi
  rw [log_two_eq]
  push_cast at h1 h2 h3 ⊢
  linarith

/-- Rescaling a lower bound from scale `D * M` down to scale `D`. -/
theorem lo_rescale {D M lo c : ℕ} {x : ℝ} (hM : 0 < M) (h : (lo : ℝ) ≤ ((D * M : ℕ) : ℝ) * x)
    (hc : c * M ≤ lo) : (c : ℝ) ≤ D * x := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hc' : (c : ℝ) * M ≤ lo := by exact_mod_cast hc
  push_cast at h
  have : (c : ℝ) * M ≤ D * x * M := by linarith
  exact le_of_mul_le_mul_right this hMr

/-- Rescaling an upper bound from scale `D * M` down to scale `D`. -/
theorem hi_rescale {D M hi c : ℕ} {x : ℝ} (hM : 0 < M) (h : ((D * M : ℕ) : ℝ) * x ≤ (hi : ℝ))
    (hc : hi ≤ c * M) : D * x ≤ (c : ℝ) := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hc' : (hi : ℝ) ≤ (c : ℝ) * M := by exact_mod_cast hc
  push_cast at h
  have : D * x * M ≤ (c : ℝ) * M := by linarith
  exact le_of_mul_le_mul_right this hMr

end Exp7.Num
