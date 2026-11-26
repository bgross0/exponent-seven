import Exp7Lean.Numerics.FixedLog
import Exp7Lean.Numerics.FixedSqrt
import Exp7Lean.Numerics.FixedExp
import Exp7Lean.Numerics.EulerGamma

/-!
# Concrete precision parameters and constants at scale `10^20`

* `P20`, `P20w` : valid precision parameters at scale `10^20` (`P20w` searches exponents up to
  `2^256` and is meant for large arguments such as `Q ≈ 10^32`; `P20` is for arguments `< 2^16`).
* enclosures of `π` (from Mathlib's 20 digits), `log 2`, `log π`, and of the Euler–Mascheroni
  constant `γ` (DeTemple bounds at `n = 10^5`, evaluated at scale `10^26`).

Every numerical fact here is checked by kernel evaluation (`decide +kernel`).
-/

namespace Exp7.Num

open Real

/-! ### `log 2` and the precision parameters -/

/-- `0.69314718055994530941 ≤ log 2`. -/
theorem log_two_lo20 :
    ((69314718055994530941 : ℕ) : ℝ) ≤ ((100000000000000000000 : ℕ) : ℝ) * log 2 :=
  lo_rescale (D := 100000000000000000000) (M := 100000)
    (lo := logTwoLo (100000000000000000000 * 100000) 12) (by norm_num)
    (logTwoLo_le (by norm_num) 12) (by decide +kernel)

/-- `log 2 ≤ 0.69314718055994530942`. -/
theorem log_two_hi20 :
    ((100000000000000000000 : ℕ) : ℝ) * log 2 ≤ ((69314718055994530942 : ℕ) : ℝ) :=
  hi_rescale (D := 100000000000000000000) (M := 100000)
    (hi := logTwoHi (100000000000000000000 * 100000) 12) (by norm_num)
    (le_logTwoHi (by norm_num) 12) (by decide +kernel)

/-- Scale `10^20`, 12 series terms, arguments below `2^16`. -/
def P20 : Prec := ⟨100000000000000000000, 12, 4, 69314718055994530941, 69314718055994530942⟩

/-- Scale `10^20`, 12 series terms, arguments below `2^256`. -/
def P20w : Prec := ⟨100000000000000000000, 12, 8, 69314718055994530941, 69314718055994530942⟩

theorem P20_valid : P20.Valid := ⟨by decide, log_two_lo20, log_two_hi20⟩
theorem P20w_valid : P20w.Valid := ⟨by decide, log_two_lo20, log_two_hi20⟩

/-- `0.69314718055994530941 ≤ log 2 ≤ 0.69314718055994530942`. -/
theorem log_two_mem :
    (69314718055994530941 : ℝ) / 10 ^ 20 ≤ log 2 ∧
      log 2 ≤ (69314718055994530942 : ℝ) / 10 ^ 20 := by
  have h1 := log_two_lo20
  have h2 := log_two_hi20
  push_cast at h1 h2
  constructor
  · rw [div_le_iff₀ (by positivity)]; linarith
  · rw [le_div_iff₀ (by positivity)]; linarith

/-! ### `π` -/

/-- `10^20 π ≥ 314159265358979323846`. -/
theorem pi_lo20 : ((314159265358979323846 : ℕ) : ℝ) ≤ ((100000000000000000000 : ℕ) : ℝ) * π := by
  have := pi_gt_d20
  push_cast
  norm_num at this ⊢
  linarith

/-- `10^20 π ≤ 314159265358979323847`. -/
theorem pi_hi20 : ((100000000000000000000 : ℕ) : ℝ) * π ≤ ((314159265358979323847 : ℕ) : ℝ) := by
  have := pi_lt_d20
  push_cast
  norm_num at this ⊢
  linarith

/-! ### `log π` -/

/-- Lower bound for `10^20 log π`. -/
def logPiLo : ℕ := logLo P20w 314159265358979323846 - logHi P20w 100000000000000000000

/-- Upper bound for `10^20 log π`. -/
def logPiHi : ℕ := logHi P20w 314159265358979323847 - logLo P20w 100000000000000000000

theorem logPiLo_le : (logPiLo : ℝ) ≤ ((100000000000000000000 : ℕ) : ℝ) * log π := by
  have h1 := logLo_le P20w_valid (n := 314159265358979323846) (by norm_num)
  have h2 := le_logHi P20w_valid (n := 100000000000000000000) (by norm_num)
  have hD : P20w.D = 100000000000000000000 := rfl
  rw [hD] at h1 h2
  have hpi := pi_lo20
  have hlog : log ((314159265358979323846 : ℕ) : ℝ) - log ((100000000000000000000 : ℕ) : ℝ)
      ≤ log π := by
    rw [← log_div (by norm_num) (by norm_num)]
    apply log_le_log (by norm_num)
    rw [div_le_iff₀ (by norm_num)]
    linarith
  have hnn : (0 : ℝ) ≤ ((100000000000000000000 : ℕ) : ℝ) * log π :=
    mul_nonneg (Nat.cast_nonneg _) (log_nonneg (by linarith [pi_gt_three]))
  unfold logPiLo
  rcases le_total (logHi P20w 100000000000000000000) (logLo P20w 314159265358979323846)
    with hle | hle
  · rw [Nat.cast_sub hle]
    have hpos : (0 : ℝ) ≤ ((100000000000000000000 : ℕ) : ℝ) := Nat.cast_nonneg _
    nlinarith
  · rw [Nat.sub_eq_zero_of_le hle]; simpa using hnn

theorem le_logPiHi : ((100000000000000000000 : ℕ) : ℝ) * log π ≤ (logPiHi : ℝ) := by
  have h1 := le_logHi P20w_valid (n := 314159265358979323847) (by norm_num)
  have h2 := logLo_le P20w_valid (n := 100000000000000000000) (by norm_num)
  have hD : P20w.D = 100000000000000000000 := rfl
  rw [hD] at h1 h2
  have hpi := pi_hi20
  have hlog : log π
      ≤ log ((314159265358979323847 : ℕ) : ℝ) - log ((100000000000000000000 : ℕ) : ℝ) := by
    rw [← log_div (by norm_num) (by norm_num)]
    apply log_le_log pi_pos
    rw [le_div_iff₀ (by norm_num)]
    linarith
  unfold logPiHi
  refine le_trans ?_ (cast_sub_ge _ _)
  have hpos : (0 : ℝ) ≤ ((100000000000000000000 : ℕ) : ℝ) := Nat.cast_nonneg _
  nlinarith

/-- `1.14472988584940017346 ≤ log π ≤ 1.14472988584940017482`. -/
theorem log_pi_mem : (114472988584940017346 : ℝ) / 10 ^ 20 ≤ log π ∧
    log π ≤ (114472988584940017482 : ℝ) / 10 ^ 20 := by
  have h1 := logPiLo_le
  have h2 := le_logPiHi
  have c1 : 114472988584940017346 ≤ logPiLo := by decide +kernel
  have c2 : logPiHi ≤ 114472988584940017482 := by decide +kernel
  have c1' : ((114472988584940017346 : ℕ) : ℝ) ≤ (logPiLo : ℝ) := by exact_mod_cast c1
  have c2' : (logPiHi : ℝ) ≤ ((114472988584940017482 : ℕ) : ℝ) := by exact_mod_cast c2
  push_cast at h1 h2 c1' c2'
  constructor
  · rw [div_le_iff₀ (by positivity)]; linarith
  · rw [le_div_iff₀ (by positivity)]; linarith

/-! ### Harmonic numbers and the Euler–Mascheroni constant -/

/-- `∑_{k=1}^n ⌊D/k⌋`. -/
def harmonicLo (D n : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0 (fun k ih => Nat.add ih (Nat.div D (Nat.succ k))) n

/-- `∑_{k=1}^n ⌈D/k⌉`. -/
def harmonicHi (D n : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0 (fun k ih => Nat.add ih (cdiv D (Nat.succ k))) n

theorem harmonicLo_succ (D n : ℕ) : harmonicLo D (n + 1) = harmonicLo D n + D / (n + 1) := rfl
theorem harmonicHi_succ (D n : ℕ) : harmonicHi D (n + 1) = harmonicHi D n + cdiv D (n + 1) := rfl

theorem harmonicLo_le (D n : ℕ) : (harmonicLo D n : ℝ) ≤ D * ((harmonic n : ℚ) : ℝ) := by
  induction n with
  | zero => simp [harmonicLo]
  | succ n ih =>
    rw [harmonicLo_succ, harmonic_succ]
    push_cast
    have := fdiv_le D (n + 1)
    push_cast at this
    have e : (D : ℝ) * (((harmonic n : ℚ) : ℝ) + ((n : ℝ) + 1)⁻¹)
        = D * ((harmonic n : ℚ) : ℝ) + (D : ℝ) / ((n : ℝ) + 1) := by ring
    rw [e]; linarith

theorem le_harmonicHi (D n : ℕ) : D * ((harmonic n : ℚ) : ℝ) ≤ (harmonicHi D n : ℝ) := by
  induction n with
  | zero => simp [harmonicHi]
  | succ n ih =>
    rw [harmonicHi_succ, harmonic_succ]
    push_cast
    have := div_le_cdiv D (n + 1) (Nat.succ_pos n)
    push_cast at this
    have e : (D : ℝ) * (((harmonic n : ℚ) : ℝ) + ((n : ℝ) + 1)⁻¹)
        = D * ((harmonic n : ℚ) : ℝ) + (D : ℝ) / ((n : ℝ) + 1) := by ring
    rw [e]; linarith

/-- Lower bound for `P.D * γ` from the DeTemple bound at `n`. -/
def gammaLo (P : Prec) (n : ℕ) : ℕ :=
  harmonicLo P.D n + P.l2lo - (logHi P (2 * n + 1) + cdiv P.D (24 * n * n))

/-- Upper bound for `P.D * γ` from the DeTemple bound at `n`. -/
def gammaHi (P : Prec) (n : ℕ) : ℕ :=
  harmonicHi P.D n + P.l2hi - (logLo P (2 * n + 1) + P.D / (24 * (n + 1) * (n + 1)))

theorem gamSeq_eq (n : ℕ) :
    gamSeq n = (harmonic n : ℝ) - log ((2 * n + 1 : ℕ) : ℝ) + log 2 := by
  unfold gamSeq
  have : ((n : ℝ) + 1 / 2) = ((2 * n + 1 : ℕ) : ℝ) / 2 := by push_cast; ring
  rw [this, log_div (by positivity) (by norm_num)]
  ring

theorem gammaLo_le {P : Prec} (hP : P.Valid) {n : ℕ} (hn : 1 ≤ n) :
    (gammaLo P n : ℝ) ≤ P.D * eulerMascheroniConstant := by
  have hD : (0 : ℝ) < P.D := by exact_mod_cast hP.pos
  have hnr : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hγ := gamSeq_sub_le_gamma hn
  rw [gamSeq_eq] at hγ
  have hH := harmonicLo_le P.D n
  have hL := le_logHi hP (n := 2 * n + 1) (by omega)
  have hC : (P.D : ℝ) * (1 / (24 * (n : ℝ) ^ 2)) ≤ (cdiv P.D (24 * n * n) : ℝ) := by
    refine le_trans (le_of_eq ?_) (div_le_cdiv _ _ (by positivity))
    push_cast; field_simp
  have h2 := hP.l2lo
  have hpos : (0 : ℝ) ≤ P.D * eulerMascheroniConstant :=
    mul_nonneg hD.le (by linarith [one_half_lt_eulerMascheroniConstant])
  have hmain := mul_le_mul_of_nonneg_left hγ hD.le
  unfold gammaLo
  rcases le_total (logHi P (2 * n + 1) + cdiv P.D (24 * n * n)) (harmonicLo P.D n + P.l2lo)
    with hle | hle
  · rw [Nat.cast_sub hle]; push_cast; nlinarith
  · rw [Nat.sub_eq_zero_of_le hle]; simpa using hpos

theorem le_gammaHi {P : Prec} (hP : P.Valid) (n : ℕ) :
    P.D * eulerMascheroniConstant ≤ (gammaHi P n : ℝ) := by
  have hD : (0 : ℝ) < P.D := by exact_mod_cast hP.pos
  have hγ := gamma_le_gamSeq_sub n
  rw [gamSeq_eq] at hγ
  have hH := le_harmonicHi P.D n
  have hL := logLo_le hP (n := 2 * n + 1) (by omega)
  have hC : ((P.D / (24 * (n + 1) * (n + 1)) : ℕ) : ℝ)
      ≤ (P.D : ℝ) * (1 / (24 * ((n : ℝ) + 1) ^ 2)) := by
    refine (fdiv_le _ _).trans (le_of_eq ?_)
    push_cast; field_simp
  have h2 := hP.l2hi
  have hmain := mul_le_mul_of_nonneg_left hγ hD.le
  unfold gammaHi
  refine le_trans ?_ (cast_sub_ge _ _)
  push_cast
  nlinarith

/-- `0.69314718055994530941723212 ≤ log 2` at scale `10^26`. -/
theorem log_two_lo26 :
    ((69314718055994530941723212 : ℕ) : ℝ) ≤ ((100000000000000000000000000 : ℕ) : ℝ) * log 2 :=
  lo_rescale (D := 100000000000000000000000000) (M := 100000)
    (lo := logTwoLo (100000000000000000000000000 * 100000) 16) (by norm_num)
    (logTwoLo_le (by norm_num) 16) (by decide +kernel)

/-- `log 2 ≤ 0.69314718055994530941723213` at scale `10^26`. -/
theorem log_two_hi26 :
    ((100000000000000000000000000 : ℕ) : ℝ) * log 2 ≤ ((69314718055994530941723213 : ℕ) : ℝ) :=
  hi_rescale (D := 100000000000000000000000000) (M := 100000)
    (hi := logTwoHi (100000000000000000000000000 * 100000) 16) (by norm_num)
    (le_logTwoHi (by norm_num) 16) (by decide +kernel)

/-- Scale `10^26`, 16 series terms, arguments below `2^32` (used for `γ`). -/
def P26 : Prec :=
  ⟨100000000000000000000000000, 16, 5, 69314718055994530941723212, 69314718055994530941723213⟩

theorem P26_valid : P26.Valid := ⟨by decide, log_two_lo26, log_two_hi26⟩

set_option maxRecDepth 100000 in
/-- `10^20 γ ≥ 57721566490153281893`. -/
theorem gamma_lo20 :
    ((57721566490153281893 : ℕ) : ℝ) ≤
      ((100000000000000000000 : ℕ) : ℝ) * eulerMascheroniConstant :=
  lo_rescale (D := 100000000000000000000) (M := 1000000) (lo := gammaLo P26 100000) (by norm_num)
    (gammaLo_le P26_valid (by norm_num)) (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `10^20 γ ≤ 57721566490153290228`. -/
theorem gamma_hi20 :
    ((100000000000000000000 : ℕ) : ℝ) * eulerMascheroniConstant ≤
      ((57721566490153290228 : ℕ) : ℝ) :=
  hi_rescale (D := 100000000000000000000) (M := 1000000) (hi := gammaHi P26 100000) (by norm_num)
    (le_gammaHi P26_valid 100000) (by decide +kernel)

/-- `0.57721566490153281893 ≤ γ ≤ 0.57721566490153290228` (width `< 8.4e-17`). -/
theorem gamma_mem : (57721566490153281893 : ℝ) / 10 ^ 20 ≤ eulerMascheroniConstant ∧
    eulerMascheroniConstant ≤ (57721566490153290228 : ℝ) / 10 ^ 20 := by
  have h1 := gamma_lo20
  have h2 := gamma_hi20
  push_cast at h1 h2
  constructor
  · rw [div_le_iff₀ (by positivity)]; linarith
  · rw [le_div_iff₀ (by positivity)]; linarith

/-- `3.14159265358979323846 ≤ π ≤ 3.14159265358979323847`. -/
theorem pi_mem : (314159265358979323846 : ℝ) / 10 ^ 20 ≤ π ∧
    π ≤ (314159265358979323847 : ℝ) / 10 ^ 20 := by
  have h1 := pi_lo20
  have h2 := pi_hi20
  push_cast at h1 h2
  constructor
  · rw [div_le_iff₀ (by positivity)]; linarith
  · rw [le_div_iff₀ (by positivity)]; linarith

end Exp7.Num
