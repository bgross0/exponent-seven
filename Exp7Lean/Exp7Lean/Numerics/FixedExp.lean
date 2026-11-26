import Exp7Lean.Numerics.FixedLog

/-!
# A verified fixed-point exponential

For a natural `x` (a fixed-point argument at scale `D`, i.e. the real number `x / D ≥ 0`):

* `expLo D N s x ≤ D * exp t` whenever `x ≤ D * t`;
* `D * exp t ≤ expHi D N s x` whenever `D * t ≤ x`;
* `expNegLo D N s x ≤ D * exp (-t)` whenever `D * t ≤ x`;
* `D * exp (-t) ≤ expNegHi D N s x` whenever `x ≤ D * t`.

Method: argument halving `y = x / 2^s`, the Taylor polynomial of degree `N` in Horner form with
directed rounding (Mathlib's `Real.sum_le_exp_of_nonneg` and `Real.exp_bound'` give the two-sided
truncation bound for `0 ≤ y ≤ 1`), then `s` squarings with directed rounding, and for negative
arguments one directed division.  All statements hold for every `D > 0`, `N`, `s`, `x`; the
parameters only affect accuracy.
-/

namespace Exp7.Num

open Real

/-! ### The Taylor polynomial in Horner form (real level) -/

/-- `expHorner y c m k = ∑_{j<m} y^j k!/(k+j)! + c y^m k!/(k+m)!`, as a Horner recursion. -/
noncomputable def expHorner (y c : ℝ) : ℕ → ℕ → ℝ
  | 0, _ => c
  | m + 1, k => 1 + y / ((k : ℝ) + 1) * expHorner y c m (k + 1)

theorem expHorner_eq (y c : ℝ) (m k : ℕ) :
    expHorner y c m k = ∑ j ∈ Finset.range m, y ^ j * (k.factorial : ℝ) / ((k + j).factorial : ℝ)
      + c * y ^ m * (k.factorial : ℝ) / ((k + m).factorial : ℝ) := by
  induction m generalizing k with
  | zero =>
    have : ((k.factorial : ℕ) : ℝ) ≠ 0 := by positivity
    simp [expHorner, this]
  | succ m ih =>
    have e1 : ∀ j : ℕ, y / ((k : ℝ) + 1) *
        (y ^ j * ((k + 1).factorial : ℝ) / ((k + 1 + j).factorial : ℝ))
        = y ^ (j + 1) * (k.factorial : ℝ) / ((k + (j + 1)).factorial : ℝ) := by
      intro j
      have hj : k + 1 + j = k + (j + 1) := by omega
      rw [hj, Nat.factorial_succ k]
      push_cast
      have h1 : ((k : ℝ) + 1) ≠ 0 := by positivity
      have h2 : (((k + (j + 1)).factorial : ℕ) : ℝ) ≠ 0 := by positivity
      field_simp
      ring
    have e2 : y / ((k : ℝ) + 1) *
        (c * y ^ m * ((k + 1).factorial : ℝ) / ((k + 1 + m).factorial : ℝ))
        = c * y ^ (m + 1) * (k.factorial : ℝ) / ((k + (m + 1)).factorial : ℝ) := by
      have hj : k + 1 + m = k + (m + 1) := by omega
      rw [hj, Nat.factorial_succ k]
      push_cast
      have h1 : ((k : ℝ) + 1) ≠ 0 := by positivity
      have h2 : (((k + (m + 1)).factorial : ℕ) : ℝ) ≠ 0 := by positivity
      field_simp
      ring
    have hk : ((k.factorial : ℕ) : ℝ) ≠ 0 := by positivity
    rw [expHorner, ih, Finset.sum_range_succ', mul_add, Finset.mul_sum, e2,
      Finset.sum_congr rfl (fun j _ => e1 j)]
    simp only [pow_zero, add_zero, one_mul, div_self hk]
    ring

theorem expHorner_nonneg {y c : ℝ} (hy : 0 ≤ y) (hc : 0 ≤ c) (m k : ℕ) :
    0 ≤ expHorner y c m k := by
  induction m generalizing k with
  | zero => simpa [expHorner] using hc
  | succ m ih =>
    rw [expHorner]
    have := ih (k + 1)
    positivity

theorem expHorner_le_exp {y : ℝ} (hy : 0 ≤ y) (N : ℕ) : expHorner y 0 N 0 ≤ exp y := by
  rw [expHorner_eq]
  simpa using sum_le_exp_of_nonneg hy N

theorem exp_remainder_le {y : ℝ} (hy : 0 ≤ y) {n : ℕ} (hn : 0 < n) :
    y ^ n * ((n : ℝ) + 1) / ((n.factorial : ℝ) * n) ≤ 2 * y ^ n / (n.factorial : ℝ) := by
  have hf : (0 : ℝ) < (n.factorial : ℝ) := by positivity
  have hnr : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  rw [div_le_div_iff₀ (by positivity) hf]
  calc y ^ n * ((n : ℝ) + 1) * (n.factorial : ℝ)
      ≤ y ^ n * (2 * (n : ℝ)) * (n.factorial : ℝ) := by gcongr; linarith
    _ = 2 * y ^ n * ((n.factorial : ℝ) * n) := by ring

theorem exp_le_expHorner {y : ℝ} (hy : 0 ≤ y) (hy1 : y ≤ 1) (N : ℕ) :
    exp y ≤ expHorner y 2 (N + 1) 0 := by
  have hb := exp_bound' hy hy1 (Nat.succ_pos N)
  have ha := exp_remainder_le hy (Nat.succ_pos N)
  rw [expHorner_eq]
  simp only [Nat.factorial_zero, Nat.cast_one, mul_one, zero_add]
  simp only [Nat.succ_eq_add_one] at hb ha
  linarith

/-! ### Fixed-point Horner evaluation -/

/-- Lower Horner sum of the exponential series, scale `D`, argument `y / D`. -/
def expSumLo (D y : ℕ) (m : ℕ) : ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ) (fun _ => 0)
    (fun _ ih k => Nat.add D (Nat.div (Nat.mul y (ih (Nat.succ k))) (Nat.mul D (Nat.succ k)))) m

/-- Upper Horner sum of the exponential series; `c` is the (scaled) remainder coefficient. -/
def expSumHi (D y c : ℕ) (m : ℕ) : ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ) (fun _ => c)
    (fun _ ih k => Nat.add D (cdiv (Nat.mul y (ih (Nat.succ k))) (Nat.mul D (Nat.succ k)))) m

theorem expSumLo_zero (D y k : ℕ) : expSumLo D y 0 k = 0 := rfl
theorem expSumLo_succ (D y m k : ℕ) :
    expSumLo D y (m + 1) k = D + y * expSumLo D y m (k + 1) / (D * (k + 1)) := rfl
theorem expSumHi_zero (D y c k : ℕ) : expSumHi D y c 0 k = c := rfl
theorem expSumHi_succ (D y c m k : ℕ) :
    expSumHi D y c (m + 1) k = D + cdiv (y * expSumHi D y c m (k + 1)) (D * (k + 1)) := rfl

theorem expSumLo_le {D : ℕ} (hD : 0 < D) {y : ℝ} {yn : ℕ} (hy : (yn : ℝ) ≤ D * y) (m k : ℕ) :
    (expSumLo D yn m k : ℝ) ≤ D * expHorner y 0 m k := by
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  have hDy : (0 : ℝ) ≤ D * y := le_trans (Nat.cast_nonneg yn) hy
  induction m generalizing k with
  | zero => simp [expSumLo_zero, expHorner]
  | succ m ih =>
    rw [expSumLo_succ, expHorner]
    push_cast
    have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have a2 : ((yn * expSumLo D yn m (k + 1) / (D * (k + 1)) : ℕ) : ℝ)
        ≤ D * (y / ((k : ℝ) + 1) * expHorner y 0 m (k + 1)) := by
      refine (fdiv_le _ _).trans ?_
      push_cast
      rw [div_le_iff₀ (by positivity)]
      have := mul_le_mul hy (ih (k + 1)) (Nat.cast_nonneg _) hDy
      calc (yn : ℝ) * (expSumLo D yn m (k + 1) : ℝ)
          ≤ D * y * (D * expHorner y 0 m (k + 1)) := this
        _ = D * (y / ((k : ℝ) + 1) * expHorner y 0 m (k + 1)) * (D * ((k : ℝ) + 1)) := by
          field_simp
    linarith

theorem le_expSumHi {D : ℕ} (hD : 0 < D) {y c : ℝ} (hy0 : 0 ≤ y) (hc0 : 0 ≤ c) {yn cn : ℕ}
    (hy : D * y ≤ (yn : ℝ)) (hc : D * c ≤ (cn : ℝ)) (m k : ℕ) :
    D * expHorner y c m k ≤ (expSumHi D yn cn m k : ℝ) := by
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  induction m generalizing k with
  | zero => simpa [expSumHi_zero, expHorner] using hc
  | succ m ih =>
    rw [expSumHi_succ, expHorner]
    push_cast
    have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have a2 : D * (y / ((k : ℝ) + 1) * expHorner y c m (k + 1))
        ≤ (cdiv (yn * expSumHi D yn cn m (k + 1)) (D * (k + 1)) : ℝ) := by
      refine le_trans ?_ (div_le_cdiv _ _ (Nat.mul_pos hD (Nat.succ_pos k)))
      push_cast
      rw [le_div_iff₀ (by positivity)]
      have := mul_le_mul hy (ih (k + 1))
        (mul_nonneg hDr.le (expHorner_nonneg hy0 hc0 m (k + 1))) (Nat.cast_nonneg _)
      calc D * (y / ((k : ℝ) + 1) * expHorner y c m (k + 1)) * (D * ((k : ℝ) + 1))
          = D * y * (D * expHorner y c m (k + 1)) := by field_simp
        _ ≤ (yn : ℝ) * (expSumHi D yn cn m (k + 1) : ℝ) := this
    linarith

/-! ### Repeated squaring -/

/-- `s` squarings at scale `D`, rounded down. -/
def sqIterLo (D v s : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) v (fun _ ih => Nat.div (Nat.mul ih ih) D) s

/-- `s` squarings at scale `D`, rounded up. -/
def sqIterHi (D v s : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) v (fun _ ih => cdiv (Nat.mul ih ih) D) s

theorem sqIterLo_succ (D v s : ℕ) :
    sqIterLo D v (s + 1) = sqIterLo D v s * sqIterLo D v s / D := rfl
theorem sqIterHi_succ (D v s : ℕ) :
    sqIterHi D v (s + 1) = cdiv (sqIterHi D v s * sqIterHi D v s) D := rfl

theorem sqIterLo_le {D : ℕ} (hD : 0 < D) {t : ℝ} {v : ℕ} (hv : (v : ℝ) ≤ D * t) (s : ℕ) :
    (sqIterLo D v s : ℝ) ≤ D * t ^ (2 ^ s) := by
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  have hDt : (0 : ℝ) ≤ D * t := le_trans (Nat.cast_nonneg v) hv
  have ht : 0 ≤ t := nonneg_of_mul_nonneg_right hDt hDr
  induction s with
  | zero => simpa [sqIterLo] using hv
  | succ s ih =>
    rw [sqIterLo_succ]
    refine (fdiv_le _ _).trans ?_
    rw [div_le_iff₀ hDr]
    push_cast
    have := mul_le_mul ih ih (Nat.cast_nonneg _) (by positivity)
    calc (sqIterLo D v s : ℝ) * (sqIterLo D v s : ℝ)
        ≤ D * t ^ 2 ^ s * (D * t ^ 2 ^ s) := this
      _ = D * t ^ 2 ^ (s + 1) * D := by rw [pow_succ 2 s, pow_mul]; ring

theorem le_sqIterHi {D : ℕ} (hD : 0 < D) {t : ℝ} (ht : 0 ≤ t) {v : ℕ} (hv : D * t ≤ (v : ℝ))
    (s : ℕ) : D * t ^ (2 ^ s) ≤ (sqIterHi D v s : ℝ) := by
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  induction s with
  | zero => simpa [sqIterHi] using hv
  | succ s ih =>
    rw [sqIterHi_succ]
    refine le_trans ?_ (div_le_cdiv _ _ hD)
    rw [le_div_iff₀ hDr]
    push_cast
    have := mul_le_mul ih ih (by positivity) (Nat.cast_nonneg _)
    calc D * t ^ 2 ^ (s + 1) * D = D * t ^ 2 ^ s * (D * t ^ 2 ^ s) := by
          rw [pow_succ 2 s, pow_mul]; ring
      _ ≤ (sqIterHi D v s : ℝ) * (sqIterHi D v s : ℝ) := this

theorem le_sqIterLo {D v : ℕ} (hD : 0 < D) (hv : D ≤ v) (s : ℕ) : D ≤ sqIterLo D v s := by
  induction s with
  | zero => simpa [sqIterLo] using hv
  | succ s ih =>
    rw [sqIterLo_succ, Nat.le_div_iff_mul_le hD]
    exact Nat.mul_le_mul ih ih

theorem exp_eq_pow_two_pow (t : ℝ) (s : ℕ) : exp t = exp (t / 2 ^ s) ^ (2 ^ s) := by
  rw [← exp_natCast_mul]
  congr 1
  push_cast
  field_simp

/-! ### `exp` of a non-negative fixed-point number -/

/-- Lower bound for `D * exp (x / D)`: `N + 1` Taylor terms at `x / 2^s`, then `s` squarings. -/
def expLo (D N s x : ℕ) : ℕ :=
  sqIterLo D (expSumLo D (Nat.div x (Nat.pow 2 s)) (Nat.succ N) 0) s

/-- Upper bound for `D * exp (x / D)`.  (The `else` branch, taken only if `x / 2^s > D`, i.e. if
`s` was chosen too small, is the crude bound `3^⌈x/D⌉`.) -/
def expHi (D N s x : ℕ) : ℕ :=
  cond (Nat.ble (cdiv x (Nat.pow 2 s)) D)
    (sqIterHi D (expSumHi D (cdiv x (Nat.pow 2 s)) (Nat.mul 2 D) (Nat.succ N) 0) s)
    (Nat.mul D (Nat.pow 3 (cdiv x D)))

theorem expLo_eq (D N s x : ℕ) :
    expLo D N s x = sqIterLo D (expSumLo D (x / 2 ^ s) (N + 1) 0) s := rfl

theorem expHi_eq (D N s x : ℕ) : expHi D N s x =
    if cdiv x (2 ^ s) ≤ D then sqIterHi D (expSumHi D (cdiv x (2 ^ s)) (2 * D) (N + 1) 0) s
    else D * 3 ^ cdiv x D := by
  rw [expHi, cond_ble]; rfl

theorem expLo_le {D : ℕ} (hD : 0 < D) (N s : ℕ) {x : ℕ} {t : ℝ} (hx : (x : ℝ) ≤ D * t) :
    (expLo D N s x : ℝ) ≤ D * exp t := by
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  have h2 : (0 : ℝ) < 2 ^ s := by positivity
  rw [expLo_eq, exp_eq_pow_two_pow t s]
  apply sqIterLo_le hD
  -- the reduced argument `y = ⌊x / 2^s⌋ / D ≤ t / 2^s`
  set yn : ℕ := x / 2 ^ s with hyn
  have hy0 : (0 : ℝ) ≤ (yn : ℝ) / D := by positivity
  have hyt : (yn : ℝ) / D ≤ t / 2 ^ s := by
    have h1 : (yn : ℝ) ≤ (x : ℝ) / 2 ^ s := by
      have := fdiv_le x (2 ^ s)
      push_cast at this
      exact this
    rw [div_le_iff₀ hDr]
    calc (yn : ℝ) ≤ (x : ℝ) / 2 ^ s := h1
      _ ≤ D * t / 2 ^ s := by gcongr
      _ = t / 2 ^ s * D := by ring
  have hS := expSumLo_le hD (y := (yn : ℝ) / D) (yn := yn)
    (le_of_eq (by field_simp)) (N + 1) 0
  calc (expSumLo D yn (N + 1) 0 : ℝ) ≤ D * expHorner ((yn : ℝ) / D) 0 (N + 1) 0 := hS
    _ ≤ D * exp ((yn : ℝ) / D) := by gcongr; exact expHorner_le_exp hy0 _
    _ ≤ D * exp (t / 2 ^ s) := by gcongr

theorem le_expHi {D : ℕ} (hD : 0 < D) (N s : ℕ) {x : ℕ} {t : ℝ} (hx : D * t ≤ (x : ℝ)) :
    D * exp t ≤ (expHi D N s x : ℝ) := by
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  have h2 : (0 : ℝ) < 2 ^ s := by positivity
  rw [expHi_eq]
  split_ifs with hle
  · rw [exp_eq_pow_two_pow t s]
    apply le_sqIterHi hD (exp_pos _).le
    set yn : ℕ := cdiv x (2 ^ s) with hyn
    have hy0 : (0 : ℝ) ≤ (yn : ℝ) / D := by positivity
    have hy1 : (yn : ℝ) / D ≤ 1 := by
      rw [div_le_one hDr]; exact_mod_cast hle
    have hyt : t / 2 ^ s ≤ (yn : ℝ) / D := by
      have h1 : (x : ℝ) / 2 ^ s ≤ (yn : ℝ) := by
        have := div_le_cdiv x (2 ^ s) (by positivity)
        push_cast at this
        exact this
      rw [le_div_iff₀ hDr]
      calc t / 2 ^ s * D = D * t / 2 ^ s := by ring
        _ ≤ (x : ℝ) / 2 ^ s := by gcongr
        _ ≤ (yn : ℝ) := h1
    have hS := le_expSumHi hD (y := (yn : ℝ) / D) (c := 2) hy0 (by norm_num) (yn := yn)
      (cn := 2 * D) (le_of_eq (by field_simp)) (le_of_eq (by push_cast; ring)) (N + 1) 0
    calc D * exp (t / 2 ^ s) ≤ D * exp ((yn : ℝ) / D) := by gcongr
      _ ≤ D * expHorner ((yn : ℝ) / D) 2 (N + 1) 0 := by
        gcongr; exact exp_le_expHorner hy0 hy1 N
      _ ≤ (expSumHi D yn (2 * D) (N + 1) 0 : ℝ) := hS
  · push_cast
    apply mul_le_mul_of_nonneg_left _ hDr.le
    have h1 : t ≤ ((cdiv x D : ℕ) : ℝ) := by
      have := div_le_cdiv x D hD
      refine le_trans ?_ this
      rw [le_div_iff₀ hDr]; linarith
    calc exp t ≤ exp ((cdiv x D : ℕ) : ℝ) := exp_le_exp.mpr h1
      _ = exp 1 ^ cdiv x D := by rw [← exp_natCast_mul, mul_one]
      _ ≤ 3 ^ cdiv x D := by
        gcongr
        exact exp_one_lt_three.le

theorem le_expLo {D : ℕ} (hD : 0 < D) (N s x : ℕ) : D ≤ expLo D N s x := by
  rw [expLo_eq]
  apply le_sqIterLo hD
  rw [expSumLo_succ]
  exact Nat.le_add_right _ _

/-! ### `exp` of a non-positive fixed-point number -/

/-- Lower bound for `D * exp (-(x / D))`. -/
def expNegLo (D N s x : ℕ) : ℕ := Nat.div (Nat.mul D D) (expHi D N s x)

/-- Upper bound for `D * exp (-(x / D))`. -/
def expNegHi (D N s x : ℕ) : ℕ := cdiv (Nat.mul D D) (expLo D N s x)

theorem expNegLo_le {D : ℕ} (hD : 0 < D) (N s : ℕ) {x : ℕ} {t : ℝ} (hx : D * t ≤ (x : ℝ)) :
    (expNegLo D N s x : ℝ) ≤ D * exp (-t) := by
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  have hH := le_expHi hD N s hx
  have hHpos : (0 : ℝ) < (expHi D N s x : ℝ) := lt_of_lt_of_le (by positivity) hH
  change ((D * D / expHi D N s x : ℕ) : ℝ) ≤ _
  refine (fdiv_le _ _).trans ?_
  rw [div_le_iff₀ hHpos, exp_neg]
  push_cast
  calc (D : ℝ) * D = D * (exp t)⁻¹ * (D * exp t) := by
        have := (exp_pos t).ne'
        field_simp
    _ ≤ D * (exp t)⁻¹ * (expHi D N s x : ℝ) := by
        apply mul_le_mul_of_nonneg_left hH
        have := exp_pos t
        positivity

theorem le_expNegHi {D : ℕ} (hD : 0 < D) (N s : ℕ) {x : ℕ} {t : ℝ} (hx : (x : ℝ) ≤ D * t) :
    D * exp (-t) ≤ (expNegHi D N s x : ℝ) := by
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  have hL := expLo_le hD N s hx
  have hLpos : 0 < expLo D N s x := lt_of_lt_of_le hD (le_expLo hD N s x)
  have hLr : (0 : ℝ) < (expLo D N s x : ℝ) := by exact_mod_cast hLpos
  change _ ≤ ((cdiv (D * D) (expLo D N s x) : ℕ) : ℝ)
  refine le_trans ?_ (div_le_cdiv _ _ hLpos)
  rw [le_div_iff₀ hLr, exp_neg]
  push_cast
  calc D * (exp t)⁻¹ * (expLo D N s x : ℝ) ≤ D * (exp t)⁻¹ * (D * exp t) := by
        apply mul_le_mul_of_nonneg_left hL
        have := exp_pos t
        positivity
    _ = (D : ℝ) * D := by
        have := (exp_pos t).ne'
        field_simp

end Exp7.Num
