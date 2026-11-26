import Exp7Lean.Numerics.Interval
import Exp7Lean.Numerics.PrimeSum

/-!
# Accuracy statements and worked examples

Soundness of the evaluators is proved once for all arguments (`logLo_le`, `le_logHi`, `sqrtLo_le`,
`le_sqrtHi`, ...).  This file adds what only a computation can give: the *accuracy* actually
achieved on the range of interest, and a few enclosures used later.

* `log_sqrt_accuracy` : for every `2 ≤ n ≤ 6400`, at scale `10^20`, the `log` enclosure has width
  at most `16` units and the `√` enclosure width at most `1` unit;
* `log_mem_6400`, `sqrt_mem_6400` : the resulting closed-form enclosures
  `L ≤ 10^20 log n ≤ L + 16`, `S ≤ 10^20 √n ≤ S + 1` with `L = logLo P20 n`, `S = sqrtLo ... n`;
* `exp_neg_mem` : `exp (-k/64)` for `k = 0, …, 960` (the range `[-15, 0]`) with absolute width
  `≤ 63e-20` and relative width `≤ 1e-13`;
* `rowConst_mem` : `log π + γ - π/2 + 3 log 2 ∈ [2.23059076563587229937, 2.23059076563587238814]`
  (the constant of every certificate row), obtained from the expression evaluator.
-/

namespace Exp7.Num

open Real

/-- The scale `10^20`, as a literal. -/
def D20 : ℕ := 100000000000000000000

/-- `⌊10^20 √n⌋`-type lower bound with the standard parameters. -/
def sqrtLo20 (n : ℕ) : ℕ := sqrtLo 100000000000000000000 4 7 n

/-- Upper bound for `10^20 √n` with the standard parameters. -/
def sqrtHi20 (n : ℕ) : ℕ := sqrtHi 100000000000000000000 4 7 n

/-- Kernel computation over all `2 ≤ n ≤ 6400`: widths of the enclosures. -/
theorem log_sqrt_accuracy_check :
    allBelow2 (fun k => Nat.ble (logHi P20 (k + 2)) (logLo P20 (k + 2) + 16) &&
      Nat.ble (sqrtHi20 (k + 2)) (sqrtLo20 (k + 2) + 1)) 80 80 = true := by
  decide +kernel

/-- For `2 ≤ n ≤ 6400`: `logHi ≤ logLo + 16` and `sqrtHi ≤ sqrtLo + 1` (units of `10^-20`). -/
theorem log_sqrt_accuracy {n : ℕ} (h2 : 2 ≤ n) (h : n ≤ 6400) :
    logHi P20 n ≤ logLo P20 n + 16 ∧ sqrtHi20 n ≤ sqrtLo20 n + 1 := by
  have hk := allBelow2_imp _ _ _ log_sqrt_accuracy_check (n - 2) (by omega)
  have e : n - 2 + 2 = n := by omega
  rw [e, Bool.and_eq_true] at hk
  exact ⟨Nat.le_of_ble_eq_true hk.1, Nat.le_of_ble_eq_true hk.2⟩

/-- `log n` to 18 decimal places for `2 ≤ n ≤ 6400`:
`L / 10^20 ≤ log n ≤ (L + 16) / 10^20` with `L = logLo P20 n`. -/
theorem log_mem_6400 {n : ℕ} (h2 : 2 ≤ n) (h : n ≤ 6400) :
    (logLo P20 n : ℝ) / 10 ^ 20 ≤ log n ∧ log n ≤ ((logLo P20 n : ℝ) + 16) / 10 ^ 20 := by
  have h1 := logLo_le P20_valid (n := n) (by omega)
  have h3 := le_logHi P20_valid (n := n) (by omega)
  have hw : (logHi P20 n : ℝ) ≤ (logLo P20 n : ℝ) + 16 := by
    exact_mod_cast (log_sqrt_accuracy h2 h).1
  have hD : ((P20.D : ℕ) : ℝ) = 10 ^ 20 := by norm_num [P20]
  rw [hD] at h1 h3
  constructor
  · rw [div_le_iff₀ (by positivity)]; linarith
  · rw [le_div_iff₀ (by positivity)]; linarith

/-- `√n` to 20 decimal places for `2 ≤ n ≤ 6400`:
`S / 10^20 ≤ √n ≤ (S + 1) / 10^20` with `S = sqrtLo20 n`. -/
theorem sqrt_mem_6400 {n : ℕ} (h2 : 2 ≤ n) (h : n ≤ 6400) :
    (sqrtLo20 n : ℝ) / 10 ^ 20 ≤ √(n : ℝ) ∧ √(n : ℝ) ≤ ((sqrtLo20 n : ℝ) + 1) / 10 ^ 20 := by
  have h1 := sqrtLo_le 100000000000000000000 4 7 n
  have h3 := le_sqrtHi 100000000000000000000 4 7 n
  have hw : (sqrtHi20 n : ℝ) ≤ (sqrtLo20 n : ℝ) + 1 := by
    exact_mod_cast (log_sqrt_accuracy h2 h).2
  have hD : ((100000000000000000000 : ℕ) : ℝ) = 10 ^ 20 := by norm_num
  rw [hD] at h1 h3
  constructor
  · rw [div_le_iff₀ (by positivity)]; exact le_trans h1 (le_of_eq (mul_comm _ _))
  · rw [le_div_iff₀ (by positivity)]
    calc √(n : ℝ) * 10 ^ 20 = 10 ^ 20 * √(n : ℝ) := mul_comm _ _
      _ ≤ (sqrtHi20 n : ℝ) := h3
      _ ≤ _ := hw

/-! ### Examples of single enclosures (literal statements) -/

/-- `log 6361`, as an instance. -/
example : (875794087667880423314 : ℝ) / 10 ^ 20 ≤ log 6361 ∧
    log 6361 ≤ (875794087667880423330 : ℝ) / 10 ^ 20 := by
  have h := log_mem_6400 (n := 6361) (by norm_num) (by norm_num)
  have e : logLo P20 6361 = 875794087667880423314 := by decide +kernel
  rw [e] at h
  norm_num at h ⊢
  exact h

/-- `√2`, as an instance. -/
example : (141421356237309504880 : ℝ) / 10 ^ 20 ≤ √2 ∧
    √2 ≤ (141421356237309504881 : ℝ) / 10 ^ 20 := by
  have h := sqrt_mem_6400 (n := 2) (by norm_num) (by norm_num)
  have e : sqrtLo20 2 = 141421356237309504880 := by decide +kernel
  rw [e] at h
  norm_num at h ⊢
  exact h

/-! ### Accuracy of `exp` on `[-15, 0]` -/

/-- Lower bound for `10^20 exp (-k/64)` (20 Taylor terms after 5 halvings). -/
def expNegLo20 (k : ℕ) : ℕ :=
  expNegLo 100000000000000000000 20 5 (Nat.mul k 1562500000000000000)

/-- Upper bound for `10^20 exp (-k/64)`. -/
def expNegHi20 (k : ℕ) : ℕ :=
  expNegHi 100000000000000000000 20 5 (Nat.mul k 1562500000000000000)

/-- Kernel computation for `k < 961`: absolute width `≤ 63` units, relative width `≤ 10^-13`. -/
theorem exp_accuracy_check :
    allBelow2 (fun k => Nat.ble (expNegHi20 k) (expNegLo20 k + 63) &&
      Nat.ble ((expNegHi20 k - expNegLo20 k) * 10000000000000) (expNegLo20 k)) 31 31 = true := by
  decide +kernel

/-- `exp (-k/64)` for `0 ≤ k ≤ 960`: `E / 10^20 ≤ exp (-k/64) ≤ (E + 63) / 10^20` with
`E = expNegLo20 k`; moreover the enclosure is relatively `10^-13`-tight. -/
theorem exp_neg_mem {k : ℕ} (hk : k ≤ 960) :
    (expNegLo20 k : ℝ) / 10 ^ 20 ≤ Real.exp (-((k : ℝ) / 64)) ∧
    Real.exp (-((k : ℝ) / 64)) ≤ ((expNegLo20 k : ℝ) + 63) / 10 ^ 20 ∧
    (expNegHi20 k - expNegLo20 k) * 10 ^ 13 ≤ expNegLo20 k := by
  have hc := allBelow2_imp _ _ _ exp_accuracy_check k (by omega)
  rw [Bool.and_eq_true] at hc
  have w1 : expNegHi20 k ≤ expNegLo20 k + 63 := Nat.le_of_ble_eq_true hc.1
  have w2 : (expNegHi20 k - expNegLo20 k) * 10000000000000 ≤ expNegLo20 k :=
    Nat.le_of_ble_eq_true hc.2
  have hx : (((k * 1562500000000000000 : ℕ) : ℝ)) = ((100000000000000000000 : ℕ) : ℝ) *
      ((k : ℝ) / 64) := by push_cast; ring
  have h1 := expNegLo_le (D := 100000000000000000000) (by norm_num) 20 5
    (x := k * 1562500000000000000) (t := (k : ℝ) / 64) (le_of_eq hx.symm)
  have h2 := le_expNegHi (D := 100000000000000000000) (by norm_num) 20 5
    (x := k * 1562500000000000000) (t := (k : ℝ) / 64) (le_of_eq hx)
  have w1' : (expNegHi20 k : ℝ) ≤ (expNegLo20 k : ℝ) + 63 := by exact_mod_cast w1
  have hD : ((100000000000000000000 : ℕ) : ℝ) = 10 ^ 20 := by norm_num
  rw [hD] at h1 h2
  refine ⟨?_, ?_, ?_⟩
  · rw [div_le_iff₀ (by positivity)]
    calc (expNegLo20 k : ℝ) ≤ 10 ^ 20 * Real.exp (-((k : ℝ) / 64)) := h1
      _ = _ := mul_comm _ _
  · rw [le_div_iff₀ (by positivity)]
    calc Real.exp (-((k : ℝ) / 64)) * 10 ^ 20 = 10 ^ 20 * Real.exp (-((k : ℝ) / 64)) :=
          mul_comm _ _
      _ ≤ (expNegHi20 k : ℝ) := h2
      _ ≤ _ := w1'
  · exact w2

/-! ### The constant of the certificate rows, via the expression evaluator -/

/-- `log π + γ - π/2 + 3 log 2` as a reified expression. -/
def rowConstExpr : RExpr :=
  .add (.sub (.add (.log .pi) .gamma) (.div .pi (.int 2))) (.mul (.int 3) (.log (.int 2)))

theorem rowConstExpr_val :
    rowConstExpr.val = log π + eulerMascheroniConstant - π / 2 + 3 * log 2 := by
  simp [rowConstExpr, RExpr.val]

theorem rowConstExpr_eval :
    rowConstExpr.eval ctx20 = some ⟨223059076563587229937, 223059076563587238814⟩ := by
  decide +kernel

/-- `2.23059076563587229937 ≤ log π + γ - π/2 + 3 log 2 ≤ 2.23059076563587238814`. -/
theorem rowConst_mem :
    (223059076563587229937 : ℝ) / 10 ^ 20 ≤ log π + eulerMascheroniConstant - π / 2 + 3 * log 2 ∧
    log π + eulerMascheroniConstant - π / 2 + 3 * log 2 ≤
      (223059076563587238814 : ℝ) / 10 ^ 20 := by
  have h := RExpr.mem_of_eval ctx20_valid rowConstExpr_eval
  rw [rowConstExpr_val] at h
  have hD : ((ctx20.P.D : ℕ) : ℝ) = 10 ^ 20 := by norm_num [ctx20, P20w]
  rw [hD] at h
  norm_num at h ⊢
  exact h

/-- A strict inequality decided by the evaluator: `exp (-(3/2048) log 6362) < 99/100`. -/
example : Real.exp (-3 / 2048 * log 6362) < 99 / 100 := by
  have h := RExpr.lt_of_isPos ctx20_valid
    (a := .exp (.mul (.rat (-3) 2048) (.log (.int 6362)))) (b := .rat 99 100) (by decide +kernel)
  simp only [RExpr.val] at h
  norm_num at h ⊢
  exact h

end Exp7.Num
