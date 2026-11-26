import Exp7Lean.Numerics.Constants

/-!
# Fixed-point interval arithmetic and a verified expression evaluator

An interval `I : FI` is a pair of integers `lo, hi`; at scale `D` it encloses the real `x` when
`I.Has D x : lo ≤ D * x ≤ hi`.  This file provides

* the arithmetic operations `add`, `neg`, `sub`, `mul`, `inv`, `div` (by a positive interval),
  `log` (of a positive interval), `sqrt` (of a non-negative interval), `exp`, constants, each
  with a soundness lemma `FI.has_*`;
* a reified expression type `RExpr` with its real value `RExpr.val` and the evaluator
  `RExpr.eval : Ctx → RExpr → Option FI`, with the single soundness theorem `RExpr.eval_sound`;
* `RExpr.pos_of_eval`, `RExpr.lt_of_eval`: certificates for strict inequalities between
  expressions, decided by kernel evaluation.

The rounding is directed everywhere (`ifloor`, `iceil`).
-/

namespace Exp7.Num

open Real

/-! ### Directed integer division -/

/-- `⌊a / b⌋` (used with `b > 0`). -/
def ifloor (a b : ℤ) : ℤ := a / b

/-- `⌈a / b⌉` (used with `b > 0`). -/
def iceil (a b : ℤ) : ℤ := -((-a) / b)

theorem ifloor_le (a : ℤ) {b : ℤ} (hb : 0 < b) : ((ifloor a b : ℤ) : ℝ) ≤ (a : ℝ) / b := by
  have h : ifloor a b * b ≤ a := Int.ediv_mul_le a hb.ne'
  have hbr : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  rw [le_div_iff₀ hbr]
  exact_mod_cast h

theorem le_iceil (a : ℤ) {b : ℤ} (hb : 0 < b) : (a : ℝ) / b ≤ ((iceil a b : ℤ) : ℝ) := by
  have h : (-a) / b * b ≤ -a := Int.ediv_mul_le (-a) hb.ne'
  have hbr : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have h' : (((-a) / b : ℤ) : ℝ) * b ≤ -(a : ℝ) := by exact_mod_cast h
  rw [div_le_iff₀ hbr]
  unfold iceil
  push_cast
  linarith

/-! ### Intervals -/

/-- A fixed-point interval: the endpoints are `lo / D` and `hi / D` for a scale `D`. -/
structure FI where
  lo : ℤ
  hi : ℤ
  deriving Repr, DecidableEq

/-- `I` encloses `x` at scale `D`. -/
def FI.Has (D : ℕ) (I : FI) (x : ℝ) : Prop := (I.lo : ℝ) ≤ D * x ∧ D * x ≤ (I.hi : ℝ)

theorem FI.Has.mem {D : ℕ} (hD : 0 < D) {I : FI} {x : ℝ} (h : I.Has D x) :
    (I.lo : ℝ) / D ≤ x ∧ x ≤ (I.hi : ℝ) / D := by
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  constructor
  · rw [div_le_iff₀ hDr, mul_comm]; exact h.1
  · rw [le_div_iff₀ hDr, mul_comm]; exact h.2

/-- A positive lower endpoint certifies positivity. -/
theorem FI.Has.pos {D : ℕ} {I : FI} {x : ℝ} (h : I.Has D x) (hlo : 0 < I.lo) : 0 < x := by
  have h1 : (0 : ℝ) < (I.lo : ℝ) := by exact_mod_cast hlo
  have h2 : (0 : ℝ) < D * x := lt_of_lt_of_le h1 h.1
  by_contra hx
  have hx' : x ≤ 0 := not_lt.mp hx
  have : (D : ℝ) * x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg D) hx'
  linarith

/-- A negative upper endpoint certifies negativity. -/
theorem FI.Has.neg' {D : ℕ} {I : FI} {x : ℝ} (h : I.Has D x) (hhi : I.hi < 0) : x < 0 := by
  have h1 : (I.hi : ℝ) < 0 := by exact_mod_cast hhi
  have h2 : (D : ℝ) * x < 0 := lt_of_le_of_lt h.2 h1
  by_contra hx
  have hx' : 0 ≤ x := not_lt.mp hx
  have : 0 ≤ (D : ℝ) * x := mul_nonneg (Nat.cast_nonneg D) hx'
  linarith

/-- Enclosure from natural-number bounds (as produced by `logLo`, `sqrtLo`, ...). -/
def FI.ofNats (lo hi : ℕ) : FI := ⟨(lo : ℤ), (hi : ℤ)⟩

theorem FI.has_ofNats {D lo hi : ℕ} {x : ℝ} (h1 : (lo : ℝ) ≤ D * x) (h2 : D * x ≤ (hi : ℝ)) :
    (FI.ofNats lo hi).Has D x := by
  constructor
  · change (((lo : ℤ) : ℝ)) ≤ _; push_cast; exact h1
  · change _ ≤ (((hi : ℤ) : ℝ)); push_cast; exact h2

/-- The integer `n`. -/
def FI.ofInt (D : ℕ) (n : ℤ) : FI := ⟨n * D, n * D⟩

theorem FI.has_ofInt (D : ℕ) (n : ℤ) : (FI.ofInt D n).Has D (n : ℝ) := by
  constructor <;> (simp only [FI.ofInt]; push_cast; linarith)

/-- The rational `p / q`, `q > 0`. -/
def FI.ofRat (D : ℕ) (p : ℤ) (q : ℕ) : FI := ⟨ifloor (p * D) q, iceil (p * D) q⟩

theorem FI.has_ofRat (D : ℕ) (p : ℤ) {q : ℕ} (hq : 0 < q) :
    (FI.ofRat D p q).Has D ((p : ℝ) / q) := by
  have hq' : (0 : ℤ) < (q : ℤ) := by exact_mod_cast hq
  have h1 := ifloor_le (p * D) hq'
  have h2 := le_iceil (p * D) hq'
  push_cast at h1 h2
  have e : (D : ℝ) * ((p : ℝ) / q) = (p : ℝ) * D / q := by ring
  exact ⟨by rw [e]; exact h1, by rw [e]; exact h2⟩

/-- Sum. -/
def FI.add (I J : FI) : FI := ⟨I.lo + J.lo, I.hi + J.hi⟩

/-- Negation. -/
def FI.neg (I : FI) : FI := ⟨-I.hi, -I.lo⟩

/-- Difference. -/
def FI.sub (I J : FI) : FI := ⟨I.lo - J.hi, I.hi - J.lo⟩

theorem FI.has_add {D : ℕ} {I J : FI} {x y : ℝ} (hx : I.Has D x) (hy : J.Has D y) :
    (I.add J).Has D (x + y) := by
  obtain ⟨h1, h2⟩ := hx
  obtain ⟨h3, h4⟩ := hy
  constructor <;> (simp only [FI.add]; push_cast; linarith)

theorem FI.has_neg {D : ℕ} {I : FI} {x : ℝ} (hx : I.Has D x) : I.neg.Has D (-x) := by
  obtain ⟨h1, h2⟩ := hx
  constructor <;> (simp only [FI.neg]; push_cast; linarith)

theorem FI.has_sub {D : ℕ} {I J : FI} {x y : ℝ} (hx : I.Has D x) (hy : J.Has D y) :
    (I.sub J).Has D (x - y) := by
  obtain ⟨h1, h2⟩ := hx
  obtain ⟨h3, h4⟩ := hy
  constructor <;> (simp only [FI.sub]; push_cast; linarith)

/-! ### Multiplication -/

theorem min4_le_mul {a b c d X Y : ℝ} (hX1 : a ≤ X) (hX2 : X ≤ b) (hY1 : c ≤ Y) (hY2 : Y ≤ d) :
    min (min (a * c) (a * d)) (min (b * c) (b * d)) ≤ X * Y := by
  have h1 : min (a * Y) (b * Y) ≤ X * Y := by
    rcases le_total 0 Y with hY | hY
    · exact (min_le_left _ _).trans (mul_le_mul_of_nonneg_right hX1 hY)
    · exact (min_le_right _ _).trans (mul_le_mul_of_nonpos_right hX2 hY)
  have h2 : min (a * c) (a * d) ≤ a * Y := by
    rcases le_total 0 a with ha | ha
    · exact (min_le_left _ _).trans (mul_le_mul_of_nonneg_left hY1 ha)
    · exact (min_le_right _ _).trans (mul_le_mul_of_nonpos_left hY2 ha)
  have h3 : min (b * c) (b * d) ≤ b * Y := by
    rcases le_total 0 b with hb | hb
    · exact (min_le_left _ _).trans (mul_le_mul_of_nonneg_left hY1 hb)
    · exact (min_le_right _ _).trans (mul_le_mul_of_nonpos_left hY2 hb)
  exact (min_le_min h2 h3).trans h1

theorem mul_le_max4 {a b c d X Y : ℝ} (hX1 : a ≤ X) (hX2 : X ≤ b) (hY1 : c ≤ Y) (hY2 : Y ≤ d) :
    X * Y ≤ max (max (a * c) (a * d)) (max (b * c) (b * d)) := by
  have h1 : X * Y ≤ max (a * Y) (b * Y) := by
    rcases le_total 0 Y with hY | hY
    · exact (mul_le_mul_of_nonneg_right hX2 hY).trans (le_max_right _ _)
    · exact (mul_le_mul_of_nonpos_right hX1 hY).trans (le_max_left _ _)
  have h2 : a * Y ≤ max (a * c) (a * d) := by
    rcases le_total 0 a with ha | ha
    · exact (mul_le_mul_of_nonneg_left hY2 ha).trans (le_max_right _ _)
    · exact (mul_le_mul_of_nonpos_left hY1 ha).trans (le_max_left _ _)
  have h3 : b * Y ≤ max (b * c) (b * d) := by
    rcases le_total 0 b with hb | hb
    · exact (mul_le_mul_of_nonneg_left hY2 hb).trans (le_max_right _ _)
    · exact (mul_le_mul_of_nonpos_left hY1 hb).trans (le_max_left _ _)
  exact h1.trans (max_le_max h2 h3)

/-- Product (all sign cases), rounded outward. -/
def FI.mul (D : ℕ) (I J : FI) : FI :=
  ⟨ifloor (min (min (I.lo * J.lo) (I.lo * J.hi)) (min (I.hi * J.lo) (I.hi * J.hi))) D,
   iceil (max (max (I.lo * J.lo) (I.lo * J.hi)) (max (I.hi * J.lo) (I.hi * J.hi))) D⟩

theorem FI.has_mul {D : ℕ} (hD : 0 < D) {I J : FI} {x y : ℝ} (hx : I.Has D x) (hy : J.Has D y) :
    (I.mul D J).Has D (x * y) := by
  obtain ⟨h1, h2⟩ := hx
  obtain ⟨h3, h4⟩ := hy
  have hD' : (0 : ℤ) < (D : ℤ) := by exact_mod_cast hD
  have hDr : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD
  have e : (D : ℝ) * (x * y) = (D * x) * (D * y) / D := by field_simp
  constructor
  · have hf := ifloor_le
      (min (min (I.lo * J.lo) (I.lo * J.hi)) (min (I.hi * J.lo) (I.hi * J.hi))) hD'
    have hm := min4_le_mul h1 h2 h3 h4
    push_cast at hf
    change ((ifloor _ _ : ℤ) : ℝ) ≤ _
    rw [e]
    exact hf.trans (div_le_div_of_nonneg_right hm hDr.le)
  · have hc := le_iceil
      (max (max (I.lo * J.lo) (I.lo * J.hi)) (max (I.hi * J.lo) (I.hi * J.hi))) hD'
    have hm := mul_le_max4 h1 h2 h3 h4
    push_cast at hc
    change _ ≤ ((iceil _ _ : ℤ) : ℝ)
    rw [e]
    exact (div_le_div_of_nonneg_right hm hDr.le).trans hc

/-! ### Inverse and division by a positive interval -/

/-- Inverse of an interval with `0 < lo`. -/
def FI.inv (D : ℕ) (I : FI) : FI := ⟨ifloor ((D : ℤ) * D) I.hi, iceil ((D : ℤ) * D) I.lo⟩

theorem FI.has_inv {D : ℕ} (hD : 0 < D) {I : FI} {x : ℝ} (hx : I.Has D x) (hlo : 0 < I.lo) :
    (I.inv D).Has D x⁻¹ := by
  obtain ⟨h1, h2⟩ := hx
  have hDr : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD
  have hlor : (0 : ℝ) < (I.lo : ℝ) := by exact_mod_cast hlo
  have hxpos : 0 < x := FI.Has.pos ⟨h1, h2⟩ hlo
  have hDx : 0 < (D : ℝ) * x := mul_pos hDr hxpos
  have hhi : (0 : ℤ) < I.hi := by
    have : (0 : ℝ) < (I.hi : ℝ) := lt_of_lt_of_le hDx h2
    exact_mod_cast this
  have hhir : (0 : ℝ) < (I.hi : ℝ) := by exact_mod_cast hhi
  have e : (D : ℝ) * x⁻¹ = (D : ℝ) * D / (D * x) := by field_simp
  constructor
  · have hf := ifloor_le ((D : ℤ) * D) hhi
    push_cast at hf
    change ((ifloor _ _ : ℤ) : ℝ) ≤ _
    rw [e]
    exact hf.trans (div_le_div_of_nonneg_left (by positivity) hDx h2)
  · have hc := le_iceil ((D : ℤ) * D) hlo
    push_cast at hc
    change _ ≤ ((iceil _ _ : ℤ) : ℝ)
    rw [e]
    exact (div_le_div_of_nonneg_left (by positivity) hlor h1).trans hc

/-- Quotient by an interval with `0 < lo`. -/
def FI.div (D : ℕ) (I J : FI) : FI := I.mul D (J.inv D)

theorem FI.has_div {D : ℕ} (hD : 0 < D) {I J : FI} {x y : ℝ} (hx : I.Has D x) (hy : J.Has D y)
    (hlo : 0 < J.lo) : (I.div D J).Has D (x / y) := by
  rw [div_eq_mul_inv]
  exact FI.has_mul hD hx (FI.has_inv hD hy hlo)

/-! ### Elementary functions -/

/-- `log` of an interval with `1 ≤ lo` (i.e. `x ≥ 1/D > 0`). -/
def FI.log (P : Prec) (I : FI) : FI :=
  ⟨(logLo P I.lo.toNat : ℤ) - (logHi P P.D : ℤ), (logHi P I.hi.toNat : ℤ) - (logLo P P.D : ℤ)⟩

theorem FI.has_log {P : Prec} (hP : P.Valid) {I : FI} {x : ℝ} (hx : I.Has P.D x)
    (hlo : 1 ≤ I.lo) : (I.log P).Has P.D (Real.log x) := by
  obtain ⟨h1, h2⟩ := hx
  have hD : 0 < P.D := hP.pos
  have hDr : (0 : ℝ) < (P.D : ℝ) := by exact_mod_cast hD
  have hxpos : 0 < x := FI.Has.pos ⟨h1, h2⟩ (by omega)
  have hlo0 : 0 ≤ I.lo := by omega
  have hhi1 : 1 ≤ I.hi := by
    have : (I.lo : ℝ) ≤ (I.hi : ℝ) := h1.trans h2
    have : I.lo ≤ I.hi := by exact_mod_cast this
    omega
  have hloN : 1 ≤ I.lo.toNat := by omega
  have hhiN : 1 ≤ I.hi.toNat := by omega
  have eLo : ((I.lo.toNat : ℕ) : ℝ) = (I.lo : ℝ) := by
    have : ((I.lo.toNat : ℕ) : ℤ) = I.lo := Int.toNat_of_nonneg hlo0
    exact_mod_cast this
  have eHi : ((I.hi.toNat : ℕ) : ℝ) = (I.hi : ℝ) := by
    have : ((I.hi.toNat : ℕ) : ℤ) = I.hi := Int.toNat_of_nonneg (by omega)
    exact_mod_cast this
  have hlor : (0 : ℝ) < (I.lo : ℝ) := by
    have : (1 : ℝ) ≤ (I.lo : ℝ) := by exact_mod_cast hlo
    linarith
  have hhir : (0 : ℝ) < (I.hi : ℝ) := lt_of_lt_of_le hlor (h1.trans h2)
  have a1 := logLo_le hP hloN
  have a2 := le_logHi hP hD
  have a3 := le_logHi hP hhiN
  have a4 := logLo_le hP hD
  rw [eLo] at a1
  rw [eHi] at a3
  -- log (lo / D) ≤ log x ≤ log (hi / D)
  have b1 : Real.log (I.lo : ℝ) - Real.log (P.D : ℝ) ≤ Real.log x := by
    rw [← Real.log_div hlor.ne' hDr.ne']
    apply Real.log_le_log (by positivity)
    rw [div_le_iff₀ hDr]; linarith
  have b2 : Real.log x ≤ Real.log (I.hi : ℝ) - Real.log (P.D : ℝ) := by
    rw [← Real.log_div hhir.ne' hDr.ne']
    apply Real.log_le_log hxpos
    rw [le_div_iff₀ hDr]; linarith
  constructor
  · change (((logLo P I.lo.toNat : ℤ) - (logHi P P.D : ℤ) : ℤ) : ℝ) ≤ _
    push_cast
    nlinarith
  · change _ ≤ (((logHi P I.hi.toNat : ℤ) - (logLo P P.D : ℤ) : ℤ) : ℝ)
    push_cast
    nlinarith

/-- `√` of an interval with `0 ≤ lo`. -/
def FI.sqrt (D bits fuel : ℕ) (I : FI) : FI :=
  ⟨(sqrtLo 1 bits fuel (I.lo.toNat * D) : ℤ), (sqrtHi 1 bits fuel (I.hi.toNat * D) : ℤ)⟩

theorem FI.has_sqrt {D : ℕ} (hD : 0 < D) (bits fuel : ℕ) {I : FI} {x : ℝ} (hx : I.Has D x)
    (hlo : 0 ≤ I.lo) : (I.sqrt D bits fuel).Has D (√x) := by
  obtain ⟨h1, h2⟩ := hx
  have hDr : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD
  have hhi0 : 0 ≤ I.hi := by
    have : (I.lo : ℝ) ≤ (I.hi : ℝ) := h1.trans h2
    have : I.lo ≤ I.hi := by exact_mod_cast this
    omega
  have eLo : ((I.lo.toNat : ℕ) : ℝ) = (I.lo : ℝ) := by
    have : ((I.lo.toNat : ℕ) : ℤ) = I.lo := Int.toNat_of_nonneg hlo
    exact_mod_cast this
  have eHi : ((I.hi.toNat : ℕ) : ℝ) = (I.hi : ℝ) := by
    have : ((I.hi.toNat : ℕ) : ℤ) = I.hi := Int.toNat_of_nonneg hhi0
    exact_mod_cast this
  have hx0 : 0 ≤ x := by
    have : (0 : ℝ) ≤ (I.lo : ℝ) := by exact_mod_cast hlo
    have : 0 ≤ (D : ℝ) * x := this.trans h1
    exact nonneg_of_mul_nonneg_right this hDr
  -- D √x = √(D · (D x))
  have e : (D : ℝ) * √x = √((D : ℝ) * ((D : ℝ) * x)) := by
    rw [← mul_assoc, Real.sqrt_mul (by positivity), Real.sqrt_mul_self hDr.le]
  have a1 := sqrtLo_le 1 bits fuel (I.lo.toNat * D)
  have a2 := le_sqrtHi 1 bits fuel (I.hi.toNat * D)
  push_cast at a1 a2
  rw [one_mul, eLo] at a1
  rw [one_mul, eHi] at a2
  constructor
  · change (((sqrtLo 1 bits fuel (I.lo.toNat * D) : ℕ) : ℤ) : ℝ) ≤ _
    push_cast
    rw [e]
    refine a1.trans (Real.sqrt_le_sqrt ?_)
    nlinarith
  · change _ ≤ (((sqrtHi 1 bits fuel (I.hi.toNat * D) : ℕ) : ℤ) : ℝ)
    push_cast
    rw [e]
    refine le_trans (Real.sqrt_le_sqrt ?_) a2
    nlinarith

/-- `exp` of an arbitrary interval. -/
def FI.exp (D N s : ℕ) (I : FI) : FI :=
  ⟨if 0 ≤ I.lo then (expLo D N s I.lo.toNat : ℤ) else (expNegLo D N s (-I.lo).toNat : ℤ),
   if 0 ≤ I.hi then (expHi D N s I.hi.toNat : ℤ) else (expNegHi D N s (-I.hi).toNat : ℤ)⟩

theorem FI.has_exp {D : ℕ} (hD : 0 < D) (N s : ℕ) {I : FI} {x : ℝ} (hx : I.Has D x) :
    (I.exp D N s).Has D (Real.exp x) := by
  obtain ⟨h1, h2⟩ := hx
  constructor
  · change ((if 0 ≤ I.lo then (expLo D N s I.lo.toNat : ℤ)
      else (expNegLo D N s (-I.lo).toNat : ℤ) : ℤ) : ℝ) ≤ _
    split_ifs with h
    · have e : ((I.lo.toNat : ℕ) : ℝ) = (I.lo : ℝ) := by
        have : ((I.lo.toNat : ℕ) : ℤ) = I.lo := Int.toNat_of_nonneg h
        exact_mod_cast this
      have := expLo_le hD N s (x := I.lo.toNat) (t := x) (by rw [e]; exact h1)
      push_cast; exact this
    · have e : (((-I.lo).toNat : ℕ) : ℝ) = -(I.lo : ℝ) := by
        have : (((-I.lo).toNat : ℕ) : ℤ) = -I.lo := Int.toNat_of_nonneg (by omega)
        exact_mod_cast this
      have := expNegLo_le hD N s (x := (-I.lo).toNat) (t := -x) (by rw [e]; linarith)
      rw [neg_neg] at this
      push_cast; exact this
  · change _ ≤ ((if 0 ≤ I.hi then (expHi D N s I.hi.toNat : ℤ)
      else (expNegHi D N s (-I.hi).toNat : ℤ) : ℤ) : ℝ)
    split_ifs with h
    · have e : ((I.hi.toNat : ℕ) : ℝ) = (I.hi : ℝ) := by
        have : ((I.hi.toNat : ℕ) : ℤ) = I.hi := Int.toNat_of_nonneg h
        exact_mod_cast this
      have := le_expHi hD N s (x := I.hi.toNat) (t := x) (by rw [e]; exact h2)
      push_cast; exact this
    · have e : (((-I.hi).toNat : ℕ) : ℝ) = -(I.hi : ℝ) := by
        have : (((-I.hi).toNat : ℕ) : ℤ) = -I.hi := Int.toNat_of_nonneg (by omega)
        exact_mod_cast this
      have := le_expNegHi hD N s (x := (-I.hi).toNat) (t := -x) (by rw [e]; linarith)
      rw [neg_neg] at this
      push_cast; exact this

/-! ### Evaluation context -/

/-- Everything the evaluator needs: precision parameters for `log`, fuel for `√`, the degree and
halving count for `exp`, and enclosures of `π` and `γ` at the scale `P.D`. -/
structure Ctx where
  P : Prec
  sqrtFuel : ℕ
  expN : ℕ
  expS : ℕ
  piLo : ℕ
  piHi : ℕ
  gamLo : ℕ
  gamHi : ℕ

/-- Soundness of a context. -/
structure Ctx.Valid (C : Ctx) : Prop where
  prec : C.P.Valid
  piLo : (C.piLo : ℝ) ≤ C.P.D * π
  piHi : C.P.D * π ≤ (C.piHi : ℝ)
  gamLo : (C.gamLo : ℝ) ≤ C.P.D * eulerMascheroniConstant
  gamHi : C.P.D * eulerMascheroniConstant ≤ (C.gamHi : ℝ)

/-- The standard context at scale `10^20` (logarithms of arguments up to `2^256`,
`exp` accurate for `|x| ≲ 32`). -/
def ctx20 : Ctx :=
  { P := P20w, sqrtFuel := 9, expN := 22, expS := 6,
    piLo := 314159265358979323846, piHi := 314159265358979323847,
    gamLo := 57721566490153281893, gamHi := 57721566490153290228 }

theorem ctx20_valid : ctx20.Valid :=
  ⟨P20w_valid, pi_lo20, pi_hi20, gamma_lo20, gamma_hi20⟩

/-! ### Reified real expressions -/

/-- Real-valued expressions built from integers, rationals, `π`, `γ`, the field operations and
`log`, `√`, `exp`. -/
inductive RExpr where
  | int (n : ℤ)
  | rat (p : ℤ) (q : ℕ)
  | pi
  | gamma
  | add (a b : RExpr)
  | sub (a b : RExpr)
  | mul (a b : RExpr)
  | div (a b : RExpr)
  | neg (a : RExpr)
  | log (a : RExpr)
  | sqrt (a : RExpr)
  | exp (a : RExpr)

/-- The real number denoted by an expression. -/
noncomputable def RExpr.val : RExpr → ℝ
  | .int n => (n : ℝ)
  | .rat p q => (p : ℝ) / (q : ℝ)
  | .pi => π
  | .gamma => eulerMascheroniConstant
  | .add a b => a.val + b.val
  | .sub a b => a.val - b.val
  | .mul a b => a.val * b.val
  | .div a b => a.val / b.val
  | .neg a => -a.val
  | .log a => Real.log a.val
  | .sqrt a => √a.val
  | .exp a => Real.exp a.val

/-- Interval evaluation.  `none` signals a side condition that could not be certified
(division by an interval not known to be positive, `log` of an interval not known to be
`≥ 1/D`, `√` of an interval not known to be non-negative, a zero denominator). -/
def RExpr.eval (C : Ctx) : RExpr → Option FI
  | .int n => some (FI.ofInt C.P.D n)
  | .rat p q => if 0 < q then some (FI.ofRat C.P.D p q) else none
  | .pi => some (FI.ofNats C.piLo C.piHi)
  | .gamma => some (FI.ofNats C.gamLo C.gamHi)
  | .add a b =>
    match a.eval C, b.eval C with
    | some I, some J => some (I.add J)
    | _, _ => none
  | .sub a b =>
    match a.eval C, b.eval C with
    | some I, some J => some (I.sub J)
    | _, _ => none
  | .mul a b =>
    match a.eval C, b.eval C with
    | some I, some J => some (I.mul C.P.D J)
    | _, _ => none
  | .div a b =>
    match a.eval C, b.eval C with
    | some I, some J => if 0 < J.lo then some (I.div C.P.D J) else none
    | _, _ => none
  | .neg a =>
    match a.eval C with
    | some I => some I.neg
    | none => none
  | .log a =>
    match a.eval C with
    | some I => if 1 ≤ I.lo then some (I.log C.P) else none
    | none => none
  | .sqrt a =>
    match a.eval C with
    | some I => if 0 ≤ I.lo then some (I.sqrt C.P.D C.P.bits C.sqrtFuel) else none
    | none => none
  | .exp a =>
    match a.eval C with
    | some I => some (I.exp C.P.D C.expN C.expS)
    | none => none

/-- **Soundness of the evaluator.** -/
theorem RExpr.eval_sound {C : Ctx} (hC : C.Valid) :
    ∀ (e : RExpr) (I : FI), e.eval C = some I → I.Has C.P.D e.val := by
  have hD : 0 < C.P.D := hC.prec.pos
  intro e
  induction e with
  | int n =>
    intro I h
    simp only [RExpr.eval, Option.some.injEq] at h
    subst h; exact FI.has_ofInt _ _
  | rat p q =>
    intro I h
    simp only [RExpr.eval] at h
    split_ifs at h with hq
    simp only [Option.some.injEq] at h
    subst h; exact FI.has_ofRat _ _ hq
  | pi =>
    intro I h
    simp only [RExpr.eval, Option.some.injEq] at h
    subst h; exact FI.has_ofNats hC.piLo hC.piHi
  | gamma =>
    intro I h
    simp only [RExpr.eval, Option.some.injEq] at h
    subst h; exact FI.has_ofNats hC.gamLo hC.gamHi
  | add a b iha ihb =>
    intro I h
    simp only [RExpr.eval] at h
    cases ha : a.eval C with
    | none => simp [ha] at h
    | some Ia =>
      cases hb : b.eval C with
      | none => simp [ha, hb] at h
      | some Ib =>
        simp only [ha, hb, Option.some.injEq] at h
        subst h; exact FI.has_add (iha _ ha) (ihb _ hb)
  | sub a b iha ihb =>
    intro I h
    simp only [RExpr.eval] at h
    cases ha : a.eval C with
    | none => simp [ha] at h
    | some Ia =>
      cases hb : b.eval C with
      | none => simp [ha, hb] at h
      | some Ib =>
        simp only [ha, hb, Option.some.injEq] at h
        subst h; exact FI.has_sub (iha _ ha) (ihb _ hb)
  | mul a b iha ihb =>
    intro I h
    simp only [RExpr.eval] at h
    cases ha : a.eval C with
    | none => simp [ha] at h
    | some Ia =>
      cases hb : b.eval C with
      | none => simp [ha, hb] at h
      | some Ib =>
        simp only [ha, hb, Option.some.injEq] at h
        subst h; exact FI.has_mul hD (iha _ ha) (ihb _ hb)
  | div a b iha ihb =>
    intro I h
    simp only [RExpr.eval] at h
    cases ha : a.eval C with
    | none => simp [ha] at h
    | some Ia =>
      cases hb : b.eval C with
      | none => simp [ha, hb] at h
      | some Ib =>
        simp only [ha, hb] at h
        split_ifs at h with hpos
        simp only [Option.some.injEq] at h
        subst h; exact FI.has_div hD (iha _ ha) (ihb _ hb) hpos
  | neg a iha =>
    intro I h
    simp only [RExpr.eval] at h
    cases ha : a.eval C with
    | none => simp [ha] at h
    | some Ia =>
      simp only [ha, Option.some.injEq] at h
      subst h; exact FI.has_neg (iha _ ha)
  | log a iha =>
    intro I h
    simp only [RExpr.eval] at h
    cases ha : a.eval C with
    | none => simp [ha] at h
    | some Ia =>
      simp only [ha] at h
      split_ifs at h with hpos
      simp only [Option.some.injEq] at h
      subst h; exact FI.has_log hC.prec (iha _ ha) hpos
  | sqrt a iha =>
    intro I h
    simp only [RExpr.eval] at h
    cases ha : a.eval C with
    | none => simp [ha] at h
    | some Ia =>
      simp only [ha] at h
      split_ifs at h with hpos
      simp only [Option.some.injEq] at h
      subst h; exact FI.has_sqrt hD _ _ (iha _ ha) hpos
  | exp a iha =>
    intro I h
    simp only [RExpr.eval] at h
    cases ha : a.eval C with
    | none => simp [ha] at h
    | some Ia =>
      simp only [ha, Option.some.injEq] at h
      subst h; exact FI.has_exp hD _ _ (iha _ ha)

/-- Boolean certificate that the expression is positive. -/
def RExpr.isPos (C : Ctx) (e : RExpr) : Bool :=
  match e.eval C with
  | some I => decide (0 < I.lo)
  | none => false

/-- If the evaluator returns an interval with positive lower endpoint, the value is positive. -/
theorem RExpr.pos_of_isPos {C : Ctx} (hC : C.Valid) {e : RExpr} (h : e.isPos C = true) :
    0 < e.val := by
  unfold RExpr.isPos at h
  cases he : e.eval C with
  | none => simp [he] at h
  | some I =>
    simp only [he, decide_eq_true_eq] at h
    exact (RExpr.eval_sound hC e I he).pos h

/-- `a < b` certified by evaluating `b - a`. -/
theorem RExpr.lt_of_isPos {C : Ctx} (hC : C.Valid) {a b : RExpr}
    (h : (RExpr.sub b a).isPos C = true) : a.val < b.val := by
  have := RExpr.pos_of_isPos hC h
  simp only [RExpr.val] at this
  linarith

/-- Rational enclosure from an evaluation. -/
theorem RExpr.mem_of_eval {C : Ctx} (hC : C.Valid) {e : RExpr} {I : FI}
    (h : e.eval C = some I) :
    (I.lo : ℝ) / C.P.D ≤ e.val ∧ e.val ≤ (I.hi : ℝ) / C.P.D :=
  (RExpr.eval_sound hC e I h).mem hC.prec.pos

end Exp7.Num
