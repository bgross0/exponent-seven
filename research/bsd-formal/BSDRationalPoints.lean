import BSDOrdinary
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.LinearAlgebra.Dimension.Basic
import Mathlib.GroupTheory.OrderOfElement

/-!
# Independent rational points on the conductor-389 pilot

This module works with Mathlib's actual affine point group for
`y² + y = x³ + x² - 2x`.  It proves that `(0,0)` and `(1,0)` are
independent over the integers.  The arithmetic inputs are exact obstructions
to halving these points (and their sum), together with absence of rational
two-torsion.  Monic rational-root integrality reduces those obstructions to
three quartics modulo eleven and one cubic modulo four.

No Mordell--Weil finite-generation theorem, point-reduction homomorphism,
Selmer-group upper bound, analytic rank, or finiteness of Sha is assumed.
-/

namespace BSDRationalPoints

open Polynomial WeierstrassCurve

noncomputable section

set_option maxHeartbeats 1000000

/-- The same rational curve used by the ordinary-root certificate. -/
abbrev E : WeierstrassCurve.Affine ℚ := BSDOrdinary.curve389 ℚ

instance elliptic : E.IsElliptic := by
  constructor
  rw [isUnit_iff_ne_zero]
  norm_num [E, BSDOrdinary.curve389, WeierstrassCurve.Δ,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

/-- The first rational point. -/
def P : E.Point := Affine.Point.mk (x := 0) (y := 0) (by
  norm_num [Affine.equation_iff, E, BSDOrdinary.curve389])

/-- The second rational point. -/
def Q : E.Point := Affine.Point.mk (x := 1) (y := 0) (by
  norm_num [Affine.equation_iff, E, BSDOrdinary.curve389])

/-- Their sum, written in affine coordinates. -/
def PQ : E.Point := Affine.Point.mk (x := -2) (y := -1) (by
  norm_num [Affine.equation_iff, E, BSDOrdinary.curve389])

/-- Numerator of the actual duplication formula. -/
def dupNum {R : Type*} [CommRing R] (x : R) : R :=
  x ^ 4 + 4 * x ^ 2 - 2 * x + 3

/-- Denominator of the actual duplication formula. -/
def dupDen {R : Type*} [CommRing R] (x : R) : R :=
  4 * x ^ 3 + 4 * x ^ 2 - 8 * x + 1

/-- A rational half of a point with integral x-coordinate `k` must satisfy
this monic quartic. -/
def halfPolynomial (k : ℤ) : Polynomial ℤ :=
  X ^ 4 + 4 * X ^ 2 - 2 * X + 3 -
    C k * (4 * X ^ 3 + 4 * X ^ 2 - 8 * X + 1)

theorem halfPolynomial_monic (k : ℤ) : (halfPolynomial k).Monic := by
  unfold halfPolynomial
  monicity!

/-- The three finite local obstructions are checked in the Lean kernel. -/
theorem half_obstruction_mod11 :
    ∀ k : ZMod 11, k = 0 ∨ k = 1 ∨ k = -2 →
      ∀ x : ZMod 11, dupNum x - k * dupDen x ≠ 0 := by
  decide +kernel

/-- The monic quartics have no rational roots. -/
theorem half_obstruction_rat (k : ℤ) (hk : k = 0 ∨ k = 1 ∨ k = -2)
    (x : ℚ) : dupNum x - (k : ℚ) * dupDen x ≠ 0 := by
  intro hx
  have hp : aeval x (halfPolynomial k) = 0 := by
    simpa [halfPolynomial, dupNum, dupDen, map_ofNat] using hx
  obtain ⟨n, hn, _⟩ := exists_integer_of_is_root_of_monic (halfPolynomial_monic k) hp
  have hx' : x = (n : ℚ) := hn
  rw [hx'] at hx
  have hz : dupNum n - k * dupDen n = 0 := by
    unfold dupNum dupDen at hx ⊢
    exact_mod_cast hx
  have hm : dupNum (n : ZMod 11) - (k : ZMod 11) * dupDen (n : ZMod 11) = 0 := by
    have hc := congrArg (fun a : ℤ => (a : ZMod 11)) hz
    simpa [dupNum, dupDen] using hc
  have hk' : (k : ZMod 11) = 0 ∨ (k : ZMod 11) = 1 ∨ (k : ZMod 11) = -2 := by
    rcases hk with rfl | rfl | rfl <;> norm_num
  exact half_obstruction_mod11 (k : ZMod 11) hk' (n : ZMod 11) hm

/-- With `u = 2x`, a rational two-torsion x-coordinate gives a root of
this monic cubic. -/
def twoTorsionObstruction : Polynomial ℤ := X ^ 3 + 2 * X ^ 2 - 8 * X + 2

theorem twoTorsionObstruction_monic : twoTorsionObstruction.Monic := by
  unfold twoTorsionObstruction
  monicity!

theorem two_torsion_obstruction_mod4 :
    ∀ u : ZMod 4, u ^ 3 + 2 * u ^ 2 - 8 * u + 2 ≠ 0 := by
  decide +kernel

/-- The duplication denominator never vanishes at a rational number. -/
theorem dupDen_ne_zero (x : ℚ) : dupDen x ≠ 0 := by
  intro hx
  have hu : (2 * x) ^ 3 + 2 * (2 * x) ^ 2 - 8 * (2 * x) + 2 = 0 := by
    unfold dupDen at hx
    linear_combination 2 * hx
  have hp : aeval (2 * x) twoTorsionObstruction = 0 := by
    simpa [twoTorsionObstruction, map_ofNat] using hu
  obtain ⟨n, hn, _⟩ := exists_integer_of_is_root_of_monic twoTorsionObstruction_monic hp
  have hn' : 2 * x = (n : ℚ) := hn
  rw [hn'] at hu
  have hz : n ^ 3 + 2 * n ^ 2 - 8 * n + 2 = 0 := by exact_mod_cast hu
  have hm : (n : ZMod 4) ^ 3 + 2 * (n : ZMod 4) ^ 2 - 8 * (n : ZMod 4) + 2 = 0 := by
    have hc := congrArg (fun a : ℤ => (a : ZMod 4)) hz
    simpa using hc
  exact two_torsion_obstruction_mod4 (n : ZMod 4) hm

/-- The actual rational point group has no nonzero element killed by two. -/
theorem double_eq_zero (R : E.Point) (hR : R + R = 0) : R = 0 := by
  cases R with
  | zero => rfl
  | some x y hxy =>
      exfalso
      have hroot := Affine.Point.isRoot_twoTorsionPolynomial_of_add_self hxy hR
      have hd : dupDen x = 0 := by
        norm_num [Polynomial.IsRoot.def, eval_toPoly_twoTorsionPolynomial,
          E, BSDOrdinary.curve389,
          WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆] at hroot
        unfold dupDen
        linear_combination hroot
      exact dupDen_ne_zero x hd

/-- None of the three relevant affine x-coordinates can occur as a double. -/
theorem not_double_of_x (k : ℤ) (hk : k = 0 ∨ k = 1 ∨ k = -2)
    (y : ℚ) (h : E.Nonsingular (k : ℚ) y) (R : E.Point) :
    R + R ≠ Affine.Point.some (k : ℚ) y h := by
  intro hR
  cases R with
  | zero =>
      change (0 : E.Point) + 0 = Affine.Point.some (k : ℚ) y h at hR
      exact Affine.Point.some_ne_zero h (by simpa using hR.symm)
  | some x z hxz =>
      have hn : z ≠ E.negY x z := by
        intro heq
        have hd := (Affine.den_duplication_eq_zero_iff hxz.left).mpr heq
        apply dupDen_ne_zero x
        norm_num [E, BSDOrdinary.curve389,
          WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆] at hd
        unfold dupDen
        linear_combination hd
      rw [Affine.Point.add_self_of_Y_ne hn] at hR
      have hxc : E.addX x x (E.slope x x z z) = (k : ℚ) := by
        exact (Affine.Point.some.inj hR).1
      rw [Affine.addX_self_of_Y_ne hxz.left hn] at hxc
      have hfrac : dupNum x / dupDen x = (k : ℚ) := by
        norm_num [E, BSDOrdinary.curve389,
          WeierstrassCurve.b₂, WeierstrassCurve.b₄,
          WeierstrassCurve.b₆, WeierstrassCurve.b₈] at hxc
        convert hxc using 1
        unfold dupNum dupDen
        ring
      have hpoly : dupNum x - (k : ℚ) * dupDen x = 0 := by
        exact sub_eq_zero.mpr ((div_eq_iff (dupDen_ne_zero x)).mp hfrac)
      exact half_obstruction_rat k hk x hpoly

theorem P_add_Q : P + Q = PQ := by
  norm_num [P, Q, PQ, Affine.Point.mk, Affine.Point.add_def, Affine.Point.add,
    Affine.addX, Affine.addY, Affine.negAddY, Affine.slope, Affine.negY,
    E, BSDOrdinary.curve389]

theorem P_not_double (R : E.Point) : R + R ≠ P := by
  exact not_double_of_x 0 (Or.inl rfl) 0 _ R

theorem Q_not_double (R : E.Point) : R + R ≠ Q := by
  exact not_double_of_x 1 (Or.inr (Or.inl rfl)) 0 _ R

theorem P_add_Q_not_double (R : E.Point) : R + R ≠ P + Q := by
  rw [P_add_Q]
  exact not_double_of_x (-2) (Or.inr (Or.inr rfl)) (-1) _ R

/-- Every integral relation has even coefficients: its three other parity
classes would exhibit one of the forbidden halves. -/
theorem relation_even (m n : ℤ) (h : m • P + n • Q = 0) : 2 ∣ m ∧ 2 ∣ n := by
  let T : E.Point := (m / 2) • P + (n / 2) • Q
  have hdecomp : T + T + (m % 2) • P + (n % 2) • Q = 0 := by
    calc
      T + T + (m % 2) • P + (n % 2) • Q =
          (2 * (m / 2) + m % 2) • P + (2 * (n / 2) + n % 2) • Q := by
            dsimp [T]
            simp only [add_zsmul, mul_zsmul, two_zsmul]
            abel
      _ = m • P + n • Q := by congr 2 <;> omega
      _ = 0 := h
  have hm : m % 2 = 0 ∨ m % 2 = 1 := by omega
  have hn : n % 2 = 0 ∨ n % 2 = 1 := by omega
  rcases hm with hm | hm <;> rcases hn with hn | hn
  · exact ⟨Int.dvd_of_emod_eq_zero hm, Int.dvd_of_emod_eq_zero hn⟩
  · exfalso
    apply Q_not_double (-T)
    apply sub_eq_zero.mp
    simp only [hm, hn, zero_zsmul, one_zsmul, add_zero] at hdecomp
    calc
      (-T + -T) - Q = -(T + T + Q) := by abel
      _ = 0 := by rw [hdecomp, neg_zero]
  · exfalso
    apply P_not_double (-T)
    apply sub_eq_zero.mp
    simp only [hm, hn, zero_zsmul, one_zsmul, add_zero] at hdecomp
    calc
      (-T + -T) - P = -(T + T + P) := by abel
      _ = 0 := by rw [hdecomp, neg_zero]
  · exfalso
    apply P_add_Q_not_double (-T)
    apply sub_eq_zero.mp
    simp only [hm, hn, one_zsmul] at hdecomp
    calc
      (-T + -T) - (P + Q) = -(T + T + P + Q) := by abel
      _ = 0 := by rw [hdecomp, neg_zero]

/-- Successive halving of a relation forces divisibility by every power
of two.  The absence of two-torsion makes each halved relation exact. -/
theorem relation_divisible (k : ℕ) (m n : ℤ) (h : m • P + n • Q = 0) :
    (2 ^ k : ℤ) ∣ m ∧ (2 ^ k : ℤ) ∣ n := by
  induction k generalizing m n with
  | zero => simp
  | succ k ih =>
      obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := relation_even m n h
      have hab : a • P + b • Q = 0 := by
        apply double_eq_zero
        calc
          (a • P + b • Q) + (a • P + b • Q) =
              (2 * a) • P + (2 * b) • Q := by
                simp only [mul_zsmul, two_zsmul]
                abel
          _ = 0 := by rw [← ha, ← hb]; exact h
      obtain ⟨⟨c, hc⟩, ⟨d, hd⟩⟩ := ih a b hab
      constructor
      · refine ⟨c, ?_⟩
        rw [ha, hc, pow_succ]
        ring
      · refine ⟨d, ?_⟩
        rw [hb, hd, pow_succ]
        ring

/-- An integer divisible by every power of two is zero. -/
theorem eq_zero_of_all_two_pow_dvd (m : ℤ) (h : ∀ k : ℕ, (2 ^ k : ℤ) ∣ m) : m = 0 := by
  by_contra hm
  have hmpos : 0 < m.natAbs := by
    have hmne : m.natAbs ≠ 0 := by simpa using hm
    omega
  have hpow : ∀ k : ℕ, k < 2 ^ k := by
    intro k
    induction k with
    | zero => norm_num
    | succ k ih =>
        rw [pow_succ]
        have hp : 0 < 2 ^ k := pow_pos (by norm_num) _
        omega
  obtain ⟨c, hc⟩ := h m.natAbs
  have hd : 2 ^ m.natAbs ∣ m.natAbs := by
    refine ⟨c.natAbs, ?_⟩
    simpa only [Int.natAbs_mul, Int.natAbs_pow, show (2 : ℤ).natAbs = 2 from rfl]
      using congrArg Int.natAbs hc
  exact (hpow m.natAbs).not_ge (Nat.le_of_dvd hmpos hd)

/-- There is no nontrivial integer relation between the two actual
rational points of the pilot curve. -/
theorem relation_zero (m n : ℤ) (h : m • P + n • Q = 0) : m = 0 ∧ n = 0 := by
  constructor
  · exact eq_zero_of_all_two_pow_dvd m (fun k => (relation_divisible k m n h).1)
  · exact eq_zero_of_all_two_pow_dvd n (fun k => (relation_divisible k m n h).2)

/-- The pilot contains an actual copy of the free abelian group on two
generators.  This does not presuppose finite generation of its full group. -/
theorem pointCombination_injective :
    Function.Injective (fun c : ℤ × ℤ => c.1 • P + c.2 • Q) := by
  intro a b hab
  have hr : (a.1 - b.1) • P + (a.2 - b.2) • Q = 0 := by
    calc
      (a.1 - b.1) • P + (a.2 - b.2) • Q =
          (a.1 • P + a.2 • Q) - (b.1 • P + b.2 • Q) := by
            simp only [sub_smul]
            abel
      _ = 0 := sub_eq_zero.mpr hab
  obtain ⟨h₁, h₂⟩ := relation_zero _ _ hr
  exact Prod.ext (sub_eq_zero.mp h₁) (sub_eq_zero.mp h₂)

/-- The concrete rank lower-bound input, stated as Mathlib linear
independence rather than a possibly misleading natural-number finrank. -/
theorem points_linearIndependent : LinearIndependent ℤ ![P, Q] := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have hr : c 0 • P + c 1 • Q = 0 := by
    simpa [Fin.sum_univ_two] using hc
  obtain ⟨h₀, h₁⟩ := relation_zero _ _ hr
  fin_cases i <;> assumption

/-- A rank lower bound in Mathlib's cardinal-valued module rank; no
finite-generation assumption is required. -/
theorem rank_at_least_two : 2 ≤ Module.rank ℤ E.Point := by
  simpa using points_linearIndependent.cardinal_le_rank

/-- The explicit positive-rank witness required by the arithmetic pilot. -/
theorem P_infinite_order : ¬ IsOfFinAddOrder P := by
  apply injective_zsmul_iff_not_isOfFinAddOrder.mp
  intro m n h
  have heq : (m, (0 : ℤ)) = (n, (0 : ℤ)) :=
    pointCombination_injective (by simpa only [zero_zsmul, add_zero] using h)
  exact congrArg Prod.fst heq

/-- Mathlib encodes an element of infinite additive order by order zero. -/
theorem P_addOrderOf : addOrderOf P = 0 := addOrderOf_eq_zero_iff.mpr P_infinite_order

end

end BSDRationalPoints
