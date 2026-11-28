import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.NumberTheory.Padics.Hensel
import Mathlib.Data.Fintype.Option
import Mathlib.Tactic

/-!
# Ordinary roots attached to the two pilot curves at five

The point counts below are counts of Mathlib's actual elliptic-curve point
types, including the point at infinity. Hensel's lemma then constructs the
ordinary unit root of each resulting Euler polynomial over `PadicInt 5`.
This does not identify an automorphic eigenfunction or construct a theta
distribution; it supplies the arithmetic ordinary-unit input to that work.
-/

namespace BSDOrdinary

open Polynomial

noncomputable section

set_option maxHeartbeats 1000000

instance primeFive : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- The integral model `y² + xy = x³ + 1`, over the chosen coefficient ring. -/
def curve433 (R : Type*) [CommRing R] : WeierstrassCurve.Affine R :=
  ⟨1, 0, 0, 0, 1⟩

/-- The integral model `y² + y = x³ + x² - 2x`. -/
def curve389 (R : Type*) [CommRing R] : WeierstrassCurve.Affine R :=
  ⟨0, 1, 1, -2, 0⟩

theorem discriminant433 : (curve433 ℤ).Δ = -433 := by
  norm_num [curve433, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]

theorem discriminant389 : (curve389 ℤ).Δ = 389 := by
  norm_num [curve389, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]

instance elliptic433 : (curve433 (ZMod 5)).IsElliptic := by
  constructor
  rw [isUnit_iff_ne_zero]
  decide +kernel

instance elliptic389 : (curve389 (ZMod 5)).IsElliptic := by
  constructor
  rw [isUnit_iff_ne_zero]
  decide +kernel

theorem pointCount433 : Nat.card (curve433 (ZMod 5)).Point = 10 := by
  let e : {xy : ZMod 5 × ZMod 5 // (curve433 (ZMod 5)).Equation xy.1 xy.2} ≃
      {xy : ZMod 5 × ZMod 5 // xy.2 ^ 2 + xy.1 * xy.2 = xy.1 ^ 3 + 1} :=
    Equiv.subtypeEquivProp (by funext xy; simp [WeierstrassCurve.Affine.equation_iff, curve433])
  rw [Nat.card_congr ((curve433 (ZMod 5)).pointEquiv.trans e.optionCongr)]
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem pointCount389 : Nat.card (curve389 (ZMod 5)).Point = 9 := by
  let e : {xy : ZMod 5 × ZMod 5 // (curve389 (ZMod 5)).Equation xy.1 xy.2} ≃
      {xy : ZMod 5 × ZMod 5 // xy.2 ^ 2 + xy.2 = xy.1 ^ 3 + xy.1 ^ 2 - 2 * xy.1} :=
    Equiv.subtypeEquivProp (by
      funext xy
      simp only [WeierstrassCurve.Affine.equation_iff, curve389, zero_mul,
        one_mul, add_zero, neg_mul, sub_eq_add_neg])
  rw [Nat.card_congr ((curve389 (ZMod 5)).pointEquiv.trans e.optionCongr)]
  rw [Nat.card_eq_fintype_card]
  decide +kernel

/-- The trace defined from the actual group of points over `ZMod 5`. -/
def traceFive (W : WeierstrassCurve.Affine (ZMod 5)) : ℤ :=
  6 - (Nat.card W.Point : ℤ)

theorem trace433 : traceFive (curve433 (ZMod 5)) = -4 := by
  simp [traceFive, pointCount433]

theorem trace389 : traceFive (curve389 (ZMod 5)) = -3 := by
  simp [traceFive, pointCount389]

/-- The Euler polynomial with its trace supplied by a point count. -/
def eulerPolynomial (a : ℤ) : Polynomial ℤ_[5] :=
  X ^ 2 - C (a : ℤ_[5]) * X + C 5

theorem euler_eval (a : ℤ) (z : ℤ_[5]) :
    (eulerPolynomial a).eval z = z ^ 2 - (a : ℤ_[5]) * z + 5 := by
  simp [eulerPolynomial]

theorem euler_derivative_eval (a : ℤ) (z : ℤ_[5]) :
    (eulerPolynomial a).derivative.eval z = 2 * z - (a : ℤ_[5]) := by
  simp [eulerPolynomial]
  norm_num

theorem unit_of_close_to_unit (z a : ℤ_[5]) (ha : ‖a‖ = 1)
    (h : ‖z - a‖ < 1) : IsUnit z := by
  apply PadicInt.isUnit_iff.mpr
  have h' : ‖-a + z‖ < ‖-a‖ := by simpa [ha, sub_eq_add_neg, add_comm] using h
  have hn := PadicInt.norm_eq_of_norm_add_lt_left h'
  simpa [ha] using hn.symm

/-- Hensel constructs a root near the ordinary trace; no root is assumed. -/
theorem exists_ordinary_root (a : ℤ) (ha : ‖(a : ℤ_[5])‖ = 1) :
    ∃ z : ℤ_[5], (eulerPolynomial a).eval z = 0 ∧ IsUnit z ∧
      (5 : ℤ_[5]) ∣ z - (a : ℤ_[5]) ∧
      ∀ z' : ℤ_[5], (eulerPolynomial a).eval z' = 0 →
        (5 : ℤ_[5]) ∣ z' - (a : ℤ_[5]) → z' = z := by
  have hv : (eulerPolynomial a).eval (a : ℤ_[5]) = 5 := by
    rw [euler_eval]
    ring
  have hd : (eulerPolynomial a).derivative.eval (a : ℤ_[5]) = (a : ℤ_[5]) := by
    rw [euler_derivative_eval]
    ring
  have hnorm : ‖(eulerPolynomial a).aeval (a : ℤ_[5])‖ <
      ‖(eulerPolynomial a).derivative.aeval (a : ℤ_[5])‖ ^ 2 := by
    simp only [coe_aeval_eq_eval, hv, hd, ha, one_pow]
    have hn5 : ‖(5 : ℤ_[5])‖ = (5 : ℝ)⁻¹ := PadicInt.norm_p
    rw [hn5]
    norm_num
  obtain ⟨z, hz, hclose, _, huniq⟩ :=
    hensels_lemma (p := 5) (F := eulerPolynomial a) (a := (a : ℤ_[5])) hnorm
  simp only [coe_aeval_eq_eval, hd, ha] at hz hclose huniq
  refine ⟨z, hz, unit_of_close_to_unit z (a : ℤ_[5]) ha hclose,
    (PadicInt.norm_lt_one_iff_dvd _).mp hclose, ?_⟩
  intro z' hz' hdiv
  exact huniq z' hz' ((PadicInt.norm_lt_one_iff_dvd _).mpr hdiv)

/-- Every unit root lies in the residue class used in the Hensel construction. -/
theorem unit_root_congruent_trace (a : ℤ) (z : ℤ_[5])
    (hz : (eulerPolynomial a).eval z = 0) (hu : IsUnit z) :
    (5 : ℤ_[5]) ∣ z - (a : ℤ_[5]) := by
  apply hu.dvd_mul_left.mp
  have hf : z * (z - (a : ℤ_[5])) = -5 := by
    rw [euler_eval] at hz
    linear_combination hz
  rw [hf]
  exact dvd_neg.mpr (dvd_refl _)

/-- The ordinary root is the unique unit root of the point-count Euler polynomial. -/
theorem existsUnique_ordinary_root (a : ℤ) (ha : ‖(a : ℤ_[5])‖ = 1) :
    ∃! z : ℤ_[5], (eulerPolynomial a).eval z = 0 ∧ IsUnit z := by
  obtain ⟨z, hz, hu, _, huniq⟩ := exists_ordinary_root a ha
  refine ⟨z, ⟨hz, hu⟩, ?_⟩
  intro z' hz'
  exact huniq z' hz'.1 (unit_root_congruent_trace a z' hz'.1 hz'.2)

theorem trace433_norm : ‖(traceFive (curve433 (ZMod 5)) : ℤ_[5])‖ = 1 := by
  rw [trace433]
  have h : ‖((4 : ℕ) : ℤ_[5])‖ = 1 :=
    PadicInt.norm_natCast_eq_one_iff.mpr (by decide)
  simpa using h

theorem trace389_norm : ‖(traceFive (curve389 (ZMod 5)) : ℤ_[5])‖ = 1 := by
  rw [trace389]
  have h : ‖((3 : ℕ) : ℤ_[5])‖ = 1 :=
    PadicInt.norm_natCast_eq_one_iff.mpr (by decide)
  simpa using h

/-- The ordinary root constructed from the E433 point count. -/
def ordinary433 : ℤ_[5] :=
  Classical.choose (existsUnique_ordinary_root _ trace433_norm)

/-- The ordinary root constructed from the E389 point count. -/
def ordinary389 : ℤ_[5] :=
  Classical.choose (existsUnique_ordinary_root _ trace389_norm)

theorem ordinary433_spec :
    (eulerPolynomial (traceFive (curve433 (ZMod 5)))).eval ordinary433 = 0 ∧
      IsUnit ordinary433 :=
  (Classical.choose_spec (existsUnique_ordinary_root _ trace433_norm)).1

theorem ordinary389_spec :
    (eulerPolynomial (traceFive (curve389 (ZMod 5)))).eval ordinary389 = 0 ∧
      IsUnit ordinary389 :=
  (Classical.choose_spec (existsUnique_ordinary_root _ trace389_norm)).1

theorem ordinary433_equation : ordinary433 ^ 2 + 4 * ordinary433 + 5 = 0 := by
  have h := ordinary433_spec.1
  simpa [euler_eval, trace433] using h

theorem ordinary389_equation : ordinary389 ^ 2 + 3 * ordinary389 + 5 = 0 := by
  have h := ordinary389_spec.1
  simpa [euler_eval, trace389] using h

theorem ordinary433_unique (z : ℤ_[5])
    (hz : (eulerPolynomial (traceFive (curve433 (ZMod 5)))).eval z = 0)
    (hu : IsUnit z) : z = ordinary433 :=
  (Classical.choose_spec (existsUnique_ordinary_root _ trace433_norm)).2 z ⟨hz, hu⟩

theorem ordinary389_unique (z : ℤ_[5])
    (hz : (eulerPolynomial (traceFive (curve389 (ZMod 5)))).eval z = 0)
    (hu : IsUnit z) : z = ordinary389 :=
  (Classical.choose_spec (existsUnique_ordinary_root _ trace389_norm)).2 z ⟨hz, hu⟩

/-- A unit-valued ordinary parameter, suitable for inverse-power normalization. -/
def ordinary433Unit : ℤ_[5]ˣ := ordinary433_spec.2.unit

def ordinary389Unit : ℤ_[5]ˣ := ordinary389_spec.2.unit

theorem ordinary433Unit_val : (ordinary433Unit : ℤ_[5]) = ordinary433 :=
  ordinary433_spec.2.unit_spec

theorem ordinary389Unit_val : (ordinary389Unit : ℤ_[5]) = ordinary389 :=
  ordinary389_spec.2.unit_spec

end

end BSDOrdinary
