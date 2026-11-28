import BSDOrdinary
import BSDThetaLimit

/-!
# The original conductor-389 finite theta data

This module keeps the original E389 pilot separate from the E433 certificate.
It checks the supplied 140 integer values and their five quotient sums, uses
the actual ordinary root of `BSDOrdinary.curve389`, and proves that only the
quadratic first-level congruence is needed once an arithmetic tower's
compatibility, symmetry and zero augmentation have been supplied.

The list is `CM_function_weights_in_cycle_order` from
`research/bsd-theta/data/cm-jet-p5.json` at commit
cf84450fb80b673c9b32c5abb71d7e26d4e87957. Source SHA256:
0fb46c8b69b82047e613cf2abf8e6235b692e10263fa917fc63f273a6030f2eb.
Its arithmetic CM/eigenfunction interpretation is not proved in this module.
In particular, the final implication does not construct the arithmetic tower
and does not assert a Selmer, rank-upper-bound, or Sha theorem.
-/

namespace BSDE389Theta

noncomputable section

def suppliedValues : List ℤ :=
  [0, 0, 0, 1, -1, 1, 0, 0, 1, -1, 0, 2, -2, 2, -2, 2, -2, 2, -2, 0,
  1, -2, 2, -1, 0, 1, -1, 1, -1, 0, 2, -2, 2, -2, 2, -2, 2, -2, 2, 0,
  -1, 1, -1, 1, 0, -1, 2, -2, 1, 0, -2, 2, -2, 2, -2, 2, -2, 2, 0, -1,
  1, 0, 0, 1, -1, 1, 0, 0, 0, 0, 0, -1, 2, -1, 0, 0, 0, -1, 0, 0,
  1, -1, 1, 0, -1, 0, 1, -1, 1, 0, -1, 2, -1, 0, 0, 0, -1, 0, 0, 1,
  -1, 0, -1, 1, -2, 1, -1, 0, -1, 1, 0, 0, -1, 0, 0, 0, -1, 2, -1, 0,
  1, -1, 1, 0, -1, 0, 1, -1, 1, 0, 0, -1, 0, 0, 0, -1, 2, -1, 0, 0]

/-- All supplied entries are included, with their original cyclic order. -/
theorem supplied_fiber_sums : suppliedValues.length = 140 ∧
    BSDThetaCertificate.quotientFiveSums suppliedValues = [5, -1, -1, 5, -8] := by
  decide +kernel

section RingAlgebra

variable {R : Type*} [CommRing R]

def finite389 (gamma : R) : R :=
  BSDThetaCertificate.groupElement
    (BSDThetaCertificate.quotientFiveSums suppliedValues) gamma

theorem finite389_eq (gamma : R) :
    finite389 gamma = 5 - gamma - gamma ^ 2 + 5 * gamma ^ 3 - 8 * gamma ^ 4 := by
  simp [finite389, supplied_fiber_sums.2, BSDThetaCertificate.groupElement, List.zipIdx]
  ring

/-- The linear coefficient is -20 exactly; divisibility by five is not
mistaken for exact linear vanishing. -/
theorem finite389_shift (T : R) :
    finite389 (1 + T) = -20 * T - 34 * T ^ 2 - 27 * T ^ 3 - 8 * T ^ 4 := by
  rw [finite389_eq]
  ring

def regularized389 (u c : R) : PowerSeries R :=
  PowerSeries.C u * finite389 (1 + PowerSeries.X) -
    PowerSeries.C c * BSDThetaCertificate.normFive (1 + PowerSeries.X)

theorem regularized389_coeff_two (u c : R) :
    PowerSeries.coeff 2 (regularized389 u c) = -34 * u - 10 * c := by
  rw [regularized389, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul,
    finite389_shift, BSDThetaCertificate.normFive_shift]
  simp [PowerSeries.coeff_X_pow, ← map_ofNat PowerSeries.C]
  ring

/-- The raw coefficient -34 is congruent to one modulo five, and the
ordinary trace correction contributes zero to that residue. -/
theorem regularized389_coeff_two_congr (u c : R) :
    (5 : R) ∣ PowerSeries.coeff 2 (regularized389 u c) - u := by
  rw [regularized389_coeff_two]
  exact ⟨-7 * u - 2 * c, by ring⟩

end RingAlgebra

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- The normalization comes from the original curve's actual point-count
Euler factor, not the different ordinary root of the E433 pilot. -/
def ordinaryScaleUnit : ℤ_[5]ˣ := (BSDOrdinary.ordinary389Unit ^ 2)⁻¹

def ordinaryScale : ℤ_[5] := ordinaryScaleUnit

theorem ordinaryScale_isUnit : IsUnit ordinaryScale := Units.isUnit ordinaryScaleUnit

theorem ordinaryScale_inverse_square :
    ordinaryScale * BSDOrdinary.ordinary389 ^ 2 = 1 := by
  rw [← BSDOrdinary.ordinary389Unit_val]
  change (↑((BSDOrdinary.ordinary389Unit ^ 2)⁻¹ *
    BSDOrdinary.ordinary389Unit ^ 2) : ℤ_[5]) = 1
  simp

/-- A single first-level quadratic congruence suffices. All-level finite
symmetry and exact zero augmentation supply the two exact lower zeros;
compatibility supplies the precision of the constructed coefficient limit. -/
theorem finite_tower_certificate_of_quadratic_congruence
    (G : ℕ → Polynomial ℤ_[5]) (hG : BSDThetaLimit.Compatible G)
    (hsym : BSDThetaLimit.FiniteSymmetric G) (hzero : (G 0).coeff 0 = 0)
    (u : ℤ_[5]) (hu : IsUnit u)
    (hquadratic : (5 : ℤ_[5]) ∣ (G 1).coeff 2 - u) :
    (BSDThetaLimit.thetaLimit G hG).order = 2 ∧
      ∃ V : PowerSeries ℤ_[5],
        BSDThetaLimit.thetaLimit G hG = PowerSeries.X ^ 2 * V ∧
          IsUnit V.constantCoeff := by
  let F := BSDThetaLimit.thetaLimit G hG
  have hF0 : F.constantCoeff = 0 :=
    (BSDThetaLimit.thetaLimit_constantCoeff G hG).trans hzero
  have hF1 : PowerSeries.coeff 1 F = 0 :=
    BSDThetaLimit.thetaLimit_coeff_one_zero G hG hsym hzero
  have hprec : (5 : ℤ_[5]) ∣ PowerSeries.coeff 2 F - (G 1).coeff 2 := by
    simpa [F] using BSDThetaLimit.thetaLimit_coeff_precision G hG
      (n := 1) (a := 1) (s := 0) (k := 2) (by decide) (by decide)
  have hcongr : (5 : ℤ_[5]) ∣ PowerSeries.coeff 2 F - u := by
    simpa using dvd_add hprec hquadratic
  have hunit : IsUnit (PowerSeries.coeff 2 F) :=
    BSDThetaCertificate.unit_of_congr_nonunit 5 u _
      PadicInt.irreducible_p.not_isUnit hu hcongr
  have hlow : ∀ k : ℕ, k < 2 → PowerSeries.coeff k F = 0 := by
    intro k hk
    rcases (show k = 0 ∨ k = 1 by omega) with rfl | rfl
    · simpa using hF0
    · exact hF1
  constructor
  · exact PowerSeries.order_eq_nat.mpr ⟨hunit.ne_zero, hlow⟩
  · obtain ⟨V, hV⟩ := PowerSeries.X_pow_dvd_iff.mpr hlow
    refine ⟨V, hV, ?_⟩
    rw [hV] at hunit
    have hc : PowerSeries.coeff 2 (PowerSeries.X ^ 2 * V) = V.constantCoeff := by
      simpa using PowerSeries.coeff_X_pow_mul V 2 0
    rwa [hc] at hunit

/-- The original E389 finite data feed the generic tower construction using
its own ordinary normalization. The arithmetic CM tower and its stated
identification are still hypotheses, explicitly visible in this theorem. -/
theorem e389_certificate_of_finite_tower
    (G : ℕ → Polynomial ℤ_[5])
    (hstep : ∀ n, BSDRankTwo.omegaPoly (R := ℤ_[5]) 5 n ∣ G (n + 1) - G n)
    (hsym : BSDThetaLimit.FiniteSymmetric G) (hzero : (G 0).coeff 0 = 0)
    (c : ℤ_[5])
    (hfirst : (5 : ℤ_[5]) ∣ (G 1).coeff 2 -
      PowerSeries.coeff 2 (regularized389 ordinaryScale c)) :
    let F := BSDThetaLimit.thetaLimit G (BSDThetaLimit.compatible_of_successive G hstep)
    F.order = 2 ∧ ∃ V : PowerSeries ℤ_[5],
      F = PowerSeries.X ^ 2 * V ∧ IsUnit V.constantCoeff := by
  apply finite_tower_certificate_of_quadratic_congruence G
    (BSDThetaLimit.compatible_of_successive G hstep) hsym hzero
    ordinaryScale ordinaryScale_isUnit
  simpa using dvd_add hfirst (regularized389_coeff_two_congr ordinaryScale c)

end

end BSDE389Theta
