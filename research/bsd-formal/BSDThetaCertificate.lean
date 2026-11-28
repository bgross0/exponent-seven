import BSDRankTwo
import BSDFiniteWitness
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.Tactic.Ring

/-!
# A kernel-checked finite theta certificate for the E433 computation

This module checks the exact 140-entry fiber sums and the ordinary
regularization algebra. The last theorem is a conditional statement about
an arbitrary power series: its identification with the arithmetic theta
series, exact constant-term vanishing, and functional equation remain
explicit hypotheses. No CM identification or BSD theorem is asserted here.

The 140 integers below are the `CM_values` in the conductor-25 entry of
`research/bsd-localization/second_theta/certificate.json` at commit
f3742fbf6ae1915cc35def76d2bc3937bebfda1e. Certificate SHA-256:
5e533e6f0ea31a2c59293448a5f2f8077de512b9e3c50e7420f6eafd2a699898.
-/

namespace BSDThetaCertificate

/-- The canonical finite-witness module supplies the values in cycle order. -/
abbrev cm433Values : List ℤ := BSDFiniteWitness.cm433Values

/-- Projection of a cyclic list to its quotient of order five. -/
def quotientFiveSums (values : List ℤ) : List ℤ :=
  (List.range 5).map fun r =>
    ((values.zipIdx.filter fun vi => vi.2 % 5 == r).map Prod.fst).sum

/-- All 140 supplied entries are included, in the five correct index fibers. -/
theorem cm433_fiber_sums :
    cm433Values.length = 140 ∧ quotientFiveSums cm433Values = [0, 1, -2, 1, 0] := by
  decide +kernel

section RingAlgebra

variable {R : Type*} [CommRing R]

/-- Evaluate integer group-ring coefficients at a chosen group generator. -/
def groupElement (values : List ℤ) (gamma : R) : R :=
  (values.zipIdx.map fun vi => (vi.1 : R) * gamma ^ vi.2).sum

/-- The finite element obtained by projecting the supplied 140-entry list. -/
def finite433 (gamma : R) : R :=
  groupElement (quotientFiveSums cm433Values) gamma

/-- The full cyclic fiber sum is the claimed integral group-ring element. -/
theorem finite433_eq (gamma : R) :
    finite433 gamma = gamma - 2 * gamma ^ 2 + gamma ^ 3 := by
  simp [finite433, cm433_fiber_sums.2, groupElement, List.zipIdx]
  ring

/-- Exact factorization before making any residue-field reduction. -/
theorem finite433_factor (gamma : R) :
    finite433 gamma = gamma * (gamma - 1) ^ 2 := by
  rw [finite433_eq]
  ring

/-- The exact shifted polynomial has a unit quadratic coefficient. -/
theorem finite433_shift (T : R) :
    finite433 (1 + T) = T ^ 2 + T ^ 3 := by
  rw [finite433_eq]
  ring

/-- The order-five trace/norm element occurring in ordinary regularization. -/
def normFive (gamma : R) : R :=
  1 + gamma + gamma ^ 2 + gamma ^ 3 + gamma ^ 4

/-- Integral formula retaining the lower coefficients divisible by five. -/
theorem normFive_shift (T : R) :
    normFive (1 + T) = 5 + 10 * T + 10 * T ^ 2 + 5 * T ^ 3 + T ^ 4 := by
  unfold normFive
  ring

/-- The quotient relation modulo which the finite theta element is defined. -/
theorem fifth_relation (T : R) :
    (1 + T) ^ 5 - 1 = 5 * T + 10 * T ^ 2 + 10 * T ^ 3 + 5 * T ^ 4 + T ^ 5 := by
  ring

/-- Regularized finite element, with its unit scalar and arbitrary lower-level
trace scalar kept explicit. -/
noncomputable def regularized433 (u c : R) : PowerSeries R :=
  PowerSeries.C u * finite433 (1 + PowerSeries.X) -
    PowerSeries.C c * normFive (1 + PowerSeries.X)

/-- The correction contributes exactly `10*c` in degree two. -/
theorem regularized433_coeff_two (u c : R) :
    PowerSeries.coeff 2 (regularized433 u c) = u - 10 * c := by
  rw [regularized433, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul,
    finite433_shift, normFive_shift]
  simp [PowerSeries.coeff_X_pow, ← map_ofNat PowerSeries.C]
  ring

/-- The quadratic correction is zero modulo five in every coefficient ring. -/
theorem regularized433_coeff_two_congr (u c : R) :
    (5 : R) ∣ PowerSeries.coeff 2 (regularized433 u c) - u := by
  rw [regularized433_coeff_two]
  exact ⟨-2 * c, by ring⟩

/-- A surviving raw quadratic residue remains nonzero after regularization. -/
theorem regularized433_quadratic_nondivisible (u c : R)
    (hu : ¬ (5 : R) ∣ u) :
    ¬ (5 : R) ∣ PowerSeries.coeff 2 (regularized433 u c) := by
  intro h
  apply hu
  have hd := dvd_sub h (regularized433_coeff_two_congr u c)
  simpa using hd

/-- If five is not invertible, every invertible normalization has the needed
nonzero residue. This applies, for example, in the 5-adic integers. -/
theorem regularized433_quadratic_nondivisible_of_unit (u c : R)
    (h5 : ¬ IsUnit (5 : R)) (hu : IsUnit u) :
    ¬ (5 : R) ∣ PowerSeries.coeff 2 (regularized433 u c) := by
  apply regularized433_quadratic_nondivisible
  exact fun hd => h5 (isUnit_of_dvd_unit hd hu)

/-- The complete algebraic certificate: finite approximation plus exact
inversion symmetry and exact constant-term vanishing imply order two.

The approximation multipliers lie in the SAME coefficient ring; allowing
arbitrary denominators would invalidate the residue argument. The hypotheses
`hzero`, `hsym`, and `happrox` are arithmetic obligations for the actual theta
series, not conclusions of the finite CM-value calculation. -/
theorem order_two_of_regularized433
    (F U H J : PowerSeries R) (u c : R)
    (h_two : ∀ a : R, a + a = 0 → a = 0)
    (hzero : F.constantCoeff = 0) (hU : U.constantCoeff = 1)
    (hsym : F = U * F.subst (BSDRankTwo.inversionSeries (R := R)))
    (hu : ¬ (5 : R) ∣ u)
    (happrox : F - regularized433 u c =
      (BSDRankTwo.omegaPoly (R := R) 5 1 : PowerSeries R) * H +
        PowerSeries.C (5 : R) * J) :
    F.order = 2 := by
  apply BSDRankTwo.exact_order_two_of_certificate
    (p := 5) (n := 1) (m := 1) (by decide) (by decide) (by omega)
    F (regularized433 u c) H J
  · simpa using happrox
  · exact BSDRankTwo.X_sq_dvd_of_inversion_symmetry F U h_two hzero hU hsym
  · simpa using regularized433_quadratic_nondivisible u c hu

/-- Version with an invertible ordinary normalization and noninvertible five. -/
theorem order_two_of_regularized433_unit
    (F U H J : PowerSeries R) (u c : R)
    (h_two : ∀ a : R, a + a = 0 → a = 0)
    (hzero : F.constantCoeff = 0) (hU : U.constantCoeff = 1)
    (hsym : F = U * F.subst (BSDRankTwo.inversionSeries (R := R)))
    (h5 : ¬ IsUnit (5 : R)) (hu : IsUnit u)
    (happrox : F - regularized433 u c =
      (BSDRankTwo.omegaPoly (R := R) 5 1 : PowerSeries R) * H +
        PowerSeries.C (5 : R) * J) :
    F.order = 2 := by
  exact order_two_of_regularized433 F U H J u c h_two hzero hU hsym
    (fun hd => h5 (isUnit_of_dvd_unit hd hu)) happrox


/-- In a local ring, a unit remains a unit after an error divisible by a
nonunit. This is the precise lifting step needed for a unit leading term. -/
theorem unit_of_congr_nonunit [IsLocalRing R]
    (p u x : R) (hp : ¬ IsUnit p) (hu : IsUnit u) (hcongr : p ∣ x - u) :
    IsUnit x := by
  have hsum : IsUnit (x + (u - x)) := by simpa using hu
  apply (IsLocalRing.isUnit_or_isUnit_of_isUnit_add hsum).resolve_right
  intro hd
  apply hp
  apply isUnit_of_dvd_unit _ hd
  simpa using dvd_neg.mpr hcongr

/-- The finite-level relation transmits the unit residue to the infinite
series. All errors remain integral in the stated local coefficient ring. -/
theorem quadratic_unit_of_regularized433 [IsLocalRing R]
    (F H J : PowerSeries R) (u c : R)
    (h5 : ¬ IsUnit (5 : R)) (hu : IsUnit u)
    (happrox : F - regularized433 u c =
      (BSDRankTwo.omegaPoly (R := R) 5 1 : PowerSeries R) * H +
        PowerSeries.C (5 : R) * J) :
    IsUnit (PowerSeries.coeff 2 F) := by
  apply unit_of_congr_nonunit 5 u _ h5 hu
  have hlevel : (5 : R) ∣ PowerSeries.coeff 2 F -
      PowerSeries.coeff 2 (regularized433 u c) := by
    have h := BSDRankTwo.finite_level_coeff_dvd (p := 5) (n := 1) (m := 1)
      (s := 0) (k := 2) (by decide) (by omega) (by decide)
      F (regularized433 u c) H J (by simpa using happrox)
    simpa using h
  simpa using dvd_add hlevel (regularized433_coeff_two_congr u c)

/-- The full `T^2`-times-unit-leading-series conclusion, in the same local
integral coefficient ring as the finite approximation. This is stronger than
order two alone: the quotient has an invertible constant coefficient. -/
theorem factorization_of_regularized433 [IsLocalRing R]
    (F U H J : PowerSeries R) (u c : R)
    (h_two : ∀ a : R, a + a = 0 → a = 0)
    (hzero : F.constantCoeff = 0) (hU : U.constantCoeff = 1)
    (hsym : F = U * F.subst (BSDRankTwo.inversionSeries (R := R)))
    (h5 : ¬ IsUnit (5 : R)) (hu : IsUnit u)
    (happrox : F - regularized433 u c =
      (BSDRankTwo.omegaPoly (R := R) 5 1 : PowerSeries R) * H +
        PowerSeries.C (5 : R) * J) :
    ∃ V : PowerSeries R, F = PowerSeries.X ^ 2 * V ∧ IsUnit V.constantCoeff := by
  obtain ⟨V, hV⟩ := BSDRankTwo.X_sq_dvd_of_inversion_symmetry
    F U h_two hzero hU hsym
  refine ⟨V, hV, ?_⟩
  have hunit := quadratic_unit_of_regularized433 F H J u c h5 hu happrox
  rw [hV] at hunit
  have hcoeff : PowerSeries.coeff 2 (PowerSeries.X ^ 2 * V) = V.constantCoeff := by
    simpa using PowerSeries.coeff_X_pow_mul V 2 0
  rwa [hcoeff] at hunit


/-- At the raw origin used by the saved cycle, inversion has multiplier
`(1+T)^4`. Requiring strict invariance would be incompatible with this origin.
This identity is proved for the actual power-series substitution. -/
theorem finite433_inversion_symmetry :
    finite433 (1 + PowerSeries.X : PowerSeries R) =
      (1 + PowerSeries.X) ^ 4 *
        (finite433 (1 + PowerSeries.X : PowerSeries R)).subst
          (BSDRankTwo.inversionSeries (R := R)) := by
  let B : PowerSeries R := BSDRankTwo.inversionSeries
  have hB0 : B.constantCoeff = 0 := BSDRankTwo.inversionSeries_constantCoeff
  have hsubst : PowerSeries.HasSubst B :=
    PowerSeries.HasSubst.of_constantCoeff_zero hB0
  have hprod : (1 + PowerSeries.X) * (1 + B) = (1 : PowerSeries R) := by
    simp [B, BSDRankTwo.inversionSeries]
  have hB : (1 + PowerSeries.X) * B = -(PowerSeries.X : PowerSeries R) := by
    calc
      (1 + PowerSeries.X) * B =
          (1 + PowerSeries.X) * (1 + B) - (1 + PowerSeries.X) := by ring
      _ = -(PowerSeries.X : PowerSeries R) := by rw [hprod]; ring
  change finite433 (1 + PowerSeries.X : PowerSeries R) =
    (1 + PowerSeries.X) ^ 4 * (finite433 (1 + PowerSeries.X : PowerSeries R)).subst B
  simp only [finite433_shift, PowerSeries.subst_add hsubst,
    PowerSeries.subst_pow hsubst, PowerSeries.subst_X hsubst]
  symm
  calc
    (1 + PowerSeries.X) ^ 4 * (B ^ 2 + B ^ 3) =
        (1 + PowerSeries.X) * ((1 + PowerSeries.X) * B) ^ 2 *
          ((1 + PowerSeries.X) * (1 + B)) := by ring
    _ = (1 + PowerSeries.X) * (-(PowerSeries.X : PowerSeries R)) ^ 2 * 1 := by
      rw [hB, hprod]
    _ = PowerSeries.X ^ 2 + PowerSeries.X ^ 3 := by ring

end RingAlgebra

/-- The raw quadratic coefficient is exactly one in the residue field. -/
theorem finite433_mod_five :
    finite433 (1 + Polynomial.X : Polynomial (ZMod 5)) =
      Polynomial.X ^ 2 + Polynomial.X ^ 3 := finite433_shift _

/-- The lower-level norm term first appears in degree four modulo five. -/
theorem normFive_mod_five :
    normFive (1 + Polynomial.X : Polynomial (ZMod 5)) = Polynomial.X ^ 4 := by
  rw [normFive_shift]
  have h5 : (5 : ZMod 5) = 0 := by decide
  have h10 : (10 : ZMod 5) = 0 := by decide
  simp only [← Polynomial.C_ofNat, h5, h10, map_zero, zero_mul, zero_add, add_zero]

/-- The group relation first appears in degree five modulo five. -/
theorem quotient_relation_mod_five :
    (1 + Polynomial.X : Polynomial (ZMod 5)) ^ 5 - 1 = Polynomial.X ^ 5 := by
  rw [fifth_relation]
  have h5 : (5 : ZMod 5) = 0 := by decide
  have h10 : (10 : ZMod 5) = 0 := by decide
  simp only [← Polynomial.C_ofNat, h5, h10, map_zero, zero_mul, zero_add, add_zero]


section FiveAdic

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- Concrete coefficient-ring specialization. All ring-theoretic premises
are discharged for the actual 5-adic integers. The remaining assumptions are
exact constant-term vanishing, the arithmetic inversion symmetry with its
origin-dependent multiplier of constant coefficient one, the ordinary unit,
and the integral finite-level approximation. Strict symmetry is not imposed:
the displayed raw origin has multiplier `(1+T)^4`. -/
theorem five_adic_certificate
    (F U H J : PowerSeries ℤ_[5]) (u c : ℤ_[5])
    (hzero : F.constantCoeff = 0) (hU : U.constantCoeff = 1)
    (hsym : F = U * F.subst (BSDRankTwo.inversionSeries (R := ℤ_[5])))
    (hu : IsUnit u)
    (happrox : F - regularized433 u c =
      (BSDRankTwo.omegaPoly (R := ℤ_[5]) 5 1 : PowerSeries ℤ_[5]) * H +
        PowerSeries.C (5 : ℤ_[5]) * J) :
    F.order = 2 ∧
      ∃ V : PowerSeries ℤ_[5], F = PowerSeries.X ^ 2 * V ∧ IsUnit V.constantCoeff := by
  have htwo : ∀ a : ℤ_[5], a + a = 0 → a = 0 :=
    fun _ h => add_self_eq_zero.mp h
  have h5 : ¬ IsUnit (5 : ℤ_[5]) := PadicInt.irreducible_p.not_isUnit
  exact ⟨order_two_of_regularized433_unit F U H J u c htwo hzero hU
      hsym h5 hu happrox,
    factorization_of_regularized433 F U H J u c htwo hzero hU
      hsym h5 hu happrox⟩


/-- A concrete witness that all inputs to the 5-adic certificate are jointly
satisfiable in the raw cycle convention. This is an algebraic example, not an
identification of this finite polynomial with the arithmetic theta function. -/
theorem raw_five_adic_inputs :
    let F := finite433 (1 + PowerSeries.X : PowerSeries ℤ_[5])
    let U := (1 + PowerSeries.X : PowerSeries ℤ_[5]) ^ 4
    F.constantCoeff = 0 ∧ U.constantCoeff = 1 ∧
    F = U * F.subst (BSDRankTwo.inversionSeries (R := ℤ_[5])) ∧
    IsUnit (1 : ℤ_[5]) ∧
    F - regularized433 (1 : ℤ_[5]) 0 =
      (BSDRankTwo.omegaPoly (R := ℤ_[5]) 5 1 : PowerSeries ℤ_[5]) * 0 +
        PowerSeries.C (5 : ℤ_[5]) * 0 := by
  dsimp only
  refine ⟨?_, ?_, finite433_inversion_symmetry, isUnit_one, ?_⟩
  · rw [finite433_shift]
    simp
  · simp
  · simp [regularized433]

end FiveAdic

end BSDThetaCertificate
