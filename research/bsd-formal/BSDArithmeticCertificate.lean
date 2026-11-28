import BSDOrdinary
import BSDThetaLimit

/-!
# The E433 certificate with its actual ordinary parameter

The ordinary root is constructed by Hensel from the point count of the
actual Mathlib curve. The infinite series is constructed from a compatible
finite family. Only the arithmetic finite-family identification, distribution,
symmetry, and augmentation remain hypotheses; neither an infinite series nor
its coefficient precision or vanishing is supplied by the caller.
-/

namespace BSDArithmeticCertificate

noncomputable section

/-- The conductor-25 normalization `alpha^(-2)` as an actual 5-adic unit. -/
def conductor25ScaleUnit : ℤ_[5]ˣ := (BSDOrdinary.ordinary433Unit ^ 2)⁻¹

def conductor25Scale : ℤ_[5] := conductor25ScaleUnit

theorem conductor25Scale_isUnit : IsUnit conductor25Scale :=
  Units.isUnit conductor25ScaleUnit

theorem conductor25Scale_inverse_square :
    conductor25Scale * BSDOrdinary.ordinary433 ^ 2 = 1 := by
  rw [← BSDOrdinary.ordinary433Unit_val]
  change (↑((BSDOrdinary.ordinary433Unit ^ 2)⁻¹ *
    BSDOrdinary.ordinary433Unit ^ 2) : ℤ_[5]) = 1
  simp

/-- Assemble the actual ordinary parameter with the constructed limit.
The exact first-level version entails a zero correction scalar; the more
flexible finite-congruence version below is the intended arithmetic interface. -/
theorem e433_certificate_of_exact_finite_tower
    (G : ℕ → Polynomial ℤ_[5])
    (hstep : ∀ n, BSDRankTwo.omegaPoly (R := ℤ_[5]) 5 n ∣ G (n + 1) - G n)
    (hsym : BSDThetaLimit.FiniteSymmetric G)
    (hzero : (G 0).coeff 0 = 0)
    (c : ℤ_[5])
    (hfirst : (G 1 : PowerSeries ℤ_[5]) =
      BSDThetaCertificate.regularized433 conductor25Scale c) :
    let F := BSDThetaLimit.thetaLimit G (BSDThetaLimit.compatible_of_successive G hstep)
    F.order = 2 ∧ ∃ V : PowerSeries ℤ_[5], F = PowerSeries.X ^ 2 * V ∧
      IsUnit V.constantCoeff := by
  exact BSDThetaLimit.finite_tower_certificate G
    (BSDThetaLimit.compatible_of_successive G hstep) hsym hzero
    conductor25Scale c conductor25Scale_isUnit hfirst

/-- The assembled E433 interface requires only first-level finite coefficient
congruences, allowing the lower-level trace scalar to remain arbitrary.
All infinite-series conclusions are derived from the finite tower. -/
theorem e433_certificate_of_finite_tower
    (G : ℕ → Polynomial ℤ_[5])
    (hstep : ∀ n, BSDRankTwo.omegaPoly (R := ℤ_[5]) 5 n ∣ G (n + 1) - G n)
    (hsym : BSDThetaLimit.FiniteSymmetric G)
    (hzero : (G 0).coeff 0 = 0)
    (c : ℤ_[5])
    (hfirst : ∀ k : ℕ, k < 5 → (5 : ℤ_[5]) ∣ (G 1).coeff k -
      PowerSeries.coeff k (BSDThetaCertificate.regularized433 conductor25Scale c)) :
    let F := BSDThetaLimit.thetaLimit G (BSDThetaLimit.compatible_of_successive G hstep)
    F.order = 2 ∧ ∃ V : PowerSeries ℤ_[5], F = PowerSeries.X ^ 2 * V ∧
      IsUnit V.constantCoeff := by
  exact BSDThetaLimit.finite_tower_certificate_mod_five G
    (BSDThetaLimit.compatible_of_successive G hstep) hsym hzero
    conductor25Scale c conductor25Scale_isUnit hfirst

end

end BSDArithmeticCertificate
