import BSDRankTwo
import BSDFiniteWitness
import BSDThetaCertificate
import BSDCMPeriods
import BSDLocalization
import BSDEigenline
import BSDCoordinateRing
import BSDHenselWitness
import BSDHenselSemantics
import BSDHenselLift
import BSDHenselDistinct
import BSDOrdinary
import BSDThetaLimit
import BSDArithmeticCertificate
import BSDHorizontal71
import BSDRationalPoints
import BSDE389Theta

/-!
# Integrated arithmetic and finite certificate entry points

These theorems connect the canonical matrix/root/cycle data with the period
algebra and the finite theta polynomial. The imported modules additionally
construct actual roots in a completed quadratic order, prove their exact
degree-seven polynomial graph, construct the curves' ordinary unit roots,
and construct a power-series limit of a compatible finite tower. The
conductor-389 curve has two proved independent actual rational points, and
its finite theta data have a separate certificate using its own ordinary
root. Arithmetic CM identification and construction of that tower, and
the Selmer/rank-upper-bound/Sha conclusions, remain proof obligations.
-/

namespace BSDCertificates

variable {R : Type*} [CommRing R]

/-- The conductor-one evaluation taken directly from the certified finite
root table, vertex function and seven-cycle. -/
def conductorOne433 (z : R) : R :=
  BSDThetaCertificate.groupElement
    (BSDFiniteWitness.cm71Cycle433.map (fun i =>
      BSDFiniteWitness.vertexValue433
        (BSDFiniteWitness.reduce433 BSDFiniteWitness.cm71Roots433[i]!))) z

theorem conductorOne433_eq_period (z : R) :
    conductorOne433 z = BSDCMPeriods.period433 z := by
  rw [conductorOne433, BSDFiniteWitness.cm71Weights_match433]
  simp [BSDThetaCertificate.groupElement, List.zipIdx, BSDCMPeriods.period433]
  ring

theorem conductorOne433_isUnit (z : R)
    (hz : BSDCMPeriods.phi7 z = 0) (h7 : IsUnit (7 : R)) :
    IsUnit (conductorOne433 z) := by
  rw [conductorOne433_eq_period]
  exact BSDCMPeriods.period433_isUnit_of_phi7 z hz h7

theorem conductorOne433_product (z : R) (hz : BSDCMPeriods.phi7 z = 0) :
    BSDCMPeriods.conjugateProduct conductorOne433 z = 49 := by
  simpa only [BSDCMPeriods.conjugateProduct, conductorOne433_eq_period] using
    BSDCMPeriods.period433_conjugateProduct_eq_49 z hz

/-- The full 140-entry projection, using the eigenfunction values read from
the root table in the certified cycle order, has this exact shifted form. -/
theorem certified_finite433_shift (T : R) :
    BSDThetaCertificate.groupElement
      (BSDThetaCertificate.quotientFiveSums
        (BSDFiniteWitness.cm433Cycle.map (fun i =>
          BSDFiniteWitness.vertexValue433
            (BSDFiniteWitness.reduce433 BSDFiniteWitness.cm433Roots[i]!)))) (1 + T) =
      T ^ 2 + T ^ 3 := by
  rw [BSDFiniteWitness.cm433Weights_match]
  exact BSDThetaCertificate.finite433_shift T

end BSDCertificates
