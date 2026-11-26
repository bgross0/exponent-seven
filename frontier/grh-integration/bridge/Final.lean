import Exp7GRHBridge.Imported
import Exp7Lean.Fundamental
import Exp7Lean.Sieve.All
import Exp7Lean.SieveLow.All

/-!
The conditional wrappers accept the two finite-search statements explicitly. The four bounded
results below apply the compiled certificates and the imported prime-conductor theorem.
-/

namespace Exp7.GRHIntegration

theorem theoremA_importedGRH (hS : Exp7.SearchHigh) {q : ℕ} (hq : q.Prime)
    (h4 : q % 4 = 3) (hlow : Exp7.QLOW ≤ q) (hhi : q ≤ Exp7.QTOP) :
    ¬ Exp7.IsExp7 q :=
  Exp7.theoremA_rows primeConductor hS hq h4 hlow hhi

theorem theoremD_importedGRH (hS : Exp7.SearchHigh) (hSL : Exp7.SearchLow) {q : ℕ}
    (hq : q.Prime) (h4 : q % 4 = 3) (hhi : q ≤ Exp7.QTOP) :
    Exp7.IsExp7 q ↔ q ∈ Exp7.known :=
  Exp7.theoremD_rows primeConductor hS hSL hq h4 hhi

/-- Theorem A for prime conductors in the certified upper interval. -/
theorem theoremA {q : ℕ} (hq : q.Prime) (h4 : q % 4 = 3)
    (hlow : Exp7.QLOW ≤ q) (hhi : q ≤ Exp7.QTOP) : ¬ Exp7.IsExp7 q :=
  theoremA_importedGRH Exp7.searchHigh hq h4 hlow hhi

/-- Theorem D for prime conductors up to the certified bound. -/
theorem theoremD {q : ℕ} (hq : q.Prime) (h4 : q % 4 = 3) (hhi : q ≤ Exp7.QTOP) :
    Exp7.IsExp7 q ↔ q ∈ Exp7.known :=
  theoremD_importedGRH Exp7.searchHigh Exp7.searchLow hq h4 hhi

/-- Theorem A for negative fundamental discriminants in the certified upper interval. -/
theorem theoremA_fundamental (a b : ℤ)
    (hfund : Int.IsFundamentalDiscr (QuadraticAlgebra.discr a b))
    (hneg : QuadraticAlgebra.discr a b < 0) [IsDomain (QuadraticAlgebra ℤ a b)]
    (hlow : (Exp7.QLOW : ℤ) ≤ -QuadraticAlgebra.discr a b)
    (hhi : -QuadraticAlgebra.discr a b ≤ (Exp7.QTOP : ℤ)) :
    Monoid.exponent (ClassGroup (QuadraticAlgebra ℤ a b)) ≠ 7 :=
  Exp7.theoremA_fundamental primeConductor Exp7.searchHigh a b hfund hneg hlow hhi

/-- Theorem D for negative fundamental discriminants up to the certified bound. -/
theorem theoremD_fundamental (a b : ℤ)
    (hfund : Int.IsFundamentalDiscr (QuadraticAlgebra.discr a b))
    (hneg : QuadraticAlgebra.discr a b < 0) [IsDomain (QuadraticAlgebra ℤ a b)]
    (hhi : -QuadraticAlgebra.discr a b ≤ (Exp7.QTOP : ℤ)) :
    Monoid.exponent (ClassGroup (QuadraticAlgebra ℤ a b)) = 7 ↔
      ∃ q ∈ Exp7.known, QuadraticAlgebra.discr a b = -(q : ℤ) :=
  Exp7.theoremD_fundamental primeConductor Exp7.searchHigh Exp7.searchLow a b hfund hneg hhi

end Exp7.GRHIntegration

#print axioms Exp7.GRHIntegration.theoremA_importedGRH
#print axioms Exp7.GRHIntegration.theoremD_importedGRH
#print axioms Exp7.GRHIntegration.theoremA
#print axioms Exp7.GRHIntegration.theoremD
#print axioms Exp7.GRHIntegration.theoremA_fundamental
#print axioms Exp7.GRHIntegration.theoremD_fundamental
