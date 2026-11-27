import Exp7GRHBridge.Imported
import Exp7Lean.Final6

namespace Exp7.GRHIntegration

/-- Theorem A for prime conductors in the certified upper interval. -/
theorem theoremA {q : ℕ} (hq : q.Prime) (h4 : q % 4 = 3)
    (hlow : Exp7.QLOW ≤ q) (hhi : q ≤ Exp7.QTOP) : ¬ Exp7.IsExp7 q :=
  Exp7.theoremA_GRH primeConductor hq h4 hlow hhi

/-- Theorem D for prime conductors up to the certified bound. -/
theorem theoremD {q : ℕ} (hq : q.Prime) (h4 : q % 4 = 3) (hhi : q ≤ Exp7.QTOP) :
    Exp7.IsExp7 q ↔ q ∈ Exp7.known :=
  Exp7.theoremD_GRH primeConductor hq h4 hhi

/-- Theorem A for negative fundamental discriminants in the certified upper interval. -/
theorem theoremA_fundamental (a b : ℤ)
    (hfund : Int.IsFundamentalDiscr (QuadraticAlgebra.discr a b))
    (hneg : QuadraticAlgebra.discr a b < 0) [IsDomain (QuadraticAlgebra ℤ a b)]
    (hlow : (Exp7.QLOW : ℤ) ≤ -QuadraticAlgebra.discr a b)
    (hhi : -QuadraticAlgebra.discr a b ≤ (Exp7.QTOP : ℤ)) :
    Monoid.exponent (ClassGroup (QuadraticAlgebra ℤ a b)) ≠ 7 :=
  Exp7.theoremA_fundamental_GRH primeConductor a b hfund hneg hlow hhi

/-- Theorem D for negative fundamental discriminants up to the certified bound. -/
theorem theoremD_fundamental (a b : ℤ)
    (hfund : Int.IsFundamentalDiscr (QuadraticAlgebra.discr a b))
    (hneg : QuadraticAlgebra.discr a b < 0) [IsDomain (QuadraticAlgebra ℤ a b)]
    (hhi : -QuadraticAlgebra.discr a b ≤ (Exp7.QTOP : ℤ)) :
    Monoid.exponent (ClassGroup (QuadraticAlgebra ℤ a b)) = 7 ↔
      ∃ q ∈ Exp7.known, QuadraticAlgebra.discr a b = -(q : ℤ) :=
  Exp7.theoremD_fundamental_GRH primeConductor a b hfund hneg hhi

end Exp7.GRHIntegration

#print axioms Exp7.GRHIntegration.theoremA
#print axioms Exp7.GRHIntegration.theoremD
#print axioms Exp7.GRHIntegration.theoremA_fundamental
#print axioms Exp7.GRHIntegration.theoremD_fundamental
