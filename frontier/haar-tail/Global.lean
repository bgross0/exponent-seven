import Exp7Lean.Tail.Exclusion
import Exp7Lean.Final6
import Exp7GRHBridge.Imported

/-! The unrestricted classifications with the imported prime-conductor GRH
theorem and both kernel-checked searches. -/

namespace Exp7.GRHIntegration

theorem excludes_above_bridge {q : ℕ} (hq : q.Prime) (h4 : q % 4 = 3)
    (hlarge : 2 ^ 135 < q) : ¬ IsExp7 q :=
  ChebyshevTail.excludes_above_bridge primeConductor hq h4 hlarge

/-- The unrestricted classification for prime conductors. -/
theorem theoremD_global {q : ℕ} (hq : q.Prime) (h4 : q % 4 = 3) :
    IsExp7 q ↔ q ∈ known :=
  ChebyshevTail.classification_prime primeConductor searchHigh searchLow hq h4

/-- The unrestricted classification for negative fundamental discriminants. -/
theorem theoremD_fundamental_global (a b : ℤ)
    (hfund : Int.IsFundamentalDiscr (QuadraticAlgebra.discr a b))
    (hneg : QuadraticAlgebra.discr a b < 0) [IsDomain (QuadraticAlgebra ℤ a b)] :
    Monoid.exponent (ClassGroup (QuadraticAlgebra ℤ a b)) = 7 ↔
      ∃ q ∈ known, QuadraticAlgebra.discr a b = -(q : ℤ) :=
  ChebyshevTail.classification_fundamental primeConductor searchHigh searchLow a b hfund hneg

end Exp7.GRHIntegration
