import Exp7GRHBridge.Imported
import Exp7Lean.Rows.Bridge30000
import Exp7Lean.Final6

/-! Discharge the finite bridge's GRH input in the shared Lean 4.35 environment. -/

namespace Exp7.GRHIntegration

theorem bridge30000 {q : ℕ} (hq : q.Prime) (h4 : q % 4 = 3)
    (hlo : 10 ^ 32 ≤ q) (hhi : q ≤ 2 ^ 135) : ¬ IsExp7 q :=
  Rows.Bridge30000.excludes primeConductor hq h4 hlo hhi

theorem bridge30000_fundamental (a b : ℤ)
    (hfund : Int.IsFundamentalDiscr (QuadraticAlgebra.discr a b))
    (hneg : QuadraticAlgebra.discr a b < 0) [IsDomain (QuadraticAlgebra ℤ a b)]
    (hlo : (10 : ℤ) ^ 32 ≤ -QuadraticAlgebra.discr a b)
    (hhi : -QuadraticAlgebra.discr a b ≤ (2 : ℤ) ^ 135) :
    Monoid.exponent (ClassGroup (QuadraticAlgebra ℤ a b)) ≠ 7 :=
  Rows.Bridge30000.excludes_fundamental primeConductor a b hfund hneg hlo hhi

/-- Combine the two closed intervals into the bounded classification through 2^135. -/
theorem theoremD_fundamental_135 (a b : ℤ)
    (hfund : Int.IsFundamentalDiscr (QuadraticAlgebra.discr a b))
    (hneg : QuadraticAlgebra.discr a b < 0) [IsDomain (QuadraticAlgebra ℤ a b)]
    (hhi : -QuadraticAlgebra.discr a b ≤ (2 : ℤ) ^ 135) :
    Monoid.exponent (ClassGroup (QuadraticAlgebra ℤ a b)) = 7 ↔
      ∃ q ∈ known, QuadraticAlgebra.discr a b = -(q : ℤ) := by
  by_cases h : -QuadraticAlgebra.discr a b ≤ (QTOP : ℤ)
  · exact Exp7.theoremD_fundamental_GRH primeConductor a b hfund hneg h
  · have hlo : (10 : ℤ) ^ 32 ≤ -QuadraticAlgebra.discr a b := by
      exact_mod_cast (lt_of_not_ge h).le
    exact ⟨fun hE => (bridge30000_fundamental a b hfund hneg hlo hhi hE).elim,
      fun ⟨_, hk, hd⟩ => exponent_seven_of_mem_known hk hd⟩

end Exp7.GRHIntegration
