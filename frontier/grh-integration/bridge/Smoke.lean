import Statements
import Exp7Lean.Analytic.Statement

/-!
Interface check only. This file proves an implication; it does not discharge GRH.
The external statement and the project's definitions are imported, not copied or redefined.
Prepared against the source pins in ../pins.json. Not compiled in the preparation environment.
-/

namespace Exp7.GRHIntegration

/-- The compact proof's Dirichlet zero statement specializes to the project's hypothesis. -/
theorem primeConductor_of_dirichletZeros
    (h : _root_.DirichletLZerosOnLine) : Exp7.GRHPrimeConductor := by
  intro q hq _h4
  letI : NeZero q := ⟨hq.out.ne_zero⟩
  exact h q (Exp7.chi q)

end Exp7.GRHIntegration

#print axioms Exp7.GRHIntegration.primeConductor_of_dirichletZeros

