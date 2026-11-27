import Main
import Exp7GRHBridge.Smoke

/-!
This file imports the actual external proof. It must be built in the SAME Lean/Mathlib
environment as Exp7Lean. An axiom, a copied statement, or a separate build is insufficient.
Prepared against the source pins in ../pins.json. Not compiled in the preparation environment.
-/

namespace Exp7.GRHIntegration

/-- GRH for the project's prime-conductor characters, from the imported theorem. -/
theorem primeConductor : Exp7.GRHPrimeConductor :=
  primeConductor_of_dirichletZeros _root_.LFunction_eq_zero_re

end Exp7.GRHIntegration

#print axioms LFunction_eq_zero_re
#print axioms Exp7.GRHIntegration.primeConductor

