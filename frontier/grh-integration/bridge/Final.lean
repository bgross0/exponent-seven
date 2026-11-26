import Exp7GRHBridge.Imported
import Exp7Lean.Final4

/-!
The numerical row margins are already discharged by Final4 at the pinned project commit.
These conclusions still require the two explicitly named finite-search statements.
They also retain q ≤ QTOP. This file does not prove a global classification.
Prepared against the source pins in ../pins.json. Not compiled in the preparation environment.
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

end Exp7.GRHIntegration

#print axioms Exp7.GRHIntegration.theoremA_importedGRH
#print axioms Exp7.GRHIntegration.theoremD_importedGRH

