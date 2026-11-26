import Exp7Lean.Analytic.EF.Continuation
import Exp7Lean.Analytic.EF.TestFunction

/-!
# Explicit formula blueprint: the theorem

`ExplicitFormulaBound` (stated in `Exp7Lean/Analytic/Statement.lean`) from the two top-level nodes
of the blueprint:

* **C4** `primeSum_le_of_weilAdmissible` (analytic side, `Continuation.lean`),
* **T10** `weilAdmissible_autocorr_stepFn` (test-function side, `TestFunction.lean`).

All leaves of `BLUEPRINT.md` are proved. `#print axioms Exp7.EF.explicitFormulaBound` shows only
`propext`, `Classical.choice` and `Quot.sound`.
-/

namespace Exp7.EF

/-- **Main theorem** (proved from C4 and T10). -/
theorem explicitFormulaBound : ExplicitFormulaBound := by
  intro q _ hq hGRH X v hX hv
  have hX' : (2 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hL : 0 < Real.log X := Real.log_pos (by linarith)
  exact primeSum_le_of_weilAdmissible q hq hGRH (weilAdmissible_autocorr_stepFn hL hv)

end Exp7.EF
