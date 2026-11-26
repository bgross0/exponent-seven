import Exp7Lean.ClassGroup.Known
import Exp7Lean.ClassGroup.GenBoundProof

/-!
Exponent 7: the class groups of the 33 fields and of the class-number-one fields, with no
hypothesis. Combines `Known.lean` (certificates checked by the kernel) with the generator bound.
-/

namespace Exp7

/-- Each of the 33 listed primes has class group of exponent 7. -/
theorem isExp7_of_mem_known (q : ℕ) (hk : q ∈ known) (hq : q.Prime) (h4 : q % 4 = 3) :
    IsExp7 q :=
  isExp7_of_known q hk hq h4 (@genBound_sqrt q ⟨hq⟩ ⟨h4⟩)

/-- The class-number-one fields do not have exponent 7. -/
theorem not_isExp7_of_mem_classNumberOne (q : ℕ) (hq1 : q ∈ [3, 7, 11, 19, 43, 67, 163])
    (hq : q.Prime) (h4 : q % 4 = 3) : ¬ IsExp7 q :=
  not_isExp7_of_classNumberOne q hq1 hq h4 (@genBound_sqrt q ⟨hq⟩ ⟨h4⟩)

/-- `ℚ(√-118843)` has class group of exponent 7. -/
theorem isExp7_118843 : IsExp7 118843 :=
  isExp7_of_mem_known 118843 (by decide) (by norm_num) (by norm_num)

end Exp7
