import Exp7Lean.Final3
import Exp7Lean.Rows.Margins

/-!
Exponent 7: the final theorems with the explicit formula and all 175 row margins proved.

The only remaining hypotheses are GRH for the characters of prime conductor (the hypothesis of the
theorem) and completeness of the two searches.
-/

namespace Exp7

/-- **Theorem A**: no prime `q ≡ 3 (mod 4)` with `3.1·10^20 ≤ q ≤ 10^32` has class group of
exponent 7, assuming GRH for the characters of prime conductor and completeness of the main
search. -/
theorem theoremA_rows (hGRH : GRHPrimeConductor) (hS : SearchHigh) {q : ℕ} (hq : q.Prime)
    (h4 : q % 4 = 3) (hlow : QLOW ≤ q) (hhi : q ≤ QTOP) : ¬ IsExp7 q :=
  theoremA_ef hGRH rowMargins_allRows hS hq h4 hlow hhi

/-- **Theorem D**: for a prime `q ≡ 3 (mod 4)` with `q ≤ 10^32`, the class group of `ℚ(√-q)` has
exponent 7 iff `q` is one of the 33 listed primes, assuming GRH for the characters of prime
conductor and completeness of the two searches. -/
theorem theoremD_rows (hGRH : GRHPrimeConductor) (hS : SearchHigh) (hSL : SearchLow) {q : ℕ}
    (hq : q.Prime) (h4 : q % 4 = 3) (hhi : q ≤ QTOP) : IsExp7 q ↔ q ∈ known :=
  theoremD_ef hGRH rowMargins_allRows rowMargins_lowRows hS hSL hq h4 hhi

end Exp7
