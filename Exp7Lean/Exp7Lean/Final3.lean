import Exp7Lean.Final2
import Exp7Lean.Analytic.EF.Main

/-!
Exponent 7: the final theorems with the explicit formula proved.

`EF.explicitFormulaBound : ExplicitFormulaBound` is proved in `Analytic/EF/` (Guinand–Weil explicit
formula for the odd real primitive character of prime conductor, with positivity under GRH, via a
damped formula, analytic continuation in the damping parameter, and Hadamard's partial fractions
proved from Jensen's formula). The remaining hypotheses are GRH itself, the numerical row
margins, and completeness of the two searches.
-/

namespace Exp7

/-- **Theorem A**: no prime `q ≡ 3 (mod 4)` with `3.1·10^20 ≤ q ≤ 10^32` has class group of
exponent 7, assuming GRH for the characters of prime conductor, the numerical margins of the 51
certificate rows, and completeness of the main search. -/
theorem theoremA_ef (hGRH : GRHPrimeConductor) (hM : RowMargins allRows) (hS : SearchHigh)
    {q : ℕ} (hq : q.Prime) (h4 : q % 4 = 3) (hlow : QLOW ≤ q) (hhi : q ≤ QTOP) : ¬ IsExp7 q :=
  theoremA_final EF.explicitFormulaBound hGRH hM hS hq h4 hlow hhi

/-- **Theorem D**: for a prime `q ≡ 3 (mod 4)` with `q ≤ 10^32`, the class group of `ℚ(√-q)` has
exponent 7 iff `q` is one of the 33 listed primes, assuming GRH for the characters of prime
conductor, the numerical margins of the 175 certificate rows, and completeness of the two
searches. -/
theorem theoremD_ef (hGRH : GRHPrimeConductor) (hM : RowMargins allRows)
    (hML : RowMargins lowRows) (hS : SearchHigh) (hSL : SearchLow) {q : ℕ} (hq : q.Prime)
    (h4 : q % 4 = 3) (hhi : q ≤ QTOP) : IsExp7 q ↔ q ∈ known :=
  theoremD_final EF.explicitFormulaBound hGRH hM hML hS hSL hq h4 hhi

end Exp7
