import Exp7Lean.Fundamental
import Exp7Lean.Sieve.All

/-!
Exponent 7: Theorem A with GRH as its only hypothesis.

`Exp7.searchHigh : Exp7.SearchHigh` (in `Sieve/All.lean`) is completeness of the main search. It is
checked in the kernel from the 465 per-prime certificates `Sieve/P<p>.lean`, one for each prime
`701 ≤ p ≤ 4297`.

These files are not part of the default build target (checking the certificates takes about
11 core-hours): build them with `lake build Exp7Full`.
-/

namespace Exp7

/-- **Theorem A**: assuming GRH for the quadratic characters of prime conductor, no prime
`q ≡ 3 (mod 4)` with `3.1·10^20 ≤ q ≤ 10^32` has class group of exponent 7. -/
theorem theoremA_GRH (hGRH : GRHPrimeConductor) {q : ℕ} (hq : q.Prime) (h4 : q % 4 = 3)
    (hlow : QLOW ≤ q) (hhi : q ≤ QTOP) : ¬ IsExp7 q :=
  theoremA_rows hGRH searchHigh hq h4 hlow hhi

/-- **Theorem A for fundamental discriminants**: assuming GRH for the quadratic characters of
prime conductor, no imaginary quadratic order of fundamental discriminant `D` with
`3.1·10^20 ≤ -D ≤ 10^32` has class group of exponent 7. -/
theorem theoremA_fundamental_GRH (hGRH : GRHPrimeConductor) (a b : ℤ)
    (hfund : Int.IsFundamentalDiscr (QuadraticAlgebra.discr a b))
    (hneg : QuadraticAlgebra.discr a b < 0)
    [IsDomain (QuadraticAlgebra ℤ a b)]
    (hlow : (QLOW : ℤ) ≤ -QuadraticAlgebra.discr a b)
    (hhi : -QuadraticAlgebra.discr a b ≤ (QTOP : ℤ)) :
    Monoid.exponent (ClassGroup (QuadraticAlgebra ℤ a b)) ≠ 7 :=
  theoremA_fundamental hGRH searchHigh a b hfund hneg hlow hhi

end Exp7

#print axioms Exp7.theoremA_GRH
#print axioms Exp7.theoremA_fundamental_GRH
