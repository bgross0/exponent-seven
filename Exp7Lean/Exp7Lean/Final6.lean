import Exp7Lean.Final5
import Exp7Lean.SieveLow.All

/-!
Exponent 7: Theorem D with GRH as its only hypothesis.

`Exp7.searchLow : Exp7.SearchLow` (in `SieveLow/All.lean`) is completeness of the low-range search.
It is checked in the kernel from the 401 per-prime certificates `SieveLow/P<p>.lean`, one for each
prime `3 ≤ p < 2760`.

Like `Final5.lean`, this file is outside the default build target: `lake build Exp7Full`.
-/

namespace Exp7

/-- **Theorem D**: assuming GRH for the quadratic characters of prime conductor, for a prime
`q ≡ 3 (mod 4)` with `q ≤ 10^32` the class group of `ℚ(√-q)` has exponent 7 if and only if `q` is
one of the 33 listed primes. -/
theorem theoremD_GRH (hGRH : GRHPrimeConductor) {q : ℕ} (hq : q.Prime) (h4 : q % 4 = 3)
    (hhi : q ≤ QTOP) : IsExp7 q ↔ q ∈ known :=
  theoremD_rows hGRH searchHigh searchLow hq h4 hhi

/-- **Theorem D for fundamental discriminants**: assuming GRH for the quadratic characters of
prime conductor, an imaginary quadratic order of fundamental discriminant `D` with `-D ≤ 10^32`
has class group of exponent 7 if and only if `D = -q` for one of the 33 listed primes `q`. -/
theorem theoremD_fundamental_GRH (hGRH : GRHPrimeConductor) (a b : ℤ)
    (hfund : Int.IsFundamentalDiscr (QuadraticAlgebra.discr a b))
    (hneg : QuadraticAlgebra.discr a b < 0)
    [IsDomain (QuadraticAlgebra ℤ a b)]
    (hhi : -QuadraticAlgebra.discr a b ≤ (QTOP : ℤ)) :
    Monoid.exponent (ClassGroup (QuadraticAlgebra ℤ a b)) = 7 ↔
      ∃ q ∈ known, QuadraticAlgebra.discr a b = -(q : ℤ) :=
  theoremD_fundamental hGRH searchHigh searchLow a b hfund hneg hhi

end Exp7

#print axioms Exp7.theoremD_GRH
#print axioms Exp7.theoremD_fundamental_GRH
