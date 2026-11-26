import Exp7Lean.Final4
import Exp7Lean.Genus.Main

/-!
Exponent 7: the final theorems for all negative fundamental discriminants.

`Final4.lean` states Theorems A and D for the ring `OK q = ℤ[ω]`, `ω^2 = ω - (q+1)/4`, attached to a
prime `q ≡ 3 (mod 4)`. Here they are restated for an arbitrary quadratic order
`QuadraticAlgebra ℤ a b` (`ω^2 = a + b ω`) of negative fundamental discriminant
`discr a b = b^2 + 4a`, in Mathlib's own terms.

Two ingredients:

* Step 0 (`Genus/Main.lean`): exponent 7 forces `discr a b = -q` with `q ≡ 3 (mod 4)` prime.
* Over `ℤ` the discriminant classifies quadratic algebras up to isomorphism
  (`QuadraticAlgebra.nonempty_algEquiv_int_iff`), and a ring isomorphism of domains induces an
  isomorphism of class groups (`ClassGroup.mulEquiv`), so the exponent of the class group depends
  only on the discriminant.
-/

namespace Exp7

open QuadraticAlgebra

/-- Isomorphic domains have class groups of the same exponent. -/
theorem exponent_classGroup_eq_of_ringEquiv {R S : Type*} [CommRing R] [IsDomain R] [CommRing S]
    [IsDomain S] (e : R ≃+* S) :
    Monoid.exponent (ClassGroup R) = Monoid.exponent (ClassGroup S) :=
  Monoid.exponent_eq_of_mulEquiv (ClassGroup.mulEquiv e)

/-- The exponent of the class group of a quadratic order over `ℤ` depends only on its
discriminant. -/
theorem exponent_classGroup_eq_of_discr_eq {a b a' b' : ℤ} [IsDomain (QuadraticAlgebra ℤ a b)]
    [IsDomain (QuadraticAlgebra ℤ a' b')] (h : discr a b = discr a' b') :
    Monoid.exponent (ClassGroup (QuadraticAlgebra ℤ a b)) =
      Monoid.exponent (ClassGroup (QuadraticAlgebra ℤ a' b')) := by
  obtain ⟨e⟩ := nonempty_algEquiv_int_iff.mpr h
  exact exponent_classGroup_eq_of_ringEquiv e.toRingEquiv

/-- For a prime `q ≡ 3 (mod 4)`, `IsExp7 q` can be read off any quadratic order of discriminant
`-q`. -/
theorem isExp7_iff_exponent {a b : ℤ} {q : ℕ} (hq : q.Prime) (h4 : q % 4 = 3)
    (hd : discr a b = -(q : ℤ)) [IsDomain (QuadraticAlgebra ℤ a b)] :
    IsExp7 q ↔ Monoid.exponent (ClassGroup (QuadraticAlgebra ℤ a b)) = 7 := by
  have := Fact.mk hq
  have := Fact.mk h4
  have key : Monoid.exponent (ClassGroup (QuadraticAlgebra ℤ a b)) =
      Monoid.exponent (ClassGroup (OK q)) :=
    exponent_classGroup_eq_of_discr_eq (hd.trans (discr_aOf h4).symm)
  constructor
  · rintro ⟨_, _, hC⟩
    have hC' : Monoid.exponent (ClassGroup (OK q)) = 7 := hC
    exact key.trans hC'
  · intro h
    have hC : Monoid.exponent (ClassGroup (OK q)) = 7 := key.symm.trans h
    exact ⟨hq, h4, hC⟩

/-- The 33 known discriminants have class group of exponent 7, unconditionally. -/
theorem exponent_seven_of_mem_known {a b : ℤ} {q : ℕ} (hk : q ∈ known)
    (hd : discr a b = -(q : ℤ)) [IsDomain (QuadraticAlgebra ℤ a b)] :
    Monoid.exponent (ClassGroup (QuadraticAlgebra ℤ a b)) = 7 :=
  (isExp7_iff_exponent (known_prime q hk).1 (known_prime q hk).2 hd).mp (isExp7_of_known_all q hk)

/-- **Theorem A for fundamental discriminants**: no imaginary quadratic order of fundamental
discriminant `D` with `3.1·10^20 ≤ -D ≤ 10^32` has class group of exponent 7, assuming GRH for the
characters of prime conductor and completeness of the main search. -/
theorem theoremA_fundamental (hGRH : GRHPrimeConductor) (hS : SearchHigh) (a b : ℤ)
    (hfund : Int.IsFundamentalDiscr (QuadraticAlgebra.discr a b))
    (hneg : QuadraticAlgebra.discr a b < 0)
    [IsDomain (QuadraticAlgebra ℤ a b)]
    (hlow : (QLOW : ℤ) ≤ -QuadraticAlgebra.discr a b)
    (hhi : -QuadraticAlgebra.discr a b ≤ (QTOP : ℤ)) :
    Monoid.exponent (ClassGroup (QuadraticAlgebra ℤ a b)) ≠ 7 := by
  intro h
  obtain ⟨q, hq, h4, hd⟩ := prime_discr_of_exponent_seven' a b hfund hneg h
  rw [hd, neg_neg] at hlow hhi
  exact theoremA_rows hGRH hS hq h4 (Nat.cast_le.mp hlow) (Nat.cast_le.mp hhi)
    ((isExp7_iff_exponent hq h4 hd).mpr h)

/-- **Theorem D for fundamental discriminants**: an imaginary quadratic order of fundamental
discriminant `D` with `-D ≤ 10^32` has class group of exponent 7 iff `D = -q` for one of the 33
listed primes `q`, assuming GRH for the characters of prime conductor and completeness of the two
searches. (The direction `←` is unconditional: `exponent_seven_of_mem_known`.) -/
theorem theoremD_fundamental (hGRH : GRHPrimeConductor) (hS : SearchHigh) (hSL : SearchLow)
    (a b : ℤ)
    (hfund : Int.IsFundamentalDiscr (QuadraticAlgebra.discr a b))
    (hneg : QuadraticAlgebra.discr a b < 0)
    [IsDomain (QuadraticAlgebra ℤ a b)]
    (hhi : -QuadraticAlgebra.discr a b ≤ (QTOP : ℤ)) :
    Monoid.exponent (ClassGroup (QuadraticAlgebra ℤ a b)) = 7 ↔
      ∃ q ∈ known, QuadraticAlgebra.discr a b = -(q : ℤ) := by
  constructor
  · intro h
    obtain ⟨q, hq, h4, hd⟩ := prime_discr_of_exponent_seven' a b hfund hneg h
    rw [hd, neg_neg] at hhi
    exact ⟨q, (theoremD_rows hGRH hS hSL hq h4 (Nat.cast_le.mp hhi)).mp
      ((isExp7_iff_exponent hq h4 hd).mpr h), hd⟩
  · rintro ⟨q, hk, hd⟩
    exact exponent_seven_of_mem_known hk hd

end Exp7

#print axioms Exp7.theoremA_fundamental
#print axioms Exp7.theoremD_fundamental
