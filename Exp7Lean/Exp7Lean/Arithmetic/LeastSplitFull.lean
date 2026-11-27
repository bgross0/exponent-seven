import Exp7Lean.Arithmetic.LeastSplitClass
import Exp7Lean.Sieve.All

/-!
Apply the existing kernel-checked high search. GRH is the only analytic or search
hypothesis of these least-split-prime exclusions. No low search is needed.

This file is included in `Exp7Full`, outside the default certificate-free target.
-/

namespace Exp7

/-- For every prime conductor at least `QLOW`, a least split prime has no norm representation
with nonzero second coordinate and odd exponent at most seven, assuming GRH. -/
theorem LeastSplit.no_norm_odd_le_seven_GRH (hGRH : GRHPrimeConductor)
    {q p n : ℕ} (h : LeastSplit q p) (hq : q.Prime) (h4 : q % 4 = 3)
    (hlo : QLOW ≤ q) (hn : Odd n) (hn7 : n ≤ 7) {x y : ℕ} (hy : 1 ≤ y) :
    4 * p ^ n ≠ x ^ 2 + q * y ^ 2 :=
  h.no_norm_odd_le_seven hGRH searchHigh hq h4 hlo hn hn7 hy

/-- At every large prime conductor there is a specific ideal class, above the least split
prime, whose first four odd powers are nontrivial. -/
theorem exists_least_split_class_surviving_odd_powers_GRH (hGRH : GRHPrimeConductor)
    {q : ℕ} [Fact q.Prime] [Fact (q % 4 = 3)] (hlo : QLOW ≤ q) :
    ∃ (p : ℕ) (hp : p.Prime) (t : ℤ), LeastSplit q p ∧
      (p : ℤ) ∣ t ^ 2 - t - aOf q ∧
      ∀ n : ℕ, Odd n → n ≤ 7 → classOf q p hp.ne_zero t ^ n ≠ 1 :=
  exists_least_split_class_surviving_odd_powers hGRH searchHigh hlo

/-- In particular, the order of the least split prime ideal class cannot be seven. -/
theorem LeastSplit.class_order_ne_seven_GRH (hGRH : GRHPrimeConductor)
    {q p : ℕ} [Fact q.Prime] [Fact (q % 4 = 3)]
    (h : LeastSplit q p) (hlo : QLOW ≤ q) {t : ℤ}
    (ht : (p : ℤ) ∣ t ^ 2 - t - aOf q) :
    orderOf (classOf q p h.prime.ne_zero t) ≠ 7 :=
  h.class_order_ne_seven hGRH searchHigh hlo ht

end Exp7

#print axioms Exp7.norm_eq_of_principal_odd_power
#print axioms Exp7.LeastSplit.no_norm_odd_le_seven_GRH
#print axioms Exp7.exists_least_split_class_surviving_odd_powers_GRH
#print axioms Exp7.LeastSplit.class_order_ne_seven_GRH
