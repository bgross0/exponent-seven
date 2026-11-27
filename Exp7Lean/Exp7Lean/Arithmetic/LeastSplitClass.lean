import Exp7Lean.Arithmetic.LeastSplit
import Exp7Lean.Arithmetic.PrincipalPower

/-!
The least split prime represents an ideal class whose powers 1, 3, 5 and 7 are
nontrivial. This strengthens the exponent-seven classification by making no
assumption about the exponent of the whole class group.
-/

namespace Exp7
namespace LeastSplit

variable {q p : ℕ} [hq : Fact q.Prime] [h4 : Fact (q % 4 = 3)]

/-- None of the first four odd powers of the least split prime ideal is principal. -/
theorem not_principal_odd_power (hGRH : GRHPrimeConductor) (hS : SearchHigh)
    (h : LeastSplit q p) (hlo : QLOW ≤ q) {t : ℤ}
    (ht : (p : ℤ) ∣ t ^ 2 - t - aOf q) {n : ℕ} (hn : Odd n) (hn7 : n ≤ 7) :
    ¬ (idealI q p t ^ n).IsPrincipal := by
  intro hprincipal
  obtain ⟨x, y, hy, he⟩ := norm_eq_of_principal_odd_power h.prime
    (h.lt_conductor hGRH hq.out h4.out hlo).ne ht hn hprincipal
  exact h.no_norm_odd_le_seven hGRH hS hq.out h4.out hlo hn hn7 hy he

/-- The class of either root ideal above the least split prime survives powers 1, 3, 5 and 7. -/
theorem class_pow_ne_one (hGRH : GRHPrimeConductor) (hS : SearchHigh)
    (h : LeastSplit q p) (hlo : QLOW ≤ q) {t : ℤ}
    (ht : (p : ℤ) ∣ t ^ 2 - t - aOf q) {n : ℕ} (hn : Odd n) (hn7 : n ≤ 7) :
    classOf q p h.prime.ne_zero t ^ n ≠ 1 := by
  intro hc
  exact h.not_principal_odd_power hGRH hS hlo ht hn hn7
    ((classOf_pow_eq_one_iff h.prime.ne_zero t n).mp hc)

/-- In particular, the least split prime ideal class does not have order seven. -/
theorem class_order_ne_seven (hGRH : GRHPrimeConductor) (hS : SearchHigh)
    (h : LeastSplit q p) (hlo : QLOW ≤ q) {t : ℤ}
    (ht : (p : ℤ) ∣ t ^ 2 - t - aOf q) :
    orderOf (classOf q p h.prime.ne_zero t) ≠ 7 := by
  intro ho
  have hc := pow_orderOf_eq_one (classOf q p h.prime.ne_zero t)
  rw [ho] at hc
  exact h.class_pow_ne_one hGRH hS hlo ht (by decide : Odd 7) le_rfl hc

/-- If oddness of this class order is supplied, its order is at least nine.
The oddness input is explicit; this module does not prove the converse genus-theory fact. -/
theorem nine_le_class_order_of_odd (hGRH : GRHPrimeConductor) (hS : SearchHigh)
    (h : LeastSplit q p) (hlo : QLOW ≤ q) {t : ℤ}
    (ht : (p : ℤ) ∣ t ^ 2 - t - aOf q)
    (hodd : Odd (orderOf (classOf q p h.prime.ne_zero t))) :
    9 ≤ orderOf (classOf q p h.prime.ne_zero t) := by
  by_contra hn
  have hn7 : orderOf (classOf q p h.prime.ne_zero t) ≤ 7 := by
    obtain ⟨k, hk⟩ := hodd
    omega
  exact h.class_pow_ne_one hGRH hS hlo ht hodd hn7
    (pow_orderOf_eq_one (classOf q p h.prime.ne_zero t))

end LeastSplit

/-- A particular ideal class survives all four small odd powers, rather than merely asserting
that the exponent of the entire class group differs from seven. -/
theorem exists_least_split_class_surviving_odd_powers (hGRH : GRHPrimeConductor)
    (hS : SearchHigh) {q : ℕ} [hq : Fact q.Prime] [h4 : Fact (q % 4 = 3)]
    (hlo : QLOW ≤ q) :
    ∃ (p : ℕ) (hp : p.Prime) (t : ℤ), LeastSplit q p ∧
      (p : ℤ) ∣ t ^ 2 - t - aOf q ∧
      ∀ n : ℕ, Odd n → n ≤ 7 → classOf q p hp.ne_zero t ^ n ≠ 1 := by
  obtain ⟨p, h⟩ := exists_leastSplit hGRH hq.out h4.out hlo
  obtain ⟨t, ht⟩ := exists_root hq.out h4.out h.prime
    (h.lt_conductor hGRH hq.out h4.out hlo).ne h.splits
  exact ⟨p, h.prime, t, h, ht, fun _ hn hn7 => h.class_pow_ne_one hGRH hS hlo ht hn hn7⟩

end Exp7
