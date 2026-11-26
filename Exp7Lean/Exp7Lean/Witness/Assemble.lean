import Exp7Lean.Final
import Exp7Lean.Witness.Survivors
import Exp7Lean.Witness.Direct

/-!
Exponent 7: what the witness tables leave of `ComputedLow`.

`ComputedLow` (in `Final.lean`) has the fields `certLow`, `direct`, `searchLow`, `exp118843`.
With the kernel-checked tables of `Witness/Survivors.lean` and `Witness/Direct.lean`, the fields
`direct`, `searchLow` and `exp118843` are reduced to the hypotheses `hpos`, `hone`, `hmem` below:

* `hpos`: the 33 primes of `known` have class group of exponent 7;
* `hone`: the seven primes `3, 7, 11, 19, 43, 67, 163` (class number one) do not;
* `hmem`: completeness of the low-range search, i.e. every `q` satisfying its conditions is one of
  the 6608 survivors `survivorQs`.
-/

namespace Exp7

theorem computedLow_of_tables
    (certLow : ∀ r ∈ lowRows, ∀ q, q.Prime → q % 4 = 3 → r.X < q → q ≤ r.Q →
      ∃ p, p.Prime ∧ p < r.X ∧ Splits q p)
    (hpos : ∀ q ∈ known, IsExp7 q)
    (hone : ∀ q ∈ [3, 7, 11, 19, 43, 67, 163], ¬ IsExp7 q)
    (hmem : ∀ p, p.Prime → 3 ≤ p → p < 2760 → ∀ x y q : ℕ, 1 ≤ y → ¬ p ∣ y →
      4 * p ^ 7 = x ^ 2 + q * y ^ 2 → QloFull p ≤ q → q < QLOW → q % 8 = 3 →
      (∀ l, l.Prime → 3 ≤ l → l < p → jacobiSym (-(q : ℤ)) l = -1) → q.Prime →
      q ∈ survivorQs) :
    ComputedLow where
  certLow := certLow
  direct := direct_of (fun q hq _ => hpos q hq) hone
  searchLow := searchLow_of_mem hmem
  exp118843 := hpos 118843 (by simp [known])

end Exp7
