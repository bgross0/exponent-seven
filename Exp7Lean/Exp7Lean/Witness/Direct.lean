import Exp7Lean.Witness.Checker
import Exp7Lean.Witness.DirectData

/-!
Exponent 7: the direct range `q < 10^5`, negative part.

Every prime `q ≡ 3 (mod 4)` below `10^5` that is not in `known` and not one of the seven primes
`3, 7, 11, 19, 43, 67, 163` has a witness in `directTable` (4769 primes), so its class group does
not have exponent 7. The table is checked by the kernel (`decide +kernel`, no `native_decide`);
the same pass shows that every other `n ≡ 3 (mod 4)` below `10^5` is composite or one of the 39
exceptions, so the table covers all primes in the range.
-/

namespace Exp7

/-- The exceptions of the direct range: the list `known` and the seven primes `q ≡ 3 (mod 4)` of
class number one. -/
def directExcl : List ℕ := known ++ [3, 7, 11, 19, 43, 67, 163]

theorem directTable_length : directTable.length = 25000 := by decide +kernel

theorem directTable_ok : checkRange directExcl 3 directTable = true := by decide +kernel

/-- No prime `q ≡ 3 (mod 4)` below `10^5` has class group of exponent 7, apart from the primes in
`known` and the seven primes of class number one (about which nothing is said here). -/
theorem direct_neg : ∀ q, q.Prime → q % 4 = 3 → q < 10 ^ 5 → q ∉ known →
    q ∉ [3, 7, 11, 19, 43, 67, 163] → ¬ IsExp7 q := by
  intro q _ h4 hlt hk hc hE
  have hq : 3 + 4 * (q / 4) = q := by omega
  have hlen : q / 4 < directTable.length := by
    rw [directTable_length]
    omega
  have hmem := mem_excl_of_checkRange directTable 3 directTable_ok (q / 4) hlen (by rwa [hq])
  rw [hq, directExcl, List.mem_append] at hmem
  exact hmem.elim hk hc

/-- The field `direct` of `ComputedLow`, from `direct_neg` and the two facts that are not proved
here: the 32 primes of `known` below `10^5` have exponent 7, and the seven primes of class number
one do not. -/
theorem direct_of (hpos : ∀ q ∈ known, q < B → IsExp7 q)
    (hone : ∀ q ∈ [3, 7, 11, 19, 43, 67, 163], ¬ IsExp7 q) :
    ∀ q, q.Prime → q % 4 = 3 → q < B → (IsExp7 q ↔ q ∈ known) := by
  intro q hq h4 hlt
  constructor
  · intro hE
    by_contra hk
    by_cases hc : q ∈ [3, 7, 11, 19, 43, 67, 163]
    · exact hone q hc hE
    · exact direct_neg q hq h4 hlt hk hc hE
  · intro hk
    exact hpos q hk hlt

end Exp7
