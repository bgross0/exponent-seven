import Exp7Lean.Analytic.Statement

/-!
Exponent 7: from the explicit-formula inequality to the certificate rows.

`Statement.lean` states the analytic input `ExplicitFormulaBound` and the hypothesis
`GRHPrimeConductor`. This file proves that they imply a statement of the shape of `Computed.cert`
for every row whose numerical margin `rowMargin` is positive.

The argument: if no prime `p < X` splits in `ℚ(√-q)`, then by quadratic reciprocity (and its
supplement for `2`) the character `n ↦ (n/q)` takes the value `-1` at every prime below `X`, so the
prime-power side `primeSum q f X` of the explicit formula equals `inertSum f X`, a quantity that
does not depend on `q`. The explicit-formula inequality then bounds `inertSum f X` from above by
`log Q - log π + ψ(3/4) + J_f`, which is what `0 < rowMargin Q X v` contradicts.

Nothing here is assumed: `ExplicitFormulaBound` and `GRHPrimeConductor` occur only as explicit
hypotheses of the theorems.
-/

namespace Exp7

open Real

/-- The value of the prime-power side when every prime below `X` is inert: `χ(p^k) = (-1)^k`. -/
noncomputable def inertSum (f : ℝ → ℝ) (X : ℕ) : ℝ :=
  2 * ∑ n ∈ Finset.range X,
    ArithmeticFunction.vonMangoldt n * (-1 : ℝ) ^ (n.factorization n.minFac) * f (Real.log n) /
      Real.sqrt n

/-- The margin of a row: positive margin contradicts the explicit-formula inequality when every
prime below `X` is inert. -/
noncomputable def rowMargin (Q X : ℕ) (v : List ℝ) : ℝ :=
  inertSum (autocorr (stepFn (Real.log X) v)) X - Jterm (autocorr (stepFn (Real.log X) v))
    - Real.log Q + Real.log Real.pi - psi34

/-! ### Reciprocity -/

/-- Quadratic reciprocity for a prime `q ≡ 3 (mod 4)` and an odd prime `p`:
`(p/q) = (-q/p)`. -/
theorem legendreSym_eq_jacobiSym_neg {q p : ℕ} [Fact q.Prime] (h4 : q % 4 = 3) (hp : p.Prime)
    (hp2 : p ≠ 2) : legendreSym q p = jacobiSym (-(q : ℤ)) p := by
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hqodd : Odd q := Nat.odd_iff.mpr (by omega)
  rw [jacobiSym.legendreSym.to_jacobiSym, jacobiSym.neg _ hpodd]
  rcases Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hpodd) with h1 | h3
  · rw [ZMod.χ₄_nat_one_mod_four h1, one_mul,
      jacobiSym.quadratic_reciprocity_one_mod_four h1 hqodd]
  · rw [ZMod.χ₄_nat_three_mod_four h3,
      jacobiSym.quadratic_reciprocity_three_mod_four h3 h4]
    ring

/-- The supplement for `2`: for a prime `q ≡ 3 (mod 8)`, `(2/q) = -1`. -/
theorem legendreSym_two_of_three_mod_eight {q : ℕ} [Fact q.Prime] (h8 : q % 8 = 3) :
    legendreSym q 2 = -1 := by
  have hq2 : q ≠ 2 := by omega
  rw [legendreSym.at_two hq2, ZMod.χ₈_nat_eq_if_mod_eight]
  have h2 : q % 2 ≠ 0 := by omega
  have h17 : ¬ (q % 8 = 1 ∨ q % 8 = 7) := by omega
  simp only [h2, h17, ite_false]

/-- A prime `p < q` that does not split in `ℚ(√-q)` is inert: `(p/q) = -1`. -/
theorem legendreSym_eq_neg_one_of_not_splits {q p : ℕ} [Fact q.Prime] (h4 : q % 4 = 3)
    (hp : p.Prime) (hpq : p < q) (hns : ¬ Splits q p) : legendreSym q p = -1 := by
  by_cases hp2 : p = 2
  · subst hp2
    have h8 : q % 8 = 3 := by
      have h7 : ¬ q % 8 = 7 := by simpa [Splits] using hns
      omega
    exact_mod_cast legendreSym_two_of_three_mod_eight h8
  · have hJ : jacobiSym (-(q : ℤ)) p ≠ 1 := by simpa [Splits, hp2] using hns
    have hne : (((p : ℕ) : ℤ) : ZMod q) ≠ 0 := by
      rw [Int.cast_natCast, Ne, ZMod.natCast_eq_zero_iff]
      exact fun hdvd => absurd (Nat.le_of_dvd hp.pos hdvd) (not_le.mpr hpq)
    rcases legendreSym.eq_one_or_neg_one q hne with h | h
    · exact absurd (by rw [← legendreSym_eq_jacobiSym_neg h4 hp hp2, h]) hJ
    · exact h

/-- Multiplicativity: `(p^k / q) = (p/q)^k`. -/
theorem legendreSym_natCast_pow (q : ℕ) [Fact q.Prime] (p k : ℕ) :
    legendreSym q ((p ^ k : ℕ) : ℤ) = legendreSym q p ^ k := by
  rw [Nat.cast_pow]
  exact map_pow (legendreSym.hom q) (p : ℤ) k

/-! ### The prime-power side when every prime below `X` is inert -/

/-- If no prime below `X` splits in `ℚ(√-q)` (with `X ≤ q`), then the prime-power side of the
explicit formula is `inertSum f X`. -/
theorem primeSum_eq_inertSum {q : ℕ} [Fact q.Prime] (h4 : q % 4 = 3) (f : ℝ → ℝ) {X : ℕ}
    (hXq : X ≤ q) (hns : ∀ p, p.Prime → p < X → ¬ Splits q p) :
    primeSum q f X = inertSum f X := by
  unfold primeSum inertSum
  congr 1
  refine Finset.sum_congr rfl fun n hn => ?_
  have hnX : n < X := Finset.mem_range.mp hn
  by_cases hpp : IsPrimePow n
  · obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff n).mp hpp
    have hpX : p < X := lt_of_le_of_lt (Nat.le_self_pow hk.ne' p) hnX
    have hleg : legendreSym q ((p ^ k : ℕ) : ℤ) = (-1) ^ k := by
      rw [legendreSym_natCast_pow,
        legendreSym_eq_neg_one_of_not_splits h4 hp (lt_of_lt_of_le hpX hXq) (hns p hp hpX)]
    rw [hleg, hp.pow_minFac hk.ne', Nat.factorization_pow_self hp]
    push_cast
    rfl
  · rw [ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hpp]
    simp

/-! ### The row statement -/

/-- A row with positive margin: under the explicit-formula inequality and GRH, every prime
`q ≡ 3 (mod 4)` with `X < q ≤ Q` has a prime below `X` that splits in `ℚ(√-q)`. -/
theorem split_prime_of_row (hEF : ExplicitFormulaBound) (hGRH : GRHPrimeConductor)
    (Q X : ℕ) (v : List ℝ) (hX : 2 ≤ X) (hv : ∃ t ∈ v, t ≠ 0) (hm : 0 < rowMargin Q X v)
    (q : ℕ) (hq : q.Prime) (h4 : q % 4 = 3) (hXq : X < q) (hqQ : q ≤ Q) :
    ∃ p, p.Prime ∧ p < X ∧ Splits q p := by
  by_contra hcon
  have hns : ∀ p, p.Prime → p < X → ¬ Splits q p := fun p hp hpX hs => hcon ⟨p, hp, hpX, hs⟩
  have : Fact q.Prime := ⟨hq⟩
  have hbound := hEF q h4 (hGRH q h4) X v hX hv
  rw [primeSum_eq_inertSum h4 _ hXq.le hns] at hbound
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq.pos
  have hlog : Real.log ((q : ℝ) / π) ≤ Real.log Q - Real.log π := by
    rw [Real.log_div hq0.ne' Real.pi_pos.ne']
    have : Real.log (q : ℝ) ≤ Real.log (Q : ℝ) :=
      Real.log_le_log hq0 (by exact_mod_cast hqQ)
    linarith
  unfold rowMargin at hm
  linarith

/-- The certificate statement (the shape of `Computed.cert` and `ComputedLow.certLow`) for any
list of rows with positive margins, from the explicit-formula inequality and GRH. -/
theorem cert_of_margins (hEF : ExplicitFormulaBound) (hGRH : GRHPrimeConductor)
    (rows : List Row)
    (hrows : ∀ r ∈ rows, 2 ≤ r.X ∧ ∃ v : List ℝ, (∃ t ∈ v, t ≠ 0) ∧ 0 < rowMargin r.Q r.X v) :
    ∀ r ∈ rows, ∀ q, q.Prime → q % 4 = 3 → r.X < q → q ≤ r.Q →
      ∃ p, p.Prime ∧ p < r.X ∧ Splits q p := by
  intro r hr q hq h4 hXq hqQ
  obtain ⟨hX, v, hv, hm⟩ := hrows r hr
  exact split_prime_of_row hEF hGRH r.Q r.X v hX hv hm q hq h4 hXq hqQ

end Exp7
