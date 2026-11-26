import Exp7Lean.Cond.Reduce

/-!
Exponent 7: threshold ("robust") certificates.

Let `q ≡ 3 (mod 4)` be a prime, `X < q`, and suppose that no prime below a threshold `T` splits in
`ℚ(√-q)`.  Nothing is assumed about the primes `T ≤ l < X`.  Then the character `χ = (·/q)` is
`-1` at the primes `l < T` and `±1` at the primes `T ≤ l < X`, so with
`primeT f X l σ = 2 log l ∑_{k ≥ 1, l^k < X} σ^k f(k log l) / l^{k/2}` (`Cond/Reduce.lean`)

    primeSum q f X = ∑_{l < X} primeT f X l (χ l) ≥ robustSum T f X,
    robustSum T f X = ∑_{l < T} primeT f X l (-1)
                        + ∑_{T ≤ l < X} min (primeT f X l 1) (primeT f X l (-1)).

Equivalently `robustSum T f X = inertSum f X - ∑_{T ≤ l < X} max 0 (d_l)` with
`d_l = primeT f X l (-1) - primeT f X l 1` (`robustSum_eq_inertSum_sub`).  With the
explicit-formula inequality, `0 < robustMargin T Q X v` forces `Q < q` (`lt_of_robustMargin`).

Nothing here is assumed: `ExplicitFormulaBound` and `GRHPrimeConductor` occur only as explicit
hypotheses.
-/

namespace Exp7

open Real

/-- The least possible value of the prime-power side when no prime below `T` splits:
`χ(l) = -1` for `l < T` and the worse sign for every prime `T ≤ l < X`. -/
noncomputable def robustSum (T : ℕ) (f : ℝ → ℝ) (X : ℕ) : ℝ :=
  ∑ l ∈ (Finset.range X).filter Nat.Prime,
    if l < T then primeT f X l (-1) else min (primeT f X l 1) (primeT f X l (-1))

/-- The margin of a threshold certificate: positive margin contradicts the explicit-formula
inequality for every prime `q ≤ Q` (`q > X`) without split prime below `T`. -/
noncomputable def robustMargin (T Q X : ℕ) (v : List ℝ) : ℝ :=
  robustSum T (autocorr (stepFn (Real.log X) v)) X - Jterm (autocorr (stepFn (Real.log X) v))
    - Real.log Q + Real.log Real.pi - psi34

/-- If no prime below `T` splits in `ℚ(√-q)` and `X ≤ q`, the prime-power side of the explicit
formula is at least `robustSum T f X`. -/
theorem robustSum_le_primeSum {q : ℕ} [Fact q.Prime] (h4 : q % 4 = 3) (f : ℝ → ℝ) {T X : ℕ}
    (hXq : X ≤ q) (hin : ∀ l, l.Prime → l < T → ¬ Splits q l) :
    robustSum T f X ≤ primeSum q f X := by
  rw [primeSum_eq_sum_primeT]
  unfold robustSum
  refine Finset.sum_le_sum fun l hl => ?_
  obtain ⟨hlX, hlp⟩ := Finset.mem_filter.mp hl
  have hlq : l < q := lt_of_lt_of_le (Finset.mem_range.mp hlX) hXq
  split_ifs with h1
  · rw [legendreSym_eq_neg_one_of_not_splits h4 hlp hlq (hin l hlp h1)]
    push_cast
    exact le_rfl
  · have hne : (((l : ℕ) : ℤ) : ZMod q) ≠ 0 := by
      rw [Int.cast_natCast, Ne, ZMod.natCast_eq_zero_iff]
      exact fun hdvd => absurd (Nat.le_of_dvd hlp.pos hdvd) (not_le.mpr hlq)
    rcases legendreSym.eq_one_or_neg_one q hne with h | h
    · rw [h]
      push_cast
      exact min_le_left _ _
    · rw [h]
      push_cast
      exact min_le_right _ _

/-- **Threshold certificate.** If `robustMargin T Q X v > 0`, then under the explicit-formula
inequality and GRH every prime `q ≡ 3 (mod 4)`, `q > X`, without split prime below `T`
satisfies `q > Q`. -/
theorem lt_of_robustMargin (hEF : ExplicitFormulaBound) (hGRH : GRHPrimeConductor)
    (T Q X : ℕ) (v : List ℝ) (hX : 2 ≤ X) (hv : ∃ t ∈ v, t ≠ 0)
    (hm : 0 < robustMargin T Q X v)
    (q : ℕ) (hq : q.Prime) (h4 : q % 4 = 3) (hXq : X < q)
    (hin : ∀ l, l.Prime → l < T → ¬ Splits q l) : Q < q := by
  by_contra hcon
  have hqQ : q ≤ Q := not_lt.mp hcon
  have : Fact q.Prime := ⟨hq⟩
  have hbound := hEF q h4 (hGRH q h4) X v hX hv
  have hcs := robustSum_le_primeSum h4 (autocorr (stepFn (Real.log X) v)) hXq.le hin
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq.pos
  have hlog : Real.log ((q : ℝ) / π) ≤ Real.log Q - Real.log π := by
    rw [Real.log_div hq0.ne' Real.pi_pos.ne']
    have : Real.log (q : ℝ) ≤ Real.log (Q : ℝ) :=
      Real.log_le_log hq0 (by exact_mod_cast hqQ)
    linarith
  unfold robustMargin at hm
  linarith

/-! ### Comparison with the other sums -/

/-- The threshold bound with `T = p` is at most the bound that also uses `χ(p) = 1`. -/
theorem robustSum_le_condSum (p : ℕ) (f : ℝ → ℝ) (X : ℕ) : robustSum p f X ≤ condSum p f X := by
  unfold robustSum condSum
  refine Finset.sum_le_sum fun l _ => ?_
  split_ifs with h1 h2
  · exact le_rfl
  · exact min_le_left _ _
  · exact le_rfl

/-- The all-inert value of the prime-power side, prime by prime. -/
theorem inertSum_eq_sum_primeT (f : ℝ → ℝ) (X : ℕ) :
    inertSum f X = ∑ l ∈ (Finset.range X).filter Nat.Prime, primeT f X l (-1) := by
  unfold inertSum
  set G : ℕ → ℝ := fun n => ArithmeticFunction.vonMangoldt n *
    (-1 : ℝ) ^ (n.factorization n.minFac) * f (Real.log n) / Real.sqrt n with hG
  have hG0 : ∀ n, ¬ IsPrimePow n → G n = 0 := by
    intro n hn
    simp only [hG]
    rw [ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hn]
    simp
  rw [sum_range_eq_sum_primePow G hG0 X X Nat.lt_two_pow_self.le, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l hl => ?_
  have hlp : l.Prime := (Finset.mem_filter.mp hl).2
  unfold primeT
  congr 1
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk1 : 1 ≤ k := (Finset.mem_Ico.mp hk).1
  split_ifs with h
  · simp only [hG, condTerm]
    rw [ArithmeticFunction.vonMangoldt_apply_pow (by omega),
      ArithmeticFunction.vonMangoldt_apply_prime hlp, hlp.pow_minFac (by omega),
      Nat.factorization_pow_self hlp]
  · rfl

/-- `robustSum` is `inertSum` minus the positive parts of
`d_l = primeT f X l (-1) - primeT f X l 1` over the primes `T ≤ l < X`. -/
theorem robustSum_eq_inertSum_sub (T : ℕ) (f : ℝ → ℝ) (X : ℕ) :
    robustSum T f X = inertSum f X - ∑ l ∈ (Finset.range X).filter Nat.Prime,
      if l < T then 0 else max 0 (primeT f X l (-1) - primeT f X l 1) := by
  rw [inertSum_eq_sum_primeT, ← Finset.sum_sub_distrib]
  unfold robustSum
  refine Finset.sum_congr rfl fun l _ => ?_
  split_ifs with h
  · rw [sub_zero]
  · rcases le_total (primeT f X l 1) (primeT f X l (-1)) with h1 | h1
    · rw [min_eq_left h1, max_eq_right (sub_nonneg.mpr h1)]
      ring
    · rw [min_eq_right h1, max_eq_left (sub_nonpos.mpr h1)]
      ring

end Exp7

#print axioms Exp7.lt_of_robustMargin
#print axioms Exp7.robustSum_eq_inertSum_sub
