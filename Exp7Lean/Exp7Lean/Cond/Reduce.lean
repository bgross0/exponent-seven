import Exp7Lean.Analytic.Reduce

/-!
Exponent 7: conditional certificates, using the least split prime.

Let `q ≡ 3 (mod 4)` be a prime and `p < X < q` the least prime that splits in `ℚ(√-q)`.  Then the
character `χ = (·/q)` is `-1` at the primes `l < p`, `+1` at `p`, and `±1` (unknown) at the primes
`p < l < X`.  Writing `primeT f X l σ = 2 log l ∑_{k ≥ 1, l^k < X} σ^k f(k log l) / l^{k/2}` for the
contribution of the prime `l` to the prime-power side of the explicit formula when `χ(l) = σ`,

    primeSum q f X = ∑_{l < X} primeT f X l (χ l) ≥ condSum p f X,

where `condSum` takes `σ = -1` below `p`, `σ = +1` at `p` and the worse of the two signs above `p`.
The explicit-formula inequality then gives `condSum ≤ log (q/π) + ψ(3/4) + J_f`, so a positive
`condMargin p Q X v` forces `Q < q` (`lt_of_condMargin`).

Nothing here is assumed: `ExplicitFormulaBound` and `GRHPrimeConductor` occur only as explicit
hypotheses.
-/

namespace Exp7

open Real

/-- The term at the prime power `l ^ k` when `χ(l) = σ` (without the factor `2`). -/
noncomputable def condTerm (f : ℝ → ℝ) (l : ℕ) (σ : ℝ) (k : ℕ) : ℝ :=
  Real.log l * σ ^ k * f (Real.log ((l ^ k : ℕ) : ℝ)) / Real.sqrt ((l ^ k : ℕ) : ℝ)

/-- The contribution `T_l(σ)` of the prime `l` to the prime-power side when `χ(l) = σ`:
`2 log l ∑_{k ≥ 1, l^k < X} σ^k f(k log l) / l^{k/2}`. -/
noncomputable def primeT (f : ℝ → ℝ) (X l : ℕ) (σ : ℝ) : ℝ :=
  2 * ∑ k ∈ Finset.Ico 1 X, if l ^ k < X then condTerm f l σ k else 0

/-- The least possible value of the prime-power side when `p` is the least split prime:
`χ(l) = -1` for `l < p`, `χ(p) = 1`, and the worse sign for every prime `p < l < X`. -/
noncomputable def condSum (p : ℕ) (f : ℝ → ℝ) (X : ℕ) : ℝ :=
  ∑ l ∈ (Finset.range X).filter Nat.Prime,
    if l < p then primeT f X l (-1) else if l = p then primeT f X l 1
    else min (primeT f X l 1) (primeT f X l (-1))

/-- The margin of a conditional certificate: positive margin contradicts the explicit-formula
inequality for every prime `q ≤ Q` whose least split prime is `p`. -/
noncomputable def condMargin (p Q X : ℕ) (v : List ℝ) : ℝ :=
  condSum p (autocorr (stepFn (Real.log X) v)) X - Jterm (autocorr (stepFn (Real.log X) v))
    - Real.log Q + Real.log Real.pi - psi34

/-! ### Sums over prime powers -/

/-- The exponents `k ≥ 1` with `l ^ k < X` all lie below `K` as soon as `X ≤ 2 ^ K`. -/
theorem sum_Ico_pow_lt (g : ℕ → ℝ) {l X K K' : ℕ} (hl : 2 ≤ l) (hK : X ≤ 2 ^ K)
    (hK' : X ≤ 2 ^ K') :
    (∑ k ∈ Finset.Ico 1 K, if l ^ k < X then g k else 0) =
      ∑ k ∈ Finset.Ico 1 K', if l ^ k < X then g k else 0 := by
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  congr 1
  ext k
  simp only [Finset.mem_filter, Finset.mem_Ico]
  have key : ∀ M : ℕ, X ≤ 2 ^ M → l ^ k < X → k < M := by
    intro M hM hk
    have h2 : 2 ^ k < 2 ^ M :=
      lt_of_le_of_lt (Nat.pow_le_pow_left hl k) (lt_of_lt_of_le hk hM)
    exact (Nat.pow_lt_pow_iff_right (by norm_num)).mp h2
  constructor
  · rintro ⟨⟨h1, -⟩, h2⟩
    exact ⟨⟨h1, key K' hK' h2⟩, h2⟩
  · rintro ⟨⟨h1, -⟩, h2⟩
    exact ⟨⟨h1, key K hK h2⟩, h2⟩

/-- `primeT` with any sufficient bound `K` on the exponents. -/
theorem primeT_eq (f : ℝ → ℝ) {X l K : ℕ} (σ : ℝ) (hl : 2 ≤ l) (hK : X ≤ 2 ^ K) :
    primeT f X l σ = 2 * ∑ k ∈ Finset.Ico 1 K, if l ^ k < X then condTerm f l σ k else 0 := by
  unfold primeT
  rw [sum_Ico_pow_lt _ hl Nat.lt_two_pow_self.le hK]

/-- A sum over `n < X` of a function vanishing outside the prime powers is a sum over the primes
`l < X` and the exponents `1 ≤ k < K` with `l ^ k < X`, as soon as `X ≤ 2 ^ K`. -/
theorem sum_range_eq_sum_primePow (G : ℕ → ℝ) (hG : ∀ n, ¬ IsPrimePow n → G n = 0) (X K : ℕ)
    (hK : X ≤ 2 ^ K) :
    ∑ n ∈ Finset.range X, G n = ∑ l ∈ (Finset.range X).filter Nat.Prime, ∑ k ∈ Finset.Ico 1 K,
      if l ^ k < X then G (l ^ k) else 0 := by
  set S : Finset (ℕ × ℕ) :=
    (((Finset.range X).filter Nat.Prime) ×ˢ (Finset.Ico 1 K)).filter (fun x => x.1 ^ x.2 < X)
    with hS
  have hmem : ∀ x : ℕ × ℕ, x ∈ S ↔ (x.1 < X ∧ x.1.Prime) ∧ (1 ≤ x.2 ∧ x.2 < K) ∧
      x.1 ^ x.2 < X := by
    intro x
    simp only [hS, Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_Ico]
    tauto
  have hinj : Set.InjOn (fun x : ℕ × ℕ => x.1 ^ x.2) (S : Set (ℕ × ℕ)) := by
    rintro ⟨p, k⟩ hx ⟨p', k'⟩ hx' h
    have hx1 := (hmem _).mp (Finset.mem_coe.mp hx)
    have hx2 := (hmem _).mp (Finset.mem_coe.mp hx')
    simp only at hx1 hx2 h
    have hpp : p = p' :=
      eq_of_prime_pow_eq hx1.1.2.prime hx2.1.2.prime (by omega) h
    subst hpp
    have hkk : k = k' := Nat.pow_right_injective hx1.1.2.two_le h
    rw [hkk]
  calc ∑ n ∈ Finset.range X, G n
      = ∑ n ∈ S.image (fun x : ℕ × ℕ => x.1 ^ x.2), G n := by
        symm
        apply Finset.sum_subset
        · intro n hn
          obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hn
          exact Finset.mem_range.mpr ((hmem x).mp hx).2.2
        · intro n hn hnot
          by_cases hpp : IsPrimePow n
          · exfalso
            obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff n).mp hpp
            have hnX : p ^ k < X := Finset.mem_range.mp hn
            apply hnot
            refine Finset.mem_image.mpr ⟨(p, k), (hmem _).mpr ⟨⟨?_, hp⟩, ⟨hk, ?_⟩, hnX⟩, rfl⟩
            · exact lt_of_le_of_lt (Nat.le_self_pow hk.ne' p) hnX
            · have h2 : 2 ^ k < 2 ^ K :=
                lt_of_le_of_lt (Nat.pow_le_pow_left hp.two_le k) (lt_of_lt_of_le hnX hK)
              exact (Nat.pow_lt_pow_iff_right (by norm_num)).mp h2
          · exact hG n hpp
    _ = ∑ x ∈ S, G (x.1 ^ x.2) := Finset.sum_image hinj
    _ = ∑ x ∈ ((Finset.range X).filter Nat.Prime) ×ˢ (Finset.Ico 1 K),
          if x.1 ^ x.2 < X then G (x.1 ^ x.2) else 0 := by
        rw [hS, Finset.sum_filter]
    _ = _ := Finset.sum_product _ _ _

/-- The prime-power side of the explicit formula, prime by prime. -/
theorem primeSum_eq_sum_primeT (q : ℕ) [Fact q.Prime] (f : ℝ → ℝ) (X : ℕ) :
    primeSum q f X =
      ∑ l ∈ (Finset.range X).filter Nat.Prime, primeT f X l ((legendreSym q l : ℤ) : ℝ) := by
  unfold primeSum
  set G : ℕ → ℝ := fun n => ArithmeticFunction.vonMangoldt n * ((legendreSym q n : ℤ) : ℝ) *
    f (Real.log n) / Real.sqrt n with hG
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
      ArithmeticFunction.vonMangoldt_apply_prime hlp, legendreSym_natCast_pow]
    push_cast
    rfl
  · rfl

/-! ### The character at the least split prime -/

/-- A prime `p` that splits in `ℚ(√-q)` has `(p/q) = 1`. -/
theorem legendreSym_eq_one_of_splits {q p : ℕ} [Fact q.Prime] (h4 : q % 4 = 3) (hp : p.Prime)
    (hs : Splits q p) : legendreSym q p = 1 := by
  by_cases hp2 : p = 2
  · subst hp2
    have h8 : q % 8 = 7 := by simpa [Splits] using hs
    have hq2 : q ≠ 2 := by omega
    have h := legendreSym.at_two hq2
    rw [ZMod.χ₈_nat_eq_if_mod_eight] at h
    have h2 : q % 2 ≠ 0 := by omega
    have h17 : q % 8 = 1 ∨ q % 8 = 7 := Or.inr h8
    simp only [h2, h17, ite_false, ite_true] at h
    exact_mod_cast h
  · have hJ : jacobiSym (-(q : ℤ)) p = 1 := by simpa [Splits, hp2] using hs
    rw [legendreSym_eq_jacobiSym_neg h4 hp hp2, hJ]

/-- If `p` is the least prime that splits in `ℚ(√-q)` and `X ≤ q`, the prime-power side of the
explicit formula is at least `condSum p f X`. -/
theorem condSum_le_primeSum {q : ℕ} [Fact q.Prime] (h4 : q % 4 = 3) (f : ℝ → ℝ) {p X : ℕ}
    (hp : p.Prime) (hXq : X ≤ q) (hsplit : Splits q p)
    (hleast : ∀ l, l.Prime → l < p → ¬ Splits q l) : condSum p f X ≤ primeSum q f X := by
  rw [primeSum_eq_sum_primeT]
  unfold condSum
  refine Finset.sum_le_sum fun l hl => ?_
  obtain ⟨hlX, hlp⟩ := Finset.mem_filter.mp hl
  have hlq : l < q := lt_of_lt_of_le (Finset.mem_range.mp hlX) hXq
  split_ifs with h1 h2
  · rw [legendreSym_eq_neg_one_of_not_splits h4 hlp hlq (hleast l hlp h1)]
    push_cast
    exact le_rfl
  · subst h2
    rw [legendreSym_eq_one_of_splits h4 hp hsplit]
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

/-! ### The reduction -/

/-- **Conditional certificate.** If `condMargin p Q X v > 0`, then under the explicit-formula
inequality and GRH every prime `q ≡ 3 (mod 4)`, `q > X`, whose least split prime is `p`
satisfies `q > Q`. -/
theorem lt_of_condMargin (hEF : ExplicitFormulaBound) (hGRH : GRHPrimeConductor)
    (p Q X : ℕ) (v : List ℝ) (hp : p.Prime) (hpX : p < X) (hv : ∃ t ∈ v, t ≠ 0)
    (hm : 0 < condMargin p Q X v)
    (q : ℕ) (hq : q.Prime) (h4 : q % 4 = 3) (hXq : X < q)
    (hsplit : Splits q p) (hleast : ∀ l, l.Prime → l < p → ¬ Splits q l) : Q < q := by
  by_contra hcon
  have hqQ : q ≤ Q := not_lt.mp hcon
  have : Fact q.Prime := ⟨hq⟩
  have hX : 2 ≤ X := le_trans hp.two_le hpX.le
  have hbound := hEF q h4 (hGRH q h4) X v hX hv
  have hcs := condSum_le_primeSum h4 (autocorr (stepFn (Real.log X) v)) hp hXq.le hsplit hleast
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq.pos
  have hlog : Real.log ((q : ℝ) / π) ≤ Real.log Q - Real.log π := by
    rw [Real.log_div hq0.ne' Real.pi_pos.ne']
    have : Real.log (q : ℝ) ≤ Real.log (Q : ℝ) :=
      Real.log_le_log hq0 (by exact_mod_cast hqQ)
    linarith
  unfold condMargin at hm
  linarith

end Exp7

#print axioms Exp7.lt_of_condMargin
