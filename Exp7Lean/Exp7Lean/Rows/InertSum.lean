import Exp7Lean.Analytic.Reduce

/-!
Certificate rows, step 1: `inertSum` as a sum over primes `p < X` and exponents `k ≥ 1`
with `p ^ k < X`.
-/

namespace Exp7.Rows

open Real

/-- The term of `inertSum` at the prime power `p ^ k` (without the factor `2`). -/
noncomputable def ppTerm (f : ℝ → ℝ) (p k : ℕ) : ℝ :=
  Real.log p * (-1 : ℝ) ^ k * f (Real.log ((p ^ k : ℕ) : ℝ)) / Real.sqrt ((p ^ k : ℕ) : ℝ)

/-- `inertSum f X` is a sum over the primes `p < X` and the exponents `1 ≤ k < K` with
`p ^ k < X`, as soon as `X ≤ 2 ^ K`. -/
theorem inertSum_eq (f : ℝ → ℝ) (X K : ℕ) (hK : X ≤ 2 ^ K) :
    inertSum f X = 2 * ∑ p ∈ (Finset.range X).filter Nat.Prime, ∑ k ∈ Finset.Ico 1 K,
      if p ^ k < X then ppTerm f p k else 0 := by
  unfold inertSum
  congr 1
  set G : ℕ → ℝ := fun n => ArithmeticFunction.vonMangoldt n *
    (-1 : ℝ) ^ (n.factorization n.minFac) * f (Real.log n) / Real.sqrt n with hG
  have hterm : ∀ p k : ℕ, p.Prime → 1 ≤ k → ppTerm f p k = G (p ^ k) := by
    intro p k hp hk
    simp only [hG, ppTerm]
    rw [ArithmeticFunction.vonMangoldt_apply_pow (by omega),
      ArithmeticFunction.vonMangoldt_apply_prime hp, hp.pow_minFac (by omega),
      Nat.factorization_pow_self hp]
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
          · simp only [hG]
            rw [ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hpp]
            simp
    _ = ∑ x ∈ S, G (x.1 ^ x.2) := Finset.sum_image hinj
    _ = ∑ x ∈ S, ppTerm f x.1 x.2 := by
        refine Finset.sum_congr rfl fun x hx => ?_
        have h := (hmem x).mp hx
        exact (hterm x.1 x.2 h.1.2 h.2.1.1).symm
    _ = ∑ x ∈ ((Finset.range X).filter Nat.Prime) ×ˢ (Finset.Ico 1 K),
          if x.1 ^ x.2 < X then ppTerm f x.1 x.2 else 0 := by
        rw [hS, Finset.sum_filter]
    _ = _ := Finset.sum_product _ _ _

end Exp7.Rows
