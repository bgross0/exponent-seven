import Exp7Lean.Final4
import Exp7Lean.Cond.RobustBounds

/-!
Exponent 7: Theorem A with the reduced main search.

The robust certificate rows (`Cond/`) exclude 137 of the 465 candidate least split primes outright
and raise the lower bound for the others from `Qlo p` to `QloR p`. They apply to prime `q` under
GRH, so the search statement is restated here for the primes that remain. The least-split-prime
argument of `Main.lean` is repeated for a structure without the search field.
-/

namespace Exp7

open Classical

/-- The reduced main search: the 328 primes `701 ≤ p ≤ 3229` not excluded analytically, with the
lower bound `QloR p`. -/
def SearchHighR : Prop :=
  ∀ p, p.Prime → 701 ≤ p → p ≤ 3229 → p ∉ excludedPrimes → ∀ x y q : ℕ, 1 ≤ y →
    4 * p ^ 7 = x ^ 2 + q * y ^ 2 → QloR p ≤ q → q % 8 = 3 →
    (∀ l, l.Prime → 3 ≤ l → l < p → jacobiSym (-(q : ℤ)) l = -1) → False

/-- The original search statement implies the reduced one. -/
theorem searchHighR_of_searchHigh (h : SearchHigh) : SearchHighR := by
  intro p hp h701 h3229 _ x y q hy he hQ h8 hj
  exact h p hp h701 (by omega) x y q hy he (le_trans (le_max_left _ _) hQ) h8 hj

namespace R

/-- Step 1 and the certificate rows, without the search. -/
structure Core (IsExp7 : ℕ → Prop) : Prop where
  normEq : ∀ q, q.Prime → q % 4 = 3 → IsExp7 q → ∀ p, p.Prime → p ≠ q → Splits q p →
    ∃ x y : ℕ, 1 ≤ y ∧ 4 * p ^ 7 = x ^ 2 + q * y ^ 2
  cert : ∀ r ∈ allRows, ∀ q, q.Prime → q % 4 = 3 → r.X < q → q ≤ r.Q →
    ∃ p, p.Prime ∧ p < r.X ∧ Splits q p

section

variable {IsExp7 : ℕ → Prop} (H : Core IsExp7) {q : ℕ} (hq : q.Prime) (h4 : q % 4 = 3)
  (hE : IsExp7 q)
include H hq h4 hE

lemma le_of_splits {p : ℕ} (hp : p.Prime) (hpq : p ≠ q) (hs : Splits q p) : q ≤ 4 * p ^ 7 := by
  obtain ⟨x, y, hy, he⟩ := H.normEq q hq h4 hE p hp hpq hs
  have h1 : q ≤ q * y ^ 2 := Nat.le_mul_of_pos_right q (by positivity)
  omega

lemma row_step {r : Row} (hr : r ∈ allRows) (hX : r.X < q) (hQ : q ≤ r.Q) {P : ℕ}
    (hP : ∀ p, p.Prime → p < r.X → p ≤ P) : q ≤ 4 * P ^ 7 := by
  obtain ⟨p, hp, hpX, hs⟩ := H.cert r hr q hq h4 hX hQ
  have hle := le_of_splits H hq h4 hE hp (by omega) hs
  have : p ^ 7 ≤ P ^ 7 := Nat.pow_le_pow_left (hP p hp hpX) 7
  omega

variable (hlow : QLOW ≤ q)
include hlow

omit H hq h4 hE in
lemma X_lt_q {r : Row} (hr : r ∈ allRows) : r.X < q := by
  have := allRows_X_le r hr
  have : 6362 < QLOW := by norm_num [QLOW]
  omega

lemma not_splits_small {p : ℕ} (hp : p.Prime) (hp691 : p ≤ 691) : ¬ Splits q p := by
  intro hs
  have hpq : p ≠ q := by
    have : 691 < QLOW := by norm_num [QLOW]
    omega
  have h1 := le_of_splits H hq h4 hE hp hpq hs
  have h2 : p ^ 7 ≤ 691 ^ 7 := Nat.pow_le_pow_left hp691 7
  have h3 := small_bound
  omega

lemma mod8 : q % 8 = 3 := by
  have h2 := not_splits_small H hq h4 hE hlow Nat.prime_two (by norm_num)
  rw [splits_two_iff] at h2
  omega

lemma exists_split_le_4297 (hhi : q ≤ QTOP) : ∃ p, p.Prime ∧ p ≤ 4297 ∧ Splits q p := by
  have mem : ∀ r ∈ bootstrapRows, r ∈ allRows := fun r hr => List.mem_append_left _ hr
  have h1 : q ≤ 4 * 6361 ^ 7 :=
    row_step H hq h4 hE (r := ⟨10 ^ 32, 6362⟩) (mem _ (by simp [bootstrapRows]))
      (X_lt_q hlow (mem _ (by simp [bootstrapRows])))
      (by simpa [QTOP] using hhi) (fun p _ hp => by dsimp only at hp; omega)
  have h2 : q ≤ 4 * 4679 ^ 7 :=
    row_step H hq h4 hE (r := ⟨4 * 6361 ^ 7, 4690⟩) (mem _ (by simp [bootstrapRows]))
      (X_lt_q hlow (mem _ (by simp [bootstrapRows]))) h1 (le_of_gap gap_4679)
  have h3 : q ≤ 4 * 4391 ^ 7 :=
    row_step H hq h4 hE (r := ⟨4 * 4679 ^ 7, 4393⟩) (mem _ (by simp [bootstrapRows]))
      (X_lt_q hlow (mem _ (by simp [bootstrapRows]))) h2 (le_of_gap gap_4391)
  have h4' : q ≤ 4 * 4327 ^ 7 :=
    row_step H hq h4 hE (r := ⟨4 * 4391 ^ 7, 4333⟩) (mem _ (by simp [bootstrapRows]))
      (X_lt_q hlow (mem _ (by simp [bootstrapRows]))) h3 (le_of_gap gap_4327)
  have h5 : q ≤ 4 * 4297 ^ 7 :=
    row_step H hq h4 hE (r := ⟨4 * 4327 ^ 7, 4319⟩) (mem _ (by simp [bootstrapRows]))
      (X_lt_q hlow (mem _ (by simp [bootstrapRows]))) h4' (le_of_gap gap_4297)
  obtain ⟨p, hp, hpX, hs⟩ := H.cert ⟨4 * 4297 ^ 7, 4312⟩ (mem _ (by simp [bootstrapRows]))
    q hq h4 (X_lt_q hlow (mem _ (by simp [bootstrapRows]))) h5
  exact ⟨p, hp, le_of_gap (b := 4312) (fun n h1 h2 => gap_4297 n h1 (by omega)) p hp hpX, hs⟩

end

end R

/-- **Theorem A** with the reduced search: no prime `q ≡ 3 (mod 4)` with `3.1·10^20 ≤ q ≤ 10^32`
has class group of exponent 7, assuming GRH for the characters of prime conductor and completeness
of the reduced main search (328 primes). -/
theorem theoremA_reduced (hGRH : GRHPrimeConductor) (hS : SearchHighR) {q : ℕ} (hq : q.Prime)
    (h4 : q % 4 = 3) (hlow : QLOW ≤ q) (hhi : q ≤ QTOP) : ¬ IsExp7 q := by
  intro hE
  have H : R.Core IsExp7 :=
    ⟨fun q hq h4 hE p hp hpq hs => by
        obtain ⟨x, y, hy, -, he⟩ := normEq_classGroup q hq h4 hE p hp hpq hs
        exact ⟨x, y, hy, he⟩,
      cert_of_margins EF.explicitFormulaBound hGRH allRows rowMargins_allRows⟩
  have hex : ∃ p, p.Prime ∧ Splits q p := by
    obtain ⟨p, hp, -, hs⟩ := R.exists_split_le_4297 H hq h4 hE hlow hhi
    exact ⟨p, hp, hs⟩
  set p := Nat.find hex with hpdef
  obtain ⟨hp, hs⟩ : p.Prime ∧ Splits q p := Nat.find_spec hex
  have hmin : ∀ m < p, ¬ (m.Prime ∧ Splits q m) := fun m hm => Nat.find_min hex hm
  have hp4297 : p ≤ 4297 := by
    obtain ⟨p', hp', hle, hs'⟩ := R.exists_split_le_4297 H hq h4 hE hlow hhi
    exact le_trans (Nat.find_min' hex ⟨hp', hs'⟩) hle
  have hp701 : 701 ≤ p := by
    by_contra hlt
    have : p ≤ 691 := le_of_gap gap_691 p hp (by omega)
    exact R.not_splits_small H hq h4 hE hlow hp this hs
  have hQL : QLOW = 310000000000000000000 := by norm_num [QLOW]
  have hpq : p ≠ q := by omega
  obtain ⟨x, y, hy, he⟩ := H.normEq q hq h4 hE p hp hpq hs
  have h8 := R.mod8 H hq h4 hE hlow
  have hjac : ∀ l, l.Prime → 3 ≤ l → l < p → jacobiSym (-(q : ℤ)) l = -1 := by
    intro l hl hl3 hlp
    have hns : ¬ Splits q l := fun h => hmin l hlp ⟨hl, h⟩
    rw [splits_odd_iff q (by omega)] at hns
    have hlq : l ≠ q := by omega
    have hcop : (-(q : ℤ)).gcd l = 1 := by
      rw [Int.neg_gcd, Int.gcd_natCast_natCast]
      exact (Nat.coprime_primes hq hl).mpr (Ne.symm hlq)
    rcases jacobiSym.eq_one_or_neg_one hcop with h | h
    · exact absurd h hns
    · exact h
  by_cases hmem : p ∈ excludedPrimes
  · exact excluded_search hGRH p hmem x y q hy he hq (by omega) h8 hjac
  · exact hS p hp hp701 (le_3229_of_not_mem hp hp4297 hmem) hmem x y q hy he
      (QloR_le_of_jacobi hGRH hq h8 hlow hjac) h8 hjac

end Exp7
