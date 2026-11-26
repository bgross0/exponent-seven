import Exp7Lean.Basic

/-!
Exponent 7: Theorem A, from three explicitly stated inputs.

Everything in this file is checked by Lean. The three fields of `Inputs` are the steps of the
note that are NOT formalized here:

* `normEq`  — Step 1 (algebraic number theory of `ℚ(√-q)`).
* `cert`    — Steps 2–3 (Guinand–Weil explicit formula under GRH, and the 51 certificate rows,
              verified outside Lean by `kernel_verify.py` and `independent/verify_fixedpoint.cjs`).
* `search`  — Step 4 (the exhaustive search, run by three independent programs).

What Lean checks: that these inputs, together with exact arithmetic, imply Theorem A. This covers
the bootstrap chain from `10^32` down to `4·4297^7`, the inertness of every prime below 701, the
existence and range of the least split prime, `q ≡ 3 (mod 8)`, the Jacobi-symbol conditions, and
the lower bounds `Qlo p` read off the ladder.
-/

namespace Exp7

open Classical

/-- The inputs established outside Lean. `IsExp7 q` stands for "the class group of `ℚ(√-q)` has
exponent 7". -/
structure Inputs (IsExp7 : ℕ → Prop) : Prop where
  /-- Step 1: if the class group has exponent 7 and `p ≠ q` splits, `(p) = 𝔭𝔭'`, then `𝔭^7 = (α)`
  with `α = (x + y√-q)/2` not rational, so `4p^7 = x² + qy²` with `y ≥ 1`. -/
  normEq : ∀ q, q.Prime → q % 4 = 3 → IsExp7 q → ∀ p, p.Prime → p ≠ q → Splits q p →
    ∃ x y : ℕ, 1 ≤ y ∧ 4 * p ^ 7 = x ^ 2 + q * y ^ 2
  /-- Steps 2–3: each certificate row `⟨Q, X⟩` forces a split prime below `X` (assuming GRH). -/
  cert : ∀ r ∈ allRows, ∀ q, q.Prime → q % 4 = 3 → r.X < q → q ≤ r.Q →
    ∃ p, p.Prime ∧ p < r.X ∧ Splits q p
  /-- Step 4: the search over the 465 primes `701 ≤ p ≤ 4297` finds no survivor. -/
  search : ∀ p, p.Prime → 701 ≤ p → p ≤ 4297 → ∀ x y q : ℕ, 1 ≤ y →
    4 * p ^ 7 = x ^ 2 + q * y ^ 2 → Qlo p ≤ q → q % 8 = 3 →
    (∀ l, l.Prime → 3 ≤ l → l < p → jacobiSym (-(q : ℤ)) l = -1) → False

/-! ### Arithmetic facts -/

lemma small_bound : 4 * 691 ^ 7 < QLOW := by norm_num [QLOW]

lemma allRows_X_le : ∀ r ∈ allRows, r.X ≤ 6362 := by decide

/-- No primes strictly between `a` and `b`, as a usable statement. -/
lemma le_of_gap {a b : ℕ} (h : ∀ n, a < n → n < b → ¬ n.Prime) :
    ∀ p, p.Prime → p < b → p ≤ a := by
  intro p hp hpb
  by_contra hpa
  exact h p (by omega) hpb hp

lemma gap_691 : ∀ n, 691 < n → n < 701 → ¬ n.Prime := by
  intro n h1 h2; interval_cases n <;> norm_num

lemma gap_4679 : ∀ n, 4679 < n → n < 4690 → ¬ n.Prime := by
  intro n h1 h2; interval_cases n <;> norm_num

lemma gap_4391 : ∀ n, 4391 < n → n < 4393 → ¬ n.Prime := by
  intro n h1 h2; interval_cases n; norm_num

lemma gap_4327 : ∀ n, 4327 < n → n < 4333 → ¬ n.Prime := by
  intro n h1 h2; interval_cases n <;> norm_num

lemma gap_4297 : ∀ n, 4297 < n → n < 4319 → ¬ n.Prime := by
  intro n h1 h2; interval_cases n <;> norm_num

lemma foldr_max_le (l : List Row) {b q : ℕ} (hb : b ≤ q) (h : ∀ r ∈ l, r.Q ≤ q) :
    l.foldr (fun r acc => max r.Q acc) b ≤ q := by
  induction l with
  | nil => simpa using hb
  | cons r t ih =>
    simp only [List.foldr_cons]
    exact max_le (h r (by simp)) (ih (fun r' hr' => h r' (by simp [hr'])))

lemma Qlo_le {p q : ℕ} (hlow : QLOW ≤ q) (h : ∀ r ∈ allRows, r.X ≤ p → r.Q ≤ q) :
    Qlo p ≤ q := by
  unfold Qlo
  refine foldr_max_le _ hlow ?_
  intro r hr
  rw [List.mem_filter] at hr
  exact h r hr.1 (by simpa using hr.2)

lemma splits_two_iff (q : ℕ) : Splits q 2 ↔ q % 8 = 7 := by simp [Splits]

lemma splits_odd_iff (q : ℕ) {l : ℕ} (hl : l ≠ 2) :
    Splits q l ↔ jacobiSym (-(q : ℤ)) l = 1 := by simp [Splits, hl]

/-! ### The argument -/

section

variable {IsExp7 : ℕ → Prop} (H : Inputs IsExp7) {q : ℕ} (hq : q.Prime) (h4 : q % 4 = 3)
  (hE : IsExp7 q)
include H hq h4 hE

/-- A split prime `p` bounds `q` by `4p^7`. -/
lemma le_of_splits {p : ℕ} (hp : p.Prime) (hpq : p ≠ q) (hs : Splits q p) : q ≤ 4 * p ^ 7 := by
  obtain ⟨x, y, hy, he⟩ := H.normEq q hq h4 hE p hp hpq hs
  have h1 : q ≤ q * y ^ 2 := Nat.le_mul_of_pos_right q (by positivity)
  omega

/-- One certificate row: `X < q ≤ Q`, and every prime below `X` is at most `P`, give `q ≤ 4P^7`. -/
lemma row_step {r : Row} (hr : r ∈ allRows) (hX : r.X < q) (hQ : q ≤ r.Q) {P : ℕ}
    (hP : ∀ p, p.Prime → p < r.X → p ≤ P) : q ≤ 4 * P ^ 7 := by
  obtain ⟨p, hp, hpX, hs⟩ := H.cert r hr q hq h4 hX hQ
  have hle := le_of_splits H hq h4 hE hp (by omega) hs
  have : p ^ 7 ≤ P ^ 7 := Nat.pow_le_pow_left (hP p hp hpX) 7
  omega

variable (hlow : QLOW ≤ q)
include hlow

lemma X_lt_q {r : Row} (hr : r ∈ allRows) : r.X < q := by
  have := allRows_X_le r hr
  have : 6362 < QLOW := by norm_num [QLOW]
  omega

/-- Every prime `p ≤ 691` is inert. -/
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

/-- The bootstrap chain: `q ≤ 10^32` implies `q ≤ 4·4297^7`, and some prime `p ≤ 4297` splits. -/
lemma exists_split_le_4297 (hhi : q ≤ QTOP) : ∃ p, p.Prime ∧ p ≤ 4297 ∧ Splits q p := by
  have mem : ∀ r ∈ bootstrapRows, r ∈ allRows := fun r hr => List.mem_append_left _ hr
  have h1 : q ≤ 4 * 6361 ^ 7 :=
    row_step H hq h4 hE (r := ⟨10 ^ 32, 6362⟩) (mem _ (by simp [bootstrapRows]))
      (X_lt_q H hq h4 hE hlow (mem _ (by simp [bootstrapRows])))
      (by simpa [QTOP] using hhi) (fun p _ hp => by dsimp only at hp; omega)
  have h2 : q ≤ 4 * 4679 ^ 7 :=
    row_step H hq h4 hE (r := ⟨4 * 6361 ^ 7, 4690⟩) (mem _ (by simp [bootstrapRows]))
      (X_lt_q H hq h4 hE hlow (mem _ (by simp [bootstrapRows]))) h1 (le_of_gap gap_4679)
  have h3 : q ≤ 4 * 4391 ^ 7 :=
    row_step H hq h4 hE (r := ⟨4 * 4679 ^ 7, 4393⟩) (mem _ (by simp [bootstrapRows]))
      (X_lt_q H hq h4 hE hlow (mem _ (by simp [bootstrapRows]))) h2 (le_of_gap gap_4391)
  have h4' : q ≤ 4 * 4327 ^ 7 :=
    row_step H hq h4 hE (r := ⟨4 * 4391 ^ 7, 4333⟩) (mem _ (by simp [bootstrapRows]))
      (X_lt_q H hq h4 hE hlow (mem _ (by simp [bootstrapRows]))) h3 (le_of_gap gap_4327)
  have h5 : q ≤ 4 * 4297 ^ 7 :=
    row_step H hq h4 hE (r := ⟨4 * 4327 ^ 7, 4319⟩) (mem _ (by simp [bootstrapRows]))
      (X_lt_q H hq h4 hE hlow (mem _ (by simp [bootstrapRows]))) h4' (le_of_gap gap_4297)
  obtain ⟨p, hp, hpX, hs⟩ := H.cert ⟨4 * 4297 ^ 7, 4312⟩ (mem _ (by simp [bootstrapRows]))
    q hq h4 (X_lt_q H hq h4 hE hlow (mem _ (by simp [bootstrapRows]))) h5
  exact ⟨p, hp, le_of_gap (b := 4312) (fun n h1 h2 => gap_4297 n h1 (by omega)) p hp hpX, hs⟩

end

/-- **Theorem A** (from the inputs): no prime `q ≡ 3 (mod 4)` with `3.1·10^20 ≤ q ≤ 10^32` has
class group of exponent 7. -/
theorem theoremA {IsExp7 : ℕ → Prop} (H : Inputs IsExp7) {q : ℕ} (hq : q.Prime) (h4 : q % 4 = 3)
    (hlow : QLOW ≤ q) (hhi : q ≤ QTOP) : ¬ IsExp7 q := by
  intro hE
  have hex : ∃ p, p.Prime ∧ Splits q p := by
    obtain ⟨p, hp, -, hs⟩ := exists_split_le_4297 H hq h4 hE hlow hhi
    exact ⟨p, hp, hs⟩
  -- the least split prime
  set p := Nat.find hex with hpdef
  obtain ⟨hp, hs⟩ : p.Prime ∧ Splits q p := Nat.find_spec hex
  have hmin : ∀ m < p, ¬ (m.Prime ∧ Splits q m) := fun m hm => Nat.find_min hex hm
  have hp4297 : p ≤ 4297 := by
    obtain ⟨p', hp', hle, hs'⟩ := exists_split_le_4297 H hq h4 hE hlow hhi
    exact le_trans (Nat.find_min' hex ⟨hp', hs'⟩) hle
  have hp701 : 701 ≤ p := by
    by_contra hlt
    have : p ≤ 691 := le_of_gap gap_691 p hp (by omega)
    exact not_splits_small H hq h4 hE hlow hp this hs
  have hpq : p ≠ q := by
    have : 4297 < QLOW := by norm_num [QLOW]
    omega
  obtain ⟨x, y, hy, he⟩ := H.normEq q hq h4 hE p hp hpq hs
  refine H.search p hp hp701 hp4297 x y q hy he ?_ (mod8 H hq h4 hE hlow) ?_
  · -- `q` exceeds every ladder bound with `X ≤ p`, by minimality of `p`
    refine Qlo_le hlow (fun r hr hXp => ?_)
    by_contra hQ
    rw [not_le] at hQ
    obtain ⟨p', hp', hp'X, hs'⟩ :=
      H.cert r hr q hq h4 (X_lt_q H hq h4 hE hlow hr) hQ.le
    exact hmin p' (by omega) ⟨hp', hs'⟩
  · -- every odd prime below `p` is inert, so its Jacobi symbol is `-1`
    intro l hl hl3 hlp
    have hns : ¬ Splits q l := fun h => hmin l hlp ⟨hl, h⟩
    rw [splits_odd_iff q (by omega)] at hns
    have hlq : l ≠ q := by
      have : 4297 < QLOW := by norm_num [QLOW]
      omega
    have hcop : (-(q : ℤ)).gcd l = 1 := by
      rw [Int.neg_gcd, Int.gcd_natCast_natCast]
      exact (Nat.coprime_primes hq hl).mpr (Ne.symm hlq)
    rcases jacobiSym.eq_one_or_neg_one hcop with h | h
    · exact absurd h hns
    · exact h

end Exp7
