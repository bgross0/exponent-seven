import Exp7Lean.Arithmetic.NormBounds
import Exp7Lean.Tail.Exclusion

/-!
Exclude norm equations at the least split prime without any assumption on the
exponent of the class group. The search and analytic rows are the existing ones.
-/

namespace Exp7

/-- `p` is the least rational prime satisfying the project's splitting criterion. -/
structure LeastSplit (q p : ℕ) : Prop where
  prime : p.Prime
  splits : Splits q p
  minimal : ∀ l, l.Prime → Splits q l → p ≤ l

namespace LeastSplit

variable {q p : ℕ} (h : LeastSplit q p)

include h

theorem not_splits_lt {l : ℕ} (hl : l.Prime) (hlp : l < p) : ¬ Splits q l := by
  intro hs
  exact (not_le.mpr hlp) (h.minimal l hl hs)

/-- A certificate bounds the least split prime, independently of class-group order. -/
theorem le_of_row (hGRH : GRHPrimeConductor) (hq : q.Prime) (h4 : q % 4 = 3)
    {r : Row} (hr : r ∈ allRows) (hXq : r.X < q) (hQr : q ≤ r.Q) {P : ℕ}
    (hP : ∀ l, l.Prime → l < r.X → l ≤ P) : p ≤ P := by
  obtain ⟨l, hl, hlX, hs⟩ :=
    cert_of_margins EF.explicitFormulaBound hGRH allRows rowMargins_allRows
      r hr q hq h4 hXq hQr
  exact (h.minimal l hl hs).trans (hP l hl hlX)

/-- One norm bound at the least split prime suffices for all six bootstrap steps. -/
theorem le_4297_of_norm_bound (hGRH : GRHPrimeConductor) (hq : q.Prime)
    (h4 : q % 4 = 3) (hlo : QLOW ≤ q) (hhi : q ≤ QTOP) (hnorm : q ≤ 4 * p ^ 7) :
    p ≤ 4297 := by
  have mem : ∀ r ∈ bootstrapRows, r ∈ allRows := fun r hr => List.mem_append_left _ hr
  have hXq : ∀ r ∈ allRows, r.X < q := by
    intro r hr
    have := allRows_X_le r hr
    have : 6362 < QLOW := by norm_num [QLOW]
    omega
  have step {r : Row} (hr : r ∈ bootstrapRows) (hQr : q ≤ r.Q) {P : ℕ}
      (hP : ∀ l, l.Prime → l < r.X → l ≤ P) : q ≤ 4 * P ^ 7 := by
    have hle := h.le_of_row hGRH hq h4 (mem r hr) (hXq r (mem r hr)) hQr hP
    exact hnorm.trans (Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left hle 7))
  have h1 : q ≤ 4 * 6361 ^ 7 := step (r := ⟨10 ^ 32, 6362⟩)
    (by simp [bootstrapRows]) hhi (fun l _ hl => by dsimp at hl; omega)
  have h2 : q ≤ 4 * 4679 ^ 7 := step (r := ⟨4 * 6361 ^ 7, 4690⟩)
    (by simp [bootstrapRows]) h1 (le_of_gap gap_4679)
  have h3 : q ≤ 4 * 4391 ^ 7 := step (r := ⟨4 * 4679 ^ 7, 4393⟩)
    (by simp [bootstrapRows]) h2 (le_of_gap gap_4391)
  have h4' : q ≤ 4 * 4327 ^ 7 := step (r := ⟨4 * 4391 ^ 7, 4333⟩)
    (by simp [bootstrapRows]) h3 (le_of_gap gap_4327)
  have h5 : q ≤ 4 * 4297 ^ 7 := step (r := ⟨4 * 4327 ^ 7, 4319⟩)
    (by simp [bootstrapRows]) h4' (le_of_gap gap_4297)
  exact h.le_of_row hGRH hq h4 (mem _ (by simp [bootstrapRows]))
    (hXq _ (mem _ (by simp [bootstrapRows]))) (r := ⟨4 * 4297 ^ 7, 4312⟩) h5
    (le_of_gap (b := 4312) (fun n h1 h2 => gap_4297 n h1 (by omega)))

/-- The existing high search excludes a norm equation at the least split prime. -/
theorem no_norm_seven_bounded (hGRH : GRHPrimeConductor) (hS : SearchHigh)
    (hq : q.Prime) (h4 : q % 4 = 3) (hlo : QLOW ≤ q) (hhi : q ≤ QTOP)
    {x y : ℕ} (hy : 1 ≤ y) : 4 * p ^ 7 ≠ x ^ 2 + q * y ^ 2 := by
  intro he
  have hnorm : q ≤ 4 * p ^ 7 := by
    have := Nat.le_mul_of_pos_right q (show 0 < y ^ 2 by positivity)
    omega
  have hp4297 := h.le_4297_of_norm_bound hGRH hq h4 hlo hhi hnorm
  have hp701 : 701 ≤ p := by
    by_contra hn
    have hp691 := le_of_gap gap_691 p h.prime (by omega)
    have := Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left hp691 7)
    have := small_bound
    omega
  have h8 : q % 8 = 3 := by
    have hn := h.not_splits_lt Nat.prime_two (by omega)
    rw [splits_two_iff] at hn
    omega
  have hQlo : Qlo p ≤ q := by
    apply Qlo_le hlo
    intro r hr hXp
    by_contra hn
    have hXq : r.X < q := by
      have := allRows_X_le r hr
      have : 6362 < QLOW := by norm_num [QLOW]
      omega
    obtain ⟨l, hl, hlX, hs⟩ :=
      cert_of_margins EF.explicitFormulaBound hGRH allRows rowMargins_allRows
        r hr q hq h4 hXq (by omega)
    exact h.not_splits_lt hl (by omega) hs
  apply hS p h.prime hp701 hp4297 x y q hy he hQlo h8
  intro l hl hl3 hlp
  have hn := h.not_splits_lt hl hlp
  rw [splits_odd_iff q (by omega)] at hn
  have hlq : l ≠ q := by
    have : 4297 < QLOW := by norm_num [QLOW]
    omega
  have hcop : (-(q : ℤ)).gcd l = 1 := by
    rw [Int.neg_gcd, Int.gcd_natCast_natCast]
    exact (Nat.coprime_primes hq hl).mpr (Ne.symm hlq)
  rcases jacobiSym.eq_one_or_neg_one hcop with heq | heq
  · exact (hn heq).elim
  · exact heq

end LeastSplit

attribute [local irreducible] rowMargin

/-- The finite bridge and dyadic tail actually produce a split prime below the norm threshold.
This statement has no class-group hypothesis. -/
theorem exists_split_below_norm_threshold (hGRH : GRHPrimeConductor) {q : ℕ}
    (hq : q.Prime) (h4 : q % 4 = 3) (hlo : QTOP ≤ q) :
    ∃ p, p.Prime ∧ Splits q p ∧ 4 * p ^ 7 < q := by
  have row {X Q : ℕ} {v : List ℝ} (hX : 2 ≤ X) (hv : ∃ t ∈ v, t ≠ 0)
      (hm : 0 < rowMargin Q X v) (hnorm : 4 * X ^ 7 < q) (hQ : q ≤ Q) :
      ∃ p, p.Prime ∧ Splits q p ∧ 4 * p ^ 7 < q := by
    obtain ⟨p, hp, hpX, hs⟩ := split_prime_of_row EF.explicitFormulaBound hGRH Q X v
      hX hv hm q hq h4 (cutoff_lt_conductor hnorm) hQ
    exact ⟨p, hp, hs, lt_of_le_of_lt
      (Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left hpX.le 7)) hnorm⟩
  rcases le_or_gt q (2 ^ 135) with hhi | hlarge
  · obtain ⟨hX, v, hv, hm⟩ : 2 ≤ (30000 : ℕ) ∧
        ∃ v : List ℝ, (∃ t ∈ v, t ≠ 0) ∧ 0 < rowMargin (2 ^ 135) 30000 v :=
      Rows.Bridge30000.rowOK
    exact row hX hv hm (lt_of_lt_of_le (by decide : 4 * 30000 ^ 7 < QTOP) hlo) hhi
  · obtain ⟨n, hn, hnorm, hbalance⟩ := ChebyshevTail.exists_cutoff_above_bridge hlarge
    let X := 2 ^ n
    have hX : 2 ≤ X := by
      calc
        2 = (2 : ℕ) ^ 1 := by simp
        _ ≤ X := Nat.pow_le_pow_right (by decide) (by omega)
    have hcast : (X : ℝ) = 2 ^ n := by simp [X]
    rw [← hcast] at hbalance
    have hsum := hbalance.trans_le (ChebyshevTail.weightedPrimeBalance_le_inertSum hX)
    have hlen : 1 ≤ Real.log (X : ℝ) := by
      rw [hcast, Real.log_pow]
      have hn' : (19 : ℝ) ≤ n := by exact_mod_cast hn
      have hc := Real.log_pos (by norm_num : (1 : ℝ) < 2)
      nlinarith [Real.log_two_gt_d9, mul_nonneg (sub_nonneg.mpr hn') hc.le]
    have hJ := Jterm_haar_le_four hlen
    have hpi := Real.log_nonneg (show 1 ≤ Real.pi by linarith [Real.pi_gt_three])
    have hpsi : psi34 ≤ 0 := by
      unfold psi34
      linarith [Real.one_half_lt_eulerMascheroniConstant, Real.pi_lt_four,
        Real.log_two_gt_d9]
    have hmargin : 0 < rowMargin q X [1, -1] := by unfold rowMargin; linarith
    exact row hX ⟨1, by simp, one_ne_zero⟩ hmargin hnorm le_rfl

/-- At every conductor above the search floor, the least split prime has no seventh norm
representation. Only GRH and the existing high search are assumed. -/
theorem LeastSplit.no_norm_seven (hGRH : GRHPrimeConductor) (hS : SearchHigh)
    {q p : ℕ} (h : LeastSplit q p) (hq : q.Prime) (h4 : q % 4 = 3) (hlo : QLOW ≤ q)
    {x y : ℕ} (hy : 1 ≤ y) : 4 * p ^ 7 ≠ x ^ 2 + q * y ^ 2 := by
  rcases le_or_gt q QTOP with hhi | hlarge
  · exact h.no_norm_seven_bounded hGRH hS hq h4 hlo hhi hy
  · intro he
    obtain ⟨l, hl, hs, hsmall⟩ := exists_split_below_norm_threshold hGRH hq h4 hlarge.le
    have hp := h.minimal l hl hs
    have hpow := Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left hp 7)
    have hqy := Nat.le_mul_of_pos_right q (show 0 < y ^ 2 by positivity)
    omega

/-- The first bootstrap row already bounds the least split prime by 6361. -/
theorem LeastSplit.le_6361 (hGRH : GRHPrimeConductor) {q p : ℕ} (h : LeastSplit q p)
    (hq : q.Prime) (h4 : q % 4 = 3) (hlo : QLOW ≤ q) (hhi : q ≤ QTOP) : p ≤ 6361 := by
  have hr : (⟨QTOP, 6362⟩ : Row) ∈ allRows := by
    simp [allRows, bootstrapRows, QTOP]
  have hXq : 6362 < q := lt_of_lt_of_le (by norm_num [QLOW]) hlo
  exact h.le_of_row hGRH hq h4 hr hXq hhi (fun l _ hl => by dsimp at hl; omega)

/-- In the large-conductor range the least split prime is unramified. -/
theorem LeastSplit.lt_conductor (hGRH : GRHPrimeConductor) {q p : ℕ} (h : LeastSplit q p)
    (hq : q.Prime) (h4 : q % 4 = 3) (hlo : QLOW ≤ q) : p < q := by
  rcases le_or_gt q QTOP with hhi | hlarge
  · have hp := h.le_6361 hGRH hq h4 hlo hhi
    have : 6361 < QLOW := by norm_num [QLOW]
    omega
  · obtain ⟨l, hl, hs, hsmall⟩ := exists_split_below_norm_threshold hGRH hq h4 hlarge.le
    exact (h.minimal l hl hs).trans_lt (cutoff_lt_conductor hsmall)

/-- Exclude all four odd powers at most seven, still without a class-group hypothesis. -/
theorem LeastSplit.no_norm_odd_le_seven (hGRH : GRHPrimeConductor) (hS : SearchHigh)
    {q p n : ℕ} (h : LeastSplit q p) (hq : q.Prime) (h4 : q % 4 = 3)
    (hlo : QLOW ≤ q) (hn : Odd n) (hn7 : n ≤ 7) {x y : ℕ} (hy : 1 ≤ y) :
    4 * p ^ n ≠ x ^ 2 + q * y ^ 2 := by
  by_cases hn_eq : n = 7
  · subst n
    exact h.no_norm_seven hGRH hS hq h4 hlo hy
  have hn5 : n ≤ 5 := by obtain ⟨k, hk⟩ := hn; omega
  intro he
  have hnorm : q ≤ 4 * p ^ n := by
    have := Nat.le_mul_of_pos_right q (show 0 < y ^ 2 by positivity)
    omega
  rcases le_or_gt q QTOP with hhi | hlarge
  · have hp := h.le_6361 hGRH hq h4 hlo hhi
    have hpn := Nat.pow_le_pow_right h.prime.one_le hn5
    have hp5 := Nat.pow_le_pow_left hp 5
    have hsmall : 4 * 6361 ^ 5 < QLOW := by norm_num [QLOW]
    omega
  · obtain ⟨l, hl, hs, hsmall⟩ := exists_split_below_norm_threshold hGRH hq h4 hlarge.le
    have hp := h.minimal l hl hs
    have hpn := Nat.pow_le_pow_right h.prime.one_le hn7
    have hp7 := Nat.pow_le_pow_left hp 7
    omega

/-- The least split prime exists throughout the range of the exclusion theorem. -/
theorem exists_leastSplit (hGRH : GRHPrimeConductor) {q : ℕ} (hq : q.Prime)
    (h4 : q % 4 = 3) (hlo : QLOW ≤ q) : ∃ p, LeastSplit q p := by
  classical
  have hex : ∃ p, p.Prime ∧ Splits q p := by
    rcases le_or_gt q QTOP with hhi | hlarge
    · have hr : (⟨QTOP, 6362⟩ : Row) ∈ allRows := by
        simp [allRows, bootstrapRows, QTOP]
      obtain ⟨p, hp, _, hs⟩ :=
        cert_of_margins EF.explicitFormulaBound hGRH allRows rowMargins_allRows
          _ hr q hq h4 (lt_of_lt_of_le (by norm_num [QLOW]) hlo) hhi
      exact ⟨p, hp, hs⟩
    · obtain ⟨p, hp, hs, _⟩ := exists_split_below_norm_threshold hGRH hq h4 hlarge.le
      exact ⟨p, hp, hs⟩
  refine ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2, ?_⟩
  intro l hl hs
  exact Nat.find_min' hex ⟨hl, hs⟩

end Exp7
