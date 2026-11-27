import Exp7Lean.Rows.Bridge30000Data
import Exp7Lean.Fundamental

/-! The finite exclusion interval between the bounded classification and the dyadic tail. -/

namespace Exp7.Rows.Bridge30000

open Real Exp7.Num

local notation "Dr" => (100000000000000000000 : ℝ)

private theorem entries_primes : entries.map Prod.fst = primesBelow 30000 := by
  have general (ps : List ℕ) :
      (ps.map (fun p => (p, logLo P20 p, sqrtLo20 p))).map Prod.fst = ps := by
    simp [List.map_map, Function.comp_def]
  exact general _

private theorem entry_bounds (e : ℕ × ℕ × ℕ) (he : e ∈ entries) :
    e.1.Prime ∧ (e.2.1 : ℝ) ≤ Dr * log e.1 ∧ Dr * log e.1 ≤ (e.2.1 : ℝ) + 16 ∧
      (e.2.2 : ℝ) ≤ Dr * √(e.1 : ℝ) ∧ Dr * √(e.1 : ℝ) ≤ (e.2.2 : ℝ) + 1 := by
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp he
  have hprime := (mem_primesBelow.mp hp).1
  have hw := (listAll_iff _ _).mp widths_checked p hp
  simp only [widthOK, Bool.and_eq_true] at hw
  obtain ⟨hl, hs⟩ := hw
  have hlog := hi_rescale (D := 100000000000000000000) (M := 1000000)
    (by decide) (le_logHi P26_valid hprime.one_le) (Nat.le_of_ble_eq_true hl)
  have hsqrt : (sqrtHi20 p : ℝ) ≤ (sqrtLo20 p : ℝ) + 1 := by
    exact_mod_cast Nat.le_of_ble_eq_true hs
  refine ⟨hprime, logLo_le P20_valid hprime.one_le, ?_, sqrtLo_le _ 4 7 p, ?_⟩
  · exact_mod_cast hlog
  · exact le_trans (le_sqrtHi _ 4 7 p) hsqrt

private theorem context :
    RowCtx 30000 (logLo P20 30000) (logHi P20 30000) 64 pack (vector.map Int.cast) 30000 := by
  refine ⟨by decide, le_rfl, ?_, by decide +kernel, logLo_le P20_valid (by decide),
    le_logHi P20_valid (by decide)⟩
  have h := packOK_of_check pack_checked
  have hsq : Nat.sub (getN pack 0) 4611686018427387904 = 64 := by decide +kernel
  rwa [hsq] at h

/-- Certified lower bound on the actual real row margin, at the evaluator's scale. -/
theorem margin_bound :
    (752277024130489382120 : ℝ) ≤ Dr * rowMargin (2 ^ 135) 30000 (vector.map Int.cast) := by
  have hT := tablePrimeLo_le (fuel := 14) context entries (by decide)
    (entries_primes ▸ primesBelow_nodup 30000)
    (by rw [entries_primes]; exact toFinset_filter_lt (fun _ => mem_primesBelow) le_rfl)
    entry_bounds
  have h := marginLower_le (Q := 2 ^ 135) (total := primeTotal) context (by decide)
    (by decide +kernel) hT
  rw [margin_eq] at h
  exact_mod_cast h

-- The remaining deductions use the real margin only through its proved lower bound.
attribute [local irreducible] rowMargin

theorem rowOK : RowOK ⟨2 ^ 135, 30000⟩ := by
  refine ⟨by decide, vector.map Int.cast, context.pk.ne, ?_⟩
  change 0 < rowMargin (2 ^ 135) 30000 (vector.map Int.cast)
  exact pos_of_mul_pos_right (lt_of_lt_of_le (by norm_num) margin_bound) (by norm_num)

/-- The row excludes prime conductors of exponent seven throughout the closed bridge interval. -/
theorem excludes (hGRH : GRHPrimeConductor) {q : ℕ} (hq : q.Prime) (h4 : q % 4 = 3)
    (hlo : 10 ^ 32 ≤ q) (hhi : q ≤ 2 ^ 135) : ¬ IsExp7 q := by
  intro hE
  obtain ⟨hX, v, hv, hm⟩ : 2 ≤ (30000 : ℕ) ∧
      ∃ v : List ℝ, (∃ t ∈ v, t ≠ 0) ∧ 0 < rowMargin (2 ^ 135) 30000 v := rowOK
  have hXq : 30000 < q := lt_of_lt_of_le (by decide : 30000 < 10 ^ 32) hlo
  obtain ⟨p, hp, hpX, hs⟩ :=
    split_prime_of_row EF.explicitFormulaBound hGRH (2 ^ 135) 30000 v hX hv hm q hq h4 hXq hhi
  obtain ⟨x, y, hy, -, he⟩ := normEq_classGroup q hq h4 hE p hp (lt_trans hpX hXq).ne hs
  have hqle : q ≤ q * y ^ 2 := Nat.le_mul_of_pos_right _ (by positivity)
  have hp7 : 4 * p ^ 7 ≤ 4 * 30000 ^ 7 := Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left hpX.le 7)
  have hsmall : 4 * 30000 ^ 7 < 10 ^ 32 := by decide
  omega

/-- The same exclusion for orders with negative fundamental discriminant. -/
theorem excludes_fundamental (hGRH : GRHPrimeConductor) (a b : ℤ)
    (hfund : Int.IsFundamentalDiscr (QuadraticAlgebra.discr a b))
    (hneg : QuadraticAlgebra.discr a b < 0) [IsDomain (QuadraticAlgebra ℤ a b)]
    (hlo : (10 : ℤ) ^ 32 ≤ -QuadraticAlgebra.discr a b)
    (hhi : -QuadraticAlgebra.discr a b ≤ (2 : ℤ) ^ 135) :
    Monoid.exponent (ClassGroup (QuadraticAlgebra ℤ a b)) ≠ 7 := by
  intro h
  obtain ⟨q, hq, h4, hd⟩ := prime_discr_of_exponent_seven' a b hfund hneg h
  rw [hd, neg_neg] at hlo hhi
  exact excludes hGRH hq h4 (by exact_mod_cast hlo) (by exact_mod_cast hhi)
    ((isExp7_iff_exponent hq h4 hd).mpr h)

end Exp7.Rows.Bridge30000

#print axioms Exp7.Rows.Bridge30000.margin_bound
#print axioms Exp7.Rows.Bridge30000.rowOK
#print axioms Exp7.Rows.Bridge30000.excludes
#print axioms Exp7.Rows.Bridge30000.excludes_fundamental
