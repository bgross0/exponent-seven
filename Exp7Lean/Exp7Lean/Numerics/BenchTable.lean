import Exp7Lean.Numerics.Bench
import Exp7Lean.Numerics.PrimeTable
import Exp7Lean.Numerics.FixedArith

/-!
# The benchmark sum from the certified table

`tableSumBelow g X T` folds `g p L S` over the entries `(p, L, S)` of a table with `p < X`.
With `T = primeTable6400` no logarithm, square root or primality test is evaluated by the kernel:
the benchmark enclosure of `∑_{p < 6362} log p / √p` then costs a few milliseconds.
This is the intended pattern for the 175 certificate rows.
-/

namespace Exp7.Num

open Real

/-- `∑ g p L S` over the entries `(p, L, S)` of `T` with `p < X` (raw `List.rec`). -/
def tableSumBelow (g : ℕ → ℕ → ℕ → ℕ) (X : ℕ) (T : List (ℕ × ℕ × ℕ)) : ℕ :=
  List.rec (motive := fun _ => ℕ) 0
    (fun e _ ih => cond (Nat.ble (Nat.succ e.1) X) (Nat.add (g e.1 e.2.1 e.2.2) ih) ih) T

theorem tableSumBelow_nil (g : ℕ → ℕ → ℕ → ℕ) (X : ℕ) : tableSumBelow g X [] = 0 := rfl

theorem tableSumBelow_cons (g : ℕ → ℕ → ℕ → ℕ) (X : ℕ) (e : ℕ × ℕ × ℕ) (T : List (ℕ × ℕ × ℕ)) :
    tableSumBelow g X (e :: T) =
      if e.1 < X then g e.1 e.2.1 e.2.2 + tableSumBelow g X T else tableSumBelow g X T := by
  change cond (Nat.ble (e.1 + 1) X) (g e.1 e.2.1 e.2.2 + tableSumBelow g X T)
    (tableSumBelow g X T) = _
  rw [cond_ble]; rfl

theorem tableSumBelow_le_aux (g : ℕ → ℕ → ℕ → ℕ) (F : ℕ → ℝ) (c : ℝ) (X : ℕ) :
    ∀ T : List (ℕ × ℕ × ℕ), (T.map Prod.fst).Nodup →
      (∀ e ∈ T, e.1 < X → (g e.1 e.2.1 e.2.2 : ℝ) ≤ c * F e.1) →
      (tableSumBelow g X T : ℝ) ≤ c * ∑ p ∈ (T.map Prod.fst).toFinset.filter (· < X), F p := by
  intro T
  induction T with
  | nil => intro _ _; simp [tableSumBelow_nil]
  | cons e T ih =>
    intro hN h
    rw [List.map_cons, List.nodup_cons] at hN
    have ih' := ih hN.2 (fun e' he' => h e' (List.mem_cons_of_mem _ he'))
    rw [tableSumBelow_cons, List.map_cons, List.toFinset_cons, Finset.filter_insert]
    split_ifs with hlt
    · rw [Finset.sum_insert (by simp [hN.1])]
      have := h e List.mem_cons_self hlt
      push_cast
      linarith
    · exact ih'

theorem le_tableSumBelow_aux (g : ℕ → ℕ → ℕ → ℕ) (F : ℕ → ℝ) (c : ℝ) (X : ℕ) :
    ∀ T : List (ℕ × ℕ × ℕ), (T.map Prod.fst).Nodup →
      (∀ e ∈ T, e.1 < X → c * F e.1 ≤ (g e.1 e.2.1 e.2.2 : ℝ)) →
      c * ∑ p ∈ (T.map Prod.fst).toFinset.filter (· < X), F p ≤ (tableSumBelow g X T : ℝ) := by
  intro T
  induction T with
  | nil => intro _ _; simp [tableSumBelow_nil]
  | cons e T ih =>
    intro hN h
    rw [List.map_cons, List.nodup_cons] at hN
    have ih' := ih hN.2 (fun e' he' => h e' (List.mem_cons_of_mem _ he'))
    rw [tableSumBelow_cons, List.map_cons, List.toFinset_cons, Finset.filter_insert]
    split_ifs with hlt
    · rw [Finset.sum_insert (by simp [hN.1])]
      have := h e List.mem_cons_self hlt
      push_cast
      linarith
    · exact ih'

theorem primeTable6400_filter {X : ℕ} (hX : X ≤ 6400) :
    (primeTable6400.map Prod.fst).toFinset.filter (· < X) =
      (Finset.range X).filter Nat.Prime :=
  toFinset_filter_lt (B := 6400)
    (fun p => by rw [primeTable6400_primes]; exact mem_primeList6400 p) hX

/-- Lower bounds term by term over the table give a lower bound for the sum over primes `< X`. -/
theorem tableSumBelow_le (g : ℕ → ℕ → ℕ → ℕ) (F : ℕ → ℝ) (c : ℝ) {X : ℕ} (hX : X ≤ 6400)
    (h : ∀ p L S, (p, L, S) ∈ primeTable6400 → p < X → (g p L S : ℝ) ≤ c * F p) :
    (tableSumBelow g X primeTable6400 : ℝ)
      ≤ c * ∑ p ∈ (Finset.range X).filter Nat.Prime, F p := by
  rw [← primeTable6400_filter hX]
  exact tableSumBelow_le_aux g F c X _ primeTable6400_nodup
    (fun e he hlt => h e.1 e.2.1 e.2.2 he hlt)

/-- Upper bounds term by term over the table give an upper bound for the sum over primes `< X`. -/
theorem le_tableSumBelow (g : ℕ → ℕ → ℕ → ℕ) (F : ℕ → ℝ) (c : ℝ) {X : ℕ} (hX : X ≤ 6400)
    (h : ∀ p L S, (p, L, S) ∈ primeTable6400 → p < X → c * F p ≤ (g p L S : ℝ)) :
    c * ∑ p ∈ (Finset.range X).filter Nat.Prime, F p
      ≤ (tableSumBelow g X primeTable6400 : ℝ) := by
  rw [← primeTable6400_filter hX]
  exact le_tableSumBelow_aux g F c X _ primeTable6400_nodup
    (fun e he hlt => h e.1 e.2.1 e.2.2 he hlt)

/-! ### The benchmark -/

/-- Lower term `⌊L S / (10^20 p)⌋`. -/
def tLo (p L S : ℕ) : ℕ := Nat.div (Nat.mul L S) (Nat.mul 100000000000000000000 p)

/-- Upper term `⌈(L+16)(S+1) / (10^20 p)⌉`. -/
def tHi (p L S : ℕ) : ℕ :=
  cdiv (Nat.mul (Nat.add L 16) (Nat.succ S)) (Nat.mul 100000000000000000000 p)

theorem tLo_le {p L S : ℕ} (h : (p, L, S) ∈ primeTable6400) :
    (tLo p L S : ℝ) ≤ 10 ^ 20 * (log (p : ℝ) / √(p : ℝ)) := by
  obtain ⟨hp, -, h1, -, h3, -⟩ := primeTable6400_spec h
  have hp1 : 1 ≤ p := hp.one_lt.le
  have hpr : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  change ((L * S / (100000000000000000000 * p) : ℕ) : ℝ) ≤ _
  refine (fdiv_le _ _).trans ?_
  push_cast
  rw [div_le_iff₀ (by positivity)]
  have e := log_div_sqrt_eq (D := (10 : ℝ) ^ 20) hp1
  have := mul_le_mul h1 h3 (Nat.cast_nonneg S)
    (mul_nonneg (by positivity) (log_nonneg (by exact_mod_cast hp1)))
  norm_num at e this ⊢
  linarith

theorem le_tHi {p L S : ℕ} (h : (p, L, S) ∈ primeTable6400) :
    10 ^ 20 * (log (p : ℝ) / √(p : ℝ)) ≤ (tHi p L S : ℝ) := by
  obtain ⟨hp, -, -, h2, -, h4⟩ := primeTable6400_spec h
  have hp1 : 1 ≤ p := hp.one_lt.le
  have hpr : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  change _ ≤ ((cdiv ((L + 16) * (S + 1)) (100000000000000000000 * p) : ℕ) : ℝ)
  refine le_trans ?_ (div_le_cdiv _ _ (Nat.mul_pos (by norm_num) hp.pos))
  push_cast
  rw [le_div_iff₀ (by positivity)]
  have e := log_div_sqrt_eq (D := (10 : ℝ) ^ 20) hp1
  have := mul_le_mul h2 h4 (by positivity) (by positivity : (0 : ℝ) ≤ (L : ℝ) + 16)
  norm_num at e this ⊢
  linarith

/-- The fixed-point lower sum, folded over the certified table. -/
def benchLoTable : ℕ := tableSumBelow tLo 6362 primeTable6400

/-- The fixed-point upper sum, folded over the certified table. -/
def benchHiTable : ℕ := tableSumBelow tHi 6362 primeTable6400

set_option maxRecDepth 100000 in
theorem bench_lo_table_check : 15222143236878865002262 ≤ benchLoTable := by decide +kernel

set_option maxRecDepth 100000 in
theorem bench_hi_table_check : benchHiTable ≤ 15222143236878865003510 := by decide +kernel

/-- The benchmark enclosure from the table (width `1.3e-17`). -/
theorem bench_enclosure_table : (15222143236878865002262 : ℝ) / 10 ^ 20 ≤
      ∑ p ∈ (Finset.range 6362).filter Nat.Prime, log (p : ℝ) / √(p : ℝ) ∧
    ∑ p ∈ (Finset.range 6362).filter Nat.Prime, log (p : ℝ) / √(p : ℝ) ≤
      (15222143236878865003510 : ℝ) / 10 ^ 20 := by
  have h1 : (benchLoTable : ℝ) ≤ 10 ^ 20 *
      ∑ p ∈ (Finset.range 6362).filter Nat.Prime, log (p : ℝ) / √(p : ℝ) := by
    unfold benchLoTable
    exact tableSumBelow_le tLo (fun p => log (p : ℝ) / √(p : ℝ)) (10 ^ 20) (by norm_num)
      (fun p L S h _ => tLo_le h)
  have h2 : 10 ^ 20 * ∑ p ∈ (Finset.range 6362).filter Nat.Prime, log (p : ℝ) / √(p : ℝ)
      ≤ (benchHiTable : ℝ) := by
    unfold benchHiTable
    exact le_tableSumBelow tHi (fun p => log (p : ℝ) / √(p : ℝ)) (10 ^ 20) (by norm_num)
      (fun p L S h _ => le_tHi h)
  have c1 : ((15222143236878865002262 : ℕ) : ℝ) ≤ (benchLoTable : ℝ) :=
    Nat.cast_le.mpr bench_lo_table_check
  have c2 : (benchHiTable : ℝ) ≤ ((15222143236878865003510 : ℕ) : ℝ) :=
    Nat.cast_le.mpr bench_hi_table_check
  push_cast at c1 c2
  constructor
  · rw [div_le_iff₀ (by positivity)]; linarith
  · rw [le_div_iff₀ (by positivity)]; linarith

end Exp7.Num
