import Exp7Lean.Numerics.Constants
import Exp7Lean.Numerics.PrimeList

/-!
# Benchmark: a certified enclosure of `∑_{p < 6362} log p / √p`

The sum runs over the 829 primes below `6362`.  Each term is enclosed at scale `10^20` by
`logDivSqrtLo`/`logDivSqrtHi` (verified `log`, verified `√`, one directed division).  Two versions:

* `bench_enclosure` : the terms are added by the loop `sumPrimes`, which also decides primality
  of every `n < 6362` by trial division (self-contained; primality dominates the kernel time);
* `bench_enclosure_list` : the terms are added by folding over the certified literal list
  `primeList6400` (no primality testing; this is the pattern to use for many rows).

In both, the final numerical comparison is a single `decide +kernel`.
-/

namespace Exp7.Num

open Real

/-- Lower bound for `P.D * (log n / √n)`. -/
def logDivSqrtLo (P : Prec) (fuel n : ℕ) : ℕ :=
  Nat.div (Nat.mul (logLo P n) (sqrtLo P.D P.bits fuel n)) (Nat.mul P.D n)

/-- Upper bound for `P.D * (log n / √n)`. -/
def logDivSqrtHi (P : Prec) (fuel n : ℕ) : ℕ :=
  cdiv (Nat.mul (logHi P n) (sqrtHi P.D P.bits fuel n)) (Nat.mul P.D n)

theorem log_div_sqrt_eq {D : ℝ} {n : ℕ} (hn : 1 ≤ n) :
    D * log (n : ℝ) * (D * √(n : ℝ)) = D * (log (n : ℝ) / √(n : ℝ)) * (D * (n : ℝ)) := by
  have hnr : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hs : √(n : ℝ) * √(n : ℝ) = (n : ℝ) := mul_self_sqrt hnr.le
  have hsp : 0 < √(n : ℝ) := sqrt_pos.mpr hnr
  calc D * log (n : ℝ) * (D * √(n : ℝ))
      = D * (log (n : ℝ) / √(n : ℝ)) * (D * (√(n : ℝ) * √(n : ℝ))) := by field_simp
    _ = D * (log (n : ℝ) / √(n : ℝ)) * (D * (n : ℝ)) := by rw [hs]

theorem logDivSqrtLo_le {P : Prec} (hP : P.Valid) (fuel : ℕ) {n : ℕ} (hn : 1 ≤ n) :
    (logDivSqrtLo P fuel n : ℝ) ≤ P.D * (log (n : ℝ) / √(n : ℝ)) := by
  have hD : (0 : ℝ) < P.D := by exact_mod_cast hP.pos
  have hnr : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have h1 := logLo_le hP hn
  have h2 := sqrtLo_le P.D P.bits fuel n
  change ((logLo P n * sqrtLo P.D P.bits fuel n / (P.D * n) : ℕ) : ℝ) ≤ _
  refine (fdiv_le _ _).trans ?_
  push_cast
  rw [div_le_iff₀ (by positivity), ← log_div_sqrt_eq hn]
  exact mul_le_mul h1 h2 (Nat.cast_nonneg _)
    (mul_nonneg hD.le (log_nonneg (by exact_mod_cast hn)))

theorem le_logDivSqrtHi {P : Prec} (hP : P.Valid) (fuel : ℕ) {n : ℕ} (hn : 1 ≤ n) :
    P.D * (log (n : ℝ) / √(n : ℝ)) ≤ (logDivSqrtHi P fuel n : ℝ) := by
  have hD : (0 : ℝ) < P.D := by exact_mod_cast hP.pos
  have hnr : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have h1 := le_logHi hP hn
  have h2 := le_sqrtHi P.D P.bits fuel n
  change _ ≤ ((cdiv (logHi P n * sqrtHi P.D P.bits fuel n) (P.D * n) : ℕ) : ℝ)
  refine le_trans ?_ (div_le_cdiv _ _ (Nat.mul_pos hP.pos (by omega)))
  push_cast
  rw [le_div_iff₀ (by positivity), ← log_div_sqrt_eq hn]
  exact mul_le_mul h1 h2 (by positivity) (Nat.cast_nonneg _)

/-- The benchmark sum `S = ∑_{p < 6362, p prime} log p / √p`. -/
noncomputable def benchSum : ℝ :=
  ∑ p ∈ (Finset.range 6362).filter Nat.Prime, log (p : ℝ) / √(p : ℝ)

/-- The fixed-point lower sum (829 primes; primality by trial division inside the loop). -/
def benchLoVal : ℕ := sumPrimes (logDivSqrtLo P20 7) 0 6362

/-- The fixed-point upper sum. -/
def benchHiVal : ℕ := sumPrimes (logDivSqrtHi P20 7) 0 6362

/-- Kernel computation of the lower sum. -/
theorem bench_lo_check : 15222143236878865002262 ≤ benchLoVal := by decide +kernel

/-- Kernel computation of the upper sum. -/
theorem bench_hi_check : benchHiVal ≤ 15222143236878865003342 := by decide +kernel

theorem benchLoVal_le : (benchLoVal : ℝ) ≤ ((P20.D : ℕ) : ℝ) * benchSum := by
  unfold benchLoVal benchSum
  exact sumPrimes_range_le (logDivSqrtLo P20 7) (fun p => log (p : ℝ) / √(p : ℝ)) (P20.D : ℝ)
    6362 (fun p hp _ => logDivSqrtLo_le P20_valid 7 hp.one_lt.le)

theorem le_benchHiVal : ((P20.D : ℕ) : ℝ) * benchSum ≤ (benchHiVal : ℝ) := by
  unfold benchHiVal benchSum
  exact le_sumPrimes_range (logDivSqrtHi P20 7) (fun p => log (p : ℝ) / √(p : ℝ)) (P20.D : ℝ)
    6362 (fun p hp _ => le_logDivSqrtHi P20_valid 7 hp.one_lt.le)

theorem P20_D : ((P20.D : ℕ) : ℝ) = 10 ^ 20 := by norm_num [P20]

/-- `152.22143236878865002262 ≤ S`. -/
theorem bench_lower : (15222143236878865002262 : ℝ) / 10 ^ 20 ≤ benchSum := by
  have h := benchLoVal_le
  have c : ((15222143236878865002262 : ℕ) : ℝ) ≤ (benchLoVal : ℝ) := Nat.cast_le.mpr bench_lo_check
  rw [P20_D] at h
  rw [div_le_iff₀ (by positivity)]
  push_cast at c
  linarith

/-- `S ≤ 152.22143236878865003342`. -/
theorem bench_upper : benchSum ≤ (15222143236878865003342 : ℝ) / 10 ^ 20 := by
  have h := le_benchHiVal
  have c : (benchHiVal : ℝ) ≤ ((15222143236878865003342 : ℕ) : ℝ) := Nat.cast_le.mpr bench_hi_check
  rw [P20_D] at h
  rw [le_div_iff₀ (by positivity)]
  push_cast at c
  linarith

/-- The benchmark statement: `S` is enclosed to within `1.1e-17`. -/
theorem bench_enclosure : (15222143236878865002262 : ℝ) / 10 ^ 20 ≤
      ∑ p ∈ (Finset.range 6362).filter Nat.Prime, log (p : ℝ) / √(p : ℝ) ∧
    ∑ p ∈ (Finset.range 6362).filter Nat.Prime, log (p : ℝ) / √(p : ℝ) ≤
      (15222143236878865003342 : ℝ) / 10 ^ 20 :=
  ⟨bench_lower, bench_upper⟩

/-! ### The same enclosure from the certified literal list of primes -/

/-- The fixed-point lower sum, folded over the literal prime list. -/
def benchLoList : ℕ := listSumBelow (logDivSqrtLo P20 7) 6362 primeList6400

/-- The fixed-point upper sum, folded over the literal prime list. -/
def benchHiList : ℕ := listSumBelow (logDivSqrtHi P20 7) 6362 primeList6400

theorem bench_lo_list_check : 15222143236878865002262 ≤ benchLoList := by decide +kernel

theorem bench_hi_list_check : benchHiList ≤ 15222143236878865003342 := by decide +kernel

theorem benchLoList_le : (benchLoList : ℝ) ≤ ((P20.D : ℕ) : ℝ) * benchSum := by
  unfold benchLoList benchSum
  exact listSumBelow_le (logDivSqrtLo P20 7) (fun p => log (p : ℝ) / √(p : ℝ)) (P20.D : ℝ)
    primeList6400_nodup mem_primeList6400 (by norm_num)
    (fun p hp _ => logDivSqrtLo_le P20_valid 7 hp.one_lt.le)

theorem le_benchHiList : ((P20.D : ℕ) : ℝ) * benchSum ≤ (benchHiList : ℝ) := by
  unfold benchHiList benchSum
  exact le_listSumBelow (logDivSqrtHi P20 7) (fun p => log (p : ℝ) / √(p : ℝ)) (P20.D : ℝ)
    primeList6400_nodup mem_primeList6400 (by norm_num)
    (fun p hp _ => le_logDivSqrtHi P20_valid 7 hp.one_lt.le)

/-- The benchmark statement again, via the literal prime list. -/
theorem bench_enclosure_list : (15222143236878865002262 : ℝ) / 10 ^ 20 ≤
      ∑ p ∈ (Finset.range 6362).filter Nat.Prime, log (p : ℝ) / √(p : ℝ) ∧
    ∑ p ∈ (Finset.range 6362).filter Nat.Prime, log (p : ℝ) / √(p : ℝ) ≤
      (15222143236878865003342 : ℝ) / 10 ^ 20 := by
  have h1 := benchLoList_le
  have h2 := le_benchHiList
  have c1 : ((15222143236878865002262 : ℕ) : ℝ) ≤ (benchLoList : ℝ) :=
    Nat.cast_le.mpr bench_lo_list_check
  have c2 : (benchHiList : ℝ) ≤ ((15222143236878865003342 : ℕ) : ℝ) :=
    Nat.cast_le.mpr bench_hi_list_check
  rw [P20_D] at h1 h2
  push_cast at c1 c2
  constructor
  · change _ ≤ benchSum
    rw [div_le_iff₀ (by positivity)]; linarith
  · change benchSum ≤ _
    rw [le_div_iff₀ (by positivity)]; linarith

end Exp7.Num
