import Exp7Lean.Final2
import Exp7Lean.Sieve.Bridge

/-!
# Assembly of `Exp7.SearchHigh` from the per-prime statements

`SearchHigh` is, by definition, `PrimeStatement p (Qlo p)` for all primes `701 ≤ p ≤ 4297`
(`searchHigh_of_primes`).  The 465 primes of that range are listed in `highPrimes`, and the list is
proved complete (`mem_highPrimes`), so that 465 theorems `PrimeStatement p (Qlo p)`, one per
generated file, give `SearchHigh` (`searchHigh_of_list`, and `Done` to chain them).  A table of
smaller bounds can be used instead of `Qlo` (`searchHigh_of_bounds`); larger bounds need the
corresponding change of `SearchHigh` itself.
-/

namespace Exp7.Sieve

/-- `SearchHigh` from the per-prime statements. -/
theorem searchHigh_of_primes
    (h : ∀ p, p.Prime → 701 ≤ p → p ≤ 4297 → PrimeStatement p (Qlo p)) : SearchHigh :=
  fun p hp h1 h2 => h p hp h1 h2

/-- The 465 primes `701 ≤ p ≤ 4297`. -/
def highPrimes : List ℕ :=
  [701, 709, 719, 727, 733, 739, 743, 751, 757, 761, 769, 773, 787, 797, 809, 811, 821, 823, 827,
   829, 839, 853, 857, 859, 863, 877, 881, 883, 887, 907, 911, 919, 929, 937, 941, 947, 953, 967,
   971, 977, 983, 991, 997, 1009, 1013, 1019, 1021, 1031, 1033, 1039, 1049, 1051, 1061, 1063,
   1069, 1087, 1091, 1093, 1097, 1103, 1109, 1117, 1123, 1129, 1151, 1153, 1163, 1171, 1181,
   1187, 1193, 1201, 1213, 1217, 1223, 1229, 1231, 1237, 1249, 1259, 1277, 1279, 1283, 1289,
   1291, 1297, 1301, 1303, 1307, 1319, 1321, 1327, 1361, 1367, 1373, 1381, 1399, 1409, 1423,
   1427, 1429, 1433, 1439, 1447, 1451, 1453, 1459, 1471, 1481, 1483, 1487, 1489, 1493, 1499,
   1511, 1523, 1531, 1543, 1549, 1553, 1559, 1567, 1571, 1579, 1583, 1597, 1601, 1607, 1609,
   1613, 1619, 1621, 1627, 1637, 1657, 1663, 1667, 1669, 1693, 1697, 1699, 1709, 1721, 1723,
   1733, 1741, 1747, 1753, 1759, 1777, 1783, 1787, 1789, 1801, 1811, 1823, 1831, 1847, 1861,
   1867, 1871, 1873, 1877, 1879, 1889, 1901, 1907, 1913, 1931, 1933, 1949, 1951, 1973, 1979,
   1987, 1993, 1997, 1999, 2003, 2011, 2017, 2027, 2029, 2039, 2053, 2063, 2069, 2081, 2083,
   2087, 2089, 2099, 2111, 2113, 2129, 2131, 2137, 2141, 2143, 2153, 2161, 2179, 2203, 2207,
   2213, 2221, 2237, 2239, 2243, 2251, 2267, 2269, 2273, 2281, 2287, 2293, 2297, 2309, 2311,
   2333, 2339, 2341, 2347, 2351, 2357, 2371, 2377, 2381, 2383, 2389, 2393, 2399, 2411, 2417,
   2423, 2437, 2441, 2447, 2459, 2467, 2473, 2477, 2503, 2521, 2531, 2539, 2543, 2549, 2551,
   2557, 2579, 2591, 2593, 2609, 2617, 2621, 2633, 2647, 2657, 2659, 2663, 2671, 2677, 2683,
   2687, 2689, 2693, 2699, 2707, 2711, 2713, 2719, 2729, 2731, 2741, 2749, 2753, 2767, 2777,
   2789, 2791, 2797, 2801, 2803, 2819, 2833, 2837, 2843, 2851, 2857, 2861, 2879, 2887, 2897,
   2903, 2909, 2917, 2927, 2939, 2953, 2957, 2963, 2969, 2971, 2999, 3001, 3011, 3019, 3023,
   3037, 3041, 3049, 3061, 3067, 3079, 3083, 3089, 3109, 3119, 3121, 3137, 3163, 3167, 3169,
   3181, 3187, 3191, 3203, 3209, 3217, 3221, 3229, 3251, 3253, 3257, 3259, 3271, 3299, 3301,
   3307, 3313, 3319, 3323, 3329, 3331, 3343, 3347, 3359, 3361, 3371, 3373, 3389, 3391, 3407,
   3413, 3433, 3449, 3457, 3461, 3463, 3467, 3469, 3491, 3499, 3511, 3517, 3527, 3529, 3533,
   3539, 3541, 3547, 3557, 3559, 3571, 3581, 3583, 3593, 3607, 3613, 3617, 3623, 3631, 3637,
   3643, 3659, 3671, 3673, 3677, 3691, 3697, 3701, 3709, 3719, 3727, 3733, 3739, 3761, 3767,
   3769, 3779, 3793, 3797, 3803, 3821, 3823, 3833, 3847, 3851, 3853, 3863, 3877, 3881, 3889,
   3907, 3911, 3917, 3919, 3923, 3929, 3931, 3943, 3947, 3967, 3989, 4001, 4003, 4007, 4013,
   4019, 4021, 4027, 4049, 4051, 4057, 4073, 4079, 4091, 4093, 4099, 4111, 4127, 4129, 4133,
   4139, 4153, 4157, 4159, 4177, 4201, 4211, 4217, 4219, 4229, 4231, 4241, 4243, 4253, 4259,
   4261, 4271, 4273, 4283, 4289, 4297]

/-- `n` has a divisor `2 ≤ d ≤ 65`, `d < n`. -/
noncomputable def compositeB (n : ℕ) : Bool :=
  Bool.not (allBelow 66 (fun d => Bool.or (Nat.ble d 1) (Bool.or (Nat.ble n d)
    (Bool.not (Nat.beq (Nat.mod n d) 0)))))

theorem compositeB_sound {n : ℕ} (h : compositeB n = true) : ¬ n.Prime := by
  intro hp
  unfold compositeB at h
  rw [Bool.not_eq_true'] at h
  have hall : allBelow 66 (fun d => Bool.or (Nat.ble d 1) (Bool.or (Nat.ble n d)
      (Bool.not (Nat.beq (Nat.mod n d) 0)))) = true := by
    rw [allBelow_iff]
    intro d _
    rw [Bool.or_eq_true, Bool.or_eq_true, Nat.ble_eq, Nat.ble_eq, Bool.not_eq_true']
    by_cases h1 : d ≤ 1
    · exact Or.inl h1
    by_cases h2 : n ≤ d
    · exact Or.inr (Or.inl h2)
    refine Or.inr (Or.inr ?_)
    cases hb : Nat.beq (Nat.mod n d) 0
    · rfl
    · rw [Nat.beq_eq] at hb
      have hdvd : d ∣ n := Nat.dvd_of_mod_eq_zero hb
      rcases (Nat.dvd_prime hp).1 hdvd with h | h <;> omega
  rw [hall] at h
  exact Bool.noConfusion h

/-- All `n` with `lo ≤ n ≤ hi` outside the (increasing) list are composite. -/
noncomputable def gapsOk : ℕ → List ℕ → ℕ → Bool
  | lo, [], hi => allBelow (hi + 1 - lo) (fun i => compositeB (lo + i))
  | lo, p :: ps, hi => allBelow (p - lo) (fun i => compositeB (lo + i)) && gapsOk (p + 1) ps hi

theorem gapsOk_sound {l : List ℕ} {hi : ℕ} :
    ∀ {lo : ℕ}, gapsOk lo l hi = true → ∀ n, lo ≤ n → n ≤ hi → n.Prime → n ∈ l := by
  induction l with
  | nil =>
    intro lo h n h1 h2 hp
    have h' : allBelow (hi + 1 - lo) (fun i => compositeB (lo + i)) = true := h
    rw [allBelow_iff] at h'
    have := h' (n - lo) (by omega)
    have e : lo + (n - lo) = n := by omega
    rw [e] at this
    exact absurd hp (compositeB_sound this)
  | cons p ps ih =>
    intro lo h n h1 h2 hp
    have h' : (allBelow (p - lo) (fun i => compositeB (lo + i)) && gapsOk (p + 1) ps hi) = true := h
    rw [Bool.and_eq_true, allBelow_iff] at h'
    rcases Nat.lt_trichotomy n p with hlt | rfl | hgt
    · have := h'.1 (n - lo) (by omega)
      have e : lo + (n - lo) = n := by omega
      rw [e] at this
      exact absurd hp (compositeB_sound this)
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih h'.2 n (by omega) h2 hp)

theorem highPrimes_gaps : gapsOk 701 highPrimes 4297 = true := by decide +kernel

/-- The list `highPrimes` contains every prime `701 ≤ p ≤ 4297`. -/
theorem mem_highPrimes {p : ℕ} (hp : p.Prime) (h1 : 701 ≤ p) (h2 : p ≤ 4297) : p ∈ highPrimes :=
  gapsOk_sound highPrimes_gaps p h1 h2 hp

/-- `SearchHigh` from the statements for the 465 listed primes. -/
theorem searchHigh_of_list (h : ∀ p ∈ highPrimes, PrimeStatement p (Qlo p)) : SearchHigh :=
  searchHigh_of_primes fun p hp h1 h2 => h p (mem_highPrimes hp h1 h2)

/-- The same with any table of bounds `B p ≤ Qlo p`. -/
theorem searchHigh_of_bounds (B : ℕ → ℕ) (hB : ∀ p ∈ highPrimes, B p ≤ Qlo p)
    (h : ∀ p ∈ highPrimes, PrimeStatement p (B p)) : SearchHigh :=
  searchHigh_of_list fun p hp => (h p hp).mono (hB p hp)

/-- The primes of the list `l` are done (for chaining the per-prime theorems). -/
def Done (l : List ℕ) : Prop := ∀ p ∈ l, PrimeStatement p (Qlo p)

theorem done_nil : Done [] := fun _ h => absurd h List.not_mem_nil

theorem Done.cons {l : List ℕ} (h : Done l) (p : ℕ) (hp : PrimeStatement p (Qlo p)) :
    Done (p :: l) := by
  intro p' hp'
  rcases List.mem_cons.1 hp' with rfl | h'
  · exact hp
  · exact h p' h'

theorem searchHigh_of_done (h : Done highPrimes) : SearchHigh := searchHigh_of_list h

end Exp7.Sieve
