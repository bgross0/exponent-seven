import Exp7Lean.Final2
import Exp7Lean.Sieve.Assembly
import Exp7Lean.SieveLow.XSieve
import Exp7Lean.SieveLow.QSieve

/-!
# Assembly of `Exp7.SearchLow` from the per-prime statements

`SearchLow` follows from `LowStatement p (QloFull p) QLOW survivorQs` for the primes `3 ≤ p < 2760`
(`searchLow_of_primes`); the hypothesis `q.Prime` of `SearchLow` is not used.  The 401 primes are
listed in `lowPrimes`, and the list is proved complete (`mem_lowPrimes`), so that 401 theorems, one
per generated file, give `SearchLow` (`searchLow_of_done`, with `DoneLow` to chain them).

The generated files prove `LowStatement p Q 310000000000000000000 (survSlice a n)`, where `Q` is the
numeral `QloFull p` and `survSlice a n` is the part of the list `survivorQs` that belongs to `p`;
`lowStatement_of_cert` turns this into the form used here.
-/

namespace Exp7.SieveLow

open Exp7.Sieve

/-- `SearchLow` from the per-prime statements. -/
theorem searchLow_of_primes
    (h : ∀ p, p.Prime → 3 ≤ p → p < 2760 → LowStatement p (QloFull p) QLOW survivorQs) :
    SearchLow :=
  fun p hp h3 hlt x y q hy hpy hS hq hqb h8 hj _ => h p hp h3 hlt x y q hy hpy hS hq hqb h8 hj

/-- The 401 primes `3 ≤ p < 2760`. -/
def lowPrimes : List ℕ :=
  [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97,
   101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193,
   197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307,
   311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419, 421,
   431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503, 509, 521, 523, 541, 547,
   557, 563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619, 631, 641, 643, 647, 653, 659,
   661, 673, 677, 683, 691, 701, 709, 719, 727, 733, 739, 743, 751, 757, 761, 769, 773, 787, 797,
   809, 811, 821, 823, 827, 829, 839, 853, 857, 859, 863, 877, 881, 883, 887, 907, 911, 919, 929,
   937, 941, 947, 953, 967, 971, 977, 983, 991, 997, 1009, 1013, 1019, 1021, 1031, 1033, 1039,
   1049, 1051, 1061, 1063, 1069, 1087, 1091, 1093, 1097, 1103, 1109, 1117, 1123, 1129, 1151, 1153,
   1163, 1171, 1181, 1187, 1193, 1201, 1213, 1217, 1223, 1229, 1231, 1237, 1249, 1259, 1277, 1279,
   1283, 1289, 1291, 1297, 1301, 1303, 1307, 1319, 1321, 1327, 1361, 1367, 1373, 1381, 1399, 1409,
   1423, 1427, 1429, 1433, 1439, 1447, 1451, 1453, 1459, 1471, 1481, 1483, 1487, 1489, 1493, 1499,
   1511, 1523, 1531, 1543, 1549, 1553, 1559, 1567, 1571, 1579, 1583, 1597, 1601, 1607, 1609, 1613,
   1619, 1621, 1627, 1637, 1657, 1663, 1667, 1669, 1693, 1697, 1699, 1709, 1721, 1723, 1733, 1741,
   1747, 1753, 1759, 1777, 1783, 1787, 1789, 1801, 1811, 1823, 1831, 1847, 1861, 1867, 1871, 1873,
   1877, 1879, 1889, 1901, 1907, 1913, 1931, 1933, 1949, 1951, 1973, 1979, 1987, 1993, 1997, 1999,
   2003, 2011, 2017, 2027, 2029, 2039, 2053, 2063, 2069, 2081, 2083, 2087, 2089, 2099, 2111, 2113,
   2129, 2131, 2137, 2141, 2143, 2153, 2161, 2179, 2203, 2207, 2213, 2221, 2237, 2239, 2243, 2251,
   2267, 2269, 2273, 2281, 2287, 2293, 2297, 2309, 2311, 2333, 2339, 2341, 2347, 2351, 2357, 2371,
   2377, 2381, 2383, 2389, 2393, 2399, 2411, 2417, 2423, 2437, 2441, 2447, 2459, 2467, 2473, 2477,
   2503, 2521, 2531, 2539, 2543, 2549, 2551, 2557, 2579, 2591, 2593, 2609, 2617, 2621, 2633, 2647,
   2657, 2659, 2663, 2671, 2677, 2683, 2687, 2689, 2693, 2699, 2707, 2711, 2713, 2719, 2729, 2731,
   2741, 2749, 2753]

theorem lowPrimes_gaps : gapsOk 3 lowPrimes 2759 = true := by decide +kernel

/-- The list `lowPrimes` contains every prime `3 ≤ p < 2760`. -/
theorem mem_lowPrimes {p : ℕ} (hp : p.Prime) (h1 : 3 ≤ p) (h2 : p < 2760) : p ∈ lowPrimes :=
  gapsOk_sound lowPrimes_gaps p h1 (by omega) hp

/-- `SearchLow` from the statements for the 401 listed primes. -/
theorem searchLow_of_list (h : ∀ p ∈ lowPrimes, LowStatement p (QloFull p) QLOW survivorQs) :
    SearchLow :=
  searchLow_of_primes fun p hp h1 h2 => h p (mem_lowPrimes hp h1 h2)

/-- The survivors number `a, …, a + n - 1` (those of one prime `p`). -/
def survSlice (a n : ℕ) : List ℕ := (survivorQs.drop a).take n

theorem mem_of_mem_survSlice {a n q : ℕ} (h : q ∈ survSlice a n) : q ∈ survivorQs :=
  List.mem_of_mem_drop (List.mem_of_mem_take h)

/-- From the statement proved by a generated file to the instance of `SearchLow`. -/
theorem lowStatement_of_cert {p Q a n : ℕ} (hQ : Q ≤ QloFull p)
    (h : LowStatement p Q 310000000000000000000 (survSlice a n)) :
    LowStatement p (QloFull p) QLOW survivorQs :=
  h.mono hQ (le_of_eq rfl) fun _ hq => mem_of_mem_survSlice hq

/-- The same for an explicit list of survivors. -/
theorem lowStatement_of_cert_list {p Q : ℕ} {listed : List ℕ} (hQ : Q ≤ QloFull p)
    (hl : ∀ q ∈ listed, q ∈ survivorQs)
    (h : LowStatement p Q 310000000000000000000 listed) :
    LowStatement p (QloFull p) QLOW survivorQs :=
  h.mono hQ (le_of_eq rfl) hl

/-- The primes of the list `l` are done (for chaining the per-prime theorems). -/
def DoneLow (l : List ℕ) : Prop := ∀ p ∈ l, LowStatement p (QloFull p) QLOW survivorQs

theorem doneLow_nil : DoneLow [] := fun _ h => absurd h List.not_mem_nil

theorem DoneLow.cons {l : List ℕ} (h : DoneLow l) (p : ℕ)
    (hp : LowStatement p (QloFull p) QLOW survivorQs) : DoneLow (p :: l) := by
  intro p' hp'
  rcases List.mem_cons.1 hp' with rfl | h'
  · exact hp
  · exact h p' h'

theorem searchLow_of_done (h : DoneLow lowPrimes) : SearchLow := searchLow_of_list h

/-- Variants of the per-range theorems with `S` given as a numeral. -/
theorem low_of_upTo' {p S Qa Qb Y : ℕ} {listed : List ℕ} (hS : S = 4 * p ^ 7)
    (hY : S < Qa * (Y + 1) ^ 2) (h : UpTo p S Qa Qb p listed Y) : LowStatement p Qa Qb listed := by
  subst hS
  exact low_of_upTo hY h

theorem nosolOk_sound' {p S q : ℕ} {t : Task} (hS : S = 4 * p ^ 7)
    (h : nosolOk p S q t = true) : NoSol p q := by
  subst hS
  exact nosolOk_sound h

end Exp7.SieveLow
