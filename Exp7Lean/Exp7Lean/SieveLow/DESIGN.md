# SearchLow: a kernel-checkable certificate for the low-range search

Status: design, soundness proofs, generator and runner are done; six primes covering both
regimes are checked end to end in the kernel (section 6). The full run over the 401 primes has
**not** been executed (section 8): it is one command (section 9), projected at 9 core-hours
(2.3 hours of wall time with 4 Lean processes).

All numbers below were measured on the project machine while it was loaded (load average 30 to
40 on 28 cores); times are CPU seconds of one Lean process unless stated otherwise.

## 1. The statement, and the one idea that makes it cheap

```lean
def SearchLow : Prop :=
  ∀ p, p.Prime → 3 ≤ p → p < 2760 → ∀ x y q : ℕ, 1 ≤ y → ¬ p ∣ y →
    4 * p ^ 7 = x ^ 2 + q * y ^ 2 → QloFull p ≤ q → q < QLOW → q % 8 = 3 →
    (∀ l, l.Prime → 3 ≤ l → l < p → jacobiSym (-(q : ℤ)) l = -1) → q.Prime →
    q ∈ survivorQs
```

The C search (`lowrange/lowsearch.c`) enumerates, for each `p`, all `y ≤ ymax = √(S / Qlo)`
(`S = 4 p ^ 7`), the square roots of `S` modulo `y ^ 2`, and the `x` in each class. Summed over
the 401 primes this is 7.3·10^7 values of `y`, 9.6·10^7 root classes and 2.8·10^12 candidates.
Mirroring this in the kernel has two regimes: small `y` (long progressions, a bitset sieve as in
`Sieve/Bridge.lean`) and large `y` (tens of millions of `y` with zero or one candidate each).
The second regime is the problem: at the costs measured in section 5 (0.06 ms of kernel and 0.2 ms
of elaboration for a `y` without roots; 12 to 17 ms of kernel and 3 ms of elaboration for a `y`
with roots and short blocks, 22 % of them), 7.3·10^7 values of `y` cost about 80 core-hours and
2 GB of source.

**The second regime is not needed.** Large `y` means small `q` (`q ≤ S / y ^ 2`), and for small
`q` the hypothesis on `q` alone is already almost contradictory: `q ≡ 3 (mod 8)` and
`(-q / l) = -1` for *every* odd prime `l < p`. This is a condition on `q` only; it involves
neither `x` nor `y` nor even `p` (except as the bound for `l`), and it is periodic in `q`
modulo each `l`. So the range of `q` is cut at a point `Qm`:

* **Part B, `Qlo ≤ q < Qm`: sieve over `q`.** A packed-bitset sieve over the interval
  `[Qlo, Qm)` of the class `q ≡ 3 (mod 8)`, with one pattern of period `l` per prime `l < p`
  (Euler's criterion for `-q`), proves `QStmt p Qlo Qm E`: every `q` of the interval satisfying
  the hypothesis is in an explicit list `E` (empty for all `p ≥ 113` with the cuts chosen by the
  generator; 315 elements in total over all primes). Each `e ∈ E` is then either
  a member of `survivorQs`, or is shown to have no solution at all (`NoSol p e`: a third little
  sieve, over `y`, with the conditions "`S - e y ^ 2` is a square modulo `m`" for auxiliary
  primes `m`).
* **Part A, `Qm ≤ q < QLOW`: sieve over `x`, for `y ≤ Y0` only**, where
  `Y0 = ⌊√(S / Qm)⌋` is now a few hundred to a few ten thousand instead of up to 1.1·10^6
  (median 3469, maximum 39 706; 3.07·10^6 values of `y` over all primes instead of 7.28·10^7).
  For each `y` the square roots of `S` modulo `y ^ 2` come from the existing certificates
  (`Sieve/RootsCert.lean`), and each class is sieved as in `Bridge.lean`, with a window
  `Xa ≤ x < Xb` (lower *and* upper bound for `q`) and with listed survivors.

The cost of part B is proportional to `Qm ≈ S / Y0 ^ 2` (about 5 ns per integer `q ≡ 3 (mod 8)`
that survives the wheel), the cost of part A grows with `Y0` (5 to 15 ms per `y`, all `y`
included, elaboration too); the generator chooses `Y0` per prime with a cost model (section 5). Part B is used for
186 primes, from `p = 29` to `p = 1187`. For larger primes `Qlo` is large, `ymax ≤ 40 000`, and
part A does everything (as it does for `p ≤ 23`, where `ymax ≤ 369`).

The three sieves (over `q`, over `x` for one `y`, over `y` for one exceptional `q`) are instances
of one generic checker (`Core.lean`), so there is a single soundness proof for the bit-level
machine.

`SearchLow` is proved **as stated**; no change of statement is proposed. The hypothesis `q.Prime`
is not used (every survivor of the search is in `survivorQs`, prime or not), and neither is GRH.

## 2. What is proved (exact statements)

`Exp7Lean/SieveLow/Stmt.lean`

```lean
def LowStatement (p Qa Qb : ℕ) (listed : List ℕ) : Prop :=
  ∀ x y q : ℕ, 1 ≤ y → ¬ p ∣ y → 4 * p ^ 7 = x ^ 2 + q * y ^ 2 → Qa ≤ q → q < Qb → q % 8 = 3 →
    (∀ l : ℕ, l.Prime → 3 ≤ l → l < p → jacobiSym (-(q : ℤ)) l = -1) → q ∈ listed

theorem LowStatement.glue (h1 : LowStatement p Qa Qm listed) (h2 : LowStatement p Qm Qb listed) :
    LowStatement p Qa Qb listed
```

`Exp7Lean/SieveLow/Core.lean` (generic: `P : ℕ → Prop` any set, `F : Fam` a family of periodic
necessary conditions, `t : Task` the classes/window/wheel/patterns/exceptions)

```lean
theorem Task.ok_sound (hF : F.Sound P) (he : ∀ p ∈ extra, PatSound P t.stepF t.nmax p)
    (h : t.ok F extra bases = true) (hx : P x) (hb : ∃ b ∈ bases, ∃ k, x = b + t.step0 * k)
    (ha : t.Xa ≤ x) (hxb : x < t.Xb) : x ∈ t.exc
theorem Task.sound (hF : F.Sound P) (he : …) (hh : t.header F bases chunk m = true)
    (hs : t.ShardsUpTo F extra bases chunk m) … : x ∈ t.exc          -- the same, cut into shards
```

`Exp7Lean/SieveLow/QSieve.lean` (part B)

```lean
def QStmt (L Qa Qb : ℕ) (E : List ℕ) : Prop := ∀ q, Qa ≤ q → q < Qb → q % 8 = 3 → Inert L q → q ∈ E
def NoSol (p q : ℕ) : Prop := ∀ x y : ℕ, ¬ p ∣ y → 4 * p ^ 7 = x ^ 2 + q * y ^ 2 → False
theorem qOk_sound (h : qOk L Qa Qb t = true) : QStmt L Qa Qb t.exc
theorem q_sound (hh : qHeader L Qa Qb t chunk m = true)
    (hs : t.ShardsUpTo (famQ L) [] [3] chunk m) : QStmt L Qa Qb t.exc
theorem nosolOk_sound (h : nosolOk p (4 * p ^ 7) q t = true) : NoSol p q
theorem low_of_q (hq : QStmt p Qa Qb E) (hE : ExcDone p listed E) : LowStatement p Qa Qb listed
```

`Exp7Lean/SieveLow/XSieve.lean` (part A)

```lean
def YStmt (p S Qa Qb L : ℕ) (listed : List ℕ) (y : ℕ) : Prop :=
  ∀ x q : ℕ, ¬ p ∣ y → S = x ^ 2 + q * y ^ 2 → Qa ≤ q → q < Qb → q % 8 = 3 → Inert L q → q ∈ listed
theorem XC.ok_sound (hy : 1 ≤ y) (h : c.ok S Qa Qb L listed y = true) : YStmt p S Qa Qb L listed y
theorem XC.sound (hy : 1 ≤ y) (hh : c.header S Qa Qb L listed y chunk m = true)
    (hs : c.ShardsUpTo S L y chunk m) : YStmt p S Qa Qb L listed y
theorem XT.ok_sound (hy : 1 ≤ y) (htp : tpOk L tp = true)
    (h : c.ok S Qa Qb L listed tp d y = true) : YStmt p S Qa Qb L listed y
theorem UpTo.range (h : UpTo p S Qa Qb L listed n)
    (hr : rangeOk p S Qa Qb L listed tp d n n' cs = true) : UpTo p S Qa Qb L listed n'
theorem low_of_upTo (hY : 4 * p ^ 7 < Qa * (Y + 1) ^ 2) (h : UpTo p (4 * p ^ 7) Qa Qb p listed Y) :
    LowStatement p Qa Qb listed
```

`Exp7Lean/SieveLow/Assembly.lean`

```lean
theorem searchLow_of_primes
    (h : ∀ p, p.Prime → 3 ≤ p → p < 2760 → LowStatement p (QloFull p) QLOW survivorQs) : SearchLow
theorem mem_lowPrimes (hp : p.Prime) (h1 : 3 ≤ p) (h2 : p < 2760) : p ∈ lowPrimes   -- 401 primes
theorem lowStatement_of_cert (hQ : Q ≤ QloFull p)
    (h : LowStatement p Q 310000000000000000000 (survSlice a n)) :
    LowStatement p (QloFull p) QLOW survivorQs
theorem searchLow_of_done (h : DoneLow lowPrimes) : SearchLow
```

A generated file `P<p>.lean` proves
`theorem Exp7.searchLow_<p> : LowStatement <p> (QloFull <p>) QLOW survivorQs`, and
`gen_low_all.py` chains the 401 of them into `theorem Exp7.searchLow : Exp7.SearchLow`.

`Audit.lean` prints the axioms of 25 theorems: all `[propext, Classical.choice, Quot.sound]`.
No `sorry`, no new axiom, no `native_decide`; every computation is `decide +kernel`.

## 3. The generic checker (`Core.lean`)

A **family** `F : Fam` gives, for the moduli `m` with `F.valid m`, a condition `F.cond m r` on
residues, with `F.Sound P : x ∈ P → F.cond m (x % m)`. A **task** is

* classes `b (mod step0)`, `b ∈ bases` (the bases are an argument: for part A they are computed
  by the kernel from the root certificate);
* a window `Xa ≤ x < Xb`;
* a wheel `top ++ rest` of moduli: each class is split into `m` classes, those whose residue
  fails `cond` are dropped (`Bridge.walk`, with one table lookup per child). The classes after
  `top` are the *frontier*: a task can be cut into shards of `chunk` frontier classes, one
  `decide +kernel` each, so that the kernel caches (which hold every intermediate big number until
  the end of the declaration) stay within a memory budget;
* groups of sieving moduli: for a group with product `P` and `inv = step⁻¹ mod P` the pattern is
  one number `tile` of `P + nmax` bits, and the block of the class `base` is
  `acc &&& (tile >>> (base * inv % P))`, exactly as in `Bridge.lean`;
* **window**: the block of a class starts at its first element `≥ Xa` (`firstFrom`) and has
  `blockLen Xb · step` bits;
* **exceptions** `exc`: after the sieve the block `acc` need not be `0`; the leaf accepts iff
  `acc ||| E = E`, where `E` has a bit for each listed exception of the block (`leafLo`,
  `excMask`). Soundness (`leafLo_sound`): an element of `P` in the block is in `exc`. What an
  exception *means* is decided by the caller.

Only the forward implication "element of `P` ⇒ bit set" is ever needed, so tables may contain
extra bits and no bound on their size has to be proved.

Kernel-time details that matter (all measured, section 5):

* *Dilated tables.* The pattern of the modulus `l` for a step `s` is `j ↦ cond l (s j mod l)`.
  Computing it by a loop over `j` costs about 50 µs per `j`, per `l` and per task, and dominated
  everything for part A. Instead `F.dil l inv = Σ_{r admissible} 2 ^ (r · inv mod l)`, a loop over
  the list `resOf (cond l) l` of admissible residues. That list is a *closed term not depending
  on the task*, so the kernel computes it once per declaration (its `whnf` cache is keyed by the
  term); 3 to 4 times cheaper.
* *Flat literals.* Elaboration, not the kernel, was the largest cost of the first version:
  2 ms per list literal `[…]`, 0.7 ms per pair `(a, b)`, 25 ms per certificate with nested
  groups. The groups of a task are therefore one flat list, each group `0, P, inv, d, l₁, …, l_k`
  (`splitZ`), and likewise the entries of a root certificate in table mode. A decoder needs no
  proof: the soundness theorems are about the decoded value.
* `List.map`, `List.append`, `List.drop` are replaced by raw-recursor versions (`mapR`,
  `appendR`, `dropR`, with `_eq` lemmas).

## 4. The three instances

### 4.1 Part B: the sieve over `q` (`QSieve.lean`)

`P = Inert L` (`(-q / l) = -1` for all primes `3 ≤ l < L`), family `famQ L`
(`cond l r = ((l - r) mod l) ^ (l / 2) mod l == l - 1`, for `primeB l`, `3 ≤ l < L`; `primeB` is
the table of primes below 400 of `Bridge.lean`), class `3 (mod 8)`, window `[Qa, Qb)`.
The wheel uses the first 4 to 8 primes (each keeps `(l - 1) / 2` of `l` classes), the patterns the
next 20 to 40. Result: `QStmt L Qa Qb t.exc`.

Primes `l ≥ 400` cannot be used (no primality table); this only matters in principle: a `q` that
survives all `l < 400` but not all `l < p` would simply be one more exception (none occurs).

**Exceptions.** For `p ≤ 109` some `q` do pass the sieve (315 in total, with the cuts chosen). Each is treated separately:
`ExcDone.listed` (it is in the list of survivors, checked by `elemL`) or `ExcDone.nosol` with a
task over `y` for the family `famY p S e`: `y ≢ 0 (mod p)`, and for auxiliary primes `m < 400`,
`(S - e y ^ 2) ^ ((m - 1) / 2) ≢ -1 (mod m)`. The window is `0 ≤ y < Xb` with `S < e Xb ^ 2`,
one block, no wheel, no exceptions allowed; 16 to 26 moduli empty it. About 70 ms per exception
(20 ms of elaboration, 50 ms of kernel).

### 4.2 Part A: the sieve over `x` for one `y` (`XSieve.lean`)

`P = SolLo S Qa Qb L y`, family `famX S L y` (`Bridge.condB` for `primeB l`, `3 ≤ l < L`,
`l ∤ y`). The certificate for one `y` is a `YC`:

| constructor | meaning | check |
|---|---|---|
| `skip` | `p ∣ y` | `y % p == 0` |
| `nonres l` | `S` is a non-residue modulo the odd prime `l ∣ y` | `Roots.noRootsOdd` |
| `two` | 2-adic obstruction | `Roots.noRootsTwo` |
| `full c` | sieve, classes modulo `8 y ^ 2` (`Roots.rootsOf8`), wheel and groups given per `y` | `XC.ok`, or `XC.header` + shards |
| `tab c` | sieve in table mode, classes modulo `y ^ 2` (`Roots.rootsOf`) | `XT.ok` |

Over all primes, 77 % of the `y ≤ Y0` are `nonres`/`two`/`skip` (0.06 ms each), 19 % are `full`
and 4 % are `tab`. `rangeOk` checks a list of `YC` for
consecutive `y` in one `decide +kernel` (up to 1500 `y`, or the memory budget), and `UpTo.range`
chains the ranges; a `y` whose blocks are too long for one declaration gets its own shards
(`XC.sound`).

**Window.** `Xb`: `S - Qa y ^ 2 < Xb ^ 2`. `Xa`: `Xa = 0` or `(Xa - 1) ^ 2 + Qb y ^ 2 ≤ S`
(`SolLo.ge`); this is what keeps the small `y` of the primes near 2700 short
(`x > √(S - QLOW y ^ 2)`).

**Survivors of the sieve** (`excOk`). For each listed `x` the kernel computes
`q = (S - x ^ 2) / y ^ 2` and accepts if one of the primes `wits` of the certificate has
`(-q / l) ≠ -1` (`witOk`, Euler's criterion on the explicit `q`; needed because the sieve cannot
use the primes dividing `y`, and uses only as many primes as pay off), or if `q` is in `listed`.
In table mode also if `q % 8 ≠ 3` (`excOk8`).

**`listed`.** The survivors of the C search are stored in `survivorQs` in the order of the search,
so those of one prime are a contiguous slice: `listed = survSlice a n =
(survivorQs.drop a).take n`, and `mem_of_mem_survSlice` needs no computation. Membership is a
linear scan (20 µs per element): 6 s for `p = 11` (708 survivors), about 1 minute for all primes
together. This is the only place where the 6608 survivors enter.

**Table mode** (blocks of at most 189 bits, i.e. `y ≥ √(X / 189)` where `X = √S`: the bulk of
the `y` for `p ≲ 700`, the last quarter for `p ≈ 1000`, none for `p ≳ 1500`). The step `y ^ 2`
changes with `y`, so the patterns have to be made for every `y`. All the
dilations of the table of `l` are computed once per declaration into one number `dilTab S l d`
(field `u < l`, of `l · 2 ^ d` bits: the pattern for `step ≡ u (mod l)`, already tiled), and the
pattern for `y` is one shift. The inverse of the step modulo `l` is computed by the kernel
(`step ^ (l - 2) mod l`) and *tested*; a prime that divides `y`, or fails a test, is skipped
(always sound), so there is no per-`y` data for the sieve at all: a table-mode certificate is the
root certificate, the window, and the (usually empty) survivors. The classes are taken modulo
`y ^ 2` instead of `8 y ^ 2`: 4 times fewer leaves, and no `rootsOf8` (which costs 0.35 ms per
root); the blocks are 8 times longer but still tiny.

The tiling depth `d` is 3 or 6 (blocks of at most 21 or 189 bits). Depth 10 (blocks up to 3069
bits) was tried and dropped: extracting a field means shifting the whole table above it
(`l² · 2^d` bits, 680 KB for `l = 73`), the kernel keeps every such intermediate until the end of
the declaration (8.7 GB peak for `p = 1009`), and at 33 ms per `y` it was no faster than the
`full` certificates (30 ms per `y`). A list of fields instead of one number would fix both; see
the improvements at the end of section 7.

### 4.3 Glue

`partB : LowStatement p Qa Qm listed` (`low_of_q`), `partA : LowStatement p Qm Qb listed`
(`low_of_upTo'`, with `S < Qm (Y0 + 1) ^ 2`), `main := partB.glue partA`,
`Exp7.searchLow_<p> := lowStatement_of_cert (by decide +kernel) main`.

## 5. Kernel cost model (measured)

| item | cost | measured on |
|---|---|---|
| start of a Lean process importing `Assembly` | 5 s, 4.1 GB mapped | `AllTest.lean` |
| one step of a raw-recursor loop (`allBelow` with `Nat.ble`) | 14 µs | 1000 iterations |
| `Nat.shiftRight` of a 64 KB literal | 124 µs (0.24 ns/bit) | 1000 iterations |
| `Nat.land` of 32 KB literals | 73 µs (0.28 ns/bit) | 1000 iterations |
| one group step of a leaf: shift + and | 45 to 60 µs + 0.7 ns per bit of the block | `p = 211`, `1009`, `2713` |
| one leaf without patterns (window, mask, compare) | 0.12 ms; 0.35 ms inside a task | 1000 leaves |
| one child of a wheel node | 30 µs | |
| table entry in a `mkBits` loop (`cond` with a `Nat.pow`) | 50 µs | base tables, 14 primes |
| `dilTab`: per entry (`Σ l²` entries per declaration) | 58 µs | 14 primes |
| table mode: pattern of one prime for one `y` | 0.22 to 0.3 ms | 1000 `y` × 14 primes; `p = 1009` |
| `full` certificate: patterns of one `y` (`Σ l` over its sieving primes) | 30 µs per unit of `l`, 15 to 45 ms per `y` | `p = 1009` |
| `rootsOk` (2 odd primes) / `rootsOf` / `rootsOf8` (4 roots) | 0.32 / 0.2 / 1.6 ms | 500 iterations |
| `noRootsOdd` | 0.05 ms | 1000 iterations |
| `elemL` in the list of survivors | 23 µs per element | 250 000 steps |
| `nosolOk` for one exception | 50 ms + 20 ms elaboration | `p = 97`, 45 exceptions |
| elaboration: list literal / pair / numeral in a flat list | 2 ms / 0.7 ms / 35 µs | 200 copies |
| elaboration: `full` / `tab` / other certificate | 8 / 3 / 0.2 ms | `p = 211` |
| kernel cache per leaf | 30 to 60 KB + 0.26 byte per bit and group step | Bridge model, rescaled |

The big-number operations of the kernel cost 1.5 to 2 ns per byte, 10 to 20 times more than a
`memcpy` (conversion between literals and GMP numbers); this, not the cache size, fixes the
0.7 ns per bit and group step. Consequences for the plans: blocks of 10^5 to 4·10^5 bits and
deep wheels in part B; in part A as few leaves as possible.

The generator (`gen_low.py`) simulates the kernel computation exactly (same blocks, same bits),
so the numbers of leaves, group steps and bits in its estimate are exact; only the constants above
are approximate. Estimate versus measurement:

| `p` | estimate: kernel + elaboration + 5 s of imports | measured (user CPU) |
|---|---|---|
| 11 | 0.2 + 0.0 + 5 = 5.2 s (the scan of the 708 survivors, 6 s, is not in the model) | 11.8 s |
| 97 | 3.3 + 0.8 + 5 = 9.1 s | 11.2 s |
| 211 | 11.1 + 2.4 + 5 = 18.5 s | 18.4 s |
| 257 | 8.4 + 2.2 + 5 = 15.6 s | 16.8 s |
| 1009 | 188.2 + 48.7 + 5 = 241.9 s | 259.8 s |
| 2713 | 9.2 + 0.6 + 5 = 14.8 s | 14.5 s |

The constants of the per-`y` costs were fitted on a first run of `p = 1009` (280 s, with table
mode up to depth 10, for which the model said 205 s); the six lines above are the final plans, run
afterwards.

## 6. End-to-end kernel-checked instances

Each line is a complete proof of `Exp7.searchLow_<p> : LowStatement p (QloFull p) QLOW
survivorQs`, ending with `'Exp7.searchLow_<p>' depends on axioms: [propext, Classical.choice,
Quot.sound]`. They were produced by `PRIMES="11 97 211 257 2713 1009" run_low.sh 1`
(`logs/times.txt`). Times are user CPU seconds of the Lean process, including 5 s of imports;
the peak memory includes 4.1 GB of mapped `.olean` files.

| `p` | `ymax` of the C search | `Y0` | part B: window, leaves, bits, exceptions | part A: sieves, leaves, bits | survivors | CPU | peak RSS |
|---|---|---|---|---|---|---|---|
| 11 | 27 | 27 | none | 8, 30, 6.7·10^3 | 708 | 11.8 s | 4.7 GB |
| 97 | 56 850 | 372 | `[10^5, 2.3·10^9)`, 30 leaves, 14 exceptions (none is a solution) | 118, 800, 4.4·10^6 | 3 | 11.2 s | 4.4 GB |
| 211 | 863 015 | 909 | `[10^5, 9.0·10^10)`, 180 leaves, none | 301, 3924, 3.3·10^7 | 0 | 18.4 s | 5.2 GB |
| 257 | 1 128 795 | 1136 | `[232 467, 2.3·10^11)`, 1440 leaves, none | 256, 2284, 4.8·10^7 | 0 | 16.8 s | 4.8 GB |
| 1009 | 87 895 | 20 679 | `[5.5·10^11, 1.0·10^13)`, 12 960 leaves, 3.1·10^9 bits, 15 shards, none | 6797, 77 590, 1.2·10^9 | 0 | 259.8 s | 6.1 GB |
| 2713 | 157 | 157 | none | 77, 3572, 6.5·10^8 | 0 | 14.5 s | 5.0 GB |

`p = 11` contains `q = 118843` (at `(x, y) = (8128, 10)`); `p = 97` is the largest prime with a
prime survivor; `p = 257` has the largest `ymax` of all primes (the C search examined 1 477 953
root classes and 2.97·10^8 candidates for it); `p = 1009` is in the most expensive zone
(`700 < p < 1500`); `p = 2713` is a prime where the lower bound of the window matters.

Three more checks, on files that are not kept:

* `p = 41` with the cut forced to `Y0 = 1000` (`--ycut 1000`): the two survivors with `y = 1373`
  and `y = 1559` are then found by the sieve over `q` and go through `ExcDone.listed`, the ten
  other exceptions through `ExcDone.nosol`, and 350 survivors through part A; 12.7 s.
* `p = 1621`, `y ≤ 3`, with `--budget 3e7`: the certificate of `y = 3` is cut into 4 shards
  (`XC.header`, `XC.sound`); theorem `UpTo … 3`, 6.2 s.
* `gen_low_all.py --test 11 97 211 257 1009 2713`: `done_test : DoneLow [11, 97, 211, 257, 1009,
  2713]` from the six compiled files, axioms `[propext, Classical.choice, Quot.sound]`, 5.2 s.

Cross-check of the survivors: the generator does not read the log of the C search to build a
certificate; it redoes the search (Python integers, the same blocks as the kernel) and then
asserts that the set of `q` it found for `p` (a) is a contiguous slice of `survivorQs`
(`Witness/SurvivorData.lean`), and (b) equals the set of `q` of the lines `S p x y q` of
`lowrange/low_survivors.txt`. Both hold for **all 401 primes**: `estimate_low.sh` planned every
prime (20 minutes of Python in total, at most 11 s per prime); the generator found 6608 survivors,
for 25 primes, and no assertion failed.

## 7. Alternatives considered

* **A bitset over `y` with the multiples of all non-residue primes struck out; per-`(p, l)`
  tables of square roots modulo `l ^ 2`; compact per-`y` records.** These are the ways to make
  the regime "large `y`" cheap. They are not needed: with the sieve over `q`, part A stops at
  `Y0 ≤ 39 706` (median 3469), 3.07·10^6 values of `y` in total instead of 7.28·10^7. A bitset
  over `y` would remove the 78 % of `y` without roots almost for free (about 40 000 primes `l` to
  strike per `p`, each with a proof that `l` is prime and `S` a non-residue, 0.05 ms each), but
  the 1.6·10^7 values of `y` *with* roots would remain, each with at least a root certificate
  check (0.5 ms), the patterns and two or more leaves: 5 ms per `y` at the very least with the
  measured kernel costs, i.e. more than 20 core-hours, against the 9 of the present design for
  everything. The existing per-`y` root certificates are used unchanged for `y ≤ Y0`.
* **Treating all `y` above a threshold by a different argument.** Adopted, in the strongest
  form: the argument for `q < Qm` does not look at `y` at all.
* **Raising the direct bound `B`.** Not useful, and no statement has to change. `B` is the lower
  end of the window of part B, whose cost is proportional to its *length* `Qm - Qlo`
  (`Qm` is 10^9 to 10^13); raising `B` from 10^5 to, say, 10^7 would shorten it by less than 1 %
  for `p ≥ 97`, at a cost of 2.4 ms per prime `q` in the direct table (about 3.3·10^5 primes
  `q ≡ 3 (mod 4)` below 10^7: 13 minutes). For the primes `p < 100` (the only ones where `B`
  is felt) everything together costs 3 minutes.
* **The GRH-conditional bounds `QloRobust`.** They would raise `Qlo` and shrink `ymax` by about
  20 %. Where there is a part B this only shortens the window of the sieve over `q` at its cheap
  end; where there is none (`p > 1187`) it removes the largest 20 % of the `y`, which are the
  cheapest ones. Not measured; certainly below 10 % of the total, and it would add GRH as a
  hypothesis of the theorem. Not used.
* **The residue tree of `Bridge.lean` for the roots modulo `8 y ^ 2`.** A level for a prime
  `l ∣ y` tests `l` children: fine for `y ≤ 126`, quadratic for `y` up to 26 000. Replaced by the
  root certificates.
* **Testing each candidate `x` directly** (compute `q`, find a prime with `(-q / l) ≠ -1`).
  About 60 µs per candidate; competitive only for blocks of one or two bits, which part B has
  removed. It survives as the treatment of the `x` left by the sieve (`witOk`).
* **A sieve over `q` for the whole range.** The window would be `[Qlo, 3.1·10^20)`: 10^17 bits
  after an 8-prime wheel. Only the part below `Qm` is feasible, hence the cut.
* **Sorting or indexing the list of survivors.** Not worth it (1 minute in total).

Possible improvements that were *not* done (each is local to the generator or to one checker,
none changes a statement):

* the `full` certificates of the `y` with blocks of 200 to 10^4 bits are the largest single cost
  for `700 ≲ p ≲ 1700` (30 ms per `y`, about half of it the patterns of the large sieving primes,
  the rest wheel tables and `rootsOf8`). Table mode with a *list* of fields (`dilList`, access by
  index instead of a shift of the whole table) would work at any depth, without the memory
  problem, at an estimated 10 to 15 ms per `y`;
* table mode uses one prime per group step (10 steps per leaf for blocks of 100 bits); dilation
  tables for the composite moduli `3·5·7` and `11·13` would save 3 of them;
* certificates still contain one to three list literals each (2 ms per literal); one flat list
  per range with a kernel-side decoder would save most of the elaboration time (15 to 20 % of
  the total);
* 5 s of imports per prime are 33 minutes over 401 files; batching several small primes per
  file would remove most of it;
* the cut `Y0` is chosen with a single average cost per `y` (`C_A`), not with the real plan.

## 8. Projected total cost, and what remains

From the plans of all 401 primes (`logs/estimate.txt`, model of section 5; the plans are exact
counts of the work, only the constants are fitted):

| primes | number | kernel | elaboration | average per prime (with imports) |
|---|---|---|---|---|
| `p < 100` | 24 | 46 s | 12 s | 7 s |
| `100 < p < 300` | 37 | 256 s | 58 s | 13 s |
| `300 < p < 700` | 63 | 2653 s | 603 s | 57 s |
| `700 < p < 1100` | 59 | 7542 s | 1668 s | 161 s |
| `1100 < p < 1500` | 55 | 8506 s | 2259 s | 201 s |
| `1500 < p < 2000` | 64 | 4125 s | 720 s | 81 s |
| `2000 < p < 2760` | 99 | 2310 s | 159 s | 30 s |
| all | 401 | 25 437 s | 5479 s | |

Kernel 7.1 h + elaboration 1.5 h + imports 0.6 h (5 s × 401) + scans of the lists of survivors
(1 minute) = **9.2 core-hours**, one core each; the most expensive prime is `p = 1171` (about
6 minutes). On `p = 1009` the measurement is 7 % above this model, on the four smaller demo primes
at or below it. Generation: 20 minutes of Python in total. Source: about 200 MB for the 401 files
(1.8 MB for `p = 1009`); `KEEP=0` deletes each file once compiled. Memory: one Lean process peaks
at 6.1 GB on `p = 1009` (4.1 GB of it are the mapped `.olean` files, shared between processes).
In total the certificates contain 705 624 sieves over `x` (127 669 in table mode), 9.7·10^6
leaves and 4.4·10^11 block bits in part A.

What is **not** done:

1. The 401 per-prime files have not been generated and checked, except the ones of section 6.
   `Exp7.searchLow : Exp7.SearchLow` is therefore not yet a theorem; `All.lean` does not exist
   (`gen_low_all.py` writes it; its mechanism was tested on the primes of section 6, theorem
   `done_test : DoneLow [11, 97, 211, 257, 1009, 2713]`). The generator has however planned all
   401 primes without a failed assertion, and the kernel does exactly the computation that the
   generator simulates.
2. A `decide +kernel` can fail only if the generator's simulation and the kernel disagree (it did
   not happen in any run), or if a declaration exceeds the memory of the machine; then lower
   `--budget` (default 6·10^8 bytes of estimated kernel cache per declaration) for that prime.
   The estimates of memory are extrapolated from the model of `Bridge.lean`; the only large
   measured case is `p = 1009` (2 GB above the imports). The primes `1100 < p < 1300` have
   about 1.5 times more work per declaration of the same kind; they have not been run.
3. The cost constants were measured on a loaded machine (load 30 to 40 on 28 cores); the
   projection is good to about ± 30 %.
4. Sieving primes `l ≥ 400` are not available (the primality table `primeB` stops at 400). No
   prime needed one; if an `x` or a `q` survived all `l < 400` without being a survivor of the
   search, the generator would stop with an assertion ("no witness below 400").

Nothing in the soundness chain is assumed: once the 401 files and `All.lean` compile,
`Exp7.searchLow` depends on `propext`, `Classical.choice`, `Quot.sound` only.

## 9. How to run

```
cd <workspace root>
Exp7Lean/SieveLow/estimate_low.sh 3          # optional: plans only (Python), logs/estimate.txt
Exp7Lean/SieveLow/run_low.sh 4               # 401 primes, 4 Lean processes; restartable
python3 Exp7Lean/SieveLow/gen_low_all.py && /home/zlab/GitHub/exp7-agents/bin/leanq Exp7Lean/SieveLow/All.lean
```

`run_low.sh` writes one line per prime to `Exp7Lean/SieveLow/logs/times.txt`
(`p OK user_s elapsed_s maxrss_kb | STAT …`), keeps the log of a failed prime, and accepts a prime
only if the axiom line is the expected one. `PRIMES="11 97" run_low.sh` does a subset.

## 10. Files

| file | content |
|---|---|
| `Core.lean` | generic sieve: `Fam`, `Task`, `leafLo`, `Task.ok_sound`, `Task.sound` |
| `Stmt.lean` | `LowStatement`, `glue`, `euler_neg`, `witOk` |
| `XSieve.lean` | part A: `famX`, `XC`, table mode (`dilTab`, `tabPats`, `XT`), `YC`, `rangeOk`, `UpTo` |
| `QSieve.lean` | part B: `famQ`, `QStmt`, `famY`, `NoSol`, `ExcDone`, `low_of_q` |
| `Assembly.lean` | `lowPrimes`, `survSlice`, `lowStatement_of_cert`, `searchLow_of_done` |
| `Audit.lean` | `#print axioms` of the 25 main theorems |
| `gen_low.py` | generator (and exact simulator) of `P<p>.lean` |
| `gen_low_all.py` | writes `All.lean` |
| `run_low.sh`, `estimate_low.sh` | runner; plans without Lean |
| `P11.lean`, `P97.lean`, `P211.lean`, `P257.lean`, `P1009.lean`, `P2713.lean` | the instances of section 6 |
