# Imaginary quadratic fields with class group of exponent 7

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24549331.svg)](https://doi.org/10.5281/zenodo.24549331)

Ben Gross. 25 November 2026, revised 27 November 2026.

**Status: computer-assisted research note for independent review. Not refereed.**

- **Main result (Theorem E), formalized in Lean 4.** Assuming GRH for the quadratic characters of prime conductor, exactly 33 negative fundamental discriminants have class group of exponent 7. The Lean statement uses Mathlib's `ClassGroup` and covers every negative fundamental discriminant, with no size bound and no published bound assumed. GRH is its only hypothesis.
- **With GRH supplied by the formal proof.** In a Lean 4.35 workspace that also builds the formal proof of GRH for Dirichlet L-functions announced by Alpöge on 20 November 2026 (`lsernau/grh-lean`), the proof supplies GRH and both searches. The statement applies to quadratic orders that are domains with negative fundamental discriminant. That proof of GRH is machine-checked but not refereed, so the unconditional reading inherits its status.
- **Searches.** The search above 3.1·10^20 has three implementations with different algorithms, one written by a different AI system; all three find 0 survivors. Both searches are also proved complete in Lean's kernel, from 465 and 401 per-prime certificates.
- **Certificate.** Checked by two independent verifiers; its margins are proved in Lean.
- **The 33 fields.** Rederived from scratch below 3.1·10^20 (Theorem D); the list agrees with the published table.

Use of AI: the argument, code and computations were produced with Claude (Anthropic), directed by the author. Codex formalized the finite bridge and dyadic tail and integrated the external GRH proof. The independent audit in `independent/AUDIT.md`, with the third search and the second certificate verifier, was produced with Codex (OpenAI). Corrections are welcome through the issue tracker.

## Result

Write E(D) for the exponent of the class group of Q(√D), D < 0 a fundamental discriminant.

**Theorem A.** Assume GRH for the Dirichlet L-functions L(s, χ_D) of the odd real primitive characters of prime conductor. Then no fundamental discriminant D with 3.1·10^20 ≤ |D| ≤ 10^32 has E(D) = 7.

**Theorem D.** Assume GRH as in Theorem A. Then exactly 33 fundamental discriminants D with |D| ≤ 10^32 have E(D) = 7. This does not use the EKN table: the same method is run from scratch below 3.1·10^20 (see "The range below 3.1·10^20").

**Theorem E.** Assume GRH as in Theorem A. Then exactly 33 negative fundamental discriminants have E(D) = 7, namely D = −q for the primes q = 71, 151, 223, 251, 463, 467, 487, 587, 811, 827, 859, 1163, 1171, 1483, 1523, 1627, 1787, 1987, 2011, 2083, 2179, 2251, 2467, 2707, 3019, 3067, 3187, 3907, 4603, 5107, 5923, 63499 and 118843. The largest absolute discriminant is 118843.

Theorem E is Theorem D together with two exclusions above 10^32 that use the same hypothesis (see "Above 10^32 (Theorem E)"). It needs neither the EKN table nor EKN Theorem 3.

**Corollary B.** Assume ERH for the Dedekind zeta functions of the imaginary quadratic fields (the hypothesis of ARSX Theorem 1.3). Then, in addition to Theorem E, exactly 40 imaginary quadratic orders have Picard group of exponent 7 (largest absolute discriminant 118843).

**Corollary C.** Assume GRH as in Theorem A. Let q ≡ 3 (mod 4) be a prime with q ≥ 3.1·10^20, let p be the least prime that splits in Q(√−q), and let 𝔭 be a prime ideal above p. Then the ideal class of 𝔭 has odd order at least 9.

Corollary C holds for every field in the range, whatever its class group. The proof is after Step 4.

The count of 40 orders in Corollary B follows from Theorem A and ARSX. The first two items below are the route used before Theorem E. They are kept because they give a second derivation of the field count from published results.

- Elsenhans–Klüners–Nicolae (EKN), Theorem 1: the list of fields with E(D) ≤ 8 is complete for |D| ≤ 3.1·10^20 (a computation; the theorem is stated without hypotheses). It has 33 fields of exponent 7 (EKN Table 1).
- EKN Theorem 3 (from Bach–Sorenson, under ERH for the Dedekind zeta function of Q(√D)): for |D| > e^25 some prime p ≤ (1.881 log|D| + 6.18)² splits. A split prime forces |D| ≤ 4p^7 when E(D) = 7 (Step 1 below), so E(D) = 7 needs h(log|D|) ≥ 0, where h(t) = log 4 + 14 log(1.881t + 6.18) − t. Now h′(t) = 14·1.881/(1.881t + 6.18) − 1 < 0 for t > 10.7, so h is decreasing for |D| ≥ 10^32. At the endpoint, log 10^32 < 74 gives 1.881 log 10^32 + 6.18 < 146, and 4·146^14 = 7998342040108832435319302324224 < 10^32, so h(log 10^32) < 0. So no |D| ≥ 10^32 has E(D) = 7 (`kernel_verify.py` also checks this in interval arithmetic).
- Aiken–Ross–Shvydkoy–Xue (ARSX), Theorem 1.3(6): under ERH, their table of 40 orders of exponent 7 is complete if no fundamental D with 3.1·10^20 ≤ |D| ≤ 3.9·10^30 has exponent 7. Theorem A supplies that hypothesis.

**What this adds.** EKN Theorem 2 gives completeness under ERH for exponents ≤ 5 and 8. For exponents 6 and 7 the ERH bounds of their Table 2 (2.5·10^25 and 3.9·10^30) lie beyond their search limit. ARSX recorded both as explicit gaps (Theorem 1.3(5) and (6)). A computer-assisted note of 23 November 2026 ([`nunavipahe60-star/exponent-six`](https://github.com/nunavipahe60-star/exponent-six)) treats the exponent-6 gap. This note treats the exponent-7 gap; a search on 25 November 2026 found no earlier claim. EKN note that finiteness was known unconditionally for exponents 2 ≤ c ≤ 8 except c = 7.

## Proof of Theorem A

Let D be fundamental with E(D) = 7 and 3.1·10^20 ≤ |D| ≤ 10^32.

**Step 0 (genus theory).** The class group has odd order, so its 2-rank is 0 and D has one prime divisor: D = −q with q ≡ 3 (mod 4) prime.

**Step 1 (norm equation).** If a prime p splits, (p) = 𝔭𝔭', then 𝔭^7 = (α) with α = (x + y√−q)/2 and y ≠ 0, because 𝔭^7 is not fixed by conjugation. Taking norms, 4p^7 = x² + q y², so q ≤ 4p^7. Since 4·691^7 < 3.1·10^20, every prime ≤ 691 is inert, and in particular q ≡ 3 (mod 8). Let p be the least split prime. Then p ≥ 701 and every prime l < p is inert.

**Step 2 (a split prime exists below an explicit bound).** Fix X and a real step function g on [0, log X] with 64 equal cells. Let f be its autocorrelation divided by ∫g², so f is even, piecewise linear, f(0) = 1, f vanishes beyond log X, and its Fourier transform is ≥ 0. The Guinand–Weil explicit formula for the odd primitive character χ = (−q/·), with GRH making every zero ordinate real, gives

    2 Σ_{n<X} Λ(n) χ(n) f(log n)/√n  ≤  log(q/π) + ψ(3/4) + J_f,
    J_f = ∫_0^∞ 2e^{−3u/2}/(1 − e^{−2u}) · (1 − f(u)) du.

If no prime below X splits, every prime below X is inert (q is the only ramified prime and q > X), so the left side is the explicit number Σ_{p<X} A_p with A_p = 2 log p Σ_{k≥1, p^k<X} (−1)^k f(k log p) p^{−k/2}. A row (Q, X, g) of the certificate is valid when

    Σ_{p<X} A_p − J_up − log Q + (log π − ψ(3/4)) > 0,     J_up ≥ J_f,

and then every prime q ≤ Q in our family has a split prime below X. `kernel_verify.py` checks each row with outward-rounded interval arithmetic (mpmath `iv`, 40 digits); the autocorrelation values are exact rationals, and the cell containing log n is found by exact integer comparison (X^k ≤ n^64 < X^(k+1)), with no floating point. A second, independently written verifier (`independent/verify_fixedpoint.cjs`, BigInt fixed point at scale 10^−30, its own log and exp series with explicit tail bounds, no mpmath) also accepts all 51 rows, with minimum certified margin 0.0126; its constants π and γ are certified by exact rational series in `independent/verify_constants.py`.

This is the positive-kernel method of the exponent-six note, which applies the explicit formula in the form of Carneiro–Milinovich–Quesada-Herrera–Ramos, Lemma 9. Step 0 simplifies it: with prime conductor there are no ramified primes to pay for.

**Step 3 (bootstrap).** Six rows, each feeding q ≤ 4P^7 (P the largest prime below X) into the next:

| q ≤ Q | X | largest prime P < X | margin > | new bound 4P^7 |
|---|---|---|---|---|
| 10^32 | 6362 | 6361 | 0.0126 | 1.686·10^27 |
| 1.686·10^27 | 4690 | 4679 | 0.0160 | 1.964·10^26 |
| 1.964·10^26 | 4393 | 4391 | 0.0188 | 1.259·10^26 |
| 1.259·10^26 | 4333 | 4327 | 0.0191 | 1.136·10^26 |
| 1.136·10^26 | 4319 | 4297 | 0.0181 | 1.082·10^26 |
| 1.082·10^26 | 4312 | 4297 | 0.0147 | 1.082·10^26 |

So q ≤ 4·4297^7 = 108197560039107534049882852 and the least split prime p satisfies 701 ≤ p ≤ 4297. A further 45 rows (the "ladder", from Q = 8.1·10^25 down to 3.1·10^20) shorten the search: if X_i ≤ p then q > Q_i.

**Step 4 (search).** For each of the 465 primes p in [701, 4297], each y ≥ 1, and each x ≥ 0 with x² ≡ 4p^7 (mod y²) and q = (4p^7 − x²)/y² ≥ Qlo(p), `sieve7` tests the necessary conditions: (−q/l) = −1 for every odd prime l < p, and q ≡ 3 (mod 8). For l ∤ y the condition reads "x² − 4p^7 is a non-residue mod l", which is sieved (a wheel on the first primes, 64-bit patterns for l < 64, then one prime at a time). Totals: 21,577 progressions, 7.8·10^12 positions after the wheel, 1.6·10^10 after the bit patterns, and **0 values of x passing all odd primes l < p**. So no such q exists. ∎

**Proof of Corollary C.** Let n be the order of the class of 𝔭. The class number is odd (genus theory), so n is odd. As in Step 1, 𝔭^n = (α) with α not rational, so q ≤ 4p^n. If q > 10^32, the two exclusions of "Above 10^32 (Theorem E)" give a split prime below some X with 4X^7 < q, so p < X and n ≤ 7 would give q ≤ 4p^7 < q. Now let q ≤ 10^32. By the first bootstrap row, p ≤ 6361. If n ≤ 5 then q ≤ 4·6361^5 < 4.2·10^19 < 3.1·10^20. If n = 7: Steps 1 to 4 used E(D) = 7 only to know that 𝔭^7 is principal for the least split prime p (for p ≥ 701 in Step 1, for q ≤ 4P^7 at each bootstrap row, and for the norm equation in Step 4), and the search found no solution. So n ≥ 9. ∎

Run time: about 25 minutes on 2 vCPUs. The logs are in `logs/prod_0.log` and `logs/prod_1.log`. A full rerun on a separate 28-thread machine (`logs/rerun.log`) gives identical output for all 465 primes.

## Above 10^32 (Theorem E)

Let q ≡ 3 (mod 4) be a prime with q ≥ 10^32. Both exclusions below are certificate rows in the sense of Step 2: under GRH they give a split prime p < X with 4X^7 < q. If the class group had exponent 7, Step 1 would give q ≤ 4p^7 < 4X^7 < q.

- **10^32 ≤ q ≤ 2^135: one row.** X = 30000, and g has 64 cells, the first 32 equal to 1 and the last 32 equal to −1. Lean certifies its margin at Q = 2^135 as at least 7.52277024130489382120 (`Exp7Lean/Exp7Lean/Rows/Bridge30000.lean`, by the same kernel-checked evaluator as the other 175 rows). Since 4·30000^7 < 10^32, the split prime below 30000 satisfies 4p^7 < q. [Proof and receipts](frontier/bridge30000/README.md)
- **q > 2^135: a closed-form row.** Here g = [1, −1] on two cells of [0, log X], so f(u) = 1 − 3u/L on [0, L/2] and f(u) = u/L − 1 on [L/2, L], where L = log X. Lean proves:
  1. For every q > 2^135 there is an n ≥ 19 with 4·(2^n)^7 < q and log q + 4 < B(2^n), where B is an explicit finite prime sum. With w_T(t) = (1 − log(t)/log(T))/√t and Y = X^(1/3), it sums 2w_X(p) log p over primes in (√X, X], subtracts 2Σ w_Y(n)Λ(n) over positive n ≤ Y, and subtracts Σ Λ(m)/m over positive m ≤ √X. The proof uses Mathlib's Chebyshev bounds and Abel summation (`Tail/PositivePrimes.lean`, `OddLoss.lean`, `EvenLoss.lean`, `WeightedComparison.lean`).
  2. B(X) is at most the inert sum Σ A_p of Step 2 for this g (`Tail/HaarInert.lean`).
  3. J_f ≤ 4 when log X ≥ 1 (`Tail/HaarJBound.lean`).

  Since log π ≥ 0 and ψ(3/4) ≤ 0, the row margin at Q = q is positive (`Tail/Exclusion.lean`). [Chebyshev sums](frontier/chebyshev-sums/README.md) · [Tail proof and receipts](frontier/haar-tail/README.md)

Floating-point evaluation using J_f gives a bridge margin of about 7.529. At X = 2^19 the tail row gives Σ − J_f + log π − ψ(3/4) ≈ 381.51, while log q ≤ 142 log 2 ≈ 98.43. The dyadic theorem proves the strict inequality for every n ≥ 19.

The Lean theorem is `Exp7.ChebyshevTail.classification_fundamental`. It takes GRH and the two search statements as explicit arguments, and both search statements are proved (`Exp7.searchHigh`, `Exp7.searchLow`). The fully applied form is `Exp7.GRHIntegration.theoremD_fundamental_global` (`frontier/haar-tail/Global.lean`), whose inputs describe the quadratic order and its discriminant.

```lean
theorem theoremD_fundamental_global (a b : ℤ)
    (hfund : Int.IsFundamentalDiscr (QuadraticAlgebra.discr a b))
    (hneg : QuadraticAlgebra.discr a b < 0) [IsDomain (QuadraticAlgebra ℤ a b)] :
    Monoid.exponent (ClassGroup (QuadraticAlgebra ℤ a b)) = 7 ↔
      ∃ q ∈ known, QuadraticAlgebra.discr a b = -(q : ℤ)
```

`#print axioms` reports `propext`, `Classical.choice` and `Quot.sound`. The theorem obtains GRH from `LFunction_eq_zero_re` of `lsernau/grh-lean@72fead1`, built in the same Lean 4.35 environment (`frontier/grh-integration/`).

## The range below 3.1·10^20 (Theorem D)

Everything for this part is in `lowrange/`. Put B = 10^5.

- **Below B** (`direct.py`). For each of the 4,808 primes q ≡ 3 (mod 4) below B the class number is computed by counting reduced forms. Exactly 32 have class group of exponent 7: the known ones other than 118843. (For q = 63499, class number 49, every split prime l ≤ √(q/3) has 𝔩^7 principal.)
- **More certificate rows** (`ladder_low.py`, `certificate_full.json`). 124 further rows, from Q ≈ 2.3·10^20 down to Q = B (X = 218). `kernel_verify.rigorous_margin` and `independent/verify_fixedpoint.cjs` both accept all of them.
- **Search** (`lowsearch.c`). For B ≤ q < 3.1·10^20 with exponent 7, the least split prime p satisfies 3 ≤ p < 2760, q ≡ 3 (mod 8), q > Q_i for every row with X_i ≤ p, and 4p^7 = x² + qy² with p ∤ y. `lowsearch` enumerates these for the 401 primes p: 2.83·10^12 candidates, y up to 1.1·10^6, **6,608 survivors** (`low_run.log`, `low_survivors.txt`; 16 minutes on 24 cores).
- **Classification** (`classify.py`). 4,685 survivors have composite q. For each of the 1,923 primes, form reduction confirms independently that 𝔭^7 is principal and that p is the least split prime. For 1,922 the second split prime l has 𝔩^7 not principal. The one left is **q = 118843** (found at p = 11, x = 8128, y = 10), class number 49, exponent 7.
- **Checks.** `test_lowsearch.py`: exact agreement with a brute-force reference on 106 configurations (105 with survivors, composite y up to 659). On p = 701..760 with l < 60, `lowsearch` and `independent/search7i` give the same 650,165 survivors. The brute-force test caught one bug during development (a sentinel value that dropped solutions when 4p^7 ≡ 1 mod l); the production run was made after the fix.

## Checks

- **Known fields.** For each of the 33 known fields, `controls.py` recomputes the class group from scratch by listing reduced forms (exponent 7 in every case; class number 7, or 49 for q = 63499 and 118843), finds the least split prime and a solution of 4p^7 = x² + q y², and confirms that the production code path of `sieve7` reports it.
- **Definition-level windows.** On 8 windows, the survivor list (with the prime set truncated so that survivors exist) is recomputed in Python from Jacobi symbols of −q and matches `sieve7` exactly.
- **Fast vs naive.** 14 runs comparing the wheel/bit-pattern path against a direct scan (9 with non-empty survivor lists, including y = 2, 3, 6, 9, 15, 35): identical lists.
- **Wheel configurations.** Full-range runs for three primes with different wheel depths give identical survivor lists.
- **Counts.** `sanity.py` truncates the prime set so that survivors exist over the full x-range, checks each survivor from the definition, and compares the count with the product of local densities: 59,086 found against 58,608 expected over six runs (for example 26,875 against 26,820 for p = 2003, l < 100). Single runs deviate by −1.8σ to +2.1σ and the total by +2.0σ, an excess; a sieve that dropped candidates would fall short.
- **Log audit.** Each of the 465 primes appears exactly once in the logs.
- **Second implementation.** `independent/search7i.c` was written from the mathematical specification alone, without access to `sieve7.c`, its logs or this README. Its design is different: for each progression x = r + y²k it enumerates the admissible residues of k by a two-sided CRT over 8 and the small primes, then filters by table lookup over every odd prime l < p, with an exact 128-bit recheck of anything that passes. It was compared with a brute-force Python reference (`independent/ref7.py`) on 240 small configurations in 4 modes each (251,096 survivors, all identical), and it reports a solution of 4p^7 = x² + qy² for all 28 known exponent-7 fields with q ≡ 3 (mod 8). On the full range (`independent/full_run.log`, 111 s on 24 threads) it finds **0 survivors**, and for every one of the 465 primes its Qlo(p), largest y and number of progressions agree with the production logs.
- **Third implementation, by a different AI system.** `independent/independent_sieve.cpp` was written by OpenAI's Codex in an independent audit (`independent/AUDIT.md`). It lifts the admissible residues of x directly modulo 8y² and then by CRT over the small primes, combines further small primes into periodic 64-bit masks, and checks primes dividing y on the exact q. It agrees exactly with a brute-force reference on 11 windows (`independent/test_sieve.py`) and recovers all 33 known fields. Its full run (465 primes, 77,049,566,290 sieve blocks, **0 survivors**) was reproduced here with identical totals and hashes (`logs/third_search.log`, 93 s on 24 cores), and its Qlo(p) and largest y agree with the production logs for every prime. `independent/verify_groups.py` also confirms from reduced forms that the two fields with class number 49 have class group C7 × C7.
- **Source.** The test options `kmax` and `nimax` were added to `sieve7.c` after the production run. With the defaults the program is unchanged: rerunning the primes 701 to 800, 1201 and 2003 reproduces the log lines exactly. The production run read a ladder file whose rows with X ≤ 4297 are identical to `ladder.txt`; rows with X > 4297 (the bootstrap rows) never affect a prime p ≤ 4297.

## Caveats

1. All three search implementations and both certificate verifiers were written by AI systems: two searches and one verifier by Claude (the second search in a separate session with only the specification), and one search and one verifier by Codex. None has been written or reviewed line by line by a person. The certificate no longer depends on the two verifiers, since its margins are proved in Lean, and the main search no longer depends on the three search programs, since its completeness is proved in Lean's kernel; the same holds for the low-range search. No computational input of Theorems A and D is left outside Lean. The Lean development was also written with AI assistance, so its definitions (class group, GRH, the two search statements) should be read by a person.
2. Theorems A, D and E are formalized in Lean 4 with Mathlib, with GRH for the quadratic characters of prime conductor as their only hypothesis (`Exp7Lean/Exp7Lean/Final5.lean`, `Final6.lean`, `Tail/Exclusion.lean`). There is no `sorry`, no `native_decide` and no added axiom, and no published bound is assumed. A formal proof is only as good as its statement: the definitions it uses (Mathlib's `ClassGroup` and `Int.IsFundamentalDiscr`, `GRHPrimeConductor`, the list `known` of 33 primes) are short and should be read by a person. Also proved in Lean:
   - Step 0 (genus theory) and Step 1 (for Mathlib's `ClassGroup` of the ring of integers, so the statements are about actual class groups);
   - the explicit-formula inequality behind every certificate row, and the margins of all 176 rows (the 175 of Theorems A and D and the bridge row), by a verified fixed-point evaluator run in Lean's kernel;
   - the tail above 2^135, by explicit Chebyshev estimates;
   - the generator bound for the class group, that the 33 fields have exponent 7, and that no other prime below 10^5 and no other survivor of the low search does;
   - completeness of the main search, from 465 kernel-checked certificates (`Exp7Lean/Exp7Lean/Sieve/`, about 11 core-hours), and of the low-range search, from 401 (`Exp7Lean/Exp7Lean/SieveLow/`, about 8 core-hours). Both are outside the default build (`lake build Exp7Full`).

   See `Exp7Lean/README.md` for the status of each step.
3. Where each form of the theorem has been checked:
   - The form with GRH as a hypothesis builds in the native project (Lean v4.37.0-rc1, a release candidate).
   - The form with GRH imported as a theorem builds only in a combined Lean 4.35 workspace. That workspace applies compatibility patches to this project (`frontier/grh-integration/compat435/`), and it has been built on one machine.

   On the Precision, both versions printed identical types for the norm-equation theorem, explicit-formula bound, upper-tail exclusion, and the prime and fundamental classification theorems. The shared 4.35 build still awaits independent reproduction on a second machine.
4. The unconditional reading of Theorem E rests on the formal proof of GRH for Dirichlet L-functions (Alpöge, with Claude, 20 November 2026; here through the compact edition in `lsernau/grh-lean`). That proof has been accepted by Lean's kernel and independent checkers but has not been refereed.
5. The count of 33 fields does not rest on EKN's table or on EKN Theorem 3, and it agrees with that table. The count of 40 orders in Corollary B rests on ARSX and is not formalized. Corollary C is proved in this README but not in Lean. `lowsearch` has one implementation; it is checked against brute force and against `search7i` on an overlapping range.
6. Priority: a search found no earlier claim on exponent 7, but unpublished or very recent work cannot be excluded.

## Reproduce

    pip install mpmath sympy numpy
    gcc -O3 -march=native -o sieve7 sieve7.c -lm
    python3 kernel_verify.py check          # re-verify all 51 certificate rows, rewrite ladder.txt  (10 s)
    python3 controls.py                     # positive controls and window tests                   (20 s)
    python3 sanity.py                       # soundness and expected counts on full ranges         (1 min)
    ./sieve7 ladder.txt 701 4297            # the search; for N cores run N copies with stride=N offset=0..N-1
    gcc -O3 -march=native -fopenmp -o independent/search7i independent/search7i.c -lm
    (cd independent && ./search7i)          # the second implementation (about 2 min on 24 threads)
    python3 independent/validate.py         # second implementation against the brute-force reference
    node independent/verify_fixedpoint.cjs certificate.json   # second certificate verifier
    g++ -O3 -march=native -std=c++17 independent/independent_sieve.cpp -o independent_sieve
    python3 independent/test_sieve.py && ./independent_sieve ladder.txt 701 4297   # third implementation
    python3 figures.py                      # regenerate the figures in paper/
    (cd Exp7Lean && lake exe cache get && lake build)   # Lean formalization
    python3 lowrange/direct.py              # Theorem D: class groups below 10^5              (30 s)
    python3 lowrange/ladder_low.py          # Theorem D: build and verify the 124 extra rows  (5 min)
    gcc -O3 -march=native -o lowrange/lowsearch lowrange/lowsearch.c -lm
    python3 lowrange/test_lowsearch.py      # Theorem D: lowsearch against brute force        (4 min)
    ./lowrange/lowsearch lowrange/ladder_full.txt 3 2759    # Theorem D: the search (stride=N offset=i to split)
    python3 lowrange/classify.py lowrange/low_run.log lowrange/low_survivors.txt
    python3 kernel_verify.py build          # optional: regenerate the certificate from scratch
    (cd Exp7Lean && lake build Exp7Lean.Rows.Bridge30000 Exp7Lean.Tail.Exclusion)   # Theorem E above 10^32
    (cd Exp7Lean && lake build Exp7Full)    # both search certificates in the kernel (about 20 core-hours)

The search prints one line per prime and ends with `DONE survivors 0`. The Lean 4.35 build with the imported GRH theorem is described in [`frontier/haar-tail/README.md`](frontier/haar-tail/README.md).

## Files

| File | What it is |
|---|---|
| `sieve7.c` | the search (Step 4) |
| `kernel_verify.py` | interval-arithmetic check of the certificate (Steps 2 and 3) |
| `kernel_opt.py` | floating-point search for the step functions; not part of the proof |
| `certificate.json`, `ladder.txt` | the 51 certificate rows, and the (X, Q) pairs read by the search |
| `controls.py`, `sanity.py` | the checks listed above |
| `independent/` | the second and third search implementations, the second certificate verifier, the Codex audit notes (`AUDIT.md`), brute-force references, validation and run summaries |
| `lowrange/` | Theorem D: extended certificate, the search below 3.1·10^20, class groups below 10^5, classification of survivors, logs |
| `Exp7Lean/` | Lean 4 formalization of Theorems A, D and E |
| `frontier/` | build receipts and notes for the bridge row, the tail above 2^135, the Lean 4.35 integration, and the low-height zero-obstruction work |
| `figures.py` | regenerates the three figures from the certificate and the logs |
| `CITATION.cff`, `.zenodo.json` | citation metadata |
| `logs/` | output of the production run, the rerun, the third search and the checks |
| `paper/` | the note in LaTeX (arXiv source) and the compiled PDF |
| `work/` | the exact source of the production binary and its hash, the ladder file the production run read, and the first certificate and ladder (bootstrap from 3.9·10^30) |

## References

- A.-S. Elsenhans, J. Klüners, F. Nicolae, *Imaginary quadratic number fields with class groups of small exponent*, Acta Arith. 193 (2020). [arXiv:1803.02056](https://arxiv.org/abs/1803.02056)
- Aiken, Ross, Shvydkoy, Xue, *Boundary CM points and class groups of small exponent*. [arXiv:2605.26020](https://arxiv.org/abs/2605.26020)
- E. Bach, J. Sorenson, *Explicit bounds for primes in residue classes*, Math. Comp. 65 (1996)
- E. Carneiro, M. Milinovich, E. Quesada-Herrera, A. Ramos, [arXiv:2404.08380](https://arxiv.org/abs/2404.08380), Lemma 9
- [`nunavipahe60-star/exponent-six`](https://github.com/nunavipahe60-star/exponent-six): the positive-kernel certificate method and the exponent-6 case
- L. Alpöge, with Claude, *Remark* and Lean archive, 20 November 2026; Luke Sernau and collaborators’ compact edition [`grh-compact`](https://github.com/lsernau/grh-lean/tree/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact); community repository [`leanprover-community/riemann-hypothesis`](https://github.com/leanprover-community/riemann-hypothesis)

## Related branches

- The [Lean 4.35 GRH integration](frontier/grh-integration/README.md) builds this project together with the external Dirichlet-GRH theorem. It applies that theorem to the bounded results in `Final5` and `Final6` and, with the [tail](frontier/haar-tail/README.md), to the global classification. The native Lean 4.37 project states the same results with an explicit `GRHPrimeConductor` argument.

Research branches and ongoing work:

- `frontier-zero-obstruction`: the original draft was strengthened to height 60 on `grh-import-audit`, with an analytic audit and an independent integer verifier. The [formal continuation on main](frontier/zero-obstruction/README.md) proves the unconditional damped formula, zero-mass and tail bounds, reflection, row coverage and conditional obstruction assembly. The full height-60 theorem remains unformalized: the smoothed-kernel identity, bounds and Lean numerical certificates are still required.
- `explicit-formula-wip`, `lean-sieve-handoff`, `sieve-reduction-audit`, `independent-audit`: earlier working branches, merged into `main`.

## License

Apache-2.0. See `LICENSE`.
