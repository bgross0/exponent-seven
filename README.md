# Imaginary quadratic fields with class group of exponent 7

Ben Gross. 25 November 2026.

**Status: computer-assisted research note for independent review. Not refereed. The search has two implementations with different algorithms; both find 0 survivors.**

Use of AI: the argument, code and computations were produced with Claude (Anthropic's AI model), directed by the author. Corrections are welcome through the issue tracker.

## Result

Write E(D) for the exponent of the class group of Q(√D), D < 0 a fundamental discriminant.

**Theorem A.** Assume GRH for the Dirichlet L-functions L(s, χ_D) of the odd real primitive characters of prime conductor. Then no fundamental discriminant D with 3.1·10^20 ≤ |D| ≤ 10^32 has E(D) = 7.

**Corollary B.** Assume the Riemann hypothesis for ζ(s) and for the L-functions L(s, χ_D), that is, ERH for the Dedekind zeta functions of the imaginary quadratic fields (the hypothesis of EKN Theorem 3 and ARSX Theorem 1.3). Then exactly 33 imaginary quadratic fields have class group of exponent 7, the largest being Q(√−118843), and exactly 40 imaginary quadratic orders have Picard group of exponent 7 (largest discriminant −118843).

Corollary B follows from Theorem A and three published results:

- Elsenhans–Klüners–Nicolae (EKN), Theorem 1: the list of fields with E(D) ≤ 8 is complete for |D| ≤ 3.1·10^20 (a computation; the theorem is stated without hypotheses). It has 33 fields of exponent 7 (EKN Table 1).
- EKN Theorem 3 (from Bach–Sorenson, under ERH for the Dedekind zeta function of Q(√D)): for |D| > e^25 some prime p ≤ (1.881 log|D| + 6.18)² splits. A split prime forces |D| ≤ 4p^7 when E(D) = 7 (Step 1 below), so E(D) = 7 needs h(log|D|) ≥ 0, where h(t) = log 4 + 14 log(1.881t + 6.18) − t. Now h′(t) = 14·1.881/(1.881t + 6.18) − 1 < 0 for t > 10.7, so h is decreasing for |D| ≥ 10^32, and h(log 10^32) < −2.64. So no |D| ≥ 10^32 has E(D) = 7 (`kernel_verify.py` checks this in interval arithmetic).
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

and then every prime q ≤ Q in our family has a split prime below X. `kernel_verify.py` checks each row with outward-rounded interval arithmetic (mpmath `iv`, 40 digits); the autocorrelation values are exact rationals, and the cell containing log n is found by exact integer comparison (X^k ≤ n^64 < X^(k+1)), with no floating point.

This is the positive-kernel method of the exponent-six note, which applies the explicit formula in the form of Carneiro–Milinovich–Quesada-Herrera–Ramos, Lemma 9. Step 0 simplifies it: with prime conductor there are no ramified primes to pay for.

**Step 3 (bootstrap).** Six rows, each feeding q ≤ 4P^7 (P the largest prime below X) into the next:

| q ≤ Q | X | largest prime P < X | margin > | new bound 4P^7 |
|---|---|---|---|---|
| 10^32 | 6362 | 6361 | 0.0126 | 1.686·10^27 |
| 1.686·10^27 | 4690 | 4679 | 0.0161 | 1.964·10^26 |
| 1.964·10^26 | 4393 | 4391 | 0.0188 | 1.259·10^26 |
| 1.259·10^26 | 4333 | 4327 | 0.0191 | 1.136·10^26 |
| 1.136·10^26 | 4319 | 4297 | 0.0181 | 1.082·10^26 |
| 1.082·10^26 | 4312 | 4297 | 0.0147 | 1.082·10^26 |

So q ≤ 4·4297^7 = 108197560039107534049882852 and the least split prime p satisfies 701 ≤ p ≤ 4297. A further 45 rows (the "ladder", from Q = 8.1·10^25 down to 3.1·10^20) shorten the search: if X_i ≤ p then q > Q_i.

**Step 4 (search).** For each of the 465 primes p in [701, 4297], each y ≥ 1, and each x ≥ 0 with x² ≡ 4p^7 (mod y²) and q = (4p^7 − x²)/y² ≥ Qlo(p), `sieve7` tests the necessary conditions: (−q/l) = −1 for every odd prime l < p, and q ≡ 3 (mod 8). For l ∤ y the condition reads "x² − 4p^7 is a non-residue mod l", which is sieved (a wheel on the first primes, 64-bit patterns for l < 64, then one prime at a time). Totals: 21,577 progressions, 7.8·10^12 positions after the wheel, 1.6·10^10 after the bit patterns, and **0 values of x passing all odd primes l < p**. So no such q exists. ∎

Run time: about 25 minutes on 2 vCPUs. The logs are in `logs/prod_0.log` and `logs/prod_1.log`. A full rerun on a separate 28-thread machine (`logs/rerun.log`) gives identical output for all 465 primes.

## Checks

- **Known fields.** For each of the 33 known fields, `controls.py` recomputes the class group from scratch by listing reduced forms (exponent 7 in every case; class number 7, or 49 for q = 63499 and 118843), finds the least split prime and a solution of 4p^7 = x² + q y², and confirms that the production code path of `sieve7` reports it.
- **Definition-level windows.** On 8 windows, the survivor list (with the prime set truncated so that survivors exist) is recomputed in Python from Jacobi symbols of −q and matches `sieve7` exactly.
- **Fast vs naive.** 14 runs comparing the wheel/bit-pattern path against a direct scan (9 with non-empty survivor lists, including y = 2, 3, 6, 9, 15, 35): identical lists.
- **Wheel configurations.** Full-range runs for three primes with different wheel depths give identical survivor lists.
- **Counts.** `sanity.py` truncates the prime set so that survivors exist over the full x-range, checks each survivor from the definition, and compares the count with the product of local densities: 59,086 found against 58,608 expected over six runs (for example 26,875 against 26,820 for p = 2003, l < 100). Single runs deviate by −1.8σ to +2.1σ and the total by +2.0σ, an excess; a sieve that dropped candidates would fall short.
- **Log audit.** Each of the 465 primes appears exactly once in the logs.
- **Second implementation.** `independent/search7i.c` was written from the mathematical specification alone, without access to `sieve7.c`, its logs or this README. Its design is different: for each progression x = r + y²k it enumerates the admissible residues of k by a two-sided CRT over 8 and the small primes, then filters by table lookup over every odd prime l < p, with an exact 128-bit recheck of anything that passes. It was compared with a brute-force Python reference (`independent/ref7.py`) on 240 small configurations in 4 modes each (251,096 survivors, all identical), and it reports a solution of 4p^7 = x² + qy² for all 28 known exponent-7 fields with q ≡ 3 (mod 8). On the full range (`independent/full_run.log`, 111 s on 24 threads) it finds **0 survivors**, and for every one of the 465 primes its Qlo(p), largest y and number of progressions agree with the production logs.
- **Source.** The test options `kmax` and `nimax` were added to `sieve7.c` after the production run. With the defaults the program is unchanged: rerunning the primes 701 to 800, 1201 and 2003 reproduces the log lines exactly. The production run read a ladder file whose rows with X ≤ 4297 are identical to `ladder.txt`; rows with X > 4297 (the bootstrap rows) never affect a prime p ≤ 4297.

## Caveats

1. Both search implementations were written with Claude: the second by a separate session that had only the specification, not the first program. They are independent designs, but not independent authors. A search written by a person would strengthen the result further.
2. The interval check relies on mpmath's `iv` arithmetic.
3. The result rests on EKN's 2020 computation below 3.1·10^20, on Bach–Sorenson (through EKN Theorem 3) above 10^32, and on ARSX for the count of orders.
4. Priority: a search found no earlier claim on exponent 7, but unpublished or very recent work cannot be excluded.

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
    python3 figures.py                      # regenerate the figures in paper/
    python3 kernel_verify.py build          # optional: regenerate the certificate from scratch

The search prints one line per prime and ends with `DONE survivors 0`.

## Files

| File | What it is |
|---|---|
| `sieve7.c` | the search (Step 4) |
| `kernel_verify.py` | interval-arithmetic check of the certificate (Steps 2 and 3) |
| `kernel_opt.py` | floating-point search for the step functions; not part of the proof |
| `certificate.json`, `ladder.txt` | the 51 certificate rows, and the (X, Q) pairs read by the search |
| `controls.py`, `sanity.py` | the checks listed above |
| `independent/` | the second search implementation, its brute-force reference, validation and full-run logs |
| `figures.py` | regenerates the three figures from the certificate and the logs |
| `CITATION.cff`, `.zenodo.json` | citation metadata |
| `logs/` | output of the production run, the rerun and the checks |
| `paper/` | the note in LaTeX (arXiv source) and the compiled PDF |
| `work/` | the exact source of the production binary and its hash, the ladder file the production run read, and the first certificate and ladder (bootstrap from 3.9·10^30) |

## References

- A.-S. Elsenhans, J. Klüners, F. Nicolae, *Imaginary quadratic number fields with class groups of small exponent*, Acta Arith. 193 (2020). [arXiv:1803.02056](https://arxiv.org/abs/1803.02056)
- Aiken, Ross, Shvydkoy, Xue, *Boundary CM points and class groups of small exponent*. [arXiv:2605.26020](https://arxiv.org/abs/2605.26020)
- E. Bach, J. Sorenson, *Explicit bounds for primes in residue classes*, Math. Comp. 65 (1996)
- E. Carneiro, M. Milinovich, E. Quesada-Herrera, A. Ramos, [arXiv:2404.08380](https://arxiv.org/abs/2404.08380), Lemma 9
- [`nunavipahe60-star/exponent-six`](https://github.com/nunavipahe60-star/exponent-six): the positive-kernel certificate method and the exponent-6 case

## License

Apache-2.0. See `LICENSE`.
