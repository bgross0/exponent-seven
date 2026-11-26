# Sieve reduction audit and handoff (26 November 2026)

Base: d9bc0f602f364e37820fd000a5f3a320357892ec. All changes are isolated on this branch. No new Lean theorem was compiled here; the Python and JavaScript experiments below were executed. The purpose is to reduce the trusted kernel's workload, not to replace it with external computations.

## 1. Statement audit

- `ExplicitFormulaBound` has the correct sign, factor 2, cutoff, and gamma term. `psi34 = -gamma + pi/2 - 3 log 2` is correct. `stepFn` and `autocorr` have the intended support and normalization; a nonzero vector and X >= 2 give a positive denominator. `primeSum` uses (n/q); reciprocity for q = 3 mod 4 gives (-q/l) at odd primes and the supplement for 2. The n=0 and n=1 terms vanish by von Mangoldt. `Zeros.lean` explicitly handles the zero-free boundaries via nonvanishing and functional equation, so GRHFor's strict strip is appropriate. No weakness/vacuity identified at the statement level.
- `IsExp7` is defined using actual Mathlib ClassGroup of the quadratic integral algebra, with the prime and mod-4 facts present, not an unconstrained predicate. Step1 establishes its Dedekind instance from the integral-closure theorem. The domain is precisely the prime discriminant case; Step 0 is still to be connected to a global field-classification statement.
- `SearchHigh` is sufficient and stronger than necessary (all natural q, not just prime q; no p-splitting or p-not-dividing-y assumption). For the actual theorem q is prime. SearchLow is sufficient: its primitive norm equation is supplied by Step1, and inclusion of all prime survivors in survivorQs is the right obligation, not absence of survivors.
- Important: the new analytic reductions below apply to prime q under GRH, not arbitrary composite q. They cannot discharge the existing unconditional SearchHigh proposition as written. Introduce a specialized prime-q search interface with the stronger lower bound and thread it through the least-split-prime proof in Main/Final (or keep the original proof and use only the purely modular optimizations). For low search, likewise make the strengthened-bound application explicitly GRH-dependent. Do not silently change or assume SearchHigh.
- A clean build and axiom audit is still required for the new analytical files. Some comments refer to historical sorry placeholders. Statement audit is not a replacement for kernel verification. The global range above 10^32 still relies on EKN/Bach–Sorenson as in the paper.

## 2. Multi-y benchmark

`packed_multi.py` directly follows the agreed certificate design: roots modulo 8*y^2, Euclidean decomposition, CRT wheel and packed periodic masks. Run from repository root:

    python Exp7Lean/sieve-reduction/packed_multi.py ladder.txt 2767 17 skip 4
    python Exp7Lean/sieve-reduction/packed_multi.py ladder.txt 2767 17 all 1

Both complete, all 126 y values covered. Skip mode: 384 roots, 794304 blocks, 32056895134 total block bits, zero survivors. In particular skipping l|y leaves NO nonzero block for this p. Last prime required <=181. All-prime mode: 1161216 blocks, 21702319428 total block bits, zero survivors; last prime <=179. Nominal sum of AND bit lengths reduced from 638792630323 to 435301492788. Wall times are not comparable (different worker counts, overlapping runs).

### One polynomial for all primes

Let S=4*p^7, x=r+m*t, m=8*y^2. Exact root congruence gives q0=(S-r^2)/y^2. Then

    q(t)=q0-16*r*t-64*y^2*t^2.

Evaluate (-q(t) / l)=-1 directly for every odd l<p, even l|y. The latter reduces to an affine congruence. No modular division by y is needed; use Int or ZMod. A fixed wheel is then possible. The p=2767 experiments show the tradeoff: more blocks but fewer total bits when including these conditions in the wheel.

### Fourfold root compression, independent of GRH

The exact period for x congruence can be taken as 2*y^2, not 8*y^2. If x^2+3*y^2=S mod 8*y^2, then x and y have equal parity (S divisible by 4). For any integer t,

    (x+2*y^2*t)^2-x^2=4*y^2*(x*t+y^2*t^2),

and the bracket is even because t^2=t mod 2 and x=y mod 2. Thus the congruence is invariant. Enumerate roots r<2*y^2 satisfying the original modulus 8*y^2, and write x=r+2*y^2*t. Every old root maps to exactly one of these, and each compressed root has exactly four lifts. In the new polynomial q(t)=q0-4*r*t-4*y^2*t^2. This cuts the root/block count fourfold when full wheel periods are present, but blocks are longer. It is a purely arithmetic optimization applicable even to the original unconditional SearchHigh. `packed_period2.py` demonstrates it.

## 3. Wheel choice

`wheel_cost.py` and `wheel-cost.json` give reproducible combinatorial upper bounds across the 465 p cases. For each root, T is progression length, W is the wheel modulus and A is the product of admissible residue counts for included wheel primes. There are at most min(A,T) nonempty blocks, each <=ceil(T/W) bits. Total nominal bit count bounded by A*ceil(T/W). These are not measured Lean times and do not include repeated AND/tiling.

Original design (8*y^2, skip divisors):
- through 17 (W=255255): 102821528 blocks, 12657420625836 bits.
- add 19: 925279080 blocks, 6351478254584 bits.
- add 23: 10028957568 blocks, 3182401615712 bits.

Recommendation: do not universally add 19 or 23. Proof/evaluation overhead per block likely dominates. Try through 13 and 17 and choose adaptively by block length, using actual kernel calibration. With compressed roots, all primes, and robust26 bounds, through 13 yields <=1648555 blocks, <=5801573019504 bits, max block ~95.7 million bits; through 17 yields <=13998601 blocks, <=2911190825552 bits, max block ~5.63 million bits. Calibrate memory as well as speed. Use a maximum allowed block length and the smallest wheel meeting it; chunk huge blocks if needed. Do not mistake total bits for total CPU time.

## 4. Low search: use the same exclusion checker

For each (p,y,r,rho) block, let ks be the indices k corresponding to listed survivors. Construct an additional Pattern of period n, phase 0, depth 0, whose bits retain all indices in [0,n) EXCEPT ks. Then

    intersect (exceptionPattern :: ps) n = 0

proves there are no unlisted surviving indices. This reuses exclude_block directly. For each k in ks, check that the computed q belongs to survivorQs (or is composite via a nontrivial factor); no need to prove listed indices actually survive, only that unlisted indices do not. Most blocks have empty ks and use ordinary exclusion. An exception mask can be generated as full n-bit mask XOR sparse OR of (1 <<< k) for k in ks, with all k<n, avoiding an O(n) dense membership scan. Prove its one-sided testBit property once. Draft `Exp7Lean/SieveExceptions.lean` supplies the abstract bridge and a semantic dense constructor, not yet compiled. The sparse production constructor is left to the Lean agent. All primes dividing y can be tested with the polynomial above; otherwise false positive candidates due to skipped conditions must be checked, not discarded.

## 5. Stronger analytic reduction

This is optional but substantial. For a test function f, define A_l as the prime-power contribution when l inert, and d_l=A_l-(contribution when l splits):

    d_l=-4 log(l) * sum_{odd k, l^k<X} f(log(l^k))/sqrt(l^k).

If q>X is prime, q=3 mod 4 and no prime < threshold T splits, then

    primeSum(q,f,X) >= inertSum(f,X) - sum_{T<=l<X} max(0,d_l).

No information about the splitting of l>=T is required. Consequently, if

    rowMargin(Q,X,v) - sum_{T<=l<X} max(0,d_l) > 0,

then under GRH any prime q with X<q<=Q has a split prime < T. Apply to least split p>=T to get q>Q. This is a one-sided worst-case bound, not a heuristic. It follows by grouping the existing primeSum/inertSum proofs by prime powers and using (l/q)=+-1; the even powers are identical. The existing positive kernel/explicit formula works for these new v and X. For a Lean implementation, extend the numerical table beyond 6400 up to at least 8209, and certify the robust margin with a directed upper bound for each positive-part penalty (or min of the two possible prime contributions).

I optimized the kernel using a minimax eigenvalue search over [0,1] splitting weights, then rounded vectors to integers and verified 83 rows using independent fixed-point arithmetic. A selected set of 26 achieves almost the same effect and is committed here in `robust26.txt`. Each line is T X Q, 32 integer vector entries, and a certified margin lower endpoint in units 10^-30. The full 64-vector is the given half followed by its reversed negative. Re-run:

    node Exp7Lean/sieve-reduction/verify_robust.cjs Exp7Lean/sieve-reduction/robust26.txt

This ran on the committed data and matched all 26 recorded margins exactly (minimum >0.030025). No optimizer is needed to verify. Bounds can be used as Qlo'(p)=max(Qlo(p),Q for T<=p). In the relevant ranges q>X for every new row (X<=8209, q>=1e5).

- With 26 rows, high: 465 -> 328 active p, largest remaining p=3229, sum Ymax 14770 -> 5520. With all 83 rows: same 328 active p and sum Ymax 5225.
- Low: active p 400 -> 325, largest p=2179, sum Ymax 72796110 -> 57114892. All 401 p originally considered; p=3 has no feasible y before the optimization.
- Exact arithmetic work proxy sum floor(sqrt(4*p^7))*Ymax decreases ~83.0% high and ~57.9% low; not runtime.

Example p=2767, selected T=2700 row gives Q=108800000000000000000000, Ymax=6 rather than 126. Combined with period 2*y^2 and all primes, the Python prototype checked 18144 wheel blocks, zero survivors, 24.77s single-worker. Compared to baseline skip mode 794304 blocks, this is ~43.8x fewer blocks. Nominal AND bits ~432.5 billion vs baseline 638.8 billion. These are actual external computations, not a Lean-verified search. `p2767-optimized.json` records results. Reproduce by using a copy of ladder.txt with first line replaced by Q above, and run packed_period2.py with p=2767, wheel 17, all 1.

## Integration priority

1. Immediately use the root compression and exception-pattern bridge if compatible with the existing agent's code; neither depends on robust analytic rows.
2. Calibrate adaptive wheels and reuse precomputed masks across residues when possible.
3. Consider robust26 as a parallel optional analytic proof branch: its new implication needs a Lean proof and row margins checked in Lean, and SearchHigh needs a prime-q interface. Existing unconditional SearchHigh should remain available if the agent has already substantially completed it.
4. All external numerical outputs are evidence for selecting strategies; the theorem must rely on checked computations, not these JSON files alone.
