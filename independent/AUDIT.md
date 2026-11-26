# Independent audit of the exponent-seven candidate proof

Audit date: 25 November 2026. Independent implementation by ChatGPT, at the author's request. This is computational corroboration, not external peer review or a full Lean formalization.

## Mathematical checks

**Explicit formula.** The primary source is Carneiro–Milinovich–Quesada-Herrera–Ramos, arXiv:2404.08380v2, Lemma 9. With the Fourier convention in that paper, set
h(z) = integral f(u) exp(i z u) du,
where f is the normalized autocorrelation of the real compactly supported step function g. For real z, h(z) = |integral g(u) exp(i z u) du|^2 / integral g^2 >= 0. Because g is compactly supported and piecewise constant, h is entire and O(|Re z|^-2) on every fixed horizontal strip. Thus h meets Lemma 9's hypotheses, including at a central zero. Fourier inversion gives hat h(v) = 2 pi f(2 pi v). For an odd real primitive character the gamma term is Re psi(3/4+it/2). Using the standard integral representation of psi and Fourier inversion, its weighted integral, divided by 2 pi, is

    psi(3/4) + integral_0^infty 2 exp(-3u/2)/(1-exp(-2u)) (1-f(u)) du.

The interchange is justified by the O(t^-2) decay of h and the piecewise-linear Lipschitz continuity of f at 0; equivalently use Tonelli on h(t)(1-cos(tu/2)) >= 0 for real t. GRH gives a nonnegative zero sum. Substitution produces exactly the inequality in the main README, with no zeta term for this nonprincipal character.

**No gaps at the top.** EKN Theorem 3 gives p <= (1.881 log q + 6.18)^2 for q > exp(25). The main README should compare the ratio, not claim the increasing right-hand side is uniformly bounded by its value at 10^32. Define R(q)=4(1.881 log q+6.18)^14/q. Its logarithmic derivative with respect to log q is 14*1.881/(1.881 log q+6.18)-1 < 0 for q >= 10^32. At the endpoint use log(10^32)<74, hence 1.881 log(10^32)+6.18<146, and the exact integer inequality

    4*146^14 = 7998342040108832435319302324224 < 10^32.

Therefore R(q)<1 throughout this half-line, contradicting the norm bound q<=4p^7. No rounding gap is possible.

**Genus theory.** For odd-order class groups a negative fundamental discriminant is a single prime discriminant. D=-4 and D=-8 are excluded by the lower cutoff, leaving D=-q, q prime and 3 mod 4. In the search interval q exceeds every prime used in the certificate or sieve, so there is no ramified-prime exception. The least split prime is >=701 because 4*691^7<3.1*10^20; this also forces 2 inert, hence q=3 mod 8.

**Norm equation.** For a split prime p, the seventh power of either prime ideal is principal. Its generator has norm p^7 and is not rational (conjugation would otherwise identify the two distinct ideal powers). Hence 4p^7=x^2+qy^2 with y>=1 and x>=0 after signs/conjugation. No coprimality or primality restrictions beyond the necessary conditions are needed for a zero-survivor search.

## Independent certificate

Run from repository root:

    node independent/verify_fixedpoint.cjs certificate.json

This implementation uses BigInt fixed-point intervals, scale 10^-30, with directed integer division, integer square roots, exact integer cell selection n^64 versus X^k, and independently evaluated log/exp Taylor series with explicit tail allowances. It verifies the entire bootstrap chain, all 45 ladder rows, and the endpoints and count of the prime range. It does not call mpmath. The two classical constant enclosures for pi and Euler's gamma are hardcoded to 30 decimal places; their independent derivation is a remaining small audit task. See certificate-result.json. The original ladder was separately reconstructed from the exact integer JSON fields and matched ladder.txt byte for byte.

## Independent sieve

    g++ -O3 -march=native -std=c++17 independent/independent_sieve.cpp -o independent_sieve
    python3 independent/test_sieve.py
    python3 independent/verify_groups.py
    ./independent_sieve ladder.txt 701 4297

A lower bound Q(p) is the maximum of the base cutoff and all Q_i with X_i<=p. The ladder only raises the lower bound, never excludes an admissible solution. Search y=1..floor(sqrt(4p^7/Q)), then x=0..floor(sqrt(4p^7-Q*y^2)), including endpoints.

Rather than generating roots modulo y^2 and testing q mod 8 at the end, the new implementation generates all roots x modulo 8y^2 satisfying x^2=4p^7-3y^2 modulo 8y^2. This is equivalent to divisibility by y^2 and q=3 mod 8. For each odd l<p not dividing y, a precomputed table retains exactly the residues for which x^2-4p^7 is a nonzero non-square modulo l. Direct CRT lifts each retained x residue to the next prime modulus, skipping only residues whose least nonnegative representative is already beyond xmax. Remaining small-prime tests are combined into paired periodic 64-bit masks on absolute x residues. Remaining odd primes are checked individually; primes dividing y are checked on the exact recovered q. The search is a superset of possible prime discriminants; zero survivors is sufficient.

All production integer bounds are well inside the representations: 4p^7<2^87, x<2^44, y<600, 8y^2<2^22; CRT stride is limited by xmax/64. Products for x^2 and q are computed with unsigned 128-bit integers; small prime residue products are below 4297^2. No floating-point square root or cast is used. The optional last command-line argument truncates odd-prime tests and is only for controls; omit it for the proof.

The brute-force reference compares exact survivor sets, not just counts, for 11 windows with nonempty results. All 33 known fields are also recovered from the production search path when the lower bound is reduced. Independently, reduced-form enumeration gives 31 fields of class number 7 and two of class number 49. For the latter, every split prime <=sqrt(q/3) has a primitive norm-p^7 representation (p does not divide y); this proves that the prime-ideal generators all have order dividing 7. Thus both groups are C7 x C7, not C49.

## Dependencies and status

* EKN arXiv:1803.02056 Theorems 1 and 3 and Table 1, as published in Acta Arith. 193 (2020). The small-discriminant table is imported, not exhaustively recomputed here.
* ARSX arXiv:2605.26020v1 Theorem 1.3(6) and Table A.7 explicitly record the open interval and the 40-order consequence.
* Retain GRH/ERH hypotheses in the theorem statements pending broad mathematical review of Alpoge's formal proof. See Michael Rubinstein's independent verification report: https://www.math.uwaterloo.ca/~mrubinst/alpoge_claude_grh/ . For a quadratic field, zeta_K(s)=zeta(s)L(s,chi_D), so the relevant Dedekind-zeta hypothesis is covered by the two claimed formal results. This does not assert general ERH for all number fields.
* The independent implementation is not a formally verified program. Its source, proof of coverage, execution logs, and constants should be independently reviewed. No claim to priority is established by this audit.
