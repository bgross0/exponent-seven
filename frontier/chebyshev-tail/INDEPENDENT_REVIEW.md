# Independent review of the uniform Chebyshev tail

26 November 2026. This review independently checks the mathematical steps in
[DERIVATION.md](DERIVATION.md) and evaluates its finite bridge row with a
separate integer-interval program. It is not a Lean compilation or a claim
that the required formal bridges have already been implemented.

## Assessment

I found no sign, factor, endpoint, or coverage error in the proposed argument.
Subject to formalizing the stated weighted-sum and autocorrelation lemmas,
the existing GRH explicit formula and the unconditional norm obstruction
give `q < 2^135`. One finite row with `X=30000` then excludes the interval
`10^32 <= q <= 2^135`.

The significance is that the infinite tail uses elementary, uniform
Chebyshev estimates. It does not enumerate arbitrarily large primes and
does not need the separate published least-split-prime interface
`Above.Published.ekn3`. It continues to use the explicitly stated GRH input.

## Source audit of the Chebyshev inputs

I fetched `Mathlib/NumberTheory/Chebyshev.lean` at both exact revisions:

- Compact GRH: `56a005855ea17e0b0958f73ec801ae140b0a1679`, file blob
  `ce7ba96acd239c3e1255305c68aef5c3fde8fae3`.
- Exponent-seven checkpoint: `31ce06eaadf4a200c0e1407c5f10953cf606b8f8`, file
  blob `e04524b48d396688cd1992d29e322fb6d0a247c2`.

The three required theorem statements agree at both revisions:

```lean
theorem theta_le_log4_mul_x {x : ℝ} (hx : 0 ≤ x) :
  theta x ≤ log 4 * x

theorem theta_ge' {x : ℝ} (hx : 1 ≤ x) :
  (x - 1) * log 2 - log (x + 2) - 2 * √x * log x ≤ theta x

theorem psi_le {x : ℝ} (hx : 1 ≤ x) :
  psi x ≤ log 4 * x + 2 * x.sqrt * x.log
```

Primary source:
<https://github.com/leanprover-community/mathlib4/blob/31ce06eaadf4a200c0e1407c5f10953cf606b8f8/Mathlib/NumberTheory/Chebyshev.lean>.

For `t>=4`, `2(t+2)<=t^2` implies
`log 2 + log(t+2) <= 2log t`. Thus the simplified lower bound used in the
derivation follows with its advertised constants and in the full integration
range.

## Test function and archimedean bound

The two-cell step function is +1 on the first half of `[0,L]` and -1 on its
second half. Computing the four signed overlaps in its autocorrelation
gives

```text
f(u) = 1-3u/L        (0 <= u <= L/2),
f(u) = u/L-1         (L/2 <= u <= L),
f(u) = 0            (u >= L).
```

The two branches meet at `-1/2`. This is the existing step-function
autocorrelation, without the smoothing used in the separate zero-rectangle
work.

For every nonnegative u, `1-f(u)<=3u/L`. Expanding the positive geometric
series in the definition of J gives

```text
J <= (3/L) sum_{k>=0} 2/(3/2+2k)^2
  <= (3/L)(8/9+2/3) = 14/(3L).
```

The second bound follows from the first term plus the integral of the
positive decreasing summand. The numerical constant is correct. The
inequality `-log pi+psi(3/4)<=0` needed for the coarse upper bound also
follows from the elementary constants listed in DERIVATION.md.

## Independent summation checks

Put `c=log 2`, `L=log X`, and `s=sqrt X`.

### Selected positive primes

For `s<p<X`, the prime term is positive with weight
`w(t)=(1-log(t)/L)/sqrt(t)`. Its negative derivative is

```text
K(t) = (L+2-log t)/(2L*t^(3/2)).
```

Abel summation over `(s,X]` gives
`-2 theta(s)w(s)+2 integral_s^X theta(t)K(t)dt` because `w(X)=0`.
The lower endpoint subtraction is necessary and has been included.

Using the upper bound for `theta(s)` and the lower bound inside the positive
integral, the main contribution is exactly

```text
8c sqrt(X)/L - c(3+8/L)X^(1/4).
```

Independently integrating the `2sqrt(t)log t` error with `v=log t` gives
`L^2/6+3L/2`. The remaining `2log t` error is bounded by
`(2L+8)X^(-1/4)`, as claimed. In fact direct integration gives the slightly
smaller exact expression

```text
(L+4-16/L)X^(-1/4) + (16/L)X^(-1/2)
  <= (L+4)X^(-1/4),
```

but the stated larger bound is valid and sufficient; no improvement is
needed for the base case.

Including `p=X` changes nothing because its weight is zero. Omitting
`p=sqrt X` discards a nonnegative term. Thus these endpoints are consistent
with the original strict prime-power cutoff.

### Negative odd powers

An odd prime power is negative only below `Y=X^(1/3)`. The retained
triangular factor is essential. With `ell=L/3`, the majorant is twice

```text
sum_{n<=Y} Lambda(n)(1-log(n)/ell)/sqrt(n).
```

Enlarging to all n is allowed because both Lambda and the weight are
nonnegative there. Abel summation has no boundary term: the weight vanishes
at Y, and `psi(1)=0`.

The `log4*t` part of `psi_le` contributes before multiplication by two

```text
log4*(4sqrt(Y)/ell - 1 - 4/ell).
```

The `2sqrt(t)log t` part contributes `ell^2/6+ell`. Consequently the stated
loss `24log4*X^(1/6)/L+L^2/27+2L/3` is correct. This negative range is
disjoint from the selected positive-prime range.

### Negative even powers

For `n=m^2` a prime power, `Lambda(n)=Lambda(m)`. Since `-2f<=1` wherever f
is negative, enlarging the loss to `sum_{m<=sqrt X} Lambda(m)/m` is valid.
Abel summation gives, at `M=sqrt X`,

```text
psi(M)/M + integral_1^M psi(t)/t^2 dt
 <= log4*(1+log M) + 8 - (2log M+8)/sqrt M.
```

Dropping the final nonpositive correction yields exactly the bound in the
derivation. Keeping Lambda(m), rather than replacing it with log(m), is
what keeps this error small enough.

Every omitted term outside these two negative families is nonnegative.
The combined `11/54` quadratic-log coefficient equals `1/6+1/27`; the
linear-log coefficient `13/6+c` equals `3/2+2/3+c`. These checks agree with
the seven error terms after multiplying the dyadic inequality by n.

## Dyadic induction and conductor coverage

I independently reconstructed all seven error terms after setting
`X=2^n`, subtracting `(7n+9)c+14/(3nc)`, and multiplying by n. They agree
with DERIVATION.md.

The ratio bounds for n>=19 follow from positive coefficients and
`(n+1)/n<=20/19`. In particular the largest displayed polynomial ratio is
`(20/19)^3<7/5`, and the first exponential error has ratio at most
`(20/19)(6/5)=24/19<7/5`. The main term grows by `sqrt2>7/5`.

An independent exact-Fraction calculation reproduces the base values:

```text
main lower bound      = 28672/5,
sum of error bounds   = 56695939/10800,
strict slack          = 5235581/10800 > 0.
```

The integer comparisons for `2^(19/4)<27` and `2^(19/6)<9` both reduce to
`2^19<531441`; the other root and growth comparisons also check exactly.
Thus the induction is a uniform argument, not a test of finitely many n.

For an odd prime q above the claimed boundary, choose the integer k with
`2^k<=q<2^(k+1)` and put `n=floor((k-2)/7)`. Then n>=19 and

```text
2^(7n+2) < q < 2^(7n+9).
```

The lower strictness uses that an odd prime is not a power of two. The upper
inequality uses the integer fact `k+1<=7n+9`. Thus there is no gap between
successive dyadic conductor intervals. `4X^7<q` implies `q>X`, so all primes
in the finite sum are also unramified; the existing norm/splitting interface
must supply that their quadratic-character values are -1.

## Independently checked finite bridge

Run:

```sh
python3 frontier/chebyshev-tail/verify_bridge.py
```

The verifier uses the stdlib-only integer interval implementation in
`../zero-integer/verify.py`. Its Haar evaluator is separately checked against
the four signed interval overlaps at 1,001 rational arguments and with an
interval straddling the corner at `1/2`.

The exact structural gate is

```text
4*30000^7 = 87480000000000000000000000000000 < 10^32,
2^135    = 43556142965880123323311949751266331066368.
```

The 3,320 prime-power terms give the following outward enclosures:

| quantity | lower | upper |
| --- | ---: | ---: |
| inert prime sum P | 99.242565 | 99.242566 |
| J upper-bound expression | 0.452680 | 0.452681 |
| log Qmax | 93.574869 | 93.574870 |
| log pi - psi(3/4) | 2.230590 | 2.230591 |
| final positive margin | **7.445605** | **7.445606** |

The final margin is computed before display rounding; subtracting only the
six-decimal table endpoints would give a slightly weaker valid bound.
The complete output is [bridge-result.json](bridge-result.json).

## Coarse J bound using the existing finite Jplus theorem

The finite bridge and the infinite tail also work with the coarser bound
`J<=4`. This is useful for formalization because it follows directly from
the project's already proved `Jterm_le_Jplus`, without a new argument
interchanging an integral and a geometric series.

The bound holds for **every L>=1**, including `L=log 30000` (enclosed by
`[10.308952,10.308953]`). In the two-cell specialization:

- `corr([1,-1],1)=-1/2`, so the first-cell bound is `3/2`.
- Write `step=L/32`. Each of the 16 middle terms is at most `3/32`:
  `step*aKer(step*(16+i))<=1/16` follows from `aKer(u)*u<=1`, while its
  remaining midpoint factor lies between zero and `3/2`. The middle sum is
  at most `3/2`.
- For L>=1, `exp(3L/2)>=5/2` and `exp(2L)>=3`, from `1+x<=exp x`.
  Thus `exp(-2L)<=1/3`, and the existing tail expression has denominator
  at least `3*(5/2)*(2/3)=5`. Its value is at most `4/5`.

In fact this proves `Jplus<=19/5<4`. The Lean implementation in
[HaarJBound.lean](HaarJBound.lean), using the existing definitions directly,
**compiled successfully** in the isolated common environment with Lean
4.35.0 and Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`.
Both `Exp7.Jplus_haar_le_four` and `Exp7.Jterm_haar_le_four` report exactly
`propext`, `Classical.choice`, and `Quot.sound`. The imported Autocorr and
JBound source files compiled unchanged. The file's original creation-time
header is retained so that delivered source bytes exactly match the build;
the current status and hashes are in [haar-build-receipt.json](haar-build-receipt.json),
with the complete output in [haar-build.log](haar-build.log).

The bridge verifier now also checks the coarse profile, with positive margin

```text
P_30000 - 4 + log pi - psi(3/4) - 135log2
  in [3.898286, 3.898287].
```

For the uniform induction, replace E5 by `(11c+12)n` and omit E7. At n=19
this increases the total error bound by `4*19-7=69`, leaving exact positive
slack `4490381/10800`. Its growth factor is unchanged. I independently
checked these substitutions. The same cutoff `q<2^135` therefore survives
with this easier J bound.

## Remaining proof obligations

The independent review supports the mathematical argument, and the coarse
Haar J bound now has a checked Lean proof. Further formal work remains:
the exact Haar autocorrelation identity, the sign-based prime-power
partition, Abel summation and elementary integrals, and the certified bridge
row must be connected to the separately developed dyadic arithmetic. A generated
certificate should reference the existing step-function and row-margin
definitions directly. The final theorem must still show its GRH proof or
hypothesis explicitly.

Until these steps compile and their axioms are inspected, this remains an
audited derivation with an independent finite arithmetic check, rather than
a replacement theorem already established in the repository.
