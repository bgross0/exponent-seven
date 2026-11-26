# Independent integer-interval verifier

This directory independently evaluates all four zero-obstruction rows using
only the Python standard library. It replaces the original evaluator's
`mpmath.iv`, `sympy`, and supplied decimal Euler-constant enclosure with
integer arithmetic and explicit remainder estimates.

**All four rows pass at heights 1000, 100, and 60 with the corresponding
analytic estimates.** This is an external check of numerical inequalities.
It is not a Lean proof, does not compute any L-function zeros, and does not
by itself exclude any exponent-seven field.

The height-60 profile uses the additional kernel-shape and variation
arguments in [the analytic audit](../zero-audit/AUDIT.md), sections 5 and 7.
Those arguments must be proved before the stronger numerical profile is
used in a formal theorem.

## Run

From the repository root:

```sh
python3 frontier/zero-integer/verify.py
python3 -m unittest discover -s frontier/zero-integer -p 'test_*.py' -v
```

For a single row, append the three integers `X Qmin Qmax`. The script rejects
failed structural inequalities, taper conditions, or nonpositive final
intervals with exceptions. These final acceptance checks also run under
Python's optimized mode.

The recorded [result.json](result.json) was produced by the complete
four-row run. Runtime was approximately 4.0 seconds in the current workspace;
this is an observation of this run, not a hardware-normalized benchmark.
Seven differential test suites passed in approximately 0.47 seconds.

## Numerical results

Each entry below is the **lower endpoint** of an outward enclosure, in actual
real units. The JSON endpoints are integers in units of `10^-6`.

| X | Conductor interval | Original, T=1000 | Shifted tail, T=100 | Exact Haar loss, T=60 |
| ---: | --- | ---: | ---: | ---: |
| 19,000 | [3.9e30, 1e32] | 1.548595 | 1.520510 | 1.040803 |
| 30,000 | [1e32, 1e40] | 0.754337 | 0.723110 | 0.253506 |
| 100,000 | [1e40, 1e60] | 23.506604 | 23.464231 | 23.119888 |
| 1,000,000 | [1e60, 1e162] | 77.515171 | 77.406693 | 75.929004 |

The prime-power counts are respectively 2,222, 3,320, 9,700 and 78,734.
The original profile's prime sums, archimedean bounds, margins, losses and
final residual enclosures match the previously recorded evaluator at all
six displayed decimals. Some improved-profile endpoints are one unit larger
than the other audit's conservative endpoints because that audit first
rounded the common margin to six decimals; this evaluator retains its full
integer precision until the final output.

## Arithmetic and transcendental enclosures

Every interval is represented by two integers `(lo, hi)` and means
`[lo / S, hi / S]`, where `S = 10^40`. Addition and subtraction are exact at
this scale. Products use the four endpoint products, rounded down and up.
Division separates the possible signs and rounds the extreme quotients
outward. A divisor interval containing zero is rejected.

Floating-point operations are used only for elapsed-time reporting. They
do not affect the mathematical intervals or pass/fail decisions.

### Logarithms

Write a positive integer as `n = 2^k r`, where `1 <= r < 2`. With
`z = (r-1)/(r+1)`, the identity

```text
log r = 2 sum_{j>=0} z^(2j+1)/(2j+1)
```

has `0 <= z <= 1/3`. After `m=50` terms the positive remainder is bounded by

```text
2 z^(2m+1) / ((2m+1)(1-z^2))
  <= 9 / (4(2m+1) 3^(2m+1)).
```

The code computes `log 2` by the same formula, adds `k log 2`, and includes
all rounding errors in the intervals. Logs of general positive intervals
are computed at their endpoints by
`log(endpoint/S) = log(endpoint) - log(S)` and monotonicity.

### Square roots

The lower integer endpoint is `isqrt(lo*S)`; the upper is the ceiling of
`sqrt(hi*S)`, detected by an exact square comparison. Python's arbitrary
precision integers avoid machine-integer overflow.

### Exponentials and hyperbolic functions

For a nonnegative endpoint, divide the argument by a power of two until it
is at most one. Evaluate the exponential Taylor polynomial through degree
40 with interval arithmetic. Since the following term ratios are at most
`1/42`, the remaining positive tail is less than twice the first omitted
term. Repeated squaring restores the original argument.

Negative arguments use `exp(-x) = 1/exp(x)`. Endpoint monotonicity gives
the exponential of an interval. `sinh` and `cosh` follow from their
definitions in terms of exponentials.

### Pi

Machin's identity

```text
pi = 16 atan(1/5) - 4 atan(1/239)
```

is evaluated with 40 terms of each alternating arctangent series. The
partial sum and the partial sum plus the first omitted term enclose the
answer. Those partial sums are exact `Fraction` values before conversion
to outward integer intervals. No decimal digits of pi occur in the code.

### Euler's constant

Let `A_n = H_n - log n - 1/(2n)`. We use

```text
A_n < gamma < A_n + 1/(12n^2),       n = 10,000.
```

An elementary proof of the remainder bound is useful for later
formalization. Put `y = 1/(2n+1)`. Then

```text
A_(n+1) - A_n
  = (1/2)(1/n + 1/(n+1)) - log(1+1/n)
  = sum_{j>=1} (4j/(2j+1)) y^(2j+1) > 0.
```

On the other hand,

```text
(1/12)(1/n^2 - 1/(n+1)^2)
  = sum_{j>=1} (4j/3) y^(2j+1).
```

Coefficient comparison bounds the first difference by the second. Summing
from `n` to infinity and using the definition of Euler's constant proves
the displayed enclosure. Harmonic sums are sums of outward-rounded exact
rationals. The resulting gamma interval has width less than `10^-9`;
that is ample for these positive margins.

## Prime sum and test function

An ordinary Eratosthenes sieve enumerates every prime below the largest X.
Each prime power is generated with exact integer multiplication, while
`log(p^k) = k log p` avoids an unnecessary second logarithm computation.

The normalized kernel uses `a/L = 99/200`, `b/L = 1/200`, and
`N/L = 2a/L - 2b/L = 49/50`. Its exact truncated-cube representation is
compiled to rational piecewise polynomials. Boundary comparisons use exact
integer/rational cross-products. If an interval overlaps multiple pieces,
the evaluator takes a hull of all applicable polynomial intervals.

The compiler is tested against the direct exact truncated-cube formula at
all breakpoints, 1,001 grid points, and intervals straddling every interior
breakpoint. This specifically checks cancellation and piece-selection
behavior independently of floating-point arithmetic.

## Analytic profiles being evaluated

With `d=1/100`, use the notation `L,a,b,N,P,J,A,B,C` from the analytic audit.
The common numerical margin is

```text
M = P - 14/(3N) + log pi + gamma - pi/2 + 3 log 2 - log Qmax.
```

The original profile subtracts

```text
low  = (A+B)(log Qmax+4),
high = C(1+T^2)/T^4 (log Qmax+4),            T=1000.
```

The shifted profile retains that low loss but uses

```text
W_T = (log Qmax-log pi+H_(T/2)-gamma+4)/(2T),
high = C((T+1)^2+T^2)/T^4 W_T,              T=100.
```

The sharper height-60 profile uses the same shifted high loss and

```text
A_exact = 4(cosh(ad)-1)^2 sinh(bd)^2 / (N b^2 d^4),
B_exact = 16 sinh(d(a-b))^2 / N,
low = (A_exact+B_exact)(log Qmax+1).
```

The code additionally verifies the two required numerical gates:

```text
3-gamma-(log 2)/2-log pi < 1,
sinh(d(a-b)) - 2bd cosh(d(a-b)) > 0.
```

The first constant is enclosed by `[0.931480, 0.931481]`. The second
margin's lower endpoints are respectively `0.047308`, `0.049503`,
`0.055290`, and `0.066363`.

The mathematical low-zero improvement follows from the exact shape of the
smoothed Haar kernel. The function `g(u)sinh(eta*u)` has one extremum on
each half-line under the taper condition. Its total variation is
`4 sinh(eta(a-b))`, and its L1 norm is the value obtained by evaluating its
Fourier transform at zero. These are analytic obligations in addition to
the finite numerical checks.

## Trust and remaining work

The computations now depend on Python's integer arithmetic, `isqrt`, the
standard rational implementation used to build coefficients, and the
visible evaluator code. They do not depend on numerical special-function
libraries or a supplied transcendental constant table.

The tests compare interval arithmetic with exact rational corner values,
logarithms and exponentials with longer exact rational series, the sieve
with trial division, square roots with exact inequalities, and the
piecewise kernel with the truncated-cube representation. Passing these
tests is evidence against implementation errors, not a proof of the entire
program.

Lean formalization must still prove the arithmetic enclosures and the
analytic explicit-formula, zero-mass, Fourier and variation lemmas, then
combine them with the exponent-seven norm obstruction. Neither the JSON
nor the test suite discharges `SearchHigh`, `SearchLow`, or the project's
GRH hypothesis.
