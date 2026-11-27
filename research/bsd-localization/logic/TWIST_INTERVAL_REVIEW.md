# Independent review of the quadratic-twist interval

Reviewed 2026-11-27 by the localization/logic worker, independently of the author of `../eligibility/arithmetic/check_twist_lvalue.py`.

**Result:** no error found in the reviewed analytic identity, coefficient recurrence, interval directions, or tail bound. A fresh exact recomputation matched the committed data file:

```sh
python research/bsd-localization/eligibility/arithmetic/check_twist_lvalue.py \
  --check research/bsd-localization/eligibility/arithmetic/twist-lvalue.json
```

Exit code: 0. Output: `PASS: exact rational recomputation agrees with research/bsd-localization/eligibility/arithmetic/twist-lvalue.json`.

## Mathematical checks

* The integral twist model has invariants c4 = 112*(-71)^2, c6 = -856*(-71)^3, and discriminant 389*(-71)^6. Discriminant valuations six and one imply minimality at 71 and 389. The standard local classification gives conductor 389*71^2 = 1,960,949.
* The primitive character chi_(-71)(n) is the Legendre symbol (n/71), including zero on multiples of 71. The coprime quadratic-twist sign formula gives sign +1 from chi_(-71)(-389) = +1.
* The good-prime traces are obtained from the exact discriminant of the quadratic equation in y. The recurrence a_(p^r) = a_p a_(p^(r-1)) - p a_(p^(r-2)) is used at good primes, with multiplicativity and the split-multiplicative trace a_389 = 1 at the bad prime. Twisting the coefficients by chi_(-71) also gives the correct zero local coefficients at the additive prime 71.
* Splitting the Mellin integral at 1/sqrt(N), and using the Fricke equation with global sign +1, yields the factor two in L(1) = 2 sum_(n>=1) a_n exp(-2*pi*n/sqrt(N))/n.
* Hasse and Euler-factor multiplicativity give |a_n| <= d(n)*sqrt(n) <= 2n. The omitted terms are therefore bounded by 4*r^6001/(1-r), with r = exp(-2*pi/sqrt(N)).

## Interval checks

* The Machin formula combines lower and upper arctangent endpoints with the correct sign for the negative term.
* The lower and upper square-root endpoints are reversed correctly when bounding 2*pi/sqrt(N).
* The 20-term alternating exponential sum ends with the negative degree-19 term; adding the positive degree-20 term supplies an upper endpoint. Monotonicity of exp(-x) reverses the argument endpoints correctly.
* Integer floor and ceiling are used outwards for powers, both signs of Fourier coefficients, and the tail. The scaling factor in the tail expression is correct.

The resulting interval is

\[
0.9360088537803042525901954783264223920549
\le L(E^{(-71)},1)\le
0.9360088573972690020870684844656754102100.
\]

The arithmetic is exact and the positive lower endpoint is separated substantially from zero. Its interpretation as an elliptic-curve L-value uses the explicitly stated standard modularity, local-reduction, character-twist, Mellin/Fricke, and Hasse theorems. Those analytic inputs and this program have not been formalized in Lean here.

This establishes only the quadratic-twist factor of the Castella–Hsieh auxiliary nonvanishing condition. The nontrivial class-character factor is the separate seven-Gross-point task in `C7_AUXILIARY_PERIOD.md`.
