# A uniform Chebyshev tail using the existing GRH explicit formula

26 November 2026. The analytic conductor-bound argument remains a research
derivation. Its uniform arithmetic comparison and dyadic-index selection
have been checked by Lean as recorded below.

## Intended replacement

The current `Above.Published.ekn3` field imports a published least-split-prime
bound. There is a route to replace that input using the explicit formula already
proved in the project and elementary Chebyshev bounds already in Mathlib.

The proposed uniform statement is:

> Assuming the project's `ExplicitFormulaBound` and `GRHPrimeConductor`, an
> imaginary quadratic field with class-group exponent 7 has `q < 2^135`.

The remaining interval `10^32 <= q <= 2^135` is covered by one finite row:
`X=30000`, `Q=2^135`, `v=[1,-1]`. The gate is
`4*30000^7 = 87480000000000000000000000000000 < 10^32`.
A preliminary floating-point check of that row gives a positive margin about
7.4456; the separate integer interval verifier supplies the rigorous finite
arithmetic certificate. This would prove the desired exclusion `q>=10^32`
without using `Published.ekn3`, once the analytic bridges below are formalized.
It still assumes GRH. It does not solve the unconditional exponent-seven problem.

## Existing sources and the test function

Mathlib source, checked locally against v4.35.0:
`Mathlib/NumberTheory/Chebyshev.lean`.
The public source is
<https://github.com/leanprover-community/mathlib4/blob/v4.35.0/Mathlib/NumberTheory/Chebyshev.lean>.

The needed bounds, with `c=log 2`, are:

* `Chebyshev.theta_le_log4_mul_x`: `theta(t) <= 2c*t` for t>=0.
* `Chebyshev.theta_ge'`:
  `theta(t) >= (t-1)c-log(t+2)-2sqrt(t)log(t)` for t>=1.
* `Chebyshev.psi_le`:
  `psi(t) <= 2c*t+2sqrt(t)log(t)` for t>=1.

Here theta sums log p over primes p<=t; psi sums Lambda(n) over n<=t.
For t>=4 the lower theta bound implies the convenient form

`theta(t) >= c*t - 2sqrt(t)log(t) - 2log(t)`,                    (1)

because `2(t+2)<=t^2`, hence `c+log(t+2)<=2log(t)`.

Use the existing two-cell step function `v=[1,-1]` on [0,L], where
`L=log X`. Its normalized autocorrelation is

`f(u)=1-3u/L` for `0<=u<=L/2`,
`f(u)=u/L-1` for `L/2<=u<=L`,
`f(u)=0` for `u>=L`.

This is the existing `stepFn`/`autocorr` interface. No new smooth kernel or
unconditional zero-sum explicit formula is needed for this route.
The slope bound gives `Jterm(f)<=14/(3L)` by the same positive geometric-series
argument as the original frontier audit.

If q has exponent 7 and `4X^7<q`, the unconditional norm equation implies
that every prime p<X is inert. Thus the finite prime sum in the explicit
formula is

`P = 2 sum_{p^k<X} (-1)^k log(p) f(log(p^k))/sqrt(p^k)`.

Under GRH the existing explicit-formula inequality gives

`P <= log(q/pi)+psi(3/4)+14/(3L) <= log q+14/(3L)`.             (2)

The second inequality only needs `gamma>=0`, `pi<=4`, `log 2>=2/3`, and
`pi>=1`: `psi(3/4)=-gamma+pi/2-3log2<=0` and `-log pi<=0`.

## 1. A lower bound for the positive prime contribution

Use **all** primes between sqrt(X) and X. Restricting to [X/16,X/4] loses
too large a constant. On the larger interval the prime contribution is

`2 log(p) w(p)`, where `w(t)=log(X/t)/(L sqrt(t))`.

The function w is nonnegative and decreasing on [sqrt(X),X], with
`w(X)=0` and `w(sqrt(X))=1/(2X^(1/4))`. Abel summation gives

`2 sum_{sqrt(X)<p<=X} log(p)w(p)`
`= -2 theta(sqrt(X))w(sqrt(X)) + 2 integral_sqrt(X)^X theta(t)K(t)dt`,

where

`K(t)=-w'(t)=[(L-log(t))/2+1]/(L*t^(3/2)) >=0`.

The endpoint p=X contributes zero, so it does not matter that the original
sum uses the strict cutoff p<X. The endpoint p=sqrt(X) is omitted and can
only be an extra nonnegative contribution. For the dyadic X used below,
sqrt(X)>=4, so (1) applies throughout the integral.

The boundary term is at least `-2c*X^(1/4)`. For the c*t term in (1), direct
integration yields

`2c integral_sqrt(X)^X t K(t)dt`
`= 8c sqrt(X)/L - c(1+8/L)X^(1/4)`.

For the `2sqrt(t)log(t)` error, substitute u=log(t):

`4/L integral_(L/2)^L u[(L-u)/2+1]du = L^2/6+3L/2`.

For the `2log(t)` error, use log(t)<=L and
`(L-log(t))/2+1<=L/4+1`. Its contribution is at most

`(2L+8)*(X^(-1/4)-X^(-1/2)) <= (2L+8)X^(-1/4)`.

Consequently the selected positive prime contribution is at least

`Bplus(X)=8c sqrt(X)/L - c(3+8/L)X^(1/4)`
`          -L^2/6-3L/2-(2L+8)X^(-1/4)`.                    (3)

## 2. Negative odd prime powers

An odd prime power can contribute negatively only when `log(p^k)<L/3`.
Set `Y=X^(1/3)` and `ell=log Y=L/3`. Do not discard the triangular weight:
for n<=Y its magnitude is bounded by

`2 Lambda(n) h(n)`, where `h(t)=(1-log(t)/ell)/sqrt(t)`.

We may enlarge from odd prime powers to all integers n<=Y, because h>=0
and Lambda>=0. The weight vanishes at Y and psi(1)=0. Abel summation gives

`sum_{n<=Y} Lambda(n)h(n) = integral_1^Y psi(t)[-h'(t)]dt`,

where

`-h'(t)=t^(-3/2)*[(1/2+1/ell)-log(t)/(2ell)] >=0`.

Use `psi(t)<=log4*t+2sqrt(t)log(t)` in this integral. The first term evaluates
exactly to

`log4*[4sqrt(Y)/ell-1-4/ell] <= 4log4*sqrt(Y)/ell`.

For the second term, setting u=log(t) gives

`integral_0^ell [(1+2/ell)u-u^2/ell]du = ell^2/6+ell`.

Restoring the factor of 2, the total magnitude of the negative odd terms is
therefore at most

`Bodd(X)=24log4*X^(1/6)/L + L^2/27 + 2L/3`.                (4)

This includes the negatively contributing small primes. It does not overlap
with the selected positive primes in (3), because `X^(1/3)<sqrt(X)`.

## 3. Negative even prime powers

Write an even prime power as n=m^2, where m is a prime power. Then
`Lambda(n)=Lambda(m)`. Wherever f is negative, `2|f|<=1` for this Haar
autocorrelation. Thus the magnitude of all negative even terms is at most

`sum_{m<=sqrt(X)} Lambda(m)/m`.

This uses Lambda(m), not log(m); replacing it with log(m) needlessly loses
a logarithm. Abel summation and the same upper bound on psi give, for M>=1,

`sum_{m<=M} Lambda(m)/m = psi(M)/M + integral_1^M psi(t)/t^2 dt`
`<= log4*(1+log M) + 8 - (2log M+8)/sqrt(M)`
`<= log4*(1+log M)+8`.

Putting M=sqrt(X), the negative even loss is at most

`Beven(X)=log4*(1+L/2)+8 = 2c+cL+8`.                      (5)

The original strict n<X cutoff only removes terms from this upper bound.
The term m=1 is zero because Lambda(1)=0.

## 4. Combined lower bound

Keep the positive primes from (3), discard all other nonnegative terms,
and subtract the bounds (4) and (5). The result is

`P >= 8c sqrt(X)/L - c(3+8/L)X^(1/4)`
`     -24log4*X^(1/6)/L -(11/54)L^2`
`     -(13/6+c)L -(2c+8) -(2L+8)X^(-1/4)`.                 (6)

Every prime-power term is accounted for: the parity of k determines its sign
before multiplying by f, and the sign of f determines whether it is retained
or covered by one of the two negative bounds.

## 5. A uniform inequality by dyadic induction

Choose `X=2^n`, n>=19, so L=nc. Suppose also

`q < 2^(7n+9)`, hence `log q < (7n+9)c`.

Multiplying the desired strict inequality `P>(7n+9)c+14/(3nc)` by n and
using (6), it is enough to show

`8*2^(n/2) > E1(n)+E2(n)+E3(n)+E4(n)+E5(n)+E6(n)+E7`,     (7)

where

| term | expression |
| --- | --- |
| E1 | `(3cn+8)*2^(n/4)` |
| E2 | `48*2^(n/6)` |
| E3 | `(11/54)*c^2*n^3` |
| E4 | `(55/6+c)*c*n^2` |
| E5 | `(11c+8)*n` |
| E6 | `n*(2cn+8)*2^(-n/4)` |
| E7 | `14/(3c)` |

All terms are nonnegative. From n to n+1, the left side grows by sqrt(2),
which is greater than 7/5. For n>=19, every error term grows by at most 7/5:

| term | upper bound on its growth factor |
| --- | --- |
| E1 | `(20/19)*(6/5)=24/19 < 7/5` |
| E2 | `6/5 < 7/5` |
| E3 | `(20/19)^3 < 7/5` |
| E4 | `(20/19)^2 < 7/5` |
| E5 | `20/19 < 7/5` |
| E6 | `(20/19)^2 < 7/5` |
| E7 | `1 < 7/5` |

For E1/E6, `(a(n+1)+b)/(an+b) <= (n+1)/n` when a,b>=0. The root bounds
`2^(1/4)<6/5`, `2^(1/6)<6/5`, and `2^(-1/4)<=1` suffice.
Therefore a single rational base check at n=19 proves (7) for all n>=19.

Use `2/3<=c<=7/10`, `sqrt2>=7/5`,
`2^(19/4)<=27`, `2^(19/6)<=9`, and `2^(19/4)>=16`.
The root inequalities follow by raising positive numbers to integer powers.
The base main term is at least `28672/5`, while the sum of error bounds is
at most `56695939/10800`. The strict rational slack is

`5235581/10800 > 0`.

`verify_induction.py` checks all the rational and integer inequalities used
in this induction and records them in `induction-result.json`. It does not
claim to certify the Abel-summation derivation or the properties of log 2;
those are separate explicit proof obligations.

## 6. Turning the uniform inequality into a q bound

For an odd prime `q>=2^135`, choose n>=19 so that

`2^(7n+2) < q < 2^(7n+9)`.

For example, let `k=floor(log_2 q)` and `n=floor((k-2)/7)`.
Then `7n+2<=k<7n+9`. The lower power-of-two equality cannot occur because
q is an odd prime. The upper strict inequality follows from q<2^(k+1).

With `X=2^n`, the lower bound is `4X^7<q`, so every prime below X is inert.
The upper bound puts log q below `(7n+9)c`. The uniform lower bound (7)
then contradicts the GRH explicit-formula upper bound (2).

Hence `q<2^135`. This is an explicit, fully uniform conductor bound derived
from the same GRH hypothesis and the project's own explicit formula.

## 7. Finite bridge to the existing 10^32 cutoff

For `10^32<=q<=2^135`, the fixed cutoff X=30000 satisfies `4X^7<q`.
The same Haar function therefore has the inert prime sum. A positive row
margin

`P_30000 - 14/(3log30000) + log pi - psi(3/4) -135log2 >0`

contradicts the existing explicit-formula inequality. The new row can also
be fed through the project's existing positive-row-to-split-prime reduction:
it produces p<30000, and Step 1 gives `q<=4p^7<10^32`.

This bridge requires a certified prime table only through 30000, not through
the uniform tail's variable X. No primes are enumerated in the infinite tail.

## 8. Simpler integration profile using the existing Jplus theorem

The sharper `J<=14/(3L)` bound above is optional. To minimize new analytic
formalization, one can use the already proved `Jterm_le_Jplus` and derive the
coarser `J<=4` for this two-cell vector and L>=2:

* The first-cell contribution in Jplus is `1-corr([1,-1],1)=3/2`.
* In each of the 16 middle subcells, put `h=L/32` and `u=h(16+i)`.
  Then `u>=16h`, the factor `1-f` is at most 3/2, and the existing lemma
  `aKer_mul_self_le_one` gives `h*aKer(u)<=1/16`. The sum is at most 3/2.
* The remaining tail is `4/[3exp(3L/2)(1-exp(-2L))]`. For L>=2,
  `exp(3L/2)>=4` and `exp(2L)>=5` follow from `exp(x)>=1+x`.
  Hence this tail is at most 5/12, in particular at most 1.

The upper bound in (2) becomes `P<=log q+4`. In (7), replace E5 by
`(11c+12)n` and omit E7. The same growth bounds hold. At n=19 the rational
slack becomes

`4490381/10800 > 0`.

Thus the same uniform cutoff `2^135` works with this simpler profile. The
fixed bridge row also still has a positive margin when 4 replaces its J
bound: the independent integer interval verifier encloses it in
`[3.898286,3.898287]`. `ChebyshevTailArithmetic.lean` uses this coarse profile
explicitly.

## 9. Kernel-checked arithmetic component

`ChebyshevTailArithmetic.lean` was checked successfully with Lean 4.35.0 and
Mathlib commit `56a005855ea17e0b0958f73ec801ae140b0a1679`. The final run
returned exit code 0 with no errors or warnings. Its two main public results
are:

* `haarLowerBound_gt`: for every natural n>=19, the explicit lower-bound
  expression obtained from (6), with the actual constants `log 2`,
  `2^(1/2)`, `2^(1/4)`, and `2^(1/6)`, exceeds
  `(7n+9)log 2+4`. No numerical root bounds are assumed by this theorem;
  they are proved from Mathlib inside the file.
* `exists_dyadic_index_of_mod_four`: if `q>=2^135` and q is 3 modulo 4,
  there exists n>=19 with `4*(2^n)^7<q` and `q<=2^(7n+9)`. The weak upper
  endpoint is sufficient because the arithmetic comparison is strict.

Both declarations depend only on `propext`, `Classical.choice`, and
`Quot.sound`. Neither depends on `sorryAx`, `native_decide`, an asserted
Chebyshev inequality, or any GRH declaration. The exact source hashes,
toolchain, command, and axiom output are in `arithmetic-lean-receipt.json`;
the output is also retained in `arithmetic-lean.log`.

This checks the infinite algebraic induction and the integer choice of
cutoff. It does **not** yet check that the actual inert prime sum is bounded
below by `haarLowerBound n`. The Abel-summation argument, function identities,
finite bridge certificate, and composition with the existing explicit formula
remain the integration work listed next.

## Formalization obligations and limits

The argument has been written so that the difficult inputs already exist:
GRH explicit formula, norm equation, and elementary Chebyshev bounds. What
remains is meaningful work, not a one-line theorem application:

1. Specialize `autocorr_stepFn_of_mem_cell` to the two-cell vector. Either
   prove the sharper J bound or specialize the existing Jplus theorem as in
   Section 8.
2. Express the inert prime sum as prime powers and partition by parity and
   sign. Check the finite-sum endpoints as described above.
3. Apply Abel summation with the three displayed weights. Establish the
   weighted theta/psi integral bounds and evaluate the elementary integrals.
4. Prove the algebraic dyadic induction and select n from q.
5. Kernel-check the single bridge row and connect the resulting above-cutoff
   theorem to the project classification theorem.

This route is intended to remove one published-result interface while
preserving the explicit GRH hypothesis. It does not make the global
classification unconditional. No compiled theorem should be claimed until
the listed bridges have actually been built and checked.

For item 3, Mathlib already provides `sum_mul_eq_sub_sub_integral_mul` for
the positive-prime interval with real endpoints, and
`sum_mul_eq_sub_integral_mul₀` for the two psi sums with lower integral
endpoint 1. `Chebyshev.theta_eq_sum_Icc` and `Chebyshev.psi_eq_sum_Icc`
identify the finite coefficient sums. The proof of
`Chebyshev.primeCounting_eq_theta_div_log_add_integral` provides a concrete
example of the derivative and integrability obligations for this interface.
