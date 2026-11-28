# Zero obstruction with the certified smoothed Haar cubic

The frontier now has a Lean-checked unconditional damped explicit formula,
weighted zero-mass bounds, the actual smoothed-Haar complex transform,
exact L2 normalization and Fourier inversion, absolute convergence of its
zero sum, and a concrete-kernel conditional obstruction assembly. The actual
row kernel satisfies the damped formula and equals the cubic used by the integer verifier. The
full height-60 obstruction is **not yet formalized**. No new unconditional classification is claimed.

This work continues the height-60 argument in commit
`462b231fb1fdd3133de798e2d89501434a86e1a3` on `grh-import-audit`, beyond the
original `frontier-zero-obstruction` branch. The [historical source tree](https://github.com/bgross0/exponent-seven/tree/462b231fb1fdd3133de798e2d89501434a86e1a3/frontier)
retains the original interval implementation and auxiliary audit scripts.
The historical analytic audit and
integer verifier are restored unchanged in `../zero-audit/` and
`../zero-integer/`. Their original review and execution statements describe
that earlier work. The new replay is recorded separately here.

## What is proved

Statements about zeros and class groups use the existing quadratic character
`chi q`, completed L-function multiplicity `EF.mult`, and arithmetic predicate
`IsExp7`. The number-theoretic analytic statements concern prime `q` with `q % 4 = 3`. They do not replace
zeros by an arbitrary finite list or introduce a new L-function model.

| Module in `Exp7Lean/Exp7Lean/Frontier/` | Proved result |
| --- | --- |
| `Pointwise.lean` | The pointwise explicit-formula identity with each zero's real part retained, and absolute summability of its kernel. Under a separate GRH hypothesis it recovers the old kernel. |
| `DampedFormula.lean` | For every existing `WeilAdmissible` test function and real damping `delta > 1/2`, the unconditional integrated identity. The exchange of the zero sum and integral is justified by a uniform Poisson bound and the existing weighted zero density. |
| `ZeroMass.lean` | Exact real-axis partial fractions; the standard zero mass is at most twice the completed logarithmic derivative at 2; the shifted mass at `T > 0` is at most the completed logarithmic derivative at `T+1`, divided by T. |
| `ZeroLoss.lean` | The quartic high-zero tail comparison, summability and total high loss; the combined lower bound for the zero sum given explicit low/high test-function estimates. No high-zero critical-line assumption is needed. |
| `Obstruction.lean` | Multiplicity-preserving reflection; a negative certificate margin forces an actual L-function zero with `Re rho > 1/2+d` and `abs (Im rho) <= T`. The final wrapper connects the existing exponent-seven norm cutoff to the inert prime sum. |
| `ComplexTransform.lean` | Exponential twisting and convolution factorization for complex frequencies; direct box integration proves the transform of the actual smoothed Haar function. |
| `SmoothedKernel.lean` | Entire extensions of G and H via complex sinc; the removable value at zero; the closed transform formula and nonnegativity on the real axis. |
| `SmoothedCorrelation.lean` | H is the complex Fourier transform of the actual correlation divided by the explicit constant `2a-2b`, at every complex frequency. Its identification with the squared L2 norm is proved in `SmoothedNorm`. |
| `SmoothedDecay.lean` | The exact quartic strip bound and high-zero loss for H, with the same constant as the height-60 audit. No high-zero strip hypothesis or GRH is required. |
| `SmoothedSum.lean` | Absolute convergence of the concrete complex zero sum; its real-part lower bound; the concrete-kernel obstruction wrapper with convergence and high-zero decay discharged. |
| `SmoothedShape.lean` | Interval overlap identifies the actual convolution with a real continuous function; oddness, compact support and the central ramp, plateau and outer ramp are proved. |
| `SmoothedNorm.lean` | Integrating the three squared pieces proves `integral norm(g)^2 = 2a-2b` when `0 < b` and `2b <= a`. The actual correlation is real and has value one at zero. |
| `SmoothedSupport.lean` | The correlation is continuous, integrable, even, and vanishes whenever `abs u >= 2(a+b)`. |
| `SmoothedAdmissible.lean` | Fourier and cosine inversion; spectral integral `2*pi`; `abs f <= 1`; `WeilAdmissible` for the concrete kernel and the exact row parameters. The unconditional damped formula is instantiated for every natural `X > 1`. |
| `SmoothedCubic.lean` | The actual correlation equals the exact truncated cube sum for every real argument and natural `X > 1`. All seven closed polynomial cells agree with it, including both evaluations at every shared endpoint. |
| `Rows.lean` | The four exact integer intervals cover `[39*10^29, 10^162]`, each cutoff satisfies `4*X^7 < Qmin`, and every hypothetical exponent-seven field in the range supplies an inert row. |

There are 127 named theorems, plus three exact numerical regression examples.
`Checks.lean` prints all 127 theorem axiom dependencies. The only permitted
axioms are `propext`, `Classical.choice`, and `Quot.sound`. Hypotheses of the
conditional assembly theorem are still hypotheses even though they do not
appear in the axiom list.

The unconditional kernel uses

```text
(1/2 + delta - Re rho) /
  ((1/2 + delta - Re rho)^2 + (t - Im rho)^2).
```

Its width is positive when `delta > 1/2`. The previous pipeline's width was
`delta`, obtained only after imposing GRH. This difference is why the old
continuation proof cannot simply be reused to assert the undamped formula.

## Concrete kernel and proof boundary

For `0 < b < a`, the formal definitions use the actual convolution
`g = (1_[-a,0) - 1_[0,a)) * (1_[-b,b)/(2b))` and its reflected correlation
`f(u) = (g * g(-.))(u)/(2a-2b)`. The complex transform is proved to be

```text
G(z) = -i*a^2*z*sinc(a*z/2)^2*sinc(b*z),
H(z) = a^4*z^2*sinc(a*z/2)^4*sinc(b*z)^2/(2a-2b).
```

Complex sinc is defined by the analytic divided difference of sine, so these
formulas include zero without a division-by-zero convention. For nonzero z,
Lean proves the equivalent closed formulas in the historical audit.

The concrete obstruction wrapper uses `Re f` and `Re H((rho-1/2)/i)`.
It proves convergence and supplies the high-zero estimate, but still takes
as inputs the undamped explicit formula, the low-zero bound, the archimedean
bound and a strict numeric margin. Normalization and admissibility are now
proved under `0 < b` and `2b <= a`, including the boundary case.

For `x >= 0`, the spatial function is `-x/b` on `[0,b]`, `-1` on
`[b,a-b]`, `(x-a-b)/(2b)` on `[a-b,a+b]`, and zero beyond. Its squared
integrals on the three pieces are respectively `b/3`, `a-2b`, and `2b/3`.
Oddness doubles their sum to `2a-2b`; this establishes `f(0)=1` for the
actual convolution. Fourier inversion then proves the existing
`WeilAdmissible` interface.

`smoothed_row_damped_formula` uses exactly `a=99*log(X)/200` and
`b=log(X)/200`. Its assumptions are prime `q`, `q % 4 = 3`, natural
`X > 1`, and real damping `delta > 1/2`. It does not ask the caller to
supply normalization, support, admissibility, or a transform identity.
It still does not assert the undamped zero-sum identity.

`smoothCorrelation_row_eq_truncatedCubic` expresses the autocorrelation as a
sum of translated positive-part cubes at `t = u/log X`. The proof integrates
pairs of overlapping linear ramps exactly. `smoothCorrelation_row_eq_piece`
covers every polynomial selected by a closed cell of the evaluator. Verification
reads the rational shifts, divisor and Horner coefficients from the integer
program and checks both symbolic identities in Lean for arbitrary real `t`.

## What remains

1. Derive the undamped identity retaining the full zero sum. Continue an
   appropriate analytic transform, with locally uniform convergence proved,
   rather than substituting zero damping into the positive-width Poisson formula.
   Absolute convergence at the final zero sum is proved, but does not by itself
   justify analytic continuation.
2. Prove the exact low-zero shape and total-variation bound. The high-zero
   quartic bound is already proved and supplied by
   `smoothH_zero_obstruction_of_inert_certificate`; the low-zero estimate
   remains an explicit hypothesis.
3. Bound the real logarithmic derivatives and gamma terms numerically to
   convert `logDerivativeMass q 2` and `logDerivativeMass q 61` into the
   conductor-only mass bounds used by the integer verifier. The current
   mass theorems retain the exact analytic quantities.
4. Prove the explicit archimedean bound and certify the four finite prime-power
   sums in Lean, including a prime table through one million. General
   admissibility and `abs f <= 1` are now proved, but the sharper archimedean
   constant and positive Python margins are not Lean certificates.
5. Instantiate the conditional assembly at `d=1/100`, `T=60`, then connect
   the existing fundamental-discriminant reduction.

Even after these steps, excluding the forced low, off-line zero uniformly is
a further mathematical problem. The necessary-condition theorem would not
itself prove unconditional exclusion of exponent-seven fields.

The classical target identity is consistent with the normalization in
[Carneiro et al., Lemma 9, equation (3.1)](https://arxiv.org/html/2404.08380v2#S3).
This source guides the target statement; it is not an imported Lean axiom.

## Verification

The pinned toolchain is Lean `v4.37.0-rc1`. Run from the repository root:

```sh
python3 frontier/zero-obstruction/verify.py
```

The script builds the focused frontier target, checks the root import,
replays all 18 frontier modules with `leanchecker` against compiled imports, audits
the printed axiom dependencies, runs the seven integer arithmetic tests,
and reproduces all four rows. It records source hashes, commands, results
and logs in `verification/`. This does not rebuild the old class-group search
certificates, reprove the external analytic argument, or check every imported
Mathlib module afresh.

The reproduced height-60 residual lower endpoints are:

| X | Residual lower endpoint |
| ---: | ---: |
| 19,000 | 1.040803 |
| 30,000 | 0.253506 |
| 100,000 | 23.119888 |
| 1,000,000 | 75.929004 |

These are outward-rounded Python integer-interval results, not yet formally
certified inequalities. `integer-replay.json` retains the complete run.
