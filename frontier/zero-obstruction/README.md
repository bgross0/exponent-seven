# Zero obstruction: first formal analytic milestone

The frontier now has a Lean-checked unconditional damped explicit formula,
weighted zero-mass bounds, a quartic high-zero loss estimate, and the final
conditional obstruction assembly. The full height-60 obstruction is **not yet
formalized**. No new unconditional classification is claimed.

This work continues the height-60 argument in commit
`462b231fb1fdd3133de798e2d89501434a86e1a3` on `grh-import-audit`, beyond the
original `frontier-zero-obstruction` branch. The [historical source tree](https://github.com/bgross0/exponent-seven/tree/462b231fb1fdd3133de798e2d89501434a86e1a3/frontier)
retains the original interval implementation and auxiliary audit scripts.
The historical analytic audit and
integer verifier are restored unchanged in `../zero-audit/` and
`../zero-integer/`. Their original review and execution statements describe
that earlier work. The new replay is recorded separately here.

## What is proved

All new declarations use the existing quadratic character `chi q`, completed
L-function multiplicity `EF.mult`, and arithmetic predicate `IsExp7`. The
analytic statements concern prime `q` with `q % 4 = 3`. They do not replace
zeros by an arbitrary finite list or introduce a new L-function model.

| Module in `Exp7Lean/Exp7Lean/Frontier/` | Proved result |
| --- | --- |
| `Pointwise.lean` | The pointwise explicit-formula identity with each zero's real part retained, and absolute summability of its kernel. Under a separate GRH hypothesis it recovers the old kernel. |
| `DampedFormula.lean` | For every existing `WeilAdmissible` test function and real damping `delta > 1/2`, the unconditional integrated identity. The exchange of the zero sum and integral is justified by a uniform Poisson bound and the existing weighted zero density. |
| `ZeroMass.lean` | Exact real-axis partial fractions; the standard zero mass is at most twice the completed logarithmic derivative at 2; the shifted mass at `T > 0` is at most the completed logarithmic derivative at `T+1`, divided by T. |
| `ZeroLoss.lean` | The quartic high-zero tail comparison, summability and total high loss; the combined lower bound for the zero sum given explicit low/high test-function estimates. No high-zero critical-line assumption is needed. |
| `Obstruction.lean` | Multiplicity-preserving reflection; a negative certificate margin forces an actual L-function zero with `Re rho > 1/2+d` and `abs (Im rho) <= T`. The final wrapper connects the existing exponent-seven norm cutoff to the inert prime sum. |
| `Rows.lean` | The four exact integer intervals cover `[39*10^29, 10^162]`, each cutoff satisfies `4*X^7 < Qmin`, and every hypothetical exponent-seven field in the range supplies an inert row. |

There are 27 named theorems, plus three exact numerical regression examples.
`Checks.lean` prints all 27 theorem axiom dependencies. The only permitted
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

## What remains

1. Prove the smoothed Haar kernel's normalization, Fourier transform,
   admissibility and complex-strip decay. The numerical verifier's truncated
   cubic formula must be connected to that actual kernel.
2. Derive the undamped identity retaining the full zero sum. Continue an
   appropriate analytic transform, with convergence proved, rather than
   substituting zero damping into the positive-width Poisson formula.
3. Prove the exact low-zero shape/variation bound and the complex high-zero
   quartic bound for that kernel. These are explicit hypotheses in
   `zero_obstruction_of_inert_certificate`.
4. Bound the real logarithmic derivatives and gamma terms numerically to
   convert `logDerivativeMass q 2` and `logDerivativeMass q 61` into the
   conductor-only mass bounds used by the integer verifier. The current
   mass theorems retain the exact analytic quantities.
5. Prove the archimedean bound and certify the four finite prime-power sums
   in Lean, including a prime table through one million. Row coverage and
   the norm cutoffs are already proved, but positive Python margins are not
   Lean certificates.
6. Instantiate the conditional assembly at `d=1/100`, `T=60`, then connect
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
replays each new module with `leanchecker` against compiled imports, audits
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
