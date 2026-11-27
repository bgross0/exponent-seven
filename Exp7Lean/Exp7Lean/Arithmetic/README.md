# Unconditional arithmetic lemmas

This module builds reusable consequences of the existing `Exp7.normEq_classGroup`
theorem. It imports the existing `IsExp7`, `Splits`, and analytic prime-sum
definitions. It neither changes their meaning nor assumes GRH, BSD, or a
low-height zero hypothesis.

`NormWitness q p x y` packages the existing conclusion:

```text
1 <= y
p != 2 -> p does not divide y
4*p^7 = x^2 + q*y^2
```

It is a necessary condition. A witness for one prime does not establish that the
class group has exponent seven. The raw arithmetic results also apply to
composite candidate conductors; primality is explicit wherever it is needed.

## How the lemmas connect

```text
IsExp7 q + an unramified split prime p
  -> exists_normWitness
     -> conductor_le, y_sq_le, y_sq_le_of_lower, x_sq_lt
     -> residual_isSquare
     -> y_eq_one -> first_slice (when 4*p^7 < 4*q)
     -> not_dvd_x (when p is odd, q is prime, and p != q)

IsExp7 q + 4*X^7 < q
  -> no_split_le
     -> legendre_eq_neg_one_of_cutoff -> legendre_pow_of_cutoff
     -> primeSum_eq_inertSum_of_cutoff

IsExp7 q + two distinct unramified split primes p,r, with p odd
  -> exists_paired_normWitness
     -> eliminate_conductor
     -> cross_products_ne -> determinant_ne_zero -> one_le_determinant_sq
     -> determinant_factorization and composition_identity
```

The arithmetic modules contain 27 reusable theorems, excluding example fixtures.
These are elementary consequences and integration lemmas, not a claim of new
number theory or an improved classification bound.

## Entry points for the research branches

| Consumer | Proved input | Obligation that remains |
| --- | --- | --- |
| Low-height zero argument | `IsExp7.primeSum_eq_inertSum_of_cutoff` gives the inert prime sum for any test function when `4*X^7 < q` | Establish the appropriate explicit formula, zero estimates, and contradiction with this prime sum |
| Diophantine or possible BSD route | `IsExp7.exists_paired_normWitness` gives two compatible primitive witnesses and a nonzero determinant | Supply and prove the actual reduction to the chosen curve or arithmetic problem; no BSD connection is asserted here |
| Finite search | `NormWitness.y_sq_le_of_lower` and `x_sq_lt` give finite bounds; `residual_isSquare` and `first_slice` give square obstructions | Prove coverage and exclusion of the resulting candidate ranges |

For two witnesses `(x,y)` at `p` and `(u,v)` at `r`, the main identities are:

```text
4*p^7*v^2 + u^2*y^2 = 4*r^7*y^2 + x^2*v^2
(x*v-u*y)*(x*v+u*y) = 4*(p^7*v^2-r^7*y^2)
(x*u+q*y*v)^2 + q*(x*v-u*y)^2 = 16*(p*r)^7
```

The last two identities are over the integers, preserving the determinant's
sign. Primitivity and distinct primes show `x*v != u*y`; the first prime must be
odd because Step 1 only supplies its primitivity in that case.

`not_isExp7_of_no_paired_normWitness` is the explicit downstream exclusion
criterion. Its exclusion hypothesis is still a hypothesis. The identities alone
do not rule out paired witnesses: `Examples.lean` checks a real pair at conductor
71, with `(p,x,y) = (3,92,2)` and `(r,u,v) = (2,21,1)`.

## Boundaries and validation

The first-slice theorem requires the strict inequality `4*p^7 < 4*q`. At equality,
`NormWitness 128 2 0 2` is a counterexample to concluding `y = 1`; this boundary
is included in the checked examples. The conductor cutoff `4*X^7 < q` is also
strict. The character lemmas cover primes `p <= X`, while the existing
`primeSum q f X` sums over integers strictly below `X`.

From `Exp7Lean/`, with the pinned toolchain and dependencies installed:

```sh
lake build Exp7Lean.Arithmetic.All Exp7Lean.Arithmetic.Examples
```

`Arithmetic.All` is imported by the default `Exp7Lean` target. The examples are a
separate target and print the axiom dependencies of the principal entry points.
Validation of this addition concerns these modules and their integration; it
does not constitute a fresh run of the 866 existing search certificates.

On 27 November 2026, all three theorem modules, `Examples.lean`, `All.lean`, and
the updated root `Exp7Lean.lean` were compiled successfully with Lean
`4.37.0-rc1`. This focused check used the existing baseline dependency artifacts
from commit `04d5535` and wrote new artifacts into the isolated worktree. It was
not a clean rebuild of Mathlib or the full repository. The eight axiom reports in
`Examples.lean` contain only `propext`, `Classical.choice`, and `Quot.sound`
(some use fewer).
