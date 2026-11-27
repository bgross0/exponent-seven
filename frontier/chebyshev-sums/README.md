# Weighted prime sums above the finite bridge

For every natural number `q > 2^135`, Lean proves that some `n ≥ 19`
satisfies both `4 * (2^n)^7 < q` and
`log q + 4 < weightedPrimeBalance (2^n)`.
The theorem is `Exp7.ChebyshevTail.exists_cutoff_above_bridge`.

At a cutoff `X`, the balance counts the positive weight of primes in
`(√X, X]`, subtracts twice a triangularly weighted von Mangoldt sum up
to the cube root of `X`, and subtracts the sum of `Λ(m)/m` up to `√X`.
The two subtracted sums bound the potential losses in the proposed Haar
argument. Every sum has an explicit finite range.

| Lean theorem | Proof |
|---|---|
| `positive_primes_ge` | Abel summation with Mathlib's lower and upper Chebyshev θ bounds, including the lower endpoint contribution |
| `odd_loss_le` | Abel summation of a logarithmic weight against ψ, with a checked antiderivative |
| `even_loss_le` | The divisor identity for Λ counts multiples exactly. Rounding the counts costs at most ψ. The stronger result is `mangoldt_div_sum_le`. |
| `weightedPrimeBalance_gt` | The three inequalities imply the strict dyadic comparison for every `n ≥ 19`. |
| `exists_cutoff_above_bridge` | Dyadic index selection gives the strict threshold for each `q > 2^135`. |

The remaining link is to prove that the project's `Exp7.inertSum` for the
two-cell Haar row dominates this balance. This requires the autocorrelation
values on both half intervals and the signs and cutoffs of the prime-power
terms. Combining that link with the Archimedean bound and the explicit
formula would yield the exclusion above the bridge. The certified
classification currently reaches `|D| ≤ 2^135`.

`DyadicArithmetic.lean` is the unchanged arithmetic proof from the [pinned
handoff](https://github.com/bgross0/exponent-seven/blob/248889f68a9a399ac1c4a011f89af1c4aa87ecd3/frontier/chebyshev-tail/ChebyshevTailArithmetic.lean).
The [tail derivation](https://github.com/bgross0/exponent-seven/blob/248889f68a9a399ac1c4a011f89af1c4aa87ecd3/frontier/chebyshev-tail/DERIVATION.md)
gives the formulas used for the three estimates. The Prime Number Theorem+
project also develops the explicit [Mertens bound for the even term](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/471f10c8164d59ed782680c5cd5d884e632e43c9/PrimeNumberTheoremAnd/IEANTN/Mertens.lean#L506-L535).
The proof here uses the existing pinned Mathlib dependencies.

## Reproduce

From the native `Exp7Lean` package on this branch, run

```sh
lake exe cache get
lake build Exp7Lean.Tail.WeightedComparison
lake env lean ../frontier/chebyshev-sums/Declarations.lean
```

For the 4.35 integration, copy `Exp7Lean/Exp7Lean/Tail/` to
`src/Exp7Lean/Tail/` in a separate prepared integration workspace.
Run the same Lake build target there, then run `lake env lean` on
the absolute path to [Declarations.lean](Declarations.lean).

The Precision compiled each module from source in separate project build
directories, reusing cached Mathlib dependencies. A fresh Lean process
imported the result and checked the axiom output for six public theorems.
Each printed exactly `propext`, `Classical.choice`, and `Quot.sound`.
[Lean 4.35 receipt](lean435-receipt.json) · [4.35 declarations](lean435-declarations.log) ·
[Lean 4.37.0-rc1 receipt](lean437-receipt.json) · [4.37 declarations](lean437-declarations.log)
