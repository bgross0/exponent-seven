# Finite bridge to 2^135

The 64-cell row with 32 entries of each sign has `X = 30000` and `Q = 2^135`.
Lean proves that its **real margin is at least 7.52277024130489382120**.
The fixed-point lower sum is `9924256547414500872107` at scale `10^20`.
The computation enumerates primes with the project's certified `primesBelow`
and includes powers through exponent 14. For each prime, the upper logarithm
is certified at precision P26 before rescaling to P20.

For `10^32 ≤ q ≤ 2^135`, the row and the explicit formula supply a split
prime `p < 30000` under the project's GRH input. Exponent seven would imply
`q ≤ 4 p^7 ≤ 4·30000^7 < 10^32`. The genus reduction gives the same exclusion
for negative fundamental discriminants with absolute value in the closed
interval. The proof beyond `2^135` remains open on the dyadic route.

## Project build

From the `Exp7Lean` package, use its pinned toolchain and run:

```sh
lake exe cache get
lake build Exp7Lean.Rows.Bridge30000
lake env lean ../frontier/bridge30000/Declarations437.lean
```

The target prints the axioms for the real margin, the `RowOK` certificate
and the two exclusion theorems. The native build uses Lean 4.37.0-rc1.
[Exact declarations](lean437-declarations.log) · [Build receipt](lean437-receipt.json)

## With the imported GRH proof

The optional Lean 4.35 bridge applies the proved `GRHPrimeConductor` to
both exclusions. It then applies the original Theorem D below the cutoff and
the new exclusion above it to obtain a single `theoremD_fundamental_135`.
This theorem classifies the 33 known cases throughout `|D| ≤ 2^135`.
Its input workspace is the pinned `04d5535` integration
built by [PR #1](https://github.com/bgross0/exponent-seven/pull/1).
Use a separate copy of that workspace. In the following commands `ROW_REPO`
points to this branch, `GRH_ROOT` to the worker root and `BRIDGE_WORK` to a
new directory outside those checkouts.

```sh
cp -a --reflink=auto "$GRH_ROOT/combined" "$BRIDGE_WORK"
git -C "$ROW_REPO" diff 04d553508eb27e2a5a8e3e4becd1da64ccfedd0e HEAD \
  -- Exp7Lean/Exp7Lean/Rows > "$BRIDGE_WORK/row.patch"
cd "$BRIDGE_WORK"
git apply --directory=src -p2 row.patch
cp "$ROW_REPO/frontier/bridge30000/FiniteBridge.lean" src/Exp7GRHBridge/
export PATH="$GRH_ROOT/lean-4.35.0-linux/bin:$PATH"
LEAN_NUM_THREADS=4 lake build Exp7GRHBridge.FiniteBridge
lake env lean "$ROW_REPO/frontier/bridge30000/Declarations435.lean"
```

A fresh process imported this module and printed the two interval theorems
and the combined classification with the GRH argument discharged. All three reported exactly `propext`,
`Classical.choice`, and `Quot.sound`.
[Exact declarations](lean435-declarations.log) · [Build receipt](lean435-receipt.json)

The Precision reused the 866 previously checked prime objects after matching
their source and object hashes, both assemblies, and the source files in their
import closures. It compiled the current `Final5`, `Final6` and bridge against
those objects. [Cache comparison](search-cache.json)
