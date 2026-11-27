# Classification at all negative fundamental discriminants

In the shared Lean 4.35 environment, `Exp7.GRHIntegration.theoremD_fundamental_global`
proves that for a negative fundamental discriminant of a quadratic order
`QuadraticAlgebra ℤ a b` that is a domain, the class group has exponent 7
if and only if the discriminant is `-q` for one of the primes in `Exp7.known`.
Lean also checks that this list has length 33 and has distinct entries.
The theorem ranges over all such discriminants. The companion
`Exp7.GRHIntegration.theoremD_global` gives the prime-conductor formulation.
[Full statements and axioms](lean435-declarations.log)

## Proof

1. On the two closed half intervals the normalized autocorrelation of the
   actual row `[1,-1]` is respectively `1 − 3u/L` and `u/L − 1`.
   [HaarInert.lean](../../Exp7Lean/Exp7Lean/Tail/HaarInert.lean)
2. For each integer term of the project's `inertSum`, the proof counts the
   positive primes above the square root and bounds the odd-power loss below
   the cube root. It pairs every even prime power with its unique square root.
   The terms at zero and the upper endpoint vanish. Summing gives
   `weightedPrimeBalance X ≤ inertSum (autocorr (stepFn (log X) [1,-1])) X`
   for every integer `X > 1`. [Weighted sum estimates](../chebyshev-sums/)
3. For each prime conductor `q > 2^135` with `q ≡ 3 (mod 4)`, the dyadic
   comparison supplies `4X^7 < q` and an inert sum above `log q + 4`.
   The checked bound `J ≤ 4` gives a positive row margin. The explicit formula
   supplies a split prime `p < X` under the project's prime-conductor GRH.
   Exponent seven would force `q ≤ 4p^7`, a contradiction.
   [Exclusion.lean](../../Exp7Lean/Exp7Lean/Tail/Exclusion.lean)
4. The finite bridge covers `10^32 ≤ q ≤ 2^135`, and the bounded
   classification covers `q ≤ 10^32`. The genus reduction then gives the
   classification for fundamental discriminants. In the shared workspace
   the final adapter supplies the imported GRH theorem and both search
   certificates. [Finite bridge](../bridge30000/) · [Final adapter](Global.lean)

## Verification

The native package on Lean 4.37.0-rc1 checked the classification with
`GRHPrimeConductor`, `SearchHigh`, and `SearchLow` as explicit inputs.
In the shared Lean 4.35 build, the imported theorem originates at
`lsernau/grh-lean@72fead1` and both search certificates are proved.
The global declarations print exactly `propext`, `Classical.choice`, and
`Quot.sound`. [4.37 receipt](lean437-receipt.json) · [4.35 receipt](lean435-receipt.json) ·
[Integration pins](../grh-integration/pins.json)

The Precision reused the dependency builds and matched the sources and
objects of all 465 high and 401 low prime certificates and both assemblies
against the original build receipts. It compiled the tail and
the adapter, imported the result in a fresh process, and ran the Lean kernel
replay tool on the three proof modules added here and on the adapter.
The replay used their compiled imports. [Certificate comparison](search-cache.json) ·
[Kernel replay commands and exit codes](kernel-replay.json)

## Reproduce

For the native conditional theorem run these commands in the `Exp7Lean` package.

```sh
lake exe cache get
lake build Exp7Lean.Tail.Exclusion
lake env lean ../frontier/haar-tail/Declarations437.lean
```

For the full classification, start at the repository root in this checkout.
Use separate new directories for the pinned worker and the proof that builds
on it. The worker verifies the external GRH import and the bounded classification.
The commands below then add the finite row, tail, and global adapter to a copy.

```sh
REPO=$(pwd)
ROOT="$HOME/exp7-clean-worker435"
WORK="$HOME/exp7-clean-global435"
python3 frontier/grh-integration/worker.py --work-root "$ROOT" \
  --stages smoke external imported final --certificate-jobs 4
cp -a --reflink=auto "$ROOT/combined" "$WORK"
git diff 04d553508eb27e2a5a8e3e4becd1da64ccfedd0e HEAD -- Exp7Lean/Exp7Lean/Rows \
  > "$WORK/finite-row.patch"
cd "$WORK"
git apply --directory=src -p2 finite-row.patch
cp -r "$REPO/Exp7Lean/Exp7Lean/Tail" src/Exp7Lean/
cp "$REPO/frontier/haar-tail/Global.lean" src/Exp7GRHBridge/
export PATH="$ROOT/lean-4.35.0-linux/bin:$PATH"
export LEAN_NUM_THREADS=4
lake build Exp7Lean.Tail.Exclusion
lake env lean --root=src --tstack=400000 -o .lake/build/lib/lean/Exp7GRHBridge/Global.olean \
  src/Exp7GRHBridge/Global.lean
lake env lean "$REPO/frontier/haar-tail/Declarations435.lean"
```

The last compile imports the search objects that the worker has already
checked and assembled. The [native declaration log](lean437-declarations.log)
and [shared declaration log](lean435-declarations.log) show the expected output.
