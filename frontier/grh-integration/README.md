# Bounded classification with the imported GRH theorem

The optional Lean 4.35 workspace combines exponent-seven at `04d5535` with
the compact GRH development at `72fead1`. In that environment the external
theorem `LFunction_eq_zero_re` supplies `Exp7.GRHIntegration.primeConductor`.
The bridge applies that proof to the four project entry points in `Final5`
and `Final6`. Theorem D covers negative fundamental discriminants through
absolute value `10^32`. Theorem A excludes exponent seven from `3.1 × 10^20`
through `10^32`. Both also have prime-conductor formulations.
[Lean signatures and axioms](receipts/final.declarations.log)

## Reproduce on Linux x86-64

Use Python 3.10+, git, tar and zstd. The worker installs its pinned Lean
toolchain under the specified directory. On the 31 GiB Precision we limited
the expensive per-prime checks to four concurrent Lean processes.

```sh
python3 frontier/grh-integration/worker.py \
  --work-root "$HOME/exp7-main-grh435-build" \
  --stages smoke external imported final --certificate-jobs 4
```

The worker copies both pinned sources, checks the hashes of the 4.35 proof
backports, and compiles the 866 committed prime certificates in batches.
A fresh Lean process imports the final object and prints the types and axiom
lists. Each must report `propext`, `Classical.choice`, and `Quot.sound`.
Complete local logs are in `combined/integration-receipts/` under the work root.

The Precision verification reused its previous proof cache. All 866
certificate source and object hashes and both assembly pairs matched the
previous receipts. The existing prepared inputs matched apart from the final
bridge. We compiled the two new entry points and the revised bridge, then
imported the result in a fresh process.
[Cache comparison](receipts/cache.json) · [Final receipt](receipts/final.json) ·
[Previous certificate build](https://github.com/bgross0/exponent-seven/tree/b8af22a977bcd563945430f1e4e10c414ae9b259/frontier/grh-integration/precision7670/certificates435)
