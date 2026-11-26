# Compute handoff: exponent-seven

26 November 2026. Work on isolated branches and workspaces. The immediate
use for another machine is the full pinned GRH integration build; the local
machine can then concentrate on the new analytic lemmas.

## Allocation

| Machine | Assignment | Starting resources | Accepted result |
| --- | --- | --- | --- |
| Precision 7670 running Kubuntu | Build the complete compact GRH proof and the exponent-seven bridge in the isolated `external435` environment | Aim for 30 GB free SSD; discover RAM/CPU in preflight and use automatic threads | Successful external and imported gates; complete logs, exact source receipts, and allowed axiom lists; optional final gate afterward |
| Local development node | Finish the Haar J bound, the three weighted Chebyshev/Abel lemmas, and the single numerical bridge row | Keep enough CPU and RAM free for one focused Lean job while editing | A compiled above-cutoff theorem assembled from the actual inert prime sum, existing explicit formula, and proved arithmetic inequality |
| Additional CPU node(s) | Claude's SearchHigh or SearchLow certificate jobs | Size from Claude's actual shard measurements | Kernel-checked certificates for explicitly assigned, nonoverlapping shards, followed by the corresponding exact search theorem |
| Optional independent audit node | Reproduce the completed pinned integration on a clean checkout; optionally perform Comparator replay | Ordinary build resources for reproduction; external README estimates 64 GB RAM for Comparator | Independent source/statement/axiom match and successful replay |

The external project's pinned README reports a one-to-two-hour ordinary build
on 12 cores with 24 GB RAM. That is a reported configuration and estimate,
not a minimum requirement or a measurement of the laptop. Fewer threads can
reduce memory pressure on a smaller machine. The 30 GB free-disk target
provides operating headroom for our integration. These are CPU and memory workloads.
No GPU or quantum task is currently defined for them.

Source for the external resource estimates:
[pinned compact GRH README](https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md).

## Start on the Precision 7670 / Kubuntu

Run these commands locally on the laptop after the `grh-import-audit` handoff
branch has been published. No SSH setup is required. The worker queries the
machine's actual CPU count, available RAM, and free disk; the model name alone
does not determine those resources.

```bash
sudo apt update
sudo apt install -y python3 git tar zstd ca-certificates
git clone --branch grh-import-audit --single-branch \
  https://github.com/bgross0/exponent-seven.git \
  "$HOME/exponent-seven-grh-handoff"
cd "$HOME/exponent-seven-grh-handoff"
python3 frontier/grh-integration/worker.py \
  --work-root "$HOME/exp7-grh-worker" \
  --preflight-only
```

Preflight reports resources and missing commands without downloading the
toolchain or creating the work root. Then start the default gates:

```bash
python3 frontier/grh-integration/worker.py \
  --work-root "$HOME/exp7-grh-worker"
```

Leave `--threads` unspecified initially. Its automatic choice is at most 8,
at most half the logical CPUs, and approximately one thread per 3 GiB of
currently available RAM, with a minimum of 1. An explicit `--threads 8` is
available for a machine with suitable headroom. Keep the laptop on AC power
and awake while the build runs.

The default run performs `smoke`, `external`, and `imported`. After those
complete, optionally attempt the bounded-classification wrapper with:

```bash
python3 frontier/grh-integration/worker.py \
  --work-root "$HOME/exp7-grh-worker" \
  --stages final
```

An interrupted run resumes by repeating its command with the same work root
and matching handoff source. Successful Lake modules are reused, while each
stage attempt gets a new log and receipt. The worker holds an exclusive lock
on its work root, stages setup before committing completed directories, and
checks every prepared Lean source plus its Lake configuration and manifest.
If the worker source itself changes, its source-identity check requires a new
dedicated work root.

The exact pins are recorded in `grh-integration/pins.json`:

| Source | Commit |
| --- | --- |
| `bgross0/exponent-seven` | `be878187267cd97bf3016c21b7182968898ba242` |
| `lsernau/grh-lean`, `grh-compact` | `72fead102f663d5c7a407964a13dc0cf9d977207` |
| Mathlib for `external435` | `56a005855ea17e0b0958f73ec801ae140b0a1679` |
| Lean toolchain | `leanprover/lean4:v4.35.0` |

The isolated preparation applies the explicit, hash-guarded `compat435`
backport. It preserves the project's class-group definitions and theorem
statements. Keep the external LICENSE, NOTICE, and ATTRIBUTION files. Fetch
the matching Mathlib cache before building project sources when available.

### Build gates and acceptance

1. **Smoke:** `Exp7GRHBridge.Smoke` checks that the external zero-on-line
   statement implies the project's actual `GRHPrimeConductor` definition.
   This gate alone does not supply a proof of that hypothesis.
2. **External:** `Main` must build the complete pinned compact proof.
3. **Imported:** `Exp7GRHBridge.Imported` must apply the actual compiled
   `LFunction_eq_zero_re` theorem to the project's quadratic character.
4. **Final:** `Exp7GRHBridge.Final` must compile the bounded classification
   wrapper with the imported proof. Its remaining SearchHigh/SearchLow
   hypotheses and `q<=QTOP` range must stay visible in the recorded statement.
   This optional gate may expose further project API compatibility work; it
   is not a prerequisite for accepting the completed imported-GRH gate.

For each gate, return the worker's reported receipt and full log. A receipt
must record the exact command, exit status, elapsed time, source/provenance
hashes, toolchain, and resulting theorem/axiom output. The allowed axioms are
a subset of `propext`, `Classical.choice`, and `Quot.sound`. An unfinished or
failed command is an unfinished or failed gate; preserve its log for diagnosis.

Do not share a writable Lake workspace between nodes. If a compatibility
failure requires source edits, make a separate integration branch, retain the
patch and new hashes, and rerun the affected gates. Successful builds of the
two source projects in different environments do not establish the bridge.

## Local mathematical job: the remaining analytic input

The new Chebyshev route proposes a uniform bound `q<2^135`, followed by one
finite row covering `10^32<=q<=2^135`. It can replace the current
`Above.Published.ekn3` input once assembled. The missing mathematical interface
is the lower bound for the **actual inert prime sum**:

`haarLowerBound n <= inertSum (autocorr (stepFn (log (2^n)) [1,-1])) (2^n)`

for n>=19, in the exact project normalization. Its proof consists of the
three weighted theta/psi estimates in `chebyshev-tail/DERIVATION.md`, the
prime-power parity partition, and the function identities. Mathlib already
provides the required Abel-summation theorems.

The single finite bridge has `X=30000`, `Q=2^135`, and the Haar shape
represented conceptually by `v=[1,-1]`. The current 64-cell evaluator should
receive 32 copies of 1 followed by 32 copies of -1, so its existing generic
correlation and J evaluators can be used directly.
The independent integer interval evaluator finds a margin in
`[3.898286,3.898287]` using the coarse bound `J<=4`. Kernel verification of
that finite certificate and its connection to the actual row margin remain
separate tasks. See `chebyshev-tail/IMPLEMENTATION_PLAN.md` for the numerical
integration work and the Haar J-bound component.

### Already completed arithmetic

`chebyshev-tail/ChebyshevTailArithmetic.lean` compiled with Lean 4.35.0 and
the Mathlib pin above, with exit code 0 and no errors or warnings. It proves:

* `Exp7.ChebyshevTailArithmetic.haarLowerBound_gt`: for every n>=19,
  `(7n+9)*log 2+4 < haarLowerBound n`, with the actual real constants and
  roots proved internally.
* `Exp7.ChebyshevTailArithmetic.exists_dyadic_index_of_mod_four`: for
  `q>=2^135` and `q%4=3`, there is n>=19 with
  `4*(2^n)^7<q` and `q<=2^(7n+9)`.

Both use only `propext`, `Classical.choice`, and `Quot.sound`. Exact hashes:

| File | SHA-256 |
| --- | --- |
| `ChebyshevTailArithmetic.lean` | `050550262cec4ef349c4dd3e85a1b09b45223757edcf7761e7e98a7711ba5fd5` |
| `arithmetic-lean.log` | `a0706a3041541b8f0ba4bf3fd7035b96a4f54a38c60085913029f6ae805e8764` |

The full receipt is `chebyshev-tail/arithmetic-lean-receipt.json`. These
proved components do not yet establish the weighted-prime-sum interface or
the assembled conductor bound.

## Additional nodes: coordinate search ownership with Claude

Claude owns the current SearchHigh/SearchLow integration. Before assigning
a node, obtain his exact branch/commit, generator command, certificate target,
and shard manifest. Record which worker owns each shard. The sieve prototypes
and audit results do not themselves constitute a ready distributed runner.

For SearchHigh, require the arithmetic bridge and kernel proof for the stated
quantifiers, including the fact that SearchHigh has no `p does not divide y`
hypothesis. For SearchLow, require the prime-power-root/CRT certificates and
the proof that surviving indices map to the permitted survivor list. In both
cases, acceptance is the compiled theorem and coverage manifest; a report of
zero Python survivors is experimental evidence rather than the final gate.

Start with the primary remote integration node. It removes the largest
independent build from the local proof-development workload and has a precise
success criterion. Allocate the search nodes from Claude's concrete job list
as soon as those shards are available.
