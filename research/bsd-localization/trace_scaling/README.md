# Scalable trace arithmetic and the cubic backend input

The actual CM tame-trace jets can now be generated without forming their
complete product q-expansions. The general generator computes all eight
variants through q^2048 at twelve 5-adic digits in **10.88 seconds**. The
specialized generator computes the one cubic-field representative requested
for the next Katz calculation through **q^6825 at twelve digits in 16.90
seconds**, with peak process memory about **129 MiB**.

The specialized output is `cubic-trace-6825-12.json.gz`, **224,893 bytes**.
It retains the coefficients of 1, W, and W^2 in three scalar columns. The
complete general q^2048 calibration is also retained, compressed, as
`traces-2048-12.json.gz`; no eight-variant q^6825 product data are stored.

These files are arithmetic inputs to a cohomology calculation. They do not
establish nonvanishing of an analytic projection or of the reflected global
class. The distinctions and reductions proved in
[`../analytic_target_audit/README.md`](../analytic_target_audit/README.md)
are essential for interpreting the next stage.

## Commands

From the repository root:

```sh
# Check the retained one-input, cubic-field dataset.
python research/bsd-localization/trace_scaling/cubic_trace.py --check

# Check all 387 vectors against the independent q^128 cubic reducer.
python research/bsd-localization/trace_scaling/check_cubic_overlap.py --check

# Check the complete eight-variant calibration at q^2048 and twelve digits.
python research/bsd-localization/trace_scaling/selected_trace.py \
  --bound 2048 --digits 12 \
  --output research/bsd-localization/trace_scaling/traces-2048-12.json.gz --check

# Reproduce the bounded benchmarks and all cross-checks.
python research/bsd-localization/trace_scaling/run_benchmarks.py
```

Both generators use Python's standard library and the existing, independently
audited CM ideal/logarithm helpers. Gzip files have timestamp zero and no
embedded filename. The verifiers recompute the data and compare the complete
deterministic artifact.

## Measured scaling

Each timed case below ran in a fresh process. Times include its checks,
serialization, and compression. The old workflow includes its original
larger verification suite, so the timing ratio is a workflow comparison,
not an isolated multiplication-kernel benchmark.

| Workflow | Trace bound | 5-adic digits | Workers | Wall seconds | Peak process RSS |
|---|---:|---:|---:|---:|---:|
| Original full-product workflow | 128 | 5 | 1 | 6.301 | 120.5 MiB |
| Selected-index, all variants | 128 | 5 | 1 | 0.284 | 17.9 MiB |
| Selected-index, all variants | 512 | 5 | 1 | 0.907 | 23.8 MiB |
| Selected-index, all variants | 2048 | 5 | 1 | 4.389 | 44.3 MiB |
| Selected-index, all variants | 512 | 12 | 1 | 2.352 | 31.4 MiB |
| Selected-index, all variants | 2048 | 12 | 1 | 10.880 | 79.6 MiB |
| Selected-index, all variants | 2048 | 5 | 2 | 2.723 | See below |
| One cubic averaged representative | 6825 | 12 | 1 | 16.896 | 129.1 MiB |

For the two-worker run, the parent peaked at 52.2 MiB and the workers at
30.7 and 30.5 MiB individually. These are process peaks, not a measurement
of simultaneous aggregate memory. The result was byte-for-byte identical
to the single-worker artifact. Detailed timings and counts are in the
`benchmark-*.json` receipts, `result.json`, and `cubic-result.json`.

## Selected-index contraction

The tame-trace theorem, with its slash and oldform normalizations, is in
[`../tame_trace_theory/TAME_TRACE.md`](../tame_trace_theory/TAME_TRACE.md).
For these CM families,

\[
\operatorname{Tr}_1\Xi=\operatorname{Tr}_2\Xi=\Xi+U_{71}\Xi.
\]

Therefore a result through q^B only needs raw product coefficients at

\[
S_B=\{1,\ldots,B\}\cup\{71,142,\ldots,71B\},
\qquad |S_B|=2B-\lfloor B/71\rfloor.
\]

The two cuspidal factors in a product start at q and q^389. Thus their CM
coefficient tables need only reach 71B-389. The code never constructs a
complete product array through 71B.

For one raw index m and a pair i+389j=m, put

\[
P_{i,j}(W)=g_i(W)\,\sigma(g_j(W)),
\quad \sigma(\zeta)=\zeta^{-1},
\quad L(n)=\log_5(n)/\log_5(6).
\]

The same three-term product supplies both placements:

\[
\begin{aligned}
A:&\quad (1+W)^{-L(i)}P_{i,j}(W), &&5\nmid i,\\
B:&\quad \sigma\big((1+W)^{-L(389j)}P_{i,j}(W)\big), &&5\nmid j.
\end{aligned}
\]

The both-depleted variants additionally require the other index to be
prime to 5. The term L(389j), including L(389), is necessary for the B
placement's inverse-Bol normalization. Conjugation is applied after
summing the B contributions because it is linear over Z_5.

At q^2048 there are 27,104,045 possible convolution pairs for a full raw
product through q^145408. The selected indices reduce this to 386,276
possible pairs. Zero CM coefficients and the depletion conditions reduce
the actual shared jet products to **103,355 per embedding**. Each product
is reused across placements and depletion variants.

At q^6825 the specialized cubic calculation reaches raw index 484575 but
forms only 13,554 raw product coefficients and evaluates **597,343**
shared jet products for its single embedding and input. It enumerates
1,263,725 CM ideal representatives; only the 808,868 with norm prime to 5
are retained in its both-depleted coefficient table.

## Exact packed multiplication

Write a coefficient in the basis 1,zeta,...,zeta^5, modulo M=5^d. Its
six nonnegative coordinate residues are packed into a Python integer in
radix 2^w. Choose

\[
2^w>18(M-1)^2.
\]

A coefficient of one polynomial product sums at most six elementary
products. The W^2 coefficient sums three polynomial products, so the
displayed inequality prevents every cross-coordinate carry. The three jet
products require six ordinary integer multiplications:

\[
P_0=a_0b_0,\qquad
P_1=a_1b_0+a_0b_1,\qquad
P_2=a_2b_0+a_1b_1+a_0b_2.
\]

Unpacking is exact. Reduction first uses zeta^7=1 and then
zeta^6=-(1+zeta+...+zeta^5). There is no floating-point convolution and
no approximate coefficient recovery. The radix widths are 28 bits at five
5-adic digits and 60 bits at twelve digits. Adversarial finite checks use
maximum coordinate residues, all basis vectors, and unequal jet orders;
the carry bound itself is the general justification.

## The one cubic representative

The independent analytic-target audit proves three cohomological
reductions: second-factor depletion changes the form by an exact
differential; the two tame 389 placements have the same E projection; and
that E projection is fixed by sigma. It also proves that the base and
first derivative vanish in the full elliptic de Rham projection. These
are useful required zero checks for a future reducer. Raw q-series can
still differ and have nonzero coefficients.

Accordingly `cubic_trace.py` selects omega=2 modulo 5 and
`both_depleted_g_times_V389_h`, then takes its coefficient-field average
(1+sigma)/2. The output is **an averaged representative with the same
E-projected class**, not the identical raw CM family. This operation
retains both elliptic Frobenius directions; it only reduces the scalar
coefficient field.

Set xi=zeta+zeta^-1. Then

\[
\xi^3+\xi^2-2\xi-1=0.
\]

The polynomial is irreducible modulo 5, so its three-dimensional
coefficient algebra is the unramified cubic subfield. For a six-coordinate
vector a, the average has cubic coordinates

\[
\frac12\left(
2a_0-2a_2-2a_5+a_3+a_4,\quad
a_1-a_3-a_4,\quad
a_2+a_5-a_3-a_4
\right).
\]

Division by 2 is a 5-adic unit operation. The implementation applies this
linear map directly to packed products, avoiding unused six-coordinate
product arrays and unused variants. It checks the map against explicit
conjugation and the cubic polynomial, and compares every overlapping
coefficient with the full general calculation.

The stored orders are the coefficients of 1, W, W^2 for W=6^(kappa-1)-1.
The last entry is half of the second W derivative. No change to the weight
coordinate, period normalization, or actual-derivative convention is made.

## Verification evidence

The general benchmark suite checks:

- all 3,096 vector coefficients of the pinned q^128/five-digit artifact;
- all 49,176 vector coefficients of q^2048/twelve digits reduced modulo 5^5
  against the independent five-digit run;
- q^512 prefixes at both precisions, 12,312 vectors each;
- all 1,392 available q^57 coefficients against the original pinned
  twelve-digit CM archive;
- identical full artifacts for one and two embedding workers;
- the U_5-annihilation of each raw depletion difference: 4,920 vector checks
  at q^2048, covering every order, embedding, and placement.

The q^6825 cubic artifact adds 263 exact cubic arithmetic checks and a
full-twelve-digit comparison of 6,147 cubic vector coefficients through
q^2048. It also agrees with all 387 vectors of the independently implemented
q^128 cubic reducer in `../weight_reflection/reduced_trace_inputs.json`,
modulo 3125; that separate check is saved in `cubic-overlap.json`.
Its gzip SHA256 is

```text
bbee40091bf8f13e0b89ace6381fb323bb03e62a1c6125a1f5948368f7361d19
```

Its uncompressed SHA256 is

```text
b1c4b10504dfe04daee367941f4e9b3ae42b31ec0a55f2bcf7e00cb8383fec2c
```

## Why q^6825, and what precision it does not certify

For the proposed p=5, matrix-precision m=6 Katz calculation, the sizing
parameters are depth n=10, top classical weight 42, Sturm bound ell'=1365,
and basis working precision m'=8. Basis q precision 5*1365=6825 is safe;
the actual U_5 input for coefficients below q^1365 reaches q^6820.

The saved twelve-digit input has four more digits than that nominal
eight-digit basis precision. This is **not a final six-digit error
certificate**: the overconvergent input norm/growth, the matrix solve,
the higher-slope condition number, and the proper cohomology comparison
still need bounded precision losses. The previously certified E projector
also has a one-digit worst-case 5-adic denominator cost. The trace and the
cubic averaging introduce no 5-adic division loss.

The current finite q-expansion is large enough for that proposed basis
size. It does not itself provide a Katz decomposition, the reduction
modulo exact and residue classes, the two elliptic de Rham coordinates,
or a comparison with the finite logarithm of the reflected global class.

## Using additional CPU nodes

The general generator exposes `--embedding 2`, `--embedding 4`, and
`--workers 2`. The embeddings can be computed independently on separate
nodes and their result dictionaries combined. Weight orders should stay
together inside a worker: splitting them would repeat the shared jet
products. The specialized cubic representative needs only embedding 2,
so extra nodes are more useful for independent precision/radius checks
or the upcoming matrix calculation than for reproducing discarded
variants. GPU arithmetic is not needed for these measured input sizes.
