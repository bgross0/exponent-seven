# An exact pole-core fallback built from low-weight products

This executable avoids constructing a direct weight-ten modular-symbol
basis. It computes a weight-two q-basis once, checkpoints it immediately,
and selects products to construct weights4,6,10. Every claimed span is
checked against the full dimension and certified over the rationals by
an explicit integer minor nonzero modulo an auxiliary prime.
It finally constructs the same exact quotient

    (M10/E4^2) / d(M4/E4)

as `../de_rham_strategy/backend_probe.py`.

The full level-eleven smoke calculation has passed in Sage. The actual
level389 bases in weights2,4,6 have also completed: dimensions33,99,163,
all with full q-coefficient rank modulo5, in9.400 seconds. The higher
pole quotient is a separate run. Successful full runs write their
measured quotient checks to `backend-result.json`.

## Bounded execution

From the repository root, first exercise the same implementation at a
small level:

```sh
timeout 5m sage -python research/bsd-localization/pole_core_fast/build_core.py --level 11 --q-precision 40 --output pole-fast-smoke
```

The pilot is:

```sh
timeout 30m sage -python research/bsd-localization/pole_core_fast/build_core.py --level 389 --q-precision 390 --output pole-fast-389
```

The program makes no network calls and installs nothing. It prints and
saves progress at each stage. There is a cap of20000 candidate products
per weight and30 local-saturation rounds. A failure exits instead of
treating an incomplete span as a basis.

Once M2 has been checkpointed, it can be reused without recomputing its
modular symbols:

```sh
timeout 30m sage -python research/bsd-localization/pole_core_fast/build_core.py --input-m2 pole-fast-389/M2-basis.json.gz --output pole-fast-resume
```

`M2-raw.json.gz` is also a supported input if interruption occurred before
its certification. A reused checkpoint is provenance-bearing input; the
script checks its dimensions, precision, and exact rank, but does not
reconstruct its original modular-symbol calculation.

For the Katz supplier, stop after the required low-weight bases:

```sh
timeout 10m sage -python research/bsd-localization/pole_core_fast/build_core.py --stop-weight 6 --q-precision 390 --output katz-short-bases
```

`--stop-weight` accepts2,4,6,10 and defaults to10. For a smaller stopping
weight the program writes `basis-result.json` and exits successfully
after its last basis checkpoint, without constructing the pole quotient.

## Product and rank strategy

The expected pilot dimensions, checked independently with Sage's modular
form dimension routine, are:

| Weight | Dimension | Candidate source |
|---|---:|---|
| 2 | 33 | Direct Sage q-expansion basis |
| 4 | 99 | Pairwise weight-two products, then E4 and V389(E4) if needed |
| 6 | 163 | M2 times M4, then E6 and V389(E6) if needed |
| 10 | 293 | M4 times M6, then E10 and V389(E10) if needed |

If a product space and its two Eisenstein oldforms still miss a direction,
the script adds scaled Serre derivatives of the nearest available lower
weight basis. For a weight-k form f, the classical Serre derivative is

    D_k(f)=theta(f)-(k/12)*E2*f,       E2=1-24*sum sigma_1(n)q^n.

It is a modular form of weight k+2 on the same group. The implemented
integral multiple is

    (12/gcd(k,12))*theta(f)-(k/gcd(k,12))*E2*f.

Thus weight4 receives the forms6*theta(f)-E2*f from M2. For weight6 the
source is M4; if needed at weight10, two successive Serre derivatives
start from M6. Every step and its source basis index are recorded in the
provenance. These are proven modular forms, not arbitrary derivatives of
q-series. All spanning and exact-rank checks still apply.

The first actual pilot attempt measured rank96 for the weight-two
products in weight4, and rank98 after E4,V389(E4). The previously proposed
rank97 was therefore not used. A separate exact modular probe on that
run's checkpoints found that6*theta(f0)-E2*f0, using the first M2 basis
row, increases the rank to99 modulo65537. The revised Sage run completed
M4, including one saturation round replacing two rows, and M6 with no
further saturation. Its exact provenance is in
[the actual Katz run record](../de_rham_strategy/katz-run-8726d59.json).

If all candidates fail, the script saves the partial basis and stops. A
rank shortfall is over the selection prime and can be caused by a bad
auxiliary prime; it is not a proof that the rational candidate span is
deficient. The program never silently starts a large direct computation.

Selection uses an incremental echelon basis modulo65537. Only independent
selected products are expanded over the integers. The program retains
at most the target-dimension modular echelon rows and the selected exact
rows, rather than materializing every product in one large matrix.
After selection the program records pivot columns and the nonzero
determinant residue of a full-size minor modulo the auxiliary prime.
An integer minor nonzero modulo a prime is nonzero over Q, which proves
the exact rational rank without a separate expensive rational elimination.
The checkpoint labels this derived rank proof explicitly. Product descriptions
identify the two input basis rows or the explicit Eisenstein oldform.

An alternative `--method ring` uses the documented
`ModularFormsRing(N).q_expansion_basis(weight, prec=..., use_random=False)`
API and applies the same exact rank, saturation, and quotient checks.
It is a separate fallback, with no claim that it is faster at this level.

## The local lattice at five is checked

Clearing rational denominators or forming products does not automatically
give a saturated integral basis. By default, the program saturates each
selected q-lattice at5.

Let B be the integer matrix of q-coefficients. A row of the left kernel
of B modulo5 gives an integer combination of the basis rows whose saved
coefficients are all divisible by5. Divide that combination by5 and
replace its pivot row. A reduced kernel basis permits simultaneous
replacement of its pivot rows. The transformation preserves the rational
span and enlarges the lattice by exactly one factor5 per replaced row.
Each combination and each exact division is saved in the checkpoint.

The requested q-precision is required to exceed the full Sturm bound.
All starting rows are known modular forms. Sturm's congruence criterion
therefore promotes the checked coefficient divisibility to the full
q-expansion at every saturation step. The process stops only when the
q-basis has full rank modulo5. At that point an explicitly selected
coefficient minor is a unit at5. This certifies a saturated q-integral
lattice at5 in the rational modular-form space.

The flag `--no-saturate-5` skips this stage; in that case the output records
whether the chosen lattice happened to have full rank modulo5. It does
not assert saturation when the rank test fails. The final report always
records the actual5-denominator losses in derivative and quotient
coordinates. A comparison to a different geometric or backend lattice
is not silently included in this claim.

## Exact quotient certificate

For every selected b in M4 the program constructs the weight-ten numerator

    E4*theta(b)-b*theta(E4).

It solves for its M10 coordinates using a full-rank coefficient minor,
then checks the equality at every saved q-coefficient. Since both sides
are weight-ten modular forms and the precision exceeds the Sturm bound,
this is an exact identity. The derivative rank must be dim(M4)-1.

For the pilot, the final checks require relation rank98 and quotient
dimension195. The saved right-hand quotient matrix Q satisfies D*Q=0
exactly and has full column rank. It uses the same capsule field names as
the original pole-core backend so later consumers can read the result.

The output is finite open de Rham geometry. It contains no projected CM
vector, residue removal, Fricke transformation, cup functional, or
arithmetic regulator comparison.

## Reuse the short constructions for the larger Katz calculation

`katz_supplier.py` extends only the direct M2 q-expansion. It reconstructs
M4 and M6 from the saved product, Eisenstein, Serre-derivative, and
saturation operations. It performs no direct M4/M6 modular-symbol
construction and no rational rank calculation on the long bases.

The adapter reads the three certified short basis checkpoints. It first
matches Sage's newly extended M2 basis to the saved raw M2 basis by an
exact coordinate transformation at short precision. This avoids an
assumption that the q-expansion algorithm kept the same basis ordering or
normalization when its requested precision changed.

Let r2,r4,r6 be the numbers of simultaneous saturation rounds in the
three checkpoints. To supply coefficients modulo5^m, the replay begins
modulo5^(m+r2+r4+r6). Every round divides its kernel combinations by5,
checks divisibility at **every long coefficient**, and reduces the common
precision by one digit. It also reduces the unchanged rows to that common
precision. Thus no unresolved division is performed in a ring that has
already discarded the required guard digit. Products and the integer
scaled Serre operators need no extra guard.

At each stage, every coefficient overlapping the short exact checkpoint
is compared. The saved mod5 unit minor is checked again. The extended M2
and completed long weight bases are checkpointed, and the final package
can be cached and reused with its request and checksum verified.

A small real Sage smoke test, using the earlier level11 short run, is:

```sh
sage -python research/bsd-localization/pole_core_fast/katz_supplier.py --checkpoints pole-fast-smoke --digits 3 --q-precision 80 --output supplier-smoke
```

For the six-digit Katz matrix, its auxiliary basis precision is eight
digits. The current Sage10.10 Sturm convention gives1366 columns in the
short comparison, so the long geometry basis is needed to exclusive
q-precision6830:

```sh
sage -python research/bsd-localization/pole_core_fast/katz_supplier.py --checkpoints katz-short-bases --digits 8 --q-precision 6830 --output katz-long-bases
```

The original CM input needs coefficients only through index6825 for
U5(input) in that comparison: the last selected index is5*(1366-1).
These two precision requirements concern different data.

The parent backend can install the supplier for one Sage call:

```python
with installed_supplier(hs, checkpoint_dir, output_dir, progress=progress):
    result = hs.higher_level_UpGj(p, N, klist, m, True, 6, extra_data=True)
```

This changes only `hs.low_weight_generators` inside the context and
restores it on exit, including on errors. It returns the complete proven
bases in weights2,4,6 with bound6. No global ring-generation conjecture is
asserted: Sage's complementary-space construction must achieve the full
dimension modulo5 at every requested weight before it can return. The
backend's external timeout still bounds an unsuccessful search.

The supplier's PASS status certifies the low-weight replay. The actual
six-digit parent run subsequently passed its finite Katz matrix identity;
neither stage alone is an elliptic CM projection. The pilot supplier took
170.376 seconds, including161.285 seconds extending M2 to6830 coefficients.
It checked every saved short coefficient and every long saturation
division. The full matrix gate completed in480.888 seconds. These are
measurements from
[run46059120633](https://github.com/bgross0/exponent-seven/actions/runs/46059120633),
with hashes and parameters in the run record linked above.

For any new execution, measured Sage replay results must come from
`supplier-result.json` after an actual run.

## Files saved by an actual run

* `progress.json`: measured stage timings, refreshed throughout execution.
* `M2-raw.json.gz`: expensive direct M2 result, saved immediately.
* `M2-basis.json.gz`, `M4-basis.json.gz`, `M6-basis.json.gz`,
  `M10-basis.json.gz`: certified bases, product provenance, and saturation
  operations as each stage succeeds.
* `pole-core-capsule.json.gz`: bases, exact derivative coordinates, and
  quotient matrix.
* `backend-result.json`: measured final status, dimensions, denominator
  diagnostics, metadata, and capsule checksum.

Primary API references checked for this implementation:

* Sage modular-form spaces, q-expansion bases and Sturm precision:
  https://doc.sagemath.org/html/en/reference/modfrm/sage/modular/modform/space.html
* Sage graded rings and the product-based q-basis API:
  https://doc.sagemath.org/html/en/reference/modfrm/sage/modular/modform/ring.html
* Sage's Serre derivative documentation, including the weight increase:
  https://doc.sagemath.org/html/en/reference/modfrm/sage/modular/modform/element.html
* Sage's integral matrix saturation API documents the same meaning of
  saturation at one prime; the executable uses explicit kernel operations
  to retain an auditable transformation history:
  https://doc.sagemath.org/html/en/reference/matrices/sage/matrix/matrix_integer_dense.html
