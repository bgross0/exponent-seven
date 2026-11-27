# An exact pole-core fallback built from low-weight products

This executable avoids constructing a direct weight-ten modular-symbol
basis. It computes a weight-two q-basis once, checkpoints it immediately,
and selects products to construct weights4,6,10. Every claimed span is
checked against the full dimension and then checked over the rationals.
It finally constructs the same exact quotient

    (M10/E4^2) / d(M4/E4)

as `../de_rham_strategy/backend_probe.py`.

The script's existence and Python syntax check are not an executed Sage
result. Successful runs write their measured timings and checks to
`backend-result.json`; no runtime or successful pilot rank is asserted
before that file exists from the actual run.

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

## Product and rank strategy

The expected pilot dimensions, checked independently with Sage's modular
form dimension routine, are:

| Weight | Dimension | Candidate source |
|---|---:|---|
| 2 | 33 | Direct Sage q-expansion basis |
| 4 | 99 | Pairwise weight-two products, then E4 and V389(E4) if needed |
| 6 | 163 | M2 times M4, then E6 and V389(E6) if needed |
| 10 | 293 | M4 times M6, then E10 and V389(E10) if needed |

The expected rank97 of the weight-two products in weight4 is not assumed.
The actual rank before adding the explicit Eisenstein forms is reported.
If these candidates fail to span any required weight, the script saves
the partial basis and stops. It does not silently switch to a very large
direct computation.

Selection uses an incremental echelon basis modulo65537. Only independent
selected products are expanded over the integers. The program retains
at most the target-dimension modular echelon rows and the selected exact
rows, rather than materializing every product in one large matrix.
Exact rational rank is checked after selection. Product descriptions
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
* Sage's integral matrix saturation API documents the same meaning of
  saturation at one prime; the executable uses explicit kernel operations
  to retain an auditable transformation history:
  https://doc.sagemath.org/html/en/reference/matrices/sage/matrix/matrix_integer_dense.html
