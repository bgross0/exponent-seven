# Exact checks and a single cubic-field trace representative

The mathematical deductions are in
[analytic_target_audit/README.md](../analytic_target_audit/README.md).
This directory independently checks their finite consequences against the
previously pinned CM and trace data, and supplies a much smaller input
for the forthcoming proper-cohomology computation.

## What is now reduced

The eight original inputs consisted of two CM embeddings, two placements
of the raw V389 operator, and two depletion conventions. They need not
have the same raw q-series. Their **proper elliptic cohomology outputs**
are related as follows:

* The extra depletion changes the input by a U5-killed form. Coleman's
  cohomological quotient and invertibility of Verschiebung make this
  difference exact.
* Fricke389 exchanges the two placements with a minus sign, while its
  action on the full elliptic factor is also minus. The placements
  therefore have the same elliptic projection.
* A weight-zero Rankin--Cohen primitive identifies a placement with the
  coefficient conjugate of the other placement in cohomology. The
  elliptic output is consequently fixed by sigma(zeta7)=zeta7^-1.

One representative over the unramified cubic field is sufficient. This
halves the coefficient field degree and eliminates redundant input
variants; it retains both elliptic Frobenius directions.

## Finite identities independently checked

Put nu=log5(389)/log5(6), W=6^(kappa-1)-1, and
`iota(W)=(1+W)^(-1)-1=-W+W^2+O(W^3)`. For the doubly depleted inputs,

    A(iota(W))=(1+W)^nu B(W).

At the three saved Taylor orders this is

    A0 = B0,
    -A1 = B1 + nu*B0,
    A1+A2 = B2 + nu*B1 + nu*(nu-1)/2*B0.

The checker validates 24,582 raw vector identities through q4096 modulo
5^12 and 774 traced vector identities through q128 modulo 5^5. It also
checks 9,840 raw and 312 traced U5-zero identities for the depletion
differences, and 49,164 raw and 1,548 traced coefficient-conjugation
identities between the two CM embeddings.

The raw depletion differences are nonzero: their first q-indices are
1946 and 394 for the two placements; after tracing they are 28 and 9.
The proof identifies an exact differential, not equal q-series.

Fricke389 is independently constructed from its action on rational
cusps in the 65-dimensional Manin presentation. All 780 relations are
checked, its matrix squares to the identity, and its restriction to the
saved two-dimensional elliptic eigenspace is exactly minus the identity.
An independent count on the singular fiber at 389 also gives a389=1.

## Cubic arithmetic and the saved representative

Let

    xi=zeta7+zeta7^-1,
    xi^3+xi^2-2*xi-1=0.

The cubic polynomial has no root modulo five, so it defines the
unramified cubic coefficient field. The saved representative is the
coefficient-wise average of the traced, doubly depleted A input and its
sigma conjugate. Division by two loses no 5-adic precision.

In the six-coordinate basis 1,zeta,...,zeta^5,

    xi   = (-1,0,-1,-1,-1,-1),
    xi^2 = (2,0,1,0,0,1).

For a sigma-invariant vector v the cubic coordinates are

    (v0-2*v2+v3, -v3, v2-v3).

Every conversion is reconstructed and checked in the original basis.
[reduced_trace_inputs.json](reduced_trace_inputs.json) has all three
Taylor orders through q128 modulo 5^5. It stores 1,161 scalar residues,
compared with 18,576 in the original eight-input representation: a
factor of 16 in this input representation. This is not a measured
factor of 16 in total computation time.

The larger [q6825 input](../trace_scaling/README.md) independently applies
the same reduction while generating the selected coefficients. The
separate overlap checker compares all 387 cubic vectors of this fixture.

## The second coefficient remains the target

After the stated unit normalization, the projected family is even in
s=kappa-1. Its base value is zero by the published DL theorem and the
pilot's exact central-value zero. Therefore the complete first projected
coefficient is also zero. The remaining target is its second coefficient,
not a first derivative expected to be nonzero.

This fixes the target; it does not evaluate it. In particular, a nonzero
raw second coefficient is not a nonzero proper elliptic coefficient,
and that analytic coefficient still needs a leading-order comparison
with the chosen global regulator before it yields a finite logarithm.

For the symmetric oldspace coordinate, retain the unit factor 1/62
from tame-trace recovery. The saved series are traces, before this
cohomological projection and recovery factor.

## Run

From the repository root:

```sh
python research/bsd-localization/weight_reflection/check_reflection.py --check
```

`--write` explicitly regenerates the result and reduced fixture. Default
execution writes neither. These are exact arithmetic checks, not Lean
formalizations of the analytic-family arguments.
