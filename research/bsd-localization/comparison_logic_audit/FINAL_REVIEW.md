# Independent review of the combined comparison argument

Date: 2026-11-27.

**Subsequent source correction.** This review recorded the logic of the
comparison using the then-stated DR22 projected-edge input. The later
[edge audit](../edge_specialization_audit/README.md) found that input's
raw-moment compatibility unproved. Its earlier acceptance below must
not be read as verification of that missing step. The current theorem
uses the separately proved and reviewed
[BSV replacement](../general_criterion/BSV_REPAIR.md). The rank-one,
full-regulator and finite-separation deductions reviewed here remain
valid with that replacement. Historical family names below identify
the earlier review, not an equality between BSV and DR22.

This review concerns the written deductions in
`global_class_comparison/README.md` and
`normalized_local_comparison/README.md`, together with the named frozen
geometric, analytic, theta, and numerical inputs. It is a mathematical
audit, not a new Lean verification of those inputs.

## Verdict

The combined argument supplies a valid route from the full analytic
leading line to nonzero finite localization of the **actual reflected
CH class**. The argument does not require literal historical equality
of the CH and DR constructions, a unit relating their families, or a
simple-determinant theorem for the relative Lubin--Tate regulator.

The accepted logical chain is:

1. Both full variable classes lie in the same relaxed/strict Selmer
   module after rational localization, and are non-torsion.
2. The cited Castella--Do rank-one result makes them proportional over
   the fraction field. Applying the same full regulator preserves their
   projective line, even if the proportionality scalar has a zero or pole.
3. At the negative-twist classical weights, the projected diagonal
   cycle's syntomic functional detects both elliptic logarithm
   coordinates. CH Theorem 3.4 then determines the already normalized
   and averaged regulator vector from both test eigenvectors.
4. The existing superflat wedge argument gives the actual common
   leading projective line, with the explicit matrix `K0`.
5. CH's own reflected construction and finite local condition give
   regulator order at least two. Its own theta reciprocity, with theta
   of exact order two, makes that order exactly two.
6. The base regulator image is annihilated by
   `lambda(v)=<v,zeta>`. The computed separation of `K0*A2` from that
   line is therefore a nonzero complementary quadratic coefficient.
7. The elementary divisibility implication proved in this directory's
   README makes the finite logarithm nonzero. A simple determinant is
   not an additional premise of this implication.

Each use of a geometric or arithmetic source remains visible in this
chain. This review does not turn the finite computation alone into an
arithmetic theorem.

## Checks with particular risk of logical error

### The strict local condition is full strictness

The relevant DR22 proposition puts the localization in the **image** of
cohomology of the rank-four balanced representation. In the same-CM-type
decomposition, its projection to the variable pair is full `V` in one
component and zero in the other. The composite map to the conjugate
component is already zero at the representation level. Consequently
specialization cannot produce an extra connecting class in that
component. This is stronger than merely vanishing in an ordinary
quotient and is sufficient for the generic relaxed/strict comparison.

### Away from five, augmentation localization is sufficient

For finite `v` away from five, local rational cohomology of `V5(E)`
vanishes in every degree: finite local five-primary torsion gives
`H0=0`, self-duality and local duality give `H2=0`, and the local Euler
characteristic gives `H1=0`. This includes the multiplicative prime
389. Standard perfect local Galois complexes and derived coefficient
base change then give acyclicity over the augmentation local ring by
derived Nakayama. Flat localization preserves the finite-set Selmer
kernels. No assertion about all integral tower quotients is needed.

The elementary proof of this derived Nakayama step and primary local
duality references are in the main README, Section 9.

### Non-torsion of the DR variable class can be proved directly

For the combined argument, the cleanest alternative in the global note
is the full syntomic specialization argument. The analytic vector is
not identically zero, so it is nonzero at all sufficiently small
nonzero points of the chosen sequence of classical weights. The fixed
weight matrices are invertible, and the geometric comparison scalar
is nonzero. The selected variable logarithm and hence the selected
variable class are nonzero. A torsion family maps to zero in the
torsion-free analytic regulator target, so this proves non-torsion.

This argument requires the already stated rational projected-edge
specialization proposition. It does not rely on extracting the
variable class from an ordinary scalar reciprocity formula whose
auxiliary contribution has not separately been identified.

### Both elliptic coordinates occur in the published syntomic formula

DR I Theorem 3.8 is a formula for any admissible elliptic test class,
not only the ordinary test vector. Its proof explicitly treats first
exponent zero and arbitrary first-factor de Rham class. At weights
`(2,k,k)` with `s=k-1>0`, the two holomorphic CM factors supply enough
filtration to allow both elliptic coordinates. Their tensor pairing
annihilates the mixed auxiliary components and detects the desired
variable component. The rational syntomic/étale comparison therefore
identifies the full vector on that component.

Primary source, Theorem 3.8 and its proof on printed pages 30 and 33:

https://www.math.mcgill.ca/darmon/pub/Articles/Research/62.DR-Diagonal1/paper.pdf

### Averaging is not silently replaced by scalar multiplication

CH Theorem 3.4 applies to the map normalized in its equation (3.9).
Applying that theorem to two independent elliptic Frobenius test
vectors determines the entire vector. Thus its averaging is already
included in the resulting matrix. A rank-one CM period change becomes
a common scalar only after the same CM component and tensor
identifications have been fixed. The countermodels in this directory
show why an arbitrary semilinear average would not have this property.

### Coordinate names must distinguish two chosen generators

The local Lubin--Tate generator normalized to character value `1+p`
gives the local inversion coordinate
`T_LT=(1+W)^(-1)-1`. The global norm-two anticyclotomic generator in
the existing coordinate audit instead gives
`T_a=(1+W)^delta-1`, with `delta=2 mod5`, subject to the fixed inverse
Artin convention. These are different choices of generator, not two
contradictory evaluations of the same coordinate. The leading-line
argument only needs the actual pullback to have nonzero tangent, and
both do. The formulas should keep the two labels separate.

## The exact numerical diagnostic and its limit

The independent checker reproduces the conditional normalization:

```
original scaled ratio        = (109,75,106) mod125
PR eigenvalue correction     = (79,1,91) mod125
corrected scaled ratio       = (21,0,0) mod125
scaled zeta ratio            = 86 mod125
difference                   = (60,0,0) mod125
valuation of the difference  = 1
```

The basis is `(1,xi,xi^2)` with `xi^3+xi^2-2*xi-1=0`. These data
prove separation at the stated precision once the arithmetic
identification is applied. The cancellation of the two nonconstant
cubic coordinates is an observed finite-precision fact. It is not
an exact rational-descent theorem for the full normalized regulator.

## Scope of acceptance

The audit accepts the implications above. It does not independently
formalize the published Euler-system, syntomic/étale, or projected-edge
arguments. It also does not derive a rational Mordell--Weil point from
a Selmer class or remove any divisible Tate--Shafarevich contribution.
Those are distinct conclusions and must be stated separately.

The combined `PILOT_LOCALIZATION_THEOREM.md` was also reviewed after
assembly. Its theorem follows from the input ledger. Two notation
corrections from that review are incorporated: the full normalized
regulator is allowed coefficients in a common complete overfield of
the finite character field, and the leading comparison matrix is
distinguished from an invalid substitution at `s=0` in the
fixed-integer-weight operator. These preserve the finite coefficient
field of the Selmer class and do not add a scalar-unit, determinant,
or order-matching assumption.

Reproduction of the independent arithmetic and algebraic checks:

```
python3 research/bsd-localization/comparison_logic_audit/check_logic.py --check
```

The checker passed after this review. Its scope is explicitly recorded
in `result.json`.
