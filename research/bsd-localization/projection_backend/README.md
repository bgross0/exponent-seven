# A finite two-slope projection certificate, with measured precision loss

Date: 2026-11-27. Pilot E389.a1, K=Q(sqrt(-71)), p=5.

This directory implements the operation after `de_rham_strategy/backend_probe.py`:
fit the scaled U5 input in the returned Katz q-basis, isolate both elliptic
dual eigenfunctionals, normalize against U5(f_alpha) and U5(f_beta), and
convert the result into the saved omega,eta basis. It uses Python and NumPy;
the Sage capsule is an input, not a runtime dependency.

**The code certifies finite modular linear algebra.** A finite q-fit does
not prove an integral Katz expansion or control the infinite operator.
Those analytic hypotheses are explicitly separate. A successful run here
must not be called a certified CM de Rham value until those hypotheses have
been supplied. The arithmetic regulator comparison is a further theorem.

## 1. Running the next calculation

From the repository root, after the Katz geometry capsule exists:

```sh
python research/bsd-localization/projection_backend/project_capsule.py \
  --katz de-rham-katz6/katz-capsule.json.gz \
  --output finite-projection-output
```

The default trace is the saved q6825/twelve-digit cubic representative.
The adapter checks its dimensions and precision, and rechecks the whole
finite identity U(E)=A E rather than trusting the capsule's boolean flag.
It fits eleven columns together: the three scalar coefficients of each
of the three weight orders, plus U(f_alpha) and U(f_beta).

The outputs are:

* `finite-projection-certificate.json.gz`: coordinate vectors, scaled
  inverse-minor witnesses, primitive dual vectors, source hashes, and
  precision-bearing output balls.
* `projection-result.json`: measured guards, both slope coefficients,
  omega,eta coordinates, fixture checks, and predicted lower-zero diagnostics.

The symmetric elliptic oldspace coordinate is also reported after division
by62. This is not a silent choice of the global test vector.

Verification does not rerun the elimination algorithm:

```sh
python research/bsd-localization/projection_backend/project_capsule.py \
  --katz de-rham-katz6/katz-capsule.json.gz \
  --verify finite-projection-output/finite-projection-certificate.json.gz
```

Instead it checks the source hashes, all finite fit equations, the two-sided
scaled inverse identities, the dual eigen-equations, the classical fixture
eigen-equations, every normalization bound, and the saved outputs.

An optional `--scale b` multiplies **both** the input and all normalization
rows by5^b before fitting. This can clear denominators, and the common scale
cancels in the quotient. Its cost is retained in the precision arithmetic.
The verifier must receive the same scale. A scale that destroys all
normalization precision is rejected.

The standard-library/NumPy regression is:

```sh
python research/bsd-localization/projection_backend/check_projection.py --check
```

This regression has run successfully. It includes the actual saved
crystalline operator of the pilot; it does not supply a full Katz capsule.
The tested dependency is NumPy2.3.5.

## 2. The finite inverse-minor certificate

Let D be a square matrix over Z_p known modulo p^M. A witness consists of an
integral matrix X and an integer c<M satisfying

    D X = X D = p^c I mod p^M,

with at least one unit entry in X. For any exact integral lift D_tilde of D,

    D_tilde X / p^c = I + p^(M-c) R.

The right side is invertible over Z_p by the geometric series. Therefore
D_tilde is invertible over Q_p and

    v_p(D_tilde^(-1)) >= -c.

The unit entry of X makes c sharp for this minor. This is the norm of its
inverse, equivalently its largest local Smith exponent. The verifier needs
only the two product identities and the unit-entry check; it need not trust
an asserted Smith decomposition.

### Coordinate fits

Suppose E x=b is an overdetermined finite system, and the certificate gives
an integral solution modulo p^M together with a full-column-rank pivot
minor with guard c_fit. Any compatible exact **integral** solution has

    x_exact = x_certificate mod p^(M-c_fit).

All extra rows are checked. Their consistency is not inferred from a square
subset. Existence of an exact solution coming from an infinite modular
form is a separate input; the certificate only proves finite consistency
and the stated uniqueness bound if a compatible integral solution exists.

### Dual eigenfunctionals

Use the row-operator convention of the Sage capsule:

    U(e_i)=sum_j A[i,j]e_j,       row coefficients c -> c A.

Thus a scalar projection functional is a **right** eigenvector w of A.
Put B=A-lambda I. The certificate gives:

1. A primitive integral w with w_j=1 and B w=0 modulo p^M.
2. An (n-1)-by-(n-1) minor using all columns except j, with guard c<M.

If a compatible exact B_tilde has a nonzero kernel, the minor shows that
its kernel is one-dimensional. Its vector normalized by w_tilde_j=1 is
integral and satisfies

    w_tilde = w mod p^(M-c).

Indeed, apply the inverse-minor bound to the residual B_tilde w, which is
divisible by p^M. Existence of the exact eigenline is not inferred from a
determinant that merely vanishes modulo p^M.

The producer uses minimum-valuation Gaussian elimination over Z/p^M.
Unimodular row operations and column swaps give an upper echelon matrix.
Dividing its ith row by its pivot p^d_i leaves a unit upper-triangular
matrix. This constructs the scaled inverse witness with c=max(d_i).

If more than one direction remains invisible at the available precision,
the program stops. That can mean repeated eigenvalues or unresolved close
eigenpackets. Additional tame-Hecke conditions or more justified precision
are then needed. The code never chooses one vector arbitrarily and calls
it the elliptic projection.

## 3. Correct normalization precision

This calculation improves the earlier informal M-c-v rule by stating its
extra requirements explicitly.

Let w be primitive and known to absolute precision K=M-c. Let h be the
input coordinate row and r the normalization row. Suppose they are known
to absolute precisions K_h and K_r, and put

    eta = min_i v_p(h_i),       rho = min_i v_p(r_i).

Certified lower bounds for eta and rho suffice. Then

    N=h w is known modulo p^a,  a=min(K_h, K+eta),
    D=r w is known modulo p^b,  b=min(K_r, K+rho).

If v=v_p(D)<b and t=min(v_p(N),a), the quotient has absolute precision

    L = min(a-v, b+t-2v).                              (1)

This follows directly by subtracting N/D and (N+delta_N)/(D+delta_D).
The terms have valuations at least a-v and b+t-2v; the remaining
denominator is a unit after removing p^v. The code reports a p-adic ball,
including cases where the value is not integral.

The common slogan M-c-v follows, for example, when a=b=K and t>=v,
so that the projected coefficient is integral. It also follows in some
nonintegral cases when the normalization row carries a common p^v factor
and is known more accurately, giving b>=K+v. These are data to measure,
not automatic consequences of alpha-beta being a unit.

For the entire normalized functional w/(r w), a primitive numerator
coordinate is a unit. If the denominator is known only to precision K,
that coordinate may be known only to K-2v. A nonunit normalization can
therefore cost twice its valuation without further structure.

### Sharp counterexample to the unconditional rule

Set p=5, M=8, lambda=3, and

    A-lambda I = [[0,1],[0,25]],
    w=(1,0)^T,       r=(-25,1),       h=(1,0).

The primitive kernel guard is c=0, while r w=-25 has valuation v=2 and
h w=1 is a unit. The quotient is -1/25. Put epsilon=5^M and replace B by

    B_tilde=[[-epsilon,1],[-25*epsilon,25]].

This is the same matrix modulo5^M, its exact kernel is generated by
(1,epsilon)^T, and the **same exact row r** is a left zero eigenvector.
The new quotient is 1/(-25+epsilon). Their difference has valuation

    M-4=4,

whereas the unconditional M-c-v slogan would promise six digits.
Formula(1) correctly promises four. The checker verifies this using exact
rational numbers, as well as a separate sharp M-c kernel-direction example.

## 4. What was actually checked here

The actual crystalline operator and its saved seven-digit calibration give
a genuine arithmetic regression. Starting with the known elliptic class

    H=7[f_alpha]+11[f_beta],

the procedure applies U, extracts both dual functionals, and normalizes
against U(f_alpha), U(f_beta). It recovers7 to seven absolute digits and11
to six, then converts back to omega,eta to six digits. This checks the
row/column convention and both slope labels against the existing pilot
operator. H is a deliberately known elliptic combination, not the CM jet.

A second end-to-end regression computes actual coefficients of the curve
through q39 by finite-field point counts and the Hecke recurrences. It
builds the two p-stabilizations, feeds a deliberately restricted
two-dimensional geometry model through the same capsule adapter, fits all
eleven input columns, and recovers three chosen coefficient pairs. Both
lower weight orders are zero in that constructed input. This exercises
the actual capsule interface without presenting it as the full Katz
geometry or the actual CM series.

The alternative ordinary-product representative has its own explicit mode:

```sh
python research/bsd-localization/projection_backend/project_capsule.py \
  --katz de-rham-katz6/katz-capsule.json.gz \
  --input-kind undepleted-product \
  --output undepleted-projection-output
```

This selects `cm_product_transfer/cubic-product-6825-12.json.gz`. The first
reported stabilization and omega,eta coordinates describe Qplus. The
`target_depleted_*` fields separately apply the fixed cubic operator R(U)
from that directory to recover the original depleted H projection. The
program recomputes5R(alpha),5R(beta) at eight digits and checks them against
the independently saved Euler-transfer witness. Cubic multiplication is
performed on precision-bearing balls; division by5 is recorded after that
multiplication. Consequently the ordinary multiplier is integral and the
critical multiplier can cost one extra digit. Their coefficient precision
is accounted for as well. The symmetric oldspace coordinate always refers
to the target depleted H, after division by62.

The end-to-end elliptic-subspace regression exercises this second input
kind too, checking all six cubic target coefficients against direct
multiplication by the saved5R eigenvalues. The two raw q-series are never
declared equal. Verification of this mode requires the same
`--input-kind undepleted-product` argument and records the transfer-witness
hash in the source manifest.

Further checks include rectangular coordinate fits with nonunit pivots,
unimodularly scrambled kernels of dimensions2,3,5,8, the two sharp precision
examples, and eight rejection cases: corrupted inverses, kernels, and
coordinates; inconsistent extra equations; repeated eigenvalues;
congruences beyond available precision; zero normalization; and an integer
overflow contract violation.

All array operations use signed integers. For modular matrix products the
inner dimension is blocked so every accumulator is strictly below2^63.
For elementary row operations the modulus must satisfy modulus^2<2^62.
This covers the planned six-digit matrix/eight-digit basis calculation.
Higher precisions that violate this bound are rejected, not computed with
floating-point arithmetic or silently overflowing integers.

## 5. Remaining hypotheses and interpretation

The following implications are deliberately separate:

    finite q-fit + inverse witnesses
       -> conditional finite projection balls;

    integral input-tail bound + infinite-operator comparison
       -> actual analytic de Rham coordinates;

    explicit arithmetic regulator comparison
       -> information about the reflected global class.

The lower projected weight coefficients are predicted to vanish by the
preceding analytic proof. This adapter records their finite diagnostics.
A failure can reveal insufficient truncation or a convention error; it
does not refute that theorem before the analytic hypotheses are established.
The higher-slope component is retained throughout.

The local linear-algebra proofs in this directory are elementary and
self-contained. The cohomological interpretation and higher-slope method
are sourced in `../de_rham_strategy/SOURCES.md`. No new Lean theorem or
general BSD statement is asserted here.
