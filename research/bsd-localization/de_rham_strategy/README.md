# A concrete route from the traced jet to elliptic de Rham cohomology

Date: 2026-11-27. Pilot: E389.a1, K=Q(sqrt(-71)), p=5.

**No CM jet has yet been converted to proper de Rham coordinates here.**
The new results are an exact two-slope coordinate calibration, a finite
195-dimensional model for the open cohomology, and a targeted cup-product
formula that can extract the elliptic factor using a classical weight-12
trace. Two Sage backend gates are supplied as executable handoffs; neither
was run in this environment, which has no Sage or Magma installation.

The most useful next job is to build the backend geometry once. It is shared
by every input coefficient and every weight jet. The existing trace input
through q^6825 at twelve 5-adic digits is large enough for the standard
six-digit Katz matrix gate. Six matrix digits do **not** automatically mean
six certified digits of the final de Rham vector.

## 1. What is already executable

From the repository root:

```sh
python research/bsd-localization/de_rham_strategy/check_strategy.py --check
python research/bsd-localization/de_rham_strategy/backend_probe.py --mode plan --digits 6
```

The first checks the saved Frobenius calibration, both slope labels,
coordinate inversion, the classical dimension formulas, and the cup/trace
constant. Its deterministic result is `result.json`.

On a node which already has Sage, run one bounded geometry job:

```sh
timeout 45m sage -python research/bsd-localization/de_rham_strategy/backend_probe.py --mode katz --digits 6 --output de-rham-katz6
```

This calls the documented Sage function

```python
higher_level_UpGj(5, 389, [2], 6, True, 6, extra_data=True)
```

and saves the actual finite U5 block, its Katz q-expansion basis, version
and source hashes, and both classical p-stabilizations of f. It checks
**every** available coefficient of U5(E)=A E. It never applies an ordinary
projector. The matrix convention is rows: U5(e_i)=sum_j A[i,j]e_j, so a
form's coordinate row acts by c -> cA. A projection functional is therefore
a **right** eigenvector of this particular matrix. Transposing to the
column convention changes that terminology.

The script does not implement the subsequent Smith-kernel extraction or
assert a tail bound. It intentionally produces a reviewable matrix gate
before those operations are attempted. The operator and q-basis must be
kept together; a characteristic polynomial alone is insufficient.

An alternate, exact, smaller geometry gate is:

```sh
timeout 45m sage -python research/bsd-localization/de_rham_strategy/backend_probe.py --mode pole-core --output de-rham-pole-core
```

It constructs the weight-four and weight-ten spaces, expresses all
derivatives E4 theta(b)-b theta(E4) in the latter, and checks their rank is
98. Its output is the exact 293-to-195 quotient map. It does not pretend
that the first 390 q-coefficients of our overconvergent input determine its
image in that quotient. Those coefficients certify only the **classical
numerator identities used to construct the quotient**.

Both commands write progress to stdout. A timeout means an unfinished
backend job, not a mathematical failure. The code has passed Python syntax
checks; the Sage-dependent branches still need their first real execution.
No package installation, service configuration, or network request is made.

## 2. A calibrated conversion retaining both Frobenius slopes

Use the existing basis omega=dx/(2y+1), eta=x omega. In the normalization
that identifies the modular differential f dq/q with omega, geometric
Frobenius satisfies

\[
 F\omega=5V_5f\,dq/q,
 \quad f_\alpha=f-\beta V_5f,
 \quad f_\beta=f-\alpha V_5f,
 \quad\alpha+\beta=-3,\quad\alpha\beta=5.
\]

Consequently

\[
 [f_\alpha]=\omega-\beta(F\omega/5),\qquad
 [f_\beta]=\omega-\alpha(F\omega/5).                 \tag{1}
\]

The source Frobenius matrix is known modulo 5^8, and its first column is
divisible by 5. Thus F omega/5 is known modulo 5^7. Modulo 78125:

\[
 C=\begin{pmatrix}70116&22803\\8795&966\end{pmatrix},\qquad
 C^{-1}=\begin{pmatrix}61021&17007\\17105&28421\end{pmatrix}.       \tag{2}
\]

The columns of C are the two classes in (1). Its determinant is 70296,
a 5-adic unit. Applying C introduces no further digit loss at the stated
seven-digit precision. The checker verifies

\[
 UC=C\operatorname{diag}(\alpha,\beta),\qquad
 FC=C\operatorname{diag}(\beta,\alpha),\qquad U=5F^{-1}=-F-3I.
\]

The U and F slope labels are interchanged. Confusing them would interchange
the two de Rham directions. Equation (1) specifies a normalized elliptic
factor; an actual modular-parametrization pushforward carries its own
degree/differential scaling. No Manin constant is silently assumed.

## 3. The Katz route: a precise next contract

Lauder's public code and the maintained Sage implementation construct the
needed matrix. Darmon--Lauder explicitly cite the last sentence of
Loeffler--Skinner--Zerbes Section 6.3 for higher-slope projection. That
sentence uses the transpose-kernel to obtain a projection functional;
the preceding Smith-form calculation quantifies its precision loss.
See the primary-source ledger below.

For the six-digit gate the exact parameters are:

| Parameter | Value |
|---|---:|
| Weight, level, prime | 2, 389, 5 |
| Katz cutoff n | 10 |
| Highest auxiliary classical weight | 42 |
| Finite matrix dimension | 1333 |
| Classical Sturm bound used for this basis | 1365 |
| Basis working precision | 8 digits |
| q-expansion precision | O(q^6825) |

The numerical path after the matrix gate is specific:

1. Express **U5(H)**, for the chosen traced quadratic weight coefficient H,
   in the returned Katz basis. First applying U5 improves the radius.
   Record every pivot valuation and verify the reconstructed q-expansion.
2. Find the dual eigencovectors for alpha and beta. For each, measure the
   largest nonzero Smith exponent of A-lambda. If the target is not a
   simple isolated packet, add actual tame-Hecke conditions on the
   controlled finite space; do not assume isolation from a small residual
   eigenspace.
3. Normalize against the coordinate row of U5(f_lambda). Evaluating the
   same functional on U5(H) and dividing by this normalization recovers
   the coefficient of f_lambda in H. This records the critical-slope
   division instead of hiding it. The normalization can itself lose digits.
4. Verify the two fixtures project to (1,0) and (0,1), check stability at
   the next justified cutoff/precision, and apply (2). Stability is a
   diagnostic; the final certificate also needs the tail bound.

For a finite matrix known modulo 5^M with one-dimensional target kernel,
let c be the largest nonzero Smith exponent. The kernel direction is
determined modulo 5^(M-c). If its normalization has valuation v, the
normalized functional has at most M-c-v absolute digits. This is the
elementary-divisor mechanism behind the LSZ method, expressed in the
row-operator convention used by Sage. It is not legitimate to set c=0
merely because the elliptic roots differ by a unit: other overconvergent
eigenpackets may be congruent to either root.

The geometry matrices have rational/5-adic coefficients. They can act on
the three coefficient columns in the cubic fixed field identified by
`../analytic_target_audit/`; an extension-field matrix need not be built.
The comparison with the reflected global class remains separate even
after a vector has been computed.

### The integral-radius gap is explicit

There are two independent limitations in the cited numerical method.
Lauder's Note 2.2(3) points out the assumption of an integral matrix
solution; our finite residual check tests the produced matrix identity.
His Note 2.3(1) separately distinguishes analytic overconvergence of a
Rankin input from the integral growth estimate required for its advertised
precision. The latter is not established by a finite q-expansion fit.

The explanation in Section 2.2.2 also matters: modulo 5^m the infinite
matrix has a nonzero **infinite-by-finite strip**, not automatically just
a finite square block. The first U5 application and an integral growth
bound justify the finite input vector. The beta component then needs its
nonunit eigenvalue accounted for when undoing U5.

For this pilot, the exact CM identity

\[
 d^{-s}g_s^{[5]}=h_{-s}^{[5]}
\]

turns the input into a product of ordinary CM-family sections of
complementary weights. That removes the need to estimate a general
inverse-Bol operator. What is still required is a uniform integral norm
bound for these ordinary-family sections and their two weight jets on a
specified strict neighborhood, including the finite V5 operations.
An ordinary unit eigenvalue and integral q-coefficients alone have not
been converted here into that quantitative bound. The correct remaining
norm problem is now much more special, but it is not declared solved.

## 4. A 195-dimensional algebraic core

Let X=X0(389), let C be its two cusps, and let D be the zero divisor of
the level-one E4 viewed on X. At p=5 the reduction of E4 is the Hasse
invariant. The divisor D consists of the supersingular lifts above j=0.
There are 130 geometric points: the 390 cyclic 389-subgroups of a
j=0 elliptic curve form free orbits of size three under its automorphisms
modulo sign. Freeness uses 389=2 mod3. At 5 this divisor is étale, since
the prime-to-5 level structures on the good CM curve are étale and the
automorphism orders are prime to 5.

Here g(X)=32, deg D=130, and deg C=2. The meromorphic differential model is

\[
 H^1_{\mathrm{dR}}(X\setminus(C\cup D))
 \simeq
 \frac{H^0(X,\Omega^1(C+2D))}{dH^0(X,\mathcal O(D))}
 =\frac{M_{10}/E_4^2}{d(M_4/E_4)}.                       \tag{3}
\]

To prove this finite presentation, replace the logarithmic de Rham complex
by O(D) -> Omega^1(C+2D). Locally at a point of D, the extra principal
part a/t maps to -a dt/t^2, an isomorphism. The complexes are therefore
quasi-isomorphic. Both coherent H^1 groups needed to compute
hypercohomology by global sections vanish. The derivative has constants
as its kernel. Riemann--Roch gives dimensions 293 and 99, hence

\[
 293-(99-1)=195=2\cdot32+132-1.
\]

The modular-form identifications in (3) use f dq/q. At the two elliptic
points of order two the usual transformation law gives the required
regularity; E4 is nonzero there. E4 is nonzero at the cusps as well.
Thus no extra punctures are silently added.

For higher poles, the exact reduction identity is

\[
 d\left(\frac b{E_4^{n-1}}\right)
 =\frac{E_4\theta b-(n-1)b\theta E_4}{E_4^n}\,\frac{dq}{q},
 \qquad b\in M_{4n-4}.                                  \tag{4}
\]

The numerator has weight 4n+2; its quasimodular terms cancel. For n>=3,
one can remove its highest poles and descend to n=2. The dimension of
the corresponding quotient stays 195.

### A logarithmic, rather than factorial, pole-reduction bound

For an integral differential with poles of order at most n along the
étale divisor D, the high principal parts integrate with denominators
2,3,...,n-1. Multiplication by

\[
 5^{\lfloor\log_5(n-1)\rfloor}
\]

makes all these primitives integral. Since H^1(O(D))=0, their principal
parts of orders >=2 lift to a global section of O((n-1)D), integrally.
Subtracting its differential leaves poles of order <=2. This proves an
existence bound of at most floor(log_5(n-1)) digits for reducing a single
integral pole-n term in this saturated model.

A particular linear solver must respect the integral model or certify its
extra denominators. Repeatedly dividing at each pole step and adding the
losses would give an unnecessarily weak factorial estimate. For an
infinite Katz expansion, this bound must be combined with the **actual
coefficient growth** to bound the discarded tail; it is not a substitute
for that growth estimate.

## 5. Removing residues without enumerating them

The exact filter is proved and checked separately in `../residue_filter/`.
All 130 supersingular points are defined over F25: for a trace-zero
supersingular E0/F5, its squared Frobenius is [-5], which fixes every
cyclic 389-subgroup. The two cusps are F5-rational. On the residue
quotient, F^2=25 and U=5F^-1 therefore satisfies U^2=1.

Consequently

\[
 Z=(U^2-1)H                                                   \tag{5}
\]

has a proper cohomology class. On the elliptic factor the filter is

\[
 U^2-1=3(F+I),\qquad\det(3(F+I))=27,
 \qquad[3(F+I)]^{-1}=-(F+2I)/9.                              \tag{6}
\]

Its inversion loses no 5-adic digits in an F-stable integral lattice.
Comparison with arbitrary q-expansion coordinates has a separate
denominator cost. Frobenius is the geometric Q5-linear operator
extended linearly to the external coefficient field;
one must not insert a second Frobenius action on those coefficients.

## 6. A targeted cup functional from one classical trace

This is a constructive alternative to computing a full Hecke matrix on
the 195-dimensional core. It applies **after** (5), or after independently
verifying that the represented class has zero residues.

Write a proper differential representative as

\[
 \eta_H=\frac{H_{10}}{E_4^2}\frac{dq}{q},\qquad
 H_{10}\in M_{10}(389),\qquad\omega_f=f\frac{dq}{q}.
\]

Choose the cup-order convention
\(\langle\eta_H,\omega_f\rangle=\sum_D\operatorname{Res}(F_H\omega_f)\),
where dF_H is the polar part of eta_H. Zero residues ensure no logarithmic
primitive terms are needed. The model allows only simple cusp poles, so
zero cusp residues make the representative regular there; the local sum
therefore needs only D. At E4=0 the Ramanujan identity gives
theta(E4)=-E6/3. Taking the local primitive of its double pole yields

\[
 \langle\eta_H,\omega_f\rangle
 =-9\sum_{P\in D}\left(\frac{H_{10}f}{E_6^2}\right)(P).        \tag{7}
\]

The map X0(389)->X(1) has ramification degree three at every point above
j=0. Hence the sum in (7) is one third of the level trace divided by E6^2
and evaluated at j=0. The product H10*f is cuspidal of weight twelve, so

\[
 \operatorname{Tr}_{389/1}(H_{10}f)=b(H_{10})\,\Delta.
\]

Using E4^3-E6^2=1728 Delta gives the explicit functional

\[
 \boxed{\langle\eta_H,\omega_f\rangle=b(H_{10})/576.}           \tag{8}
\]

This avoids 130 individual evaluations in extension fields. All divisions
in the displayed constant are 5-adic units. The formula has useful exact
regressions. If H10=E4^2*h2, it gives zero, as it should for two holomorphic
differentials. If H10=E4 theta(b4)-b4 theta(E4), it also gives zero: the
relevant remaining trace is a level-one weight-six cusp form, and that
space is zero. Thus the functional annihilates the relations in (3).

The trace is a **classical weight-twelve trace**, which is legitimate
because its argument is now the classical numerator H10*f. It is not a
classical substitute for tracing the original varying input. In the
determinant-normalized slash convention:

\[
 b(H_{10})=[q](H_{10}f)
 -389^{-5}[q^{389}]((H_{10}|_{10}W_{389})f),                    \tag{9}
\]

where f|W389=-f. Thus the finite interface needs H10 and its weight-ten
Fricke transform through q^389. **Sage's modular-symbol Atkin--Lehner
operator is 389^4 times this normalized weight-ten operator.** Its square
is 389^8; divide by 389^4 before using (9). The current backend does not
yet implement this Fricke/cup stage.

### Why two scalar cup evaluations recover both slopes

Let A0=<U omega_f,omega_f>=<omega_f,F omega_f>. This is nonzero for
the elliptic factor in the pilot. If Z is proper, put

\[
 y_0=\langle Z,\omega_f\rangle,\qquad
 y_1=\langle UZ,\omega_f\rangle.
\]

Frobenius scales the cup pairing by 5, so
<UZ,omega_f>=<Z,F omega_f>. Different Hecke factors are orthogonal.
Therefore, in the normalization [f]=omega,

\[
 P_E Z=\frac{y_1\omega-y_0F\omega}{A_0},\qquad
 \Pi_E(H)=-\frac{F+2I}{9}\frac{y_1\omega-y_0F\omega}{A_0}.    \tag{10}
\]

Here Pi_E on open cohomology means P_E composed with the canonical
Frobenius-split projection to proper cohomology.

The baseline A0 is obtained with the same cup routine on U f, fixing the
normalization and any common cup-order sign. It must be measured and its
valuation recorded; unlike 576 or 9, it is not declared a unit. The
oldspace coordinate additionally divides by 62, a unit already checked
in the tame-trace package. This method retains both slopes and can avoid
the degree-32 Hecke projector entirely. It still needs the controlled
pole reductions of Z, UZ, and the baseline. Equations (8)--(10) are a
mathematical construction, not a claim that those reductions were run.

## 7. The smallest defensible output and the remaining boundary

The first input target should be the second W coefficient of one embedding
of the both-depleted cross placement, averaged to the cubic coefficient
field as proved in `../analytic_target_audit/`. The full first projected
jet is forced to vanish; it is a regression rather than the primary
research target. A first output of a few certified 5-adic digits in **both**
coordinates is more useful than an ordinary-only value at high precision.

The two practical routes now have concrete contracts:

| Route | Backend already identified | Next missing operation | Precision gate |
|---|---|---|---|
| Katz plus dual eigencovectors | Public Sage/Lauder U5 matrix construction | Fit U(input); isolate and normalize both dual eigenvectors | Integral input growth, Smith guard, normalization valuation |
| Finite pole core plus cup | Exact weight4/weight10 quotient; formulas (4),(8)--(10) | Controlled Katz-to-pole reduction and classical Fricke functional | Coefficient tail, saturated pole reduction, baseline valuation |

The supplied code executes the first geometry gate for either route. A
projector acting on a finite proper cohomology space cannot simply be
applied to 128 raw q-coefficients. Nor does a nonzero coefficient of a
trace imply a nonzero elliptic projection. Once the vector is computed,
its identification with the complementary regulator of the reflected
global class will still require the separate explicit reciprocity
comparison. None of these implementation or arithmetic boundaries is
renamed as a proved result here.
