# Independent review of the infinite Katz projection bridge

Date: 2026-11-27.

## Conclusion

The argument in ../projection_backend/INFINITE_KATZ_BRIDGE.md is valid
under its stated geometric provenance for the saved Katz head. The
operator blocks, exact eigenline existence, kernel precision, normalization
bootstrap and output error bounds all check. The proof does not infer an
infinite eigenline from a numerically zero determinant.

The pinned Sage construction gives a source-based justification of the
head provenance, at the ordinary level of trust in its modular-form
construction and exact arithmetic. The saved finite verifier alone does
not replay every higher-weight complement choice or every row operation.
These are different certification scopes, and should remain distinguished.

With that source-based provenance accepted, the analytic bounds do
preserve the reported actual CM coefficient balls:

\[
 a_2=\frac{418+150\xi+83\xi^2}{5}+O(5^3),\qquad
 b_2=\frac{14+27\xi+124\xi^2}{25}+O(5).
\]

They are coefficients in the specified classical stabilization basis
after the fixed Euler transfer. They are not an arithmetic regulator
comparison or a nonzero-localization theorem.

## 1. Material inspected

The review read the complete bridge and finite precision proof, the actual
finite projection result, the actual replay report, the CM norm argument,
and the following pinned Sage routines:

* random_new_basis_modp;
* complementary_spaces_modp and complementary_spaces;
* higher_level_katz_exp;
* ech_form.

The SHA-256 of the local Sage 10.10 source was independently recomputed:

    6292ef3c2e20c2456058fdac25ecb1576e9abdace4c47a3aae13b1469f58703a

It agrees with the source hash in the successful capsule. The custom
low-weight supplier, its guarded saturation and long-expansion
normalization were also inspected. The capsule records matrix precision
6, basis precision 8, pole cutoff 10, head dimension 1333 and q-depth
6830. Its coefficient-fit inverse guard is 1.

The primary analytic input was rechecked in Lauder,
[*Computations with classical and p-adic modular forms*](https://people.maths.ox.ac.uk/lauder/papers/LMSLauderMFJune10.pdf),
Section 2.1 and equations (2.2)--(2.3). In particular its radius hypothesis
is strict; the proof below uses a coefficientwise limit, rather than
applying the theorem at the excluded endpoint.

## 2. Uniform operator bounds and the completion

For the scaled Katz basis
\(e_{i,t}=5^{\lfloor i/6\rfloor}w_{i,t}/E_4^i\), its radius-r norm
valuation is at least \(-5/6\) for every \(0<r<1/6\).
Applying \(5U M_r\subset M_{5r}\) and taking the coefficientwise limit
gives the output-column bound

\[
 g(j)=\left\lceil\frac{5j-11}{6}\right\rceil-\left\lfloor\frac j6\right\rfloor
     =4k+(-1,-1,0,1,2,3)_s,\quad j=6k+s.
\]

Thus \(g(j)\ge7\) for every tail pole \(j\ge11\), and it tends to
infinity. The separate q-integrality bound is

\[
 v(U_{ij})\ge\lfloor i/6\rfloor-\lfloor j/6\rfloor.
\]

Together these prove the entire scaled U matrix integral: use the latter
bound for \(j=0,1\), and \(g(j)\ge0\) for \(j\ge2\).
They also prove that the tail-to-head block C is integral and that B,D
are divisible by \(5^7\), with the row-action convention of the capsule.

These are adequate operator bounds on the c0 completion. Output tails
tend to zero uniformly on its unit ball, so U is the norm limit of its
finite-output truncations. On the bounded dual, every row sum against
the high-output columns converges; the same \(5^7\) bound controls D.
Consequently its Neumann inverse at a slope-0 or slope-1 eigenvalue is
valid both on the tail and on the continuous dual.

A GL(Z5) change of the finite head preserves all these estimates. It
does not need to preserve individual pole levels inside the head.

## 3. Identifying the finite operator and its true eigenfunctional

The omitted q-expansion of U applied to a head basis vector is divisible
by \(5^8\): its tail coordinates have valuation at least 7 and every
tail basis q-series is divisible by 5. Therefore the actual head matrix
and the saved integral fit differ by \(O(5^7)\), by the inverse guard 1.

This assertion can be made without a hidden integrality assumption on
the unknown head matrix. Write the exact residual using the integral
saved fit:

    E_exact * (A_exact - A_fit)
       = U(E_exact) - E_exact*A_fit - omitted_tail.

Every term on the right is controlled to eight digits. The exact lift
of the certified evaluation minor has inverse norm at most 5.

Let \(h=v(\lambda)\in\{0,1\}\). The Schur matrix

\[
 S_\lambda=A+B(\lambda-D)^{-1}C
\]

is congruent to the saved six-digit matrix modulo \(5^6\). Exact
classical stabilizations provide a nonzero left eigenrow; their radius
can be enlarged into this completion using their exact U eigen-equation.
Its head cannot be zero, since D has no eigenvalue of valuation less
than 7. Hence \(S_\lambda-\lambda\) is actually singular.

The certified complementary minor is invertible, so its exact rank is
1332 and its right kernel is one-dimensional. The chosen normalization
coordinate cannot vanish in that kernel. Solving the complementary
equations with that coordinate equal to 1 gives an integral exact head
vector with precisions

\[
        K_\alpha=6-1=5,\qquad K_\beta=6-2=4.
\]

The tail vector
\(v=(\lambda-D)^{-1}Cu\) is bounded below in valuation by \(-h\).
It therefore defines an actual continuous dual eigenfunctional.
This supplies existence, uniqueness and boundedness, rather than
postulating them for the finite kernel.

## 4. Input and normalization errors

For the actual second CM coefficient, its scaled pole-coordinate bound is

\[
 t_i=\max\left(0,\left\lceil(20i-58)/25\right\rceil-4\right)
                  -\lfloor i/6\rfloor.
\]

The global minimum is -1, at i=6,7, and the minimum for i>=11 is 2.
The infinite assertions follow from
\(t_{i+30}=t_i+19\) once the positive linear branch begins, together with
one initial finite block. These integer calculations were independently
checked with exact rational ceiling arithmetic.

The program fits Y=UQ. Its true tail has valuation at least 6, hence its
q-tail has valuation at least 7. The fitted true head is therefore known
to 6 digits after the evaluation guard. Its measured valuation 0 is
then a fact about the true head, not just the saved residues.

The normalization bootstrap correctly allows an initially nonintegral
classical head. For \(R=Uf_\lambda\), put \(\nu=v(R_H)\). The left
eigen-equation gives

\[
 R_T=R_HB(\lambda-D)^{-1},\qquad
 v(R_H-\widehat r)\ge\min(7,\nu+7-h).
\]

If \(\nu<0\), the integral fitted row \(\widehat r\) makes the left
valuation equal to \(\nu\), contradicting the strict improvement on
the right. Thus \(\nu\ge0\). The resulting error at least 6 identifies
the measured head valuations \(\rho_\alpha=0,\rho_\beta=1\).
Substitution then improves both tail valuations to at least 7 and
both head errors to at least 7. This is a valid bootstrap; it does not
assume that q-integrality already supplies the stronger radius norm.

For the full pairings, including both tails, the exact lower precisions are:

| Direction | Head kernel K | Numerator precision | Denominator precision | Denominator valuation | Numerator valuation |
|---|---:|---:|---:|---:|---:|
| alpha | 5 | 5 | 5 | 1 | 0 |
| beta | 4 | 4 | 5 | 2 | 1 |

The denominator precision exceeds its valuation, so both normalizations
are nonzero for the actual infinite functional. The quotient error
formula gives absolute precisions 3 and 2, respectively. The Euler
transfer preserves the former and costs one digit in the latter,
leaving exactly the balls stated above.

The scaled ratio consequently remains

\[
       5b_2/a_2=109+75\xi+106\xi^2\pmod{125}.
\]

No fourth digit follows from these balls. Exact vanishing of lower
weight orders remains supplied by the separate analytic identity,
rather than by their numerically zero balls.

## 5. Why the functional is the desired analytic projection

The nonzero pairing with the exact classical fixture also removes a
possible Jordan-chain problem: a dual eigenfunctional annihilates the
image of \(U-\lambda\), so an eigenvector having nonzero pairing cannot
be the bottom of a nontrivial Jordan chain. Together with uniqueness
of the eigenline, this identifies the normalized functional as the
actual lambda-spectral coefficient.

For its proper de Rham interpretation, use the already specified
U-equivariant cohomological map and the nonzero stabilization classes.
Its continuity can also be seen from the existing integral pole
reduction: the loss is at most logarithmic in the pole index, while
the factor \(5^{\lfloor i/6\rfloor}\) grows linearly in valuation.
Thus the cohomological coefficient functional is a continuous right
U-eigenfunctional. The uniqueness just proved identifies it with the
normalized bounded dual. The saved stabilization-to-de-Rham calibration
fixes the chosen elliptic basis and differential scaling.

This is an analytic/cohomological comparison. It does not compare the
analytic family with a global diagonal class or a full Perrin--Riou
regulator.

## 6. Source-based provenance versus artifact-only replay

The inspected Sage construction selects literal products of integral
low-weight modular forms. At each stage it accepts a new row only
after a rank increase modulo 5 and reaches the full classical dimension.
Since \(E_4\equiv1\pmod5\), the previously selected lower-weight rows
are precisely the required old subspace after multiplication by E4.
Independence modulo 5, the q-expansion principle and Nakayama give
saturated integral complements. The reconstructed high-weight products
are then scaled by exactly \(5^{\lfloor i/6\rfloor}/E_4^i\).

In ech_form, the pivot has minimum valuation among eligible rows.
The routine divides only its unit part and then subtracts integral
multiples; it does not divide a row by a positive power of 5. Row
swaps and all these operations lift to GL(Z5). This verifies the
needed geometric invariant of the pinned algorithm.

The low-weight supplier's genuine divisions by 5 occur separately, with
guard digits and a full-Sturm divisibility justification. They are not
being incorrectly described as unimodular echelon operations.

The finite receipts do not contain every higher-weight product choice
and transformation matrix. Full independent replay of that provenance
would require those additional witnesses. This limitation does not
introduce an unknown analytic tail constant, but it remains a limitation
of the artifact-only certificate. No new Lean theorem is asserted here.
