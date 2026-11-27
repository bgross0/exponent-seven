# An undepleted cubic input with a fixed elliptic Euler correction

This route keeps the coefficient field cubic while replacing the depleted
inverse-Bol product by a product of two ordinary CM families. The input
norm problem is simpler, and the correction on the elliptic factor is an
explicit constant operator. It retains both Frobenius directions.

The original input and this input have different raw q-series. The
identities below concern their proper elliptic projections.

## 1. The ordinary product

Write h_s for the CM family with inverse class character, with
W=6^s-1. For the embedding omega=2 modulo5, its ordinary eigenvalue has
constant term zeta^5. Consequently

    c=alpha_h(-s)*alpha_h(s)=zeta^3

is independent of s. Set

    Q_s=h_{-s}*V389(h_s),
    A_s=d^{-s}(g_s^[5])*V389(h_s).

The CM identity d^{-s}(g_s^[5])=h_{-s}^[5] gives

    U5(A_s)=(U5-c)Q_s.

The proof uses U(F*V5(G))=U(F)*G, not an estimate for an inverse-Bol
operator. The [tail note](../cm_tail_bound/README.md) records the family
identity and its finite q-series checks. Both families have the same
tame-Fricke71-plus symmetry, so their trace is Q+U71(Q), respectively
A+U71(A), and the identity commutes with trace.

Let P be the proper E projection of Q, and H that of A, using the same
oldspace normalization (division by62). On E, U=5F^-1 is invertible, hence

\[
 H=(I-cU^{-1})P.
\]

The prior [analytic audit](../analytic_target_audit/README.md) proves that
H is fixed by sigma:zeta->zeta^-1, and that replacing A by its doubly
depleted version leaves H unchanged.

## 2. Average before converting, retaining the cubic field

Set tau=c+c^-1=1-xi-xi^2, with xi=zeta+zeta^-1. Let

    Qplus=(Q+sigma(Q))/2.

Since H is sigma-fixed and the geometric U acts linearly on external
coefficients,

\[
 \Pi_E(Qplus)=\frac12\left(\frac{U}{U-c}+
                              \frac{U}{U-c^{-1}}\right)H.
\]

Therefore

\[
 \boxed{H=R(U)\Pi_E(Qplus),\qquad
 R(U)=\frac{U^2-\tau U+1}{U(U-\tau/2)}.}
\]

This operator is constant in W. It applies separately to all three weight
coefficients, and therefore to the quadratic coefficient of interest.
It also commutes with the tame trace and the residue filter. Averaging
Q alone and treating it as H would be incorrect; R is essential.

On E, U^2+3U+5=0, so

\[
 R(U)=\frac{2(6(\tau+1)U+5\tau^2+33\tau+58)}
             {5(\tau^2+6\tau+20)}.
\]

Its inverse is

\[
 R(U)^{-1}=\frac{5(\tau^2+3\tau+8)-6(\tau+1)U}
                 {2(5\tau^2+18\tau+25)}.
\]

The norms of the two cubic denominators are respectively6329 and8737,
both units at5. Thus R costs at most one digit on a U-stable integral
lattice (equivalently F-stable on E), while its inverse is integral. In
the calibrated elliptic slope basis, R is a unit on the U-ordinary
direction and has valuation -1 on the critical direction. This one-digit
worst-case loss is actual, not merely a denominator overestimate. Any
comparison between this lattice and the backend coordinates still needs
its own precision accounting.

## 3. Actual computed input

`cubic-product-6825-12.json.gz` contains Tr71(Qplus) through q6825,
including the coefficients of 1,W,W^2, modulo5^12. It uses the same cubic
basis as the previous depleted trace. No proper projection is computed.

The generator computes only the selected raw product indices needed by
the trace. It checks all174 overlapping cubic vector coefficients
against direct ordinary multiplication and weight reflection using the
pinned original CM-family archive. The detailed sizes, timings, hashes,
and counts are in `product-result.json`.

This alternative input is intended for the explicit norm/tail estimate in
`../cm_tail_bound/`. Its existence does not by itself establish the
analytic weight-trivialization hypothesis of that estimate.

## Reproduction

From the repository root:

```sh
python research/bsd-localization/cm_product_transfer/check_transfer.py --check
python research/bsd-localization/cm_product_transfer/product_trace.py --check
```

The first command verifies the rational-function identities, exact field
norms, and concrete elliptic matrices modulo5^8. It uses SymPy. The second
regenerates the actual trace with standard-library exact integer
arithmetic and compares its compressed bytes. Neither command asserts a
new global class, a nonzero reflected logarithm, or a Lean theorem.
