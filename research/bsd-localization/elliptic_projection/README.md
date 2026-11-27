# Exact elliptic Hecke projector at level 389

This directory supplies a reproducible rational-arithmetic certificate for
projection onto the **complete two-dimensional** factor of

\[
E=389.a1:\quad y^2+y=x^3+x^2-2x
\]

in proper weight-two cohomology at level 389. It also gives a polynomial
in integral Hecke correspondences whose denominator loses at most one
5-adic digit on any Hecke-stable integral lattice.

It does not yet turn the traced overconvergent q-expansions into de Rham
coordinates. That reduction, its precision bound, and the identification
with the elliptic differential basis are separate operations.

## Certified result

Let `T2,T3` be the usual weight-two Hecke operators and set

\[
A=T_2+4T_3.
\]

There is a monic integer polynomial `q` of degree 32, with all 33
coefficients in [witness.json](witness.json), such that

\[
\boxed{P_E=\frac{q(A)}{q(-10)}},\qquad
q(-10)=4991964896182583587087694480,
\qquad v_5(q(-10))=1.
\]

The checker verifies this identity exactly on the entire 65-dimensional
relative modular-symbol space. Its image has dimension two, lies in the
64-dimensional cuspidal subspace, and satisfies

\[
T_2P_E=-2P_E,\quad T_3P_E=-2P_E,\quad T_5P_E=-3P_E.
\]

These three eigenvalues are independently counted on the stated elliptic
curve over the corresponding finite fields. The rational kernel of
`T2+2` has dimension exactly two, so no other characteristic-zero
cuspidal factor with that eigenvalue is left in the image. Modularity of
this conductor-389 curve identifies this image with its elliptic factor.

The projector is idempotent. Complex conjugation has a one-dimensional
plus and a one-dimensional minus eigenspace on its image. This is a
check that the full cohomology factor has been retained; it is not an
identification of those real eigenspaces with p-adic Frobenius slopes.

## Why the one-digit bound is representation-independent

The entries of the projector in the saved Manin lattice have least common
denominator 40. The upper-left entry is exactly `-1/40`, so this projector
is not integral on that lattice. The polynomial identity gives a stronger
portable bound than merely inspecting those entries.

If `L` is any integral lattice preserved by `T2` and `T3`, then `q(A)`
preserves `L`. Since `q(-10)=5*u` with `u` a 5-adic unit,

\[
P_E(L)\subseteq5^{-1}L.
\]

An input known modulo `5^(m+1)L` therefore gives a projected output known
modulo `5^m L`. This is an absolute-precision bound. It does not assert
that every projected input is integral. Nor does it include denominators
introduced by converting q-expansions to the chosen cohomology lattice
or by a later change to the elliptic differential basis.

Hecke correspondences are algebraic. Their action on proper Betti and
de Rham cohomology is compatible under comparison, so the same polynomial
identity defines the projector there. This transfers an identity of
operators, **not the numerical Manin basis**. In a dual cohomology basis
the homology matrices must be transposed. In the earlier crystalline
basis `omega=dx/(2y+1), eta=x*omega`, a separate comparison matrix is
required. This directory does not silently identify either of those
bases with the two columns in `E`.

The bound is useful after the tame trace: trace extraction and oldspace
recovery by `1/62` lose no 5-adic digits; this elliptic Hecke projection
has a certified worst-case loss of one. Proper overconvergent reduction
still needs its own denominator analysis.

## Exact construction and independent checks

[manin.py](manin.py) implements the prime-level weight-two Manin
presentation. It uses the 390 projective bottom-row classes
`(1:i)` and `(0:1)`, subject to the order-two and order-three Manin
relations. Sparse elimination gives 65 free coordinates. Every
presentation denominator is checked to be a 5-adic unit, and the
rational presentation is compared with an independent reduction modulo
five.

Continued fractions express rational cusp paths in these generators.
The Hecke action is constructed from its rational fractional-linear
cosets and is checked against **every** original Manin relation. For
`T2`, a separate four-matrix Manin formula gives exactly the same action.
The comparison also passes at levels 11, 23 and 37. The boundary action,
Hecke commutation and conjugation involution are checked explicitly.

The saved matrices `E,L` are respectively two independent right and
left `T2=-2` eigenvectors. Their pairing is

\[
L^tE=\begin{pmatrix}0&-10\\20&20\end{pmatrix},
\qquad
P_E=E(L^tE)^{-1}L^t.
\]

The checker recomputes the ambient matrices and verifies all the saved
eigenvector identities and ranks. It then evaluates `q(A)` by integer
Horner arithmetic and compares it entry-for-entry with `q(-10)*P_E`.
No floating point eigensolver or guessed numerical eigenvector is used.

A useful precision warning comes from the residual calculation:

| Eigenspace modulo five | Dimension |
|---|---:|
| `ker(T2+2)` | 7 |
| `ker(T2+2) intersect ker(T3+2)` | 2 |

Even though the joint residual eigenspace has the expected dimension,
the exact projector still has a factor of five in its denominator.
Residual dimensions alone would have missed this loss.

## Reproduction and scope

From `research/bsd-localization`:

```sh
python elliptic_projection/check_projector.py --check
```

SymPy 1.14.0 is the only external dependency. Default execution prints
the computed result without modifying files; `--write` explicitly
updates [result.json](result.json).

These are exact arithmetic certificates with a mathematical
interpretation through the standard modular-symbol and comparison
theorems. They are not additional Lean kernel-checked theorems.
A classical Sturm bound does not certify the overconvergent inputs,
and applying this finite matrix to arbitrary q-coefficients would not
be a valid de Rham reduction. No projected vector L-value, arithmetic
reciprocity comparison, or nonzero reflected logarithm is claimed here.

## Primary mathematical source

William Stein, *Modular Forms: A Computational Approach*, chapter
[Modular Forms of Weight 2](https://www.wstein.org/books/modform/modform/weight_two.html):
Theorem 3.4 (Hecke-equivariant pairing), Proposition 3.11 (continued
fractions), Theorem 3.13 (Manin presentation), and the four-matrix `T2`
formula in the Manin-symbol Hecke section. These supply the interpretation
of the independently implemented finite presentation and correspondences.
