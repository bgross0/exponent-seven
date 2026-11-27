# The Perrin--Riou correction to the fixed-weight syntomic vector

Date: 2026-11-27.

## Result and boundary

The full negative-twist interpolation operator in Castella--Hsieh (CH)
contributes a Frobenius factor which cancels the inverse Frobenius in
the fixed-weight syntomic calculation. Consequently, under the explicit
full-class and period comparison stated below, the analytic projective
comparison matrix is

\[
             M_{\rm PR}(W)=C(W)^{-1}N(F),
\]

whereas the matrix for a hypothetically analytic family of the raw
syntomic vectors is \(C(W)^{-1}F^{-1}N(F)\). They must not be identified.
The cancellation includes the factorial and the nonanalytic power of p;
it is performed at each integer weight, before any interpolation.

This note proves the operator algebra and an exact match of the CM
local unit after restriction to the unramified degree-seven field.
It **does not prove** that the actual full regulator of the reflected
diagonal family is the vector given by this comparison. In particular
it does not identify the arithmetic bad line. The independently
computed numerical projection is not used in this deduction.

## 1. The source convention and its full-vector meaning

The primary source is Castella--Hsieh,
[*On the nonvanishing of generalised Kato classes for elliptic curves
of rank 2*](https://web.math.ucsb.edu/~castella/Kato-print.pdf).
Use the following precise locations:

| Input | Source |
|---|---|
| Relative Lubin--Tate period and twists | Section 3.1, (3.2), printed p.12 |
| Kummer dual \(V^*=\operatorname{Hom}(V,L(1))\) | Section 3.2, printed p.13 |
| Vector-valued Coleman map | Definition 3.3, (3.7), printed p.15 |
| Frobenius-conjugate averaging, normalization and cyclotomic period \(t\) | (3.8)--(3.9), printed pp.15--16 |
| Negative-twist interpolation | Theorem 3.4, \(j<0,n=-1\), printed p.16 |
| Actual CM variable block and local extension | (2.4), printed p.11; Section 3.4, printed pp.17--18 |

Let \(V=V_pE\), identified with its Kummer dual by the Weil pairing.
Write \(F\) for geometric Frobenius on \(H^1_{\rm dR}(E)\).
After a fixed Tate trivialization the operator on \(D_{\rm cris}(V)\)
is \(\varphi=F/p\). The alternating pairing gives

\[
 \varphi^\dagger=p^{-1}\varphi^{-1},
 \qquad F^\dagger=pF^{-1}.                         \tag{1}
\]

The dagger is essential: CH's interpolation operator acts on the
**test vector**, rather than directly on the logarithm vector.

Definition 3.3 is a vector map before the pairing with \(\eta\).
Package the conjugate sum and the factors \(h_{\mathbf e}\sigma_0^i\)
in (3.9) into a vector \(\mathscr P(z)\), so that
\(\operatorname{Col}_\eta(z)=\langle\mathscr P(z),\eta\rangle\).
The eigenvector assumption preceding (3.9) specifies growth; taking
both independent elliptic eigenvectors and extending linearly retains
the full vector. This is the **averaged, normalized** CH map, not the
unaveraged vector of (3.7) with its normalization discarded.

Set \(s=k-1\ge1\), \(j=-s\), and use the unramified evaluation \(n=-1\)
of Theorem 3.4. Denote its logarithm, including the displayed
\(t^{-j}=t^s\) untwisting, by \(Z_s\). The theorem says

\[
 \langle\mathscr P(z)(\psi_{-s}),\eta\rangle
 =\frac{(-1)^{s+1}}{(s-1)!}
   \langle Z_s,A_{-s}(\varphi)\eta\rangle,
\quad
 A_j(\varphi)=
 (1-p^{j-1}\varphi^{-1})(1-p^{-j}\varphi)^{-1}.
                                                               \tag{2}
\]

All scalar extensions and finite unramified character components in
this formula must be the ones specified by CH. Replacing (3.9) by an
unweighted trace is not justified by (2).

There is no loss of a Hodge coordinate in this negative-twist case.
The filtration of \(V\) has jumps -1 and 0, and
\(\operatorname{Fil}^0D(V\langle s\rangle)
=\operatorname{Fil}^sD(V)=0\).
Thus the Bloch--Kato logarithm in (2) has the full two-dimensional
de Rham target. At \(j=0\), in contrast, CH uses the dual exponential
with its one-dimensional filtered image. These two cases cannot be
interchanged.

## 2. The adjoint operator

Taking the adjoint using (1) gives

\[
 A_j(\varphi)^\dagger
 =(1-p^j\varphi)(1-p^{-j-1}\varphi^{-1})^{-1}.
\]

In particular the operator acting on \(Z_s\) is

\[
 \begin{split}
 K_s(F)&=(1-p^{-s-1}F)(1-p^sF^{-1})^{-1}\\
 &=-p^{-s-1}F\,R_s(F),\\
 R_s(F)&=(1-p^{s+1}F^{-1})(1-p^sF^{-1})^{-1}.
 \end{split}                                                   \tag{3}
\]

Every denominator here is invertible at sufficiently large s. For
the ordinary elliptic pilot it is also nonzero at each integer s in
the stated range, by the elliptic Frobenius eigenvalues.
If s tends to infinity as an ordinary integer, then
\(R_s-I\) has valuation at least \(s-C\) in any fixed lattice.
Equation (3), not \(A_{-s}\) acting directly on \(Z_s\), is the needed
full-vector correction.

## 3. Combining it with the fixed-weight calculation

Retain the cusp-normalized cycle, tame test vectors and proper
projection of ../fixed_weight_syntomic/README.md. Let \(a,c\) be the
unit roots of \(g_k,h_k\), let \(\chi_g(p)\chi_h(p)=1\), and define

\[
\begin{split}
 N(F)&=1-F^2/p^2,\\
 C_s(F)&=(1-a\chi_h(p)F/(cp))
           (1-\chi_g(p)cF/(ap)),\\
 S_s(F)&=(1-p^{s+1}F^{-1}/(ac))
           (1-p^{s-1}F/(ac)),\\
 A_k&=\Pi[d^{-s}g_k^{[p]}h_k].
\end{split}                                                    \tag{4}
\]

Equation (10) of that note gives

\[
 \Pi\xi_k=
 -\epsilon_k(-1)^{s-1}(s-1)!\frac{p^{s+1}}{ac}
     S_s^{-1}C_s^{-1}F^{-1}N\,A_k.                 \tag{5}
\]

The unresolved global syntomic sign remains \(\epsilon_k\).
No weight-independent sign convention is needed.

**Additional arithmetic premise.** At the relevant classical
specializations, the full logarithm \(Z_s\) in (2), projected to the
actual variable CM block, is \(\lambda_s\Pi\xi_k\) for a nonzero scalar
\(\lambda_s\). Both vectors must use the same geometric F-coordinate,
CM rank-one period, cycle, test-vector map, Iwasawa involution and
weight-coordinate identification. This is a comparison of two
coordinates; agreement of one ordinary scalar pairing does not imply it.

Under this premise, substitution of (3) and (5) in (2) yields

\[
 \boxed{\quad
 \mathscr P(z)(\psi_{-s})
 =\frac{\lambda_s\epsilon_k}{ac}
   R_s S_s^{-1}C_s^{-1}N\,A_k.
 \quad}                                                       \tag{6}
\]

Here the parity factors multiply to 1, the factorials cancel,
and \(-p^{-s-1}F\) cancels \(-p^{s+1}F^{-1}\).
This is exact algebra at the fixed weight. There is no substitution
\(s=0\) into a factorial or into the nonanalytic function \(p^s\).

Suppose additionally that the actual averaged PR vector, pulled back
by its correct character map, and \(A(W)\) are analytic on the same
weight disk, \(W=(1+p)^s-1\). Suppose (6) holds along
\(s_n=2(p-1)p^n\). The superflat-wedge proof in
../fixed_weight_syntomic/PROJECTIVE_INTERPOLATION.md then applies
with both \(R_{s_n}-I\) and \(S_{s_n}-I\) of valuation at least
\(s_n-C\). It proves the conditional germ identity

\[
 \boxed{\quad
 (C(W)N(F)^{-1}\mathscr P(W))\wedge A(W)=0.
 \quad}                                                       \tag{7}
\]

For completeness, a nonzero analytic wedge of order m would have
valuation \(m(n+1)+O(1)\) at \(W_n\), whereas the exact classical
identities force valuation at least \((p-1)p^n-O(1)\).
This contradiction proves (7) without a bound on \(\lambda_{s_n}\).
The first nonzero vector coefficients therefore have the same
projective comparison \(M_{\rm PR}(0)=C(0)^{-1}N(F)\).
This argument does not prove equality of their orders or produce the
arithmetic premise.

## 4. The CM local unit is visible and checkable

Use the project's actual convention

\[
 K=\mathbf Q(\omega),\quad \omega^2-\omega+18=0,\quad
 \mathfrak a_2=(2,\omega),\quad
 \mathfrak a_2^7=(10+\omega),\quad
 \psi(\mathfrak a_2)=\zeta_7,
\]

and the embedding \(\omega\equiv2\pmod5\).
The norm-five ideal retained by the ordinary q-family is
\(\mathfrak b=(-2+3\omega)/\mathfrak a_2^5\). Exact arithmetic gives

\[
 \theta=\frac{(-2+3\omega)^7}{(10+\omega)^5}
       =-281+4\omega,\qquad
 \theta\bar\theta=5^7.                              \tag{8}
\]

Here \(\theta\) is a local unit; \(\bar\theta=-277-4\omega\)
generates the seventh power of the selected prime over five.
The other norm-five ideal has seventh-power generator
\(({-2+\omega})^7/(10+\omega)^2=277+4\omega=-\bar\theta\).
These statements are verified in the accompanying exact checker.

At arithmetic weights \(s\equiv0\pmod4\), the principal-unit
normalization in cm_weight_jets.py gives

\[
 a(s)^7=c(s)^7=\theta^s,\qquad
 \boxed{\ (a(s)c(s)5^{-s})^7
       =(\theta/\bar\theta)^s.\ }                   \tag{9}
\]

The two finite class characters cancel in \(a(s)c(s)\); they must
not be replaced individually by 1. In particular \(a(0)c(0)=1\).

CH takes the unramified local field
\(F_{\rm ur}=\widehat H_1\), of degree 7, and chooses a generator
\(\varpi\) of the seventh power of the selected prime. Set
\(\varpi=\bar\theta\). Its relative Lubin--Tate parameter is
\(\varpi/\bar\varpi=\bar\theta/\theta\).
Equation (9) is exactly the inverse s-th power of this parameter,
as required for the \(\varphi^7\)-eigenvalue of the LT twist in
CH (3.2).

On \(G_{F_{\rm ur}}\), equality of this Frobenius eigenvalue together
with the same inertia character identifies the crystalline rank-one
CM twist with the corresponding LT twist. Indeed their quotient is
unramified and has trivial Frobenius over \(F_{\rm ur}\).
A possible unramified order-seven ambiguity over \(\mathbf Q_5\)
vanishes on this subgroup. If two extensions are analytic on the
same connected weight disk and both equal 1 at the center, their
order-seven quotient is constant and hence trivial.

This removes a concrete local character mismatch. It does not
identify CH's normalized conjugate sum with a particular de Rham
period normalization of the global diagonal. CH (3.2) uses
\(t_\epsilon\); (3.9) and Theorem 3.4 also use the cyclotomic period
t and the chosen isomorphism of formal groups. Their ratio cannot
be silently set to 1. For a fixed rank-one isomorphism its effect is
scalar on the elliptic block, but compatibility of the conjugates
and the actual class still belongs to the premise of Section 3.

## 5. The corrected conditional pilot matrix

For the pilot \(p=5\), \(F^2+3F+5=0\), and
\(\tau=\zeta_7^3+\zeta_7^4=1-\xi-\xi^2\).
Then

\[
 C(0)=\frac{20-(5\tau+3)F}{25},\quad
 N(F)=\frac{30+3F}{25},\quad D_\tau=5\tau^2+18\tau+25,
\]

and exact reduction gives

\[
 \boxed{
 M_{\rm PR}(0)
 =\frac{3[(5\tau+11)+2(\tau+1)F]}{D_\tau},
 \qquad
 M_{\rm PR}(0)^{-1}
 =\frac{(5-\tau)-2(\tau+1)F}{9}.
 }                                                            \tag{10}
\]

The determinant is \(27/D_\tau\).
Since \(\tau\) has minimal polynomial
\(\tau^3+\tau^2-2\tau-1=0\), it is a 5-adic unit; therefore
\(D_\tau\equiv3\tau\pmod5\) is a unit.
Both matrices in (10) are integral and invertible on any integral
F-stable lattice.

There is a useful normalization diagnostic. The existing base
annihilator vector from CH's \(j=0\) interpolation is

\[
 \zeta=\frac{20-13F}{45}\omega.
\]

Under the self-dual alternating identification, its line is also
the candidate image line of that normalized base regulator. Applying
the inverse of (10) gives

\[
 M_{\rm PR}(0)^{-1}\zeta
   =-\frac{(10+50\tau)+(61+35\tau)F}{135}\omega.     \tag{11}
\]

It is still different from the DL candidate
\([(-2-10\tau)+(11+\tau)F]\omega/3\): the wedge of the two
coefficient pairs, with the nonzero scalar denominators removed,
is \(8(5\tau+1)(10\tau+29)\), which is nonzero.
Here coefficient pairs are projective coordinates in
\((\omega,F\omega)\), assuming the Hodge line is not F-stable.
This basis assumption must be checked in a numerical realization.

Equation (11) is **only a diagnostic under the unproved common-class
comparison**. A mismatch does not refute DL, identify a new arithmetic
line, or validate the numerical nonvanishing test. It locates the
remaining comparison question rather than eliminating it.

## 6. What remains before an arithmetic conclusion

The missing comparison must handle the actual classical diagonal
specializations with first weight 2, the variable rather than
auxiliary CM summand, the cup-product and Tate identifications,
the character inversion linking the two weight coordinates, and the
normalization and test vectors of (3.9). Any non-scalar matrix in
these steps must be recorded; it cannot be hidden in \(\lambda_s\).
The separately reviewed scalar ordinary reciprocity law supplies
only one coordinate.

The corrected [BSV specialization proof](../general_criterion/BSV_REPAIR.md)
supplies the rational projected weight-two geometric argument. The previous
raw DR22 moment argument was incomplete and is not used. The separate
[global comparison](../global_class_comparison/README.md) and
[normalized local comparison](../normalized_local_comparison/README.md)
supply the two arithmetic premises for the pilot. The algebra in this
note remains conditional on those inputs; its checker does not verify them.

No arithmetic nonzero localization or bad-line identification is
claimed by this note. Its executable result is exact algebra:

    python3 research/bsd-localization/pr_syntomic_comparison/check_comparison.py

The script uses only the Python standard library and the exact
Laurent-polynomial utility from the frozen fixed-weight checker.
It does not check the geometric or Iwasawa comparison premise.
