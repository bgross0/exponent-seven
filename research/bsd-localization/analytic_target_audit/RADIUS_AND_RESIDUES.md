# Bounded follow-up: the integral radius obligation and residue filter

Date: 2026-11-27. This is a bounded source review. It does not modify the
analytic identities proved in `README.md` or certify a Katz truncation.

## 1. The CM rewrite does not yet certify an integral tail bound

Lauder's *Efficient Computation of Rankin p-Adic L-Functions*, Section
2.3.2 and Note 2.3(1), explicitly distinguish two assertions:

* the inverse-Bol product is overconvergent over the coefficient **field**
  on each radius smaller than \(1/(p+1)\);
* it belongs to the asserted **integral** Katz lattice at that rate.

The note assumes the second assertion for the computations and says that
a complete proof requires further analysis, potentially with additional
growth or precision loss. The CM identity
\(d^{-s}g_s^{[5]}=h_{-s}^{[5]}\) removes the need to estimate an arbitrary
inverse-Bol primitive, but does not automatically supply an integral norm
for the reflected ordinary family on a specified strict neighborhood.

The integral q-expansion principle controls the ordinary locus. An
explicit norm on a larger Hasse annulus is additional information. The
fact that ordinary unit-eigenforms extend to a larger radius over the
field does not, without an integral estimate, preserve norm at most one.
Taking a dense sequence of integral classical forms also requires a
uniform bound in a specified weight trivialization; their varying
weights cannot simply be treated as one fixed integral Banach lattice.

Lauder's *Computations with classical and p-adic modular forms*, Section
2.3, records Wan's bound, in its orthonormal Katz basis,

\[
 v_p(A_{i,s}^{u,v}(j))\ge u(p-1)v_p(r)-1
\]

for the matrix of \(U_p\circ G^j\), where
\(G=E_{p-1}/V_pE_{p-1}\). This is an operator estimate on an already
specified lattice. It is not itself a certificate that an arbitrary
q-integral input lies in that lattice. Note 3.1 also distinguishes
integrality of \(pU_p\), supplied by the estimate, from the stronger
integrality of \(U_p\) observed experimentally in that implementation.

**Concrete remaining obligation.** Give an explicit Banach norm for the
normalized CM family on a stated weight disk and a stated strict
neighborhood, including its weight trivialization. Cauchy estimates then
bound its first two weight coefficients. Depletion, multiplication,
prime-to-5 degeneracy maps, and tame trace can be bounded on suitably
restricted domains. These bounds would provide a quantitative Katz tail
certificate for the weight-two jets. This bounded review did not locate
a theorem supplying that complete integral estimate for the present
normalized CM family.

### An alternative certificate design

One may instead certify the CM jets through their ordinary eigen-equation
for the weight-varying operator \(U\circ G^j\). The following elementary
Banach-space step is rigorous once its premises are provided.

Split a chosen Katz Banach space into a finite head and an infinite tail,
and write the operator as

\[
 U=\begin{pmatrix}A&B\\C&D\end{pmatrix}.
\]

For a unit eigenvalue \(\alpha\), suppose \(\|D\|<1\). Every bounded
eigenvector \((v,w)\) then satisfies

\[
 w=(\alpha-D)^{-1}Cv
   =\alpha^{-1}\sum_{n\ge0}(\alpha^{-1}D)^nCv,
 \qquad \|w\|\le\|C\|\,\|v\|.
\]

Wan's high-row estimate can make this tail contraction explicit. The
first two differentiated eigen-equations have analogous inhomogeneous
tail equations. A certificate would additionally need the first two
weight-coefficient operator bounds, a certified finite head/normalization,
and an isolated eigenline or controlled reduced resolvent. These are
specific computations and estimates to supply; the displayed argument
does not assert that they have been supplied. Extracting a finite head
from finite q-data must itself be justified and cannot assume the desired
tail bound circularly.

## 2. Independent verification of the residue filter

The proposed \(U_5^2-1\) filter passes the structural and arithmetic review.
In characteristic 5 the sole supersingular j-invariant is zero. The curve
\(E_0:y^2=x^3+1\) has six points over \(\mathbf F_5\), hence trace zero
and \(\pi^2=[-5]\). This scalar fixes every cyclic subgroup of order 389.
Thus all supersingular points of the coarse curve \(X_0(389)\) are defined
over \(\mathbf F_{25}\).

There are 390 cyclic subgroups; the effective order-three automorphism
action has no fixed line because \(389\equiv2\pmod3\). Thus the
supersingular divisor has degree 130. The two cusps are rational. On the
residue quotient, Frobenius is 5 times the permutation of the deleted
points. The permutation has square one, so

\[
 U_5=5\operatorname{Frob}^{-1},\qquad U_5^2=1
\]

on that quotient. The filter therefore sends an open-cohomology class
into proper cohomology, including when cusp residues are present.

On the elliptic factor, let \(F\) be geometric \(\mathbf Q_5\)-linear
Frobenius, extended linearly to the external coefficient field. Since
\(F^2+3F+5=0\),

\[
 U_5=-F-3,\qquad U_5^2-1=3(F+1),\qquad
 (U_5^2-1)^{-1}=-\frac{F+2}{9}.
\]

The determinant of the filter is 27. Its inverse has no 5-adic loss on
an **F-stable integral lattice**, such as the good-reduction crystalline
lattice. This integral assertion should not be transferred automatically
to an arbitrary merely Hecke-stable lattice. The separate polynomial
Hecke projector's lattice hypothesis is different.

The filter eliminates residues in cohomology. It does not supply the
remaining representative reduction, integral input-radius bound, or
second regulator coordinate. It also must not apply coefficient-field
Frobenius to the external cubic coefficients; the geometric operator is
extended linearly.

## Sources

* Lauder, *Efficient Computation of Rankin p-Adic L-Functions*, Section
  2.1.2, Section 2.3.2, and Note 2.3(1).
  [Author PDF](https://people.maths.ox.ac.uk/lauder/papers/AgbLauderFINAL.pdf).
* Lauder, *Computations with classical and p-adic modular forms*, Section
  2.3, equation (2.3), and Note 3.1.
  [Author PDF](https://people.maths.ox.ac.uk/lauder/papers/LMSLauderMFJune10.pdf).
* Coleman, *Classical and Overconvergent Modular Forms*, Theorem 5.1,
  the residue sequence around Lemma 5.3, and Theorem 5.4.
  [Author PDF](https://www.math.uchicago.edu/~fcale/Files/Cole1.pdf).
* The explicit point count, orbit count, Frobenius polynomial, and inverse
  matrix are recorded in `../residue_filter/check_filter.py` and its
  saved `result.json`. This review read that checker and verified the
  polynomial identities independently; it does not add another arithmetic
  computation of the pilot's projected jet.
