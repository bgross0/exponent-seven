# Which analytic jet can see the reflected class?

Date: 2026-11-27. This audit concerns only

\[
 E:y^2+y=x^3+x^2-2x,\quad N_E=389,\quad
 K=\mathbf Q(\sqrt{-71}),\quad p=5,
\]

and the two ordinary CM families with inverse order-seven class characters
and the **same CM type**. It does not assert a new explicit reciprocity law.

## Results

There are three additional reductions for the actual weight-two analytic
de Rham family. They hold before any proposed comparison with the reflected
Castella--Hsieh class.

1. Depleting the second CM factor changes the weight-two overconvergent form
   by an **exact differential**. Its raw q-series changes, but its de Rham
   class, cohomological tame traces, and proper elliptic projection do not.
2. After the explicit unit factor \(\langle389\rangle^{s/2}\), the elliptic
   projection is **even in \(s=k-1\)**. Its base value is zero by DL Theorem
   3.1. Therefore its entire first derivative is zero, including both
   elliptic Frobenius components. The second derivative is not forced zero.
3. The elliptic projection is fixed by
   \(\sigma:\zeta_7\mapsto\zeta_7^{-1}\). It takes values in the unramified
   cubic subfield of \(\mathbf Q_5(\zeta_7)\). This reduces the coefficient
   field, while retaining the full two-dimensional elliptic de Rham space.

These are deductions proved below, using the actual overconvergent/de Rham
family of DL and Coleman's cohomological interpretation. Finite q-series
alone do not establish overconvergence or construct its proper class. The
finite identities are independently checked in the companion
`weight_reflection/` and `trace_scaling/` computations. This directory's
small checker verifies the character decomposition, the tame matrix
normalizations, the differential identity, and the precise insufficiency
of evenness for the desired second coordinate.

## 1. The varying representation is an anticyclotomic block

Let \(\psi\) be the chosen class character, with \(\psi^c=\psi^{-1}\).
Write the common CM weight character as \(\rho_s\), normalized so that on
ideals prime to 5

\[
 \rho_s(\mathfrak b)=(1+W)^{\nu(\mathfrak b)},\qquad
 W=6^s-1,\qquad
 \rho_s\rho_s^c=\mathcal N_s,
\]

where \(\mathcal N_s(\mathfrak b)=\langle N\mathfrak b\rangle^s\).
The class-representative correction in `reflected_pilot/cm_weight_jets.py`
gives exactly
\(\nu(\mathfrak b)+\nu(\mathfrak b^c)
=\log_5(N\mathfrak b)/\log_5(6)\).
Angle brackets mean the principal-unit part. At arithmetic weights
\(s\ge0\), \(s\equiv0\pmod4\), these expressions agree with the indicated
ordinary algebraic powers. They never require a p-adically varying power
of 5.

The elementary induced-representation identity gives

\[
\begin{split}
 &\operatorname{Ind}_K^{\mathbf Q}(\psi\rho_s)
 \otimes\operatorname{Ind}_K^{\mathbf Q}(\psi^{-1}\rho_s)
 \otimes\mathcal N_s^{-1}\\
 &\hspace{12mm}\simeq
 \operatorname{Ind}_K^{\mathbf Q}(\rho_s/\rho_s^c)
 \oplus\operatorname{Ind}_K^{\mathbf Q}(\psi^2).
\end{split}                                                    \tag{1}
\]

Here the central norm twist is restricted from \(G_{\mathbf Q}\); equation
(1) writes the characters in the theta-series convention. Dual Galois
conventions may invert all characters. The convention-independent content
is a varying anticyclotomic summand and a constant auxiliary summand. CH
equation (3.12) makes this identification at the level of their cohomology.
At the base the first summand splits as \(1\oplus\epsilon_K\).

For completeness, restricted to \(G_K\), the four characters after the
central twist, in tensor order \((++,+-,-+,--)\), are

\[
 \rho_s/\rho_s^c,\quad\psi^2,\quad\psi^{-2},\quad\rho_s^c/\rho_s.
                                                               \tag{2}
\]

The trivial idempotent for the finite order-seven part of the **CM tensor
factor** projects onto the first and fourth entries; division by 7 is
5-integral. It commutes with conjugation, which exchanges these entries
and also exchanges the middle two. Tensor this endomorphism with the
identity on \(V_pE\). Averaging arbitrary lifts of class-group elements
acting on the entire elliptic tensor representation is not the same
operation.

This isolates the variable block, but it does not split that block into
an elliptic and a quadratic-twist family: away from \(s=0\), the two
characters \(\rho_s/\rho_s^c\) and its inverse differ. Thus the constant
\((1+c)/2\) eigenspace at the base does not extend to a \(G_{\mathbf Q}\)
direct summand throughout the anticyclotomic family.

In the pilot, the certified auxiliary central value is nonzero. CH Lemma
3.5 then makes the constant auxiliary component of the diagonal class
identically zero on this diagonal, for all test vectors. Its diagonal
derivatives are zero as well. Changing to that character component does
not recover the missing finite elliptic coordinate. Equation (1) is a
Galois-family identification; it is not, on its own, a formula equating
the full DL vector with the full CH regulator.

## 2. Extra second-factor depletion is exact

Use raw \(V_aF(q)=F(q^a)\), and put

\[
 A_s=d^{-s}(g_s^{[5]})\,V_Nh_s,\qquad
 B_s=d^{-s}((V_Ng_s)^{[5]})\,h_s,\qquad N=389.
                                                               \tag{3}
\]

Let \(A_s^{dd},B_s^{dd}\) additionally deplete the second factor. All four
products have total weight two. As in DL, work with their actual analytic
overconvergent families, or their overconvergent weight jets on a common
strict neighborhood. The first factor \(F\) in either placement satisfies
\(U_5F=0\).

Since \(U_5h_s=\alpha_h(s)h_s\),

\[
 A_s-A_s^{dd}=
 \alpha_h(s)\,d^{-s}(g_s^{[5]})\,V_5(V_Nh_s).
                                                               \tag{4}
\]

The q-expansion identity

\[
 U_5(F\,V_5G)=(U_5F)G                                  \tag{5}
\]

makes (4) \(U_5\)-annihilated. The same holds for \(B_s-B_s^{dd}\).
By Coleman Theorems 5.4 and 5.1, at weight two

\[
 M_2^\dagger/dM_0^\dagger\simeq H^1_{\mathrm{dR}}(\text{ordinary wide open}),
 \qquad U_5=\operatorname{Ver},\qquad
 \operatorname{Frob}\operatorname{Ver}=5.
\]

Consequently a \(U_5\)-annihilated weight-two form has zero cohomology
class. This proves

\[
 [A_s]=[A_s^{dd}],\qquad [B_s]=[B_s^{dd}].                \tag{6}
\]

The conclusion precedes the canonical proper projection; it therefore
survives that projection and tame traces. It also holds coefficient by
coefficient in the weight jets. No division by a guessed Euler factor is
used. The assertion concerns equality in cohomology, not equality of raw
series. Keeping the saved raw variants separate is correct.

## 3. An exact weight-reflection identity

Conjugating ideals in the depleted theta series, where every norm is
prime to 5, gives

\[
 d^{-s}g_s^{[5]}=h_{-s}^{[5]}.                            \tag{7}
\]

Indeed the character changes from \(\psi\) to \(\psi^{-1}\), while its
weight exponent changes from \(\nu(\mathfrak b)-\nu(N\mathfrak b)\) to
\(-\nu(\mathfrak b^c)\). The ideal permutation preserves every q-index.
This proves (7) as an analytic q-expansion identity, not an asymptotic
comparison. The q-expansion principle identifies the corresponding
modular sections. The reflected coordinate is exactly

\[
 W\longmapsto\iota(W)=(1+W)^{-1}-1.
\]

Because \(d^{-s}V_N=\langle N\rangle^{-s}V_Nd^{-s}\), (7) gives

\[
 A_s^{dd}=h_{-s}^{[5]}V_Nh_s^{[5]},\qquad
 B_s^{dd}=\langle N\rangle^{-s}(V_Nh_{-s}^{[5]})h_s^{[5]},
\]

and hence the literal q-series identity

\[
 A_{-s}^{dd}=\langle N\rangle^s B_s^{dd}.                 \tag{8}
\]

By (6), the same identity holds in cohomology for singly depleted inputs.

## 4. The tame Atkin--Lehner sign selects the even combination

Let \(\chi=\chi_{-71}\). It satisfies \(\chi(389)=-1\). At tame level
\(71N\), use the determinant-normalized slash operator and the matrix

\[
 w_N=\begin{pmatrix}389&126\\27619&8947\end{pmatrix},
 \qquad389\cdot23-71\cdot126=1.
                                                               \tag{9}
\]

Writing \(D_N=\operatorname{diag}(N,1)\),

\[
 w_N=\begin{pmatrix}1&126\\71&8947\end{pmatrix}D_N,
 \qquad
 D_Nw_N=N\begin{pmatrix}389&126\\71&23\end{pmatrix}.
\]

Both displayed determinant-one matrices are in \(\Gamma_0(71)\).
Their lower-right entries have character values 1 and \(\chi(N)=-1\).
For a native form \(F\) of weight \(j\) and character \(\chi\),

\[
 F|_jw_N=N^{j/2}V_NF,\qquad
 (V_NF)|_jw_N=-N^{-j/2}F.                               \tag{10}
\]

At actual classical level with 5-depletion, replace 71 by \(71\cdot25\)
in the determinant-one construction. One valid matrix is

\[
 \begin{pmatrix}389&254\\690475&450851\end{pmatrix},
 \qquad389\cdot1159-(71\cdot25)\cdot254=1.
\]

The character remains \(\chi\), so the two character values are again
1 and -1. Restriction to the canonical ordinary component gives the
same tame correspondence. This avoids pretending that the first matrix
normalizes every full classical 5-power level.

Apply (10) to the inverse-Bol factor of weight \(1-s\) and the other
factor of weight \(1+s\). Their powers of \(N\) leave exactly the
\(N^{-s}\) already present in the definition of \(B_s\). Therefore

\[
 A_s|_2w_N=-B_s,\qquad B_s|_2w_N=-A_s,                  \tag{11}
\]

and similarly for the doubly depleted pair. The equality extends from
classical arithmetic weights to the analytic fixed-total-weight family.

The curve has split multiplicative reduction at 389: \(v_{389}(\Delta)=1\)
and \(-c_6=856\equiv95^2\pmod{389}\). Hence \(a_{389}=1\), and its
weight-two newform has Atkin--Lehner eigenvalue \(-a_{389}=-1\). This is
also true on its full old isotypic component at level \(71\cdot389\).
For the proper elliptic projection \(\Pi_E\), (11) gives

\[
 \Pi_E[A_s]=\Pi_E[B_s].                                 \tag{12}
\]

For a fixed two-dimensional coordinate, take the symmetric oldspace
coordinate \(\Pi_E=62^{-1}P_E\operatorname{Tr}_{71,1}\) on the
Fricke71-plus input, as proved in the tame-trace notes. The saved numerical
series are traces before the factor1/62. A different global test vector
requires its prescribed degeneracy combination in the comparison.

Let \(\mathcal L(s)=\Pi_E[A_s]\). Equations (6), (8), and (12) prove

\[
 \mathcal L(-s)=\langle389\rangle^s\mathcal L(s),\qquad
 \mathcal C(s):=\langle389\rangle^{s/2}\mathcal L(s)
 \quad\text{satisfies}\quad\mathcal C(-s)=\mathcal C(s).  \tag{13}
\]

Here \(\langle389\rangle^{s/2}=(1+W)^{\nu_{389}/2}\), with
\(\nu_{389}=\log_5(389)/\log_5(6)\in\mathbf Z_5\). There is no square-root
choice of a complex period and no missing factor of 389.

DL Theorem 3.1 proves \(\mathcal L(0)=0\), because
\(L(E,V_g\otimes V_h,1)\) has the vanishing factor \(L(E,1)\). It applies
to all corresponding test vectors. Equation (6) transfers this base zero
to the doubly depleted input. Equation (13) now proves

\[
 \boxed{\mathcal L(0)=0,\qquad \mathcal L'(0)=0.}         \tag{14}
\]

The derivative in either \(s\) or \(W\) vanishes. This is a statement about
the entire two-dimensional proper de Rham vector. It does not use DL
Conjecture 3.2, finiteness of Sha, or a comparison with CH's regulator.
An exact zero at the base uses the theorem-based \(L(E,1)=0\) in the
pilot eligibility audit; a numerically small complex value is not used.

## 5. A cubic coefficient field, without discarding a Frobenius slope

Let \(\sigma\) fix \(\mathbf Q_5\) and send \(\zeta_7\) to its inverse.
It interchanges \(g_s\) and \(h_s\). For a positive arithmetic
\(s\equiv0\pmod4\), put

\[
 F=d^{-s}g_s^{[5]},\quad H=d^{-s}h_s^{[5]},\quad G=V_NH.
\]

Both \(F\) and \(G\) have weight \(1-s\), and

\[
 A_s^{dd}=N^{-s}F d^sG,\qquad
 \sigma B_s^{dd}=N^{-s}G d^sF.                          \tag{15}
\]

The raising factor \(N^{-s}\) is essential. The bilinear concomitant

\[
 R(F,G)=\sum_{i=0}^{s-1}(-1)^i(d^{s-1-i}F)(d^iG)
\]

satisfies the telescoping identity

\[
 dR=(d^sF)G-F(d^sG).                                   \tag{16}
\]

Moreover \(R\) is a weight-zero overconvergent modular form. In the
Rankin--Cohen formula of order \(s-1\), both upper binomial entries are
\((1-s)+(s-1)-1=-1\); \(\binom{-1}{i}=(-1)^i\) gives exactly this
alternating bracket, up to the harmless convention for the bracket's
sign. Its weight is \(2(1-s)+2(s-1)=0\). This is the algebraic
Gauss--Manin/Rankin--Cohen differential construction and applies to
negative integral weights; the individual intermediate derivatives need
not themselves be modular.

Equations (15)--(16) prove \([A_s^{dd}]=[\sigma B_s^{dd}]\). The class
families are analytic, so the identity at the accumulating arithmetic
weights extends to a neighborhood of \(s=0\) and to every finite jet.
No uniform overconvergence radius for the brackets of all increasing
orders is inferred or needed: the analytic cohomology family is the
object to which the identity principle is applied.

Combining (6) and (12),

\[
 \sigma\mathcal L(s)=\mathcal L(s).                     \tag{17}
\]

Since \(\operatorname{ord}_7(5)=6\) and \(5^3\equiv-1\pmod7\),
\(\mathbf Q_5(\zeta_7)\) is unramified of degree six and \(\sigma\) is
the cube of Frobenius. Its fixed field is unramified of degree three,
with basis, for example,

\[
 1,\quad\zeta_7+\zeta_7^{-1},\quad\zeta_7^2+\zeta_7^{-2}.
\]

This reduction applies to the projected analytic vector. The raw input
series need not be fixed by \(\sigma\). It halves coefficient storage;
it does not justify keeping only the ordinary elliptic slope.

## 6. Which coefficient remains arithmetically useful?

At the base,

\[
 V_g\otimes V_h\simeq1\oplus\epsilon_K\oplus
 \operatorname{Ind}_K^{\mathbf Q}(\psi^2).
\]

The pilot's two rational directions belong to the trivial summand; the
two auxiliary central values are nonzero. The DL point-regulator matrix
therefore has rank at most one, for every refinement. Its determinant
vanishes, as recorded in DL Section 2.3, Case 1. DL Conjecture 3.2 would
only predict that the *corrected Hodge quotient* of the first derivative
is zero. Equation (14) is a stronger analytic deduction for these
particular same-CM-type test vectors.

There is no analogous forced zero for

\[
 \mathcal L_2=[W^2]\mathcal L(W)\in
 H^1_{\mathrm{dR}}(E/\mathbf Q_5)\otimes
 \mathbf Q_5(\zeta_7+\zeta_7^{-1}).                     \tag{18}
\]

The factor in (13) leaves (18) unchanged because both lower coefficients
are zero. All even vector series \(s^2v+O(s^4)\), with arbitrary \(v\)
in the two-dimensional de Rham space, satisfy the same parity constraint.
The character decomposition does not further specify this vector.

This also does not manufacture the desired logarithm. In the local model
\(M=L[[t]]^2\), let

\[
 y_B=(Bt,t^2),\quad P=\operatorname{diag}(t,1),\quad
 F(a,b)=b,\quad B\in L.
\]

Then \(P(y_B)=(Bt^2,t^2)\) is even, its scalar image is always
\(F(y_B)=t^2\), its base and first jet vanish, and its coefficient field
can be \(\mathbf Q_5\). Nevertheless the finite logarithm of \(y_B/t\)
is \(B\), which can be zero or nonzero. These models check insufficiency
of the newly established symmetries; they are not claimed to be realized
by arithmetic global classes.

The target remains the **complementary second coordinate of the variable
block**. In the notation of `finite_log_reciprocity/FINITE_COORDINATE.md`,
one must prove a comparison of this DL family with the full regulator
\(P(y)\) of the same CH localization, then extract

\[
 \ell(x_0)=c_P^{-1}[t^2]\lambda(t)P(y).
\]

A regular coordinate change \(t=aW+O(W^2)\), \(a\ne0\), and a regular
invertible comparison matrix suffice at this leading order: derivatives
of the matrix do not contribute because the two lower vector
coefficients are zero. Its constant matrix, the square \(a^2\), and the
local logarithm normalization must still be identified. This is a
smaller comparison problem than determining the full varying regulator,
but it is not supplied by the scalar theta law.

## 7. Literature checks and a concrete next gate

The refinements are regular and non-exceptional. For the first CM type,
the base ordinary eigenvalues are \(\zeta_7^2\) and \(\zeta_7^5\).
They are distinct modulo 5; their product is 1. The elliptic ordinary
root is \(\alpha_f\equiv2\pmod5\), so no equation
\(\alpha_f=\alpha_g\alpha_h\) or
\(\alpha_f=\beta_g\alpha_h\) occurs. The order-four residue 2 cannot
equal a seventh root of unity. A product of CM eigenvalues equal to 1
is not an exceptional zero by itself.

The published 2026 BSV paper, Theorem 3.3 (p. 970), is a rigorous
first-order height/reciprocity formula for the scalar three-variable
Garrett function. Its Lemma 3.2 is a strict-logarithm vanishing statement.
The rationality conclusion remains Conjecture 3.5; Remark 3.6(2)--(3)
states precisely the remaining algebraic-scalar issue. Neither supplies
the second component in (18). Its observation that some CM products
vanish identically is not an assertion about every CM pair: CH
Proposition 2.5 gives a nontrivial scalar theta factor in this pilot.

Huang's finite-slope reciprocity/Gross--Zagier results are a possible
route to comparing the two elliptic refinements, but do not identify
their resulting classes with this same CH localization merely by
changing the refinement. The split good-ordinary pilot also does not
meet the multiplicative/inert hypotheses of exceptional-zero results.

There is a further source-hypothesis distinction: the Heegner-hypothesis
rank-(1,1) theorem in DLR Section 3.2 is not a theorem for this
rank-(2,0), inert-conductor pilot. Here 389 is inert in K, and the
quaternionic theta setting is definite. A generic sentence that CM
regulators are Heegner-point expressions cannot change those signs.

Before increasing precision, a proper-cohomology reducer should pass
these exact tests on the existing data:

* both depletion conventions give the same projected answer;
* the two cross placements give the same elliptic projection;
* the base and entire first weight coefficient are zero;
* the surviving second coefficient is fixed by \(\sigma\).

Passing those tests does not prove the missing reciprocity identity.
It does leave one second-order vector over a cubic field to compute,
with both elliptic slopes retained. A failure of one of these identities
is a normalization, exact-differential, or projection problem to resolve
before interpreting a nonzero output arithmetically.

## Primary sources

* Darmon--Lauder, *Stark points on elliptic curves via Perrin-Riou's
  philosophy*, Sections 1, 2.3, and Theorem 3.1/Conjecture 3.2.
  [Author PDF](https://people.maths.ox.ac.uk/lauder/papers/DL.pdf).
* Coleman, *Classical and Overconvergent Modular Forms*, Theorems 5.1
  and 5.4; Section 4 for the algebraic differential construction.
  [Author PDF](https://www.math.uchicago.edu/~fcale/Files/Cole1.pdf).
* Castella--Hsieh, *On the nonvanishing of generalised Kato classes for
  elliptic curves of rank 2*, Proposition 2.5, equation (3.12), Lemma
  3.5, and Theorem 3.6.
  [Published author PDF](https://web.math.ucsb.edu/~castella/Kato-print.pdf).
* Bertolini--Seveso--Venerucci, *On p-adic analogues of the Birch and
  Swinnerton-Dyer conjecture for Garrett L-functions*, Annales de
  l'Institut Fourier 76 (2026), 945--981, Lemma 3.2, Theorem 3.3,
  Conjecture 3.5, and Remark 3.6. Numbering is from the published
  version; the older author preprint numbers these differently.
  [Published record](https://aif.centre-mersenne.org/articles/10.5802/aif.3726/),
  [published PDF](https://aif.centre-mersenne.org/item/10.5802/aif.3726.pdf).
* Darmon--Lauder--Rotger, *Stark points and p-adic iterated integrals
  attached to modular forms of weight one*, Sections 3.1--3.2.
  [Corrected author PDF](https://web.mat.upc.edu/victor.rotger/docs/DLR1.pdf).
* Huang, *Triple product p-adic L-functions for finite slope families
  and a p-adic Gross-Zagier formula*, current preprint v2, submitted
  2026-11-06. [arXiv](https://arxiv.org/abs/2403.18620v2).

Run this directory's exact structural check with

```sh
python research/bsd-localization/analytic_target_audit/check_target.py --check research/bsd-localization/analytic_target_audit/result.json
```

The default prints stable JSON and writes nothing. `--output PATH` writes
an explicitly requested result file. The checker is not an implementation
of modular cohomology or a proof of reciprocity.
