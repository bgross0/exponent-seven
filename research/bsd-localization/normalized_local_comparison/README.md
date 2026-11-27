# Full normalized local comparison on the variable CM summand

Date: 2026-11-27. Continuation of the frozen snapshot `9364a14`.

## Result and scope

The remaining **local** comparison can be proved projectively for the
DR22-defined diagonal family, using the rational projected edge proposition
in [ARITHMETIC_SPECIALIZATION.md](../leading_comparison/ARITHMETIC_SPECIALIZATION.md).
There is no additional undetermined matrix from CM periods or from
Castella--Hsieh's Frobenius-conjugate averaging. This conclusion concerns
the fully normalized map in CH (3.9), not its unaveraged precursor.

The argument has three ingredients:

1. On the relevant CM component, the full syntomic Abel--Jacobi functional
   determines the full two-dimensional Bloch--Kato logarithm. The auxiliary
   CM component is annihilated by the CM test tensor.
2. CH Theorem 3.4 already interpolates the normalized, averaged map. Its
   evaluations on two independent elliptic Frobenius test vectors determine
   the full vector, including every Frobenius correction.
3. Remaining choices of a basis of the same rank-one CM period space act
   by one common nonzero scalar on the elliptic factor. Such scalars may
   vary with the integer weight; the projective continuation argument
   needs no analytic interpolation or valuation bound for them.

Thus the additional local premise in Section 3 of
[pr_syntomic_comparison/README.md](../pr_syntomic_comparison/README.md)
follows for that DR22-defined family from the projected geometric
specialization and the compatibility of étale and syntomic Abel--Jacobi
maps. Its transfer to the named CH global class requires the separate
global-class comparison, or generic proportionality in the same Selmer
module. This note does not establish that global result and does not
assert nonzero localization on its own.

The word “proved” here means a mathematical deduction from the cited
published comparison theorems and the repository's explicitly stated
projected edge proposition. These geometric and comparison arguments have
not been formalized in Lean. The small executable below checks the new
linear-algebra assertions, not those source theorems.

## 1. Fixed conventions

Let

\[
 E:y^2+y=x^3+x^2-2x,\qquad
 K=\mathbf Q(\omega),\quad \omega^2-\omega+18=0,\qquad p=5.
\]

Use the embedding \(\omega\equiv2\pmod5\). The selected prime is denoted
\(\mathfrak p\); its conjugate is \(\bar{\mathfrak p}\). Write
\(F_{\rm ur}=\widehat H_1\) for the unramified degree-seven completion
used in CH Section 3.4. Reserve \(F\), without a subscript, for
**coefficient-linear geometric Frobenius on untwisted elliptic
cohomology**, not for the field or for Galois action on its constants.

Fix the geometric realization of the elliptic summand and its alternating
cup/Weil identification throughout. Then

\[
 D=H^1_{\rm dR}(E),\quad F^2+3F+5=0,\qquad
 V=V_pE\simeq H^1_{\rm et}(E)(1),\quad \varphi=F/5,
\]

\[
 F^\dagger=5F^{-1},\qquad
 \varphi^\dagger=5^{-1}\varphi^{-1}.                 \tag{1}
\]

The dagger is the adjoint for the fixed alternating pairing. A different
global scalar normalization of that pairing has no effect on (1).

There is awkward prose about duals and the unit eigenvalue immediately
before CH (3.14). The present dictionary is anchored to CH's definition
of Kummer dual in Section 3.2, the Tate identification
\(V=H^1_{\rm et}(E)(1)\), and the **displayed** eigenvalue and pairing in
(3.14). It does not infer an untwisted eigenvalue from that isolated prose.

Put \(s=k-1>0\). The classical CM forms have weights \((k,k)\), and the
negative-twist interpolation parameter is

\[
                       j=-s.                         \tag{2}
\]

For the normalized distribution outputs, work if necessary over a
common complete overfield `Omega` of the finite character coefficient
field, such as `C5`, containing the unramified period coefficients.
Full vector identities are read in `D tensor Omega`. This does not
assert descent of the normalized regulator to the finite character
field; rank-one period changes are scalar over this common output
field. The underlying global Selmer classes keep their finite
coefficient field.

The regulator is pulled back along the character
\(\psi_{-s}=\varepsilon_{\mathcal F}^{-s}\), with the prescribed finite
component. In the trivial finite component and a generator on which
\(\varepsilon_{\mathcal F}\) takes value \(1+p\), this is the inversion
\(T_{\rm LT}=(1+W)^{-1}-1\), where \(W=(1+p)^s-1\). The symbol
\(T_{\rm LT}\) denotes this specifically LT-adapted generator
coordinate. It is not the norm-two Artin generator coordinate
\(T_a\) used in the global comparison, where
\(T_a=(1+W)^\delta-1\) and \(\delta\equiv2\pmod5\). Their conversion is

\[
                 T_a=(1+T_{\rm LT})^{-\delta}-1.
\]

Its Jacobian at augmentation is \(-\delta\), a 5-adic unit. This
changes the coordinate of the same character, not the twist \(j=-s\).
The projective first nonzero vector is unchanged by this coordinate
conversion. The literal coordinates must not be identified before
converting generators. This character pullback is
part of the comparison; evaluating the regulator instead at the positive
character while retaining the same CM q-family changes the statement.
All formulas below use the unramified branch \(n=-1\) of CH Theorem 3.4.
We do not extend its displayed formula to a different unramified finite
character by inserting or dropping a character factor.

## 2. Which CM component does the full syntomic pairing see?

This step is needed even if the auxiliary global class has not been
proved zero.

At a classical weight \(k=s+1\), the two ordinary CM representations
split at the selected local embedding into crystalline rank-one lines.
Use the labels

\[
 D_g=U_g\oplus H_g,\qquad D_h=U_h\oplus H_h.
\]

Here \(U\) is the unit-root line with filtration degree zero; \(H\) is
the holomorphic line of filtration degree \(s\). The Frobenius
eigenvalues are \((a,b)\) for \((U_g,H_g)\) and \((c,d)\) for
\((U_h,H_h)\). In particular

\[
 ab=\chi_g(p)p^s,\qquad cd=\chi_h(p)p^s,
 \qquad \chi_g(p)\chi_h(p)=1.
\]

Both CM families use the same varying CM type and inverse finite class
characters. Their tensor representation, with the central twist, has the
decomposition recorded in CH (2.4). Locally its four CM lines are:

| Line before the central CM twist | Filtration degree after that twist | Summand |
|---|---:|---|
| \(U_g\otimes U_h\) | \(-s\) | Variable, relaxed at the selected prime |
| \(H_g\otimes H_h\) | \(s\) | Conjugate variable line |
| \(U_g\otimes H_h\) | \(0\) | Auxiliary |
| \(H_g\otimes U_h\) | \(0\) | Auxiliary |

Equivalently, if \(\rho_s\) is the varying CM character and \(\psi\)
the finite class character, the two same-type products give the
\(\rho_s/\rho_s^c\) and conjugate characters; the mixed products give
the fixed \(\psi^2\) and conjugate characters. This is a decomposition
of full representations, before an ordinary elliptic regulator pairing.

Use the dual tensor dictated by Poincaré duality and the central
self-duality, not an unrelated copy of the CM tensor. On each rank-two
CM factor its determinant pairing satisfies

\[
 [H_g,H_g]=[U_g,U_g]=0,\qquad [H_g,U_g]\ne0,
\]

and likewise for \(h\), with the determinant twists retained. Hence
testing against \(\omega_g\otimes\omega_h\in H_g\otimes H_h\)
annihilates both mixed CM lines and the \(H_g\otimes H_h\) class line.
It pairs nontrivially with \(U_g\otimes U_h\).

This remains true for **every elliptic test vector** \(\eta\in D\).
Indeed, for \(s\ge1\), the two holomorphic CM factors already contribute
filtration degree \(2s\ge s+1\), so both elliptic coordinates are
admissible in the filtered target of DR I Theorem 3.8. The full test space
is therefore

\[
            D\otimes L(\omega_g\otimes\omega_h),
\]

not a single elliptic line. Its evaluation on the selected variable
component is the perfect elliptic pairing multiplied by one nonzero
CM scalar.

The corresponding class representation is \(V\otimes\nu_s\), where
the rank-one factor has crystalline multiplier \(acp^{-s}\). Its
filtration jumps are \(-s-1,-s\); consequently

\[
          \operatorname{Fil}^0 D_{\rm dR}(V\otimes\nu_s)=0.    \tag{3}
\]

Thus passing to the Bloch--Kato logarithm loses no elliptic coordinate.
This assertion is specific to the negative-twist classical range. At
weight one the dual exponential has a one-dimensional filtered image.

Ordinary p-stabilization in the modular construction selects a copy of
the full two-dimensional elliptic Galois representation. It must not be
confused with evaluation of a regulator against one ordinary test
vector. In this note the p-degeneracy map to the fixed tame elliptic
realization is the one in the projected edge proposition; it is applied
to the cycle and to the de Rham functional consistently.

### Why the f-stabilization map contributes no hidden Frobenius matrix

This assertion can be checked before taking any p-adic Hodge realization.
The pilot big-image argument in [galois_image/README.md](../galois_image/README.md)
gives \(\operatorname{End}_{G_{\mathbf Q}}(V\otimes L)=L\), for the
coefficient field \(L\) used here. In the f-isotypic p-old space write

\[
                  H_{f,\mathrm{old}}=V\otimes_L M.
\]

The finite-dimensional multiplicity space \(M\) records the degeneracy
copies. Every Galois-equivariant Hecke operator on this space has the
form \(I_V\otimes u\). In particular the ordinary p-stabilization
projector is \(I_V\otimes e_\alpha\); its selected multiplicity line
still carries the whole \(V\). A Galois-equivariant degeneracy or tame
test-vector map to the fixed elliptic realization has the form
\(I_V\otimes\ell\). On that selected copy it is a scalar multiple of
the fixed identity of \(V\), provided it is nonzero. Nonvanishing of
the required maps and Euler denominators at the classical weights is
part of the projected edge comparison.

This is a **global** endomorphism argument. No claim that every local
endomorphism of an ordinary representation is scalar is made. After
applying \(D_{\rm dR}\), the same scalar acts on both elliptic
coordinates. The ratio between two such nonzero identifications is
therefore one of the scalars in (4).

There are two different operations commonly called \(U_p\) in these
calculations. The p-old Hecke operator at level \(Np\) acts on \(M\).
The operator on overconvergent weight-two rigid cohomology at tame level
used in the fixed-weight syntomic proof satisfies \(U_p=pF^{-1}\) and
acts on \(D\). They cannot be substituted for one another. The
F-polynomials \(N,C_s,S_s\) below come from that syntomic primitive
calculation, while \(K_s\) comes from CH interpolation. Neither is a
replacement for the Galois-equivariant multiplicity projector, and no
extra \((1-\beta_f F/p)\)-type matrix may be introduced by identifying
these two meanings of \(U_p\).

## 3. Syntomic AJ is the logarithm of the same étale AJ class

This is a general rational comparison, not an extra reciprocity
conjecture. The published Nekovář--Nizioł paper gives functorial syntomic
period maps, compatibility of the syntomic and étale descent spectral
sequences, and compatible cycle/Chern classes in Theorem A(4), (6), (7).
Its Proposition 1.1 identifies the induced map from the de Rham quotient
to Galois cohomology with the Bloch--Kato exponential. Therefore, where
that exponential is invertible on the selected component, its inverse
identifies syntomic AJ with the Bloch--Kato logarithm of étale AJ.

DR II (81)--(82) writes this same composition explicitly. The paragraph
before its Lemma 3.3 cites the earlier numbering “Nekovář--Nizioł,
Theorem B” for the identification. The published numbering above is the
source to use for the general statement.

**Prime-five qualification.** This comparison is with rational
coefficients for varieties over p-adic fields. It has no hypothesis
\(p\nmid\phi(N)\), no Fontaine--Laffaille weight bound, and no
restriction to the integral family construction in DR II Section 1.6.
The latter restriction fails for this pilot and is not used here. The
family and its projected classical specialization are supplied by the
separate DR22 construction and edge argument. The comparison is then
applied at each fixed classical weight to the projected cycle in its
modular/Kuga--Sato realization, where \(p\nmid N\). All rational
projectors and correspondences can be applied to the comparison diagram
by functoriality.

Here is the exact weight check for our selected component. Each
weight-\(s+1\) CM form is pure of weight \(s\), so each of its
Frobenius roots, including \(a\) and \(c\), has complex absolute value
\(p^{s/2}\). The CM tensor has weight \(2s\); its central twist by
\(s\) makes it weight zero, and in particular
\(|acp^{-s}|_\infty=1\). Equivalently, the rank-one ratio of a CM
character and its conjugate has infinity type \((s,-s)\), whose total
weight is zero. Tensoring with \(V=H^1(E)(1)\), of weight \(-1\),
leaves total weight \(-1\). Thus the selected rank-two crystalline
eigenvalues have complex absolute value \(p^{-1/2}\), not a value
depending on \(s\).

The degree-seven LT comparison preserves this conclusion: since
\(\theta\) and \(\bar\theta\) are complex conjugates with product
\(5^7\), their complex absolute values both equal \(5^{7/2}\).
Consequently \((\theta/\bar\theta)^s\) has absolute value one.
Multiplying this factor by an eigenvalue of \(\varphi^7\) on \(V\)
therefore gives absolute value \(5^{-7/2}\). In particular the linear
seventh iterate has no eigenvalue 1, and semilinear Frobenius has no
fixed vector. Together with (3), the crystalline
fundamental exact sequence gives an isomorphism

\[
 \exp_{\rm BK}:D_{\rm dR}(V\otimes\nu_s)
       \xrightarrow{\ \sim\ }H^1_f(F_{\rm ur},V\otimes\nu_s)
\]

over the appropriate coefficient and base fields. This justifies the
logarithm used here without choosing a complementary Hodge line.

Let \(z_s^{\rm DR}\) be the selected variable component of the
classical DR22 specialization, transported to tame level using the
specified geometric map. The projected edge proposition identifies it
with a nonzero scalar multiple of the projected étale AJ class of the
cusp-corrected DR I cycle. DR I Theorem 3.8 says, for every permitted
elliptic \(\eta\), that the syntomic AJ functional is its pairing with
the full proper syntomic vector \(\Pi\xi_k\).

By Section 2 these evaluations detect exactly the desired rank-two
variable component. By the comparison diagram they are the pairings of
\(\log_{\rm BK}(z_s^{\rm DR})\) with those same two elliptic test
vectors. Nondegeneracy gives

\[
             Z_s=\lambda_s\,\Pi\xi_k,\qquad \lambda_s\ne0,     \tag{4}
\]

after the fixed Tate and rank-one CM untwist. This equality includes
simultaneous vanishing. Its scalar includes the projected edge
normalization, the ordering sign of the cup pairing, and the chosen
rank-one CM period. It does **not** conceal any elliptic matrix.

## 4. LT periods, descent, and the normalized averaging

The exact CM calculation already recorded in the frozen PR note gives

\[
 \theta=-281+4\omega,\quad\bar\theta=-277-4\omega,
 \quad\theta\bar\theta=5^7,
\]

\[
                  (ac5^{-s})^7=(\theta/\bar\theta)^s.          \tag{5}
\]

Here \(\theta\) is a unit at the selected embedding and
\(\bar\theta\) generates \(\mathfrak p^7\). Equation (5), together
with the common inertia character, identifies the rank-one CM twist
with the relative LT twist over \(F_{\rm ur}\). Any unramified
order-seven ambiguity over \(\mathbf Q_5\) becomes trivial after this
restriction. On the connected analytic branch centered at the trivial
character, a residual analytic order-seven quotient is constant and is
fixed by its central value.

Distinguish the two uses of a uniformizer-like parameter in CH:
the multiplier of semilinear crystalline Frobenius on a local LT period
has valuation one, whereas the global generator of \(\mathfrak p^7\)
has valuation seven. The latter controls the seventh Frobenius iterate
and is not to be substituted for the former in a single Frobenius step.

If \(b_s\) and \(b'_s\) are two nonzero bases of the **same** CM
de Rham line, then \(b'_s=c_sb_s\) for \(c_s\ne0\). On
\(D\otimes Lb_s\), the induced change is \(c_s I_D\). In particular
the relative LT/cyclotomic period change, once the rank-one characters
have been matched, can only contribute to \(\lambda_s\) in (4).
No local Schur-lemma assertion about endomorphisms of \(V|_{G_{\mathbf
Q_p}}\) is needed or used.

This rank-one fact alone would **not** justify replacing CH's
\(\sigma_0\)-weighted sum by a trace. For example, if
\(\sigma(u)=-u\), the trace of \((1,u)\) is \((2,0)\), which is
not on the original line. The averaging operator is not scalar on
arbitrary vectors with semilinear coefficients.

Instead use the theorem for the actual averaged map. Package (3.9)
linearly as \(\langle\mathscr P(z),\eta\rangle=\mathrm{Col}^\eta(z)\).
Its \(h_{\boldsymbol e}\), formal-group isomorphism, cyclotomic
period, \(\sigma_0\) translates, and distribution-group factors are
all retained.

Both eigenvector tests are covered by the source, including the one not
used in its later ordinary scalar reciprocity law. In CH Theorem 3.2
the required bound is \(D(V)=\operatorname{Fil}^{-h}D(V)\); here
the same choice \(h=1\) works on the entire rank-two module, as is
explicitly imposed immediately before (3.9). If the two roots of
\(F\) are \(\alpha,\beta\), with \(v_p(\alpha)=0\) and
\(v_p(\beta)=1\), the corresponding \(\varphi\)-eigenvalues are
\(\alpha/p,\beta/p\), of slopes \(-1,0\). The growth statement
in (3.9) therefore places their outputs in \(\mathscr H_0\) and
\(\mathscr H_1\), respectively. Both embed in \(\mathscr H_1\)
and are analytic on the open unit character disk. We change neither
the map nor \(h\) between the two tests. The interpolation statement
of Theorem 3.4 has no restriction to the slope \(-1\) test vector;
that special choice is made later for Theorem 3.6.

The standing eigenvalue condition (3.5) is also a condition on the
whole module. CH verifies it in Section 3.4 by the distinct Weil
weights of elliptic Frobenius and the LT parameter, the same distinction
made above. The standing \(H^0(F_\infty,V)=0\) hypothesis is the one
in the source's elliptic application and is independent of the chosen
test eigenvector.

CH Theorem 3.4, applied at \(j=-s,n=-1\), gives

\[
 \langle\mathscr P(z)(\psi_{-s}),\eta\rangle
 =\frac{(-1)^{s+1}}{(s-1)!}
       \langle Z_s,A_{-s}(\varphi)\eta\rangle,
\quad
 A_j(\varphi)=(1-p^{j-1}\varphi^{-1})
                         (1-p^{-j}\varphi)^{-1}.               \tag{6}
\]

The \(Z_s\) here includes the theorem's displayed cyclotomic
\(t^s\) untwist. Equation (4) is interpreted after precisely this
untwist. Apply (6) to both independent eigenvectors. Nondegeneracy and
(1), without an assumption about raw trace or raw averaging, force

\[
 \boxed{\displaystyle
 \mathscr P(z)(\psi_{-s})
 =\frac{(-1)^{s+1}}{(s-1)!}K_s(F)Z_s,\qquad
 K_s(F)=(1-p^{-s-1}F)(1-p^sF^{-1})^{-1}.}            \tag{7}
\]

Thus all effects of normalized averaging are already represented in
(7). An additional elliptic operator at these specializations would
contradict (6) on at least one of the two test vectors. This proves the
needed statement about the **actual normalized map**, without claiming
that its raw averaging operator is universally scalar.

## 5. Consequence for the analytic projective comparison

Keep the definitions from the frozen fixed-weight calculation:

\[
\begin{split}
 N(F)&=1-F^2/p^2,\\
 C_s(F)&=(1-a\chi_h(p)F/(cp))(1-\chi_g(p)cF/(ap)),\\
 S_s(F)&=(1-p^{s+1}F^{-1}/(ac))(1-p^{s-1}F/(ac)),\\
 A_k&=\Pi[d^{-s}g_k^{[p]}h_k].
\end{split}
\]

The exact identity \(K_s=-p^{-s-1}F R_s\), with
\(R_s=(1-p^{s+1}F^{-1})(1-p^sF^{-1})^{-1}\), cancels the factorial,
power of p, and inverse Frobenius in the fixed-weight syntomic vector.
Equations (4) and (7) therefore give

\[
 \mathscr P_{\rm DR}(\psi_{-s})
   =\frac{\lambda_s\epsilon_k}{ac}
                 R_s S_s^{-1} C_s^{-1}N A_k.                  \tag{8}
\]

The retained \(\epsilon_k\) is the global syntomic sign. It is
nonzero and irrelevant projectively. No value of \((s-1)!\) or
\(p^s\) is assigned at \(s=0\).

Assume the analytic q-family and its proper projection are defined on
the weight disk used in the existing calculation, and pull the actual
DR regulator back by the character map (2). Along
\(s_n=4\cdot5^n\), the exact identities (8) satisfy the hypotheses
of [PROJECTIVE_INTERPOLATION.md](../fixed_weight_syntomic/PROJECTIVE_INTERPOLATION.md):
the errors in \(R_{s_n}\) and \(S_{s_n}\) have valuations at least
\(s_n-O(1)\). The analytic wedge argument gives

\[
 \boxed{\qquad
      (C(W)N(F)^{-1}\mathscr P_{\rm DR}(W))\wedge A(W)=0.
      \qquad}                                                 \tag{9}
\]

This uses no bound on the nonzero scalars \(\lambda_{s_n}\). Any
generic proportionality of the DR and CH global classes in the same
Selmer module transfers (9) to CH after the same character pullback.
The proportionality scalar may be meromorphic at augmentation; for
this projective identity it need not be a unit. Vanishing orders and
global division are separate matters.

Consequently the comparison of the first nonzero vectors uses the
leading matrix \(K_0=C(0)^{-1}N(F)\). This notation is not a
substitution of \(s=0\) into \(K_s\): the matrix is obtained after
fixed-weight cancellation and the analytic wedge argument. With
\(\tau=\zeta_7^3+\zeta_7^4\), the exact frozen calculation is

\[
 K_0=\frac{3[(5\tau+11)+2(\tau+1)F]}{5\tau^2+18\tau+25},
 \qquad
 K_0^{-1}=\frac{(5-\tau)-2(\tau+1)F}{9}.                       \tag{10}
\]

This operator is generally non-scalar. It is the explicit Frobenius
comparison already derived, not an unidentified new averaging effect.

## 6. The base image and its annihilator

At \(j=0\), the same normalized CH interpolation formula uses the
dual exponential. Its image is in the filtered Hodge line. Therefore
the base regulator image satisfies

\[
 \operatorname{im}\mathscr P_0
 \subseteq A_0(\varphi)^\dagger\Omega\omega_E.
\]

For the pilot, direct reduction in \(\mathbf Q[F]/(F^2+3F+5)\) gives

\[
 A_0(\varphi)=\frac{59+13F}{45},\quad
 \det A_0=1,\quad
 A_0^\dagger=A_0^{-1}=\frac{20-13F}{45}.
\]

Set

\[
 \zeta=\frac{20-13F}{45}\omega_E,
 \qquad\lambda(v)=\langle v,\zeta\rangle.
\]

The alternating pairing then proves the needed assertion

\[
                     \lambda\mathscr P_0=0.                  \tag{11}
\]

Only the image containment is needed. No assertion of surjectivity,
exact determinant order, or a calibrated finite logarithm constant is
required for (11).

Combining (10) with this source-derived annihilator yields the line to
test in the computed \(A\)-coordinates:

\[
 K_0^{-1}\zeta
   =-\frac{(10+50\tau)+(61+35\tau)F}{135}\omega_E.             \tag{12}
\]

The arithmetic use of (12) for the named CH class requires the global
transfer stated above. No nonzero finite localization has been used to
derive (4), (7), (9), or (11).

## 7. Inputs still needed for the larger research claim

| Input | Status in this note |
|---|---|
| Fixed-weight full syntomic vector, including proper projection | Uses the frozen deduction in `fixed_weight_syntomic/` |
| Rational projected DR22 specialization at `(2,k,k)` | Uses the explicit edge proposition in `leading_comparison/` |
| Correct CM component and both elliptic logarithm coordinates | Proved in Sections 2--3 |
| Syntomic/étale AJ compatibility at prime five | General published rational comparison; Section 3 |
| Matched CM/LT rank-one twist | Exact arithmetic from the frozen note, used in Section 4 |
| Full normalized CH local operator | Determined by both tests in CH Theorem 3.4; Section 4 |
| Analytic projective continuation | Existing wedge lemma, applied in Section 5 |
| Named CH class versus the DR22 class | Separate global comparison or generic rank-one argument |
| Global division, correct local Selmer condition, and a nonzero finite logarithm | Not concluded by this note |

The new exact checker is:

```sh
python3 research/bsd-localization/normalized_local_comparison/check_linear_algebra.py
```

It verifies the CM tensor-selection matrix, reconstruction from two test
coordinates, the adjoint \(K_s\), the pilot base-image annihilator,
and a counterexample to an unweighted-trace shortcut. The full geometry
and source hypotheses remain mathematical proof obligations rather than
claims made by this executable.
The companion-matrix realization also does not certify that the actual
Néron differential and its Frobenius translate form a basis in the
independent numerical realization; that check belongs to that
realization. The polynomial-in-F formulas above do not require it.

## Primary sources

* Castella--Hsieh, *On the nonvanishing of generalised Kato classes for
  elliptic curves of rank 2*: [published HTML](https://www.cambridge.org/core/journals/forum-of-mathematics-sigma/article/on-the-nonvanishing-of-generalised-kato-classes-for-elliptic-curves-of-rank-2/72ED842AB428A7ED619B1B84287A6864),
  [author PDF](https://web.math.ucsb.edu/~castella/Kato-print.pdf).
  Relevant locations: (2.4); Section 3.1, especially (3.2); Definition
  3.3; (3.7)--(3.9); Theorem 3.4; (3.12)--(3.14).
* Darmon--Rotger, *Diagonal cycles and Euler systems I*: [author PDF](https://www.math.mcgill.ca/darmon/pub/Articles/Research/62.DR-Diagonal1/paper.pdf).
  Definition 3.2, (65)--(66), (73)--(78), and Theorem 3.8; its proof
  explicitly includes the case with first exponent zero.
* Darmon--Rotger, *Diagonal cycles and Euler systems II*: [author PDF](https://web.mat.upc.edu/victor.rotger/docs/DR2.pdf).
  (81)--(82), printed pp.26--27, and the paragraph before Lemma 3.3,
  printed p.34. These are used to identify the comparison diagram, not
  to bypass that paper's integral-family hypotheses.
* Nekovář--Nizioł, *Syntomic cohomology and p-adic regulators for varieties
  over p-adic fields*, Algebra & Number Theory 10 (2016), 1695--1790:
  [published PDF](https://msp.org/ant/2016/10-8/ant-v10-n8-p04-p.pdf).
  Theorem A(4), (6), (7), printed p.1697; Proposition 1.1 and following
  comparison discussion, printed p.1698. This published numbering
  replaces the preprint “Theorem B” cited in DR II.
