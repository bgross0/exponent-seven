# A full Frobenius projective identity at the classical weights (2,k,k)

Date: 2026-11-27.

## Result and boundary

At every **fixed integer k >= 2**, the terms discarded by the ordinary
projection in Darmon--Rotger I's calculation can be discarded in full
weight-two rigid cohomology. After projecting to proper cohomology this
gives the projective operator identity (8p) below, with both elliptic
Frobenius coordinates retained. The scalar form (8) retains an explicitly
unresolved global sign; its relative contractions, factorial and powers of
p are computed. This is a deduction from their primitive construction,
not a claim that their stated ordinary theorem itself supplies a new
family reciprocity law.

The deduction uses the actual overconvergent sections, not finite Fourier
series. The two reasons are that a U-annihilated weight-two differential is
exact, and that the contraction now has rank-zero coefficients. A separate
weight-one interpolation argument is necessary. Its nonanalytic factors
are displayed explicitly in Section 6.

**Global sign boundary.** Let epsilon_DR be the overall sign multiplying
the raw rho contribution before fibre contraction. The source displays
epsilon_DR=-1 in (94) and its general-weight counterpart, and that value
agrees with its (102) and Theorem 3.13. Under the standard exterior-product
interpretation, however, differentiating the bracket in (94) seems to give
the positive expression (92), whereas (91)--(94) display a negative
prefactor. Besser's weight-two formula uses a positive overall sign. The
same displayed minus persists in the published DR version, (3.30)--(3.34),
[pp. 818--819](https://www.numdam.org/item/10.24033/asens.2227.pdf).
This note does not resolve that cross-convention / source sign issue.
Consequently its claim is the projective identity; signed formulas below
retain epsilon_DR symbolically. No exact globally signed Abel--Jacobi
comparison is certified here.
The symbol may depend on k; no weight-independent choice of this sign is
needed or asserted for the projective result.

### Primary source

Henri Darmon and Victor Rotger, *Diagonal cycles and Euler systems I:
A p-adic Gross--Zagier formula*,
[author PDF](https://www.math.mcgill.ca/darmon/pub/Articles/Research/62.DR-Diagonal1/paper.pdf).
References below use the equation and theorem numbers of this 47-page
author version, not a guessed transcription from its text extraction.

| Input | Exact source location |
|---|---|
| Weight-two forms as differentials; p-depletion is exact | (18)--(19), printed pp. 11--12 |
| Frobenius and U on cohomology | Proof of Lemma 2.2: Phi = p V = p U^{-1}, printed p. 12 |
| Negative-weight Bol lift and rigid quotient | (23), (36)--(39), printed pp. 13, 16 |
| Coleman primitives and contraction convention | Proposition 2.9, (47)--(49), printed p. 19 |
| Product U-annihilation | Lemma 2.17, printed p. 24 |
| Properness, polynomial independence, full Abel--Jacobi pairing | Proposition 3.7, (72), Theorem 3.8 / (74), printed p. 30 |
| Four primitive contributions | (94)--(95), (98)--(100) and the displayed rho-alpha-alpha formula after (100), printed pp. 36--38 |
| Ordinary scalar check | (96), (102)--(103), Theorems 3.13--3.14, printed pp. 36--38 |

Two useful independent qualifications appear in Amnon Besser,
[*On the regulator formulas of Bertolini, Darmon and Rotger*](https://link.springer.com/article/10.1186/s40687-016-0073-x)
(2016): Section 2 describes the unique Frobenius-equivariant proper
retraction used in its (2.11), and Remark 4.3 explicitly identifies the
cusp-basepoint assumption in DR (95). No cross-paper cup-product sign
convention is silently substituted.

## 1. Conventions and hypotheses

Let p > 2 and p not divide N. Work on the tame modular curve X of the
source, with its ordinary wide open, over a coefficient field containing
the needed Hecke roots. Extend the geometric Frobenius **linearly in the
coefficient field**. Write F for its action on untwisted weight-two
cohomology. Thus U = p F^{-1}; this is not arithmetic Galois Frobenius
acting semilinearly on coefficient constants.

Let f have weight 2, and let g,h be classical cuspidal eigenforms of the
same weight k >= 2, with

    chi_f chi_g chi_h = 1,       r = k-2.

The tame test forms may be oldforms in the prescribed eigenspaces. Use
the source's normalized fibre contractions, symmetrizing projectors and
cycle Delta_(2,k,k). At k=2 choose its base point to be the infinity cusp
and the primitives to have zero constant term. This makes the horizontal
and vertical terms of the modified diagonal pullback vanish as in (95).
No conversion to a different cycle normalization is made here.

Write a,b for the two p-Hecke roots of g and c,d for those of h:

\[
 ab=\chi_g(p)p^{k-1},\quad cd=\chi_h(p)p^{k-1},
 \quad a\ne b,\ c\ne d,\quad \Delta=(a-b)(c-d).
\]

Distinct roots are enough for the displayed partial-fraction derivation.
The ordinary CM specializations under study satisfy this. We make no
extension to repeated roots here. Label a,c as the unit roots when
discussing ordinary families in Section 6.

The forms and operators have the following normalizations:

\[
 Vj(q)=j(q^p),\quad dj=q\frac{dj}{dq},\quad
 g_a=g-bVg,\quad h_c=h-dVh,
\]

where d on the right of h_c is the Hecke root; the differential operator
will always have an argument or an exponent. In particular,

\[
 g^{[p]}=(1-aV)(1-bV)g,\qquad
 h^{[p]}=(1-cV)(1-dV)h.
\]

Let Pi be a Frobenius-equivariant **proper** projection followed by a tame
Hecke projection to the f-star summand, or a specified map from that
summand to the elliptic curve. In the pilot chi_f=1, so the star has no
effect. Proper cohomology is the zero-residue subspace of rigid
cohomology. One may first take its Frobenius spectral summand: proper
eigenvalues have complex absolute value sqrt(p), whereas the residue
quotient has eigenvalues of absolute value p. This gives a canonical
Frobenius-equivariant retraction before the tame projection.

It is essential to keep this proper projection. We do not assert that the
unprojected inverse-Bol product has zero annular residues.

## 2. All discarded product terms are exact

Set

\[
 G=d^{1-k}g^{[p]},\quad H=d^{1-k}h^{[p]},\quad
 A=\Pi[Gh],\quad B=\Pi[gH].                         \tag{1}
\]

These G,H are overconvergent forms of weight 2-k, not just formal inverse
derivatives. Indeed the source's primitives are overconvergent sections
of L_r. Their projections to the quotient L_r / Fil^1 = omega^{-r}
have q-expansions (-1)^r r! G and (-1)^r r! H, by (47)/(98)/(99).
Dividing by the nonzero scalar (-1)^r r! proves the assertion. Thus every
product used next is a genuine overconvergent differential of weight two,
on a common smaller wide open if necessary.

For any two q-series J,K,

\[
 U(J\,VK)=(UJ)K.
\]

Since UG=UH=0, each individual product

\[
 G V^j h,\qquad (V^j g)H\qquad (j\ge1)             \tag{2}
\]

is U-annihilated. In rigid weight-two cohomology, U=p F^{-1} is
invertible. Therefore all the differentials in (2) have zero rigid
cohomology class. In particular they have zero residues and give zero
in proper cohomology; no ordinary projection is needed.

This proves all four replacements needed by the source calculation:

\[
\begin{split}
 &[G(1+cV)h_c]=[Gh],\
 &[(1+aV)g_aH]=[gH],\
 &[G h^{[p]}]=[Gh],\
 &[g^{[p]}H]=[gH].
\end{split}                                                   \tag{3}
\]

For example (1+cV)h_c-h=(c-d)Vh-cdV^2h. Every term removed in this
equality is one of (2). Equations (2)--(3) are equalities in rigid
cohomology even before Pi is applied.

## 3. The sign and factorial

Let script-G, script-H be the L_r-valued primitives in (98)--(99).
Their connections are omega_(g^[p]) and omega_(h^[p]). Let C denote the
horizontal contraction L_r tensor L_r -> O(-r), in the convention of
(48)--(49). Its two orientations give

\[
\begin{split}
 C(\mathcal G,\omega_h)&=(-1)^r r!\,Gh\,dq/q,\
 C(\omega_g,\mathcal H)&=r!\,gH\,dq/q.              \tag{4}
\end{split}
\]

To see the second sign rather than guess it, only the eta^r coefficient
of the primitive survives pairing with omega^r. That coefficient is
(-1)^r r! times the inverse-Bol form. Equation (49) fixes the orientation
of the first contraction. Reversing the symplectic pairing in each of
the r fibre factors multiplies it by (-1)^r. Consequently the coefficient
of the second contraction is r!, not (-1)^r r!.

By horizontality of C,

\[
 d C(\mathcal G,\mathcal H)
 =r!\{g^{[p]}H+(-1)^r G h^{[p]}\}\,dq/q.
\]

It follows from exactness and (3) that

\[
 B=(-1)^{r+1}A=(-1)^{k-1}A.                         \tag{5}
\]

Equivalently, a scalar primitive is supplied, up to a nonzero constant,
by the genuine weight-zero bilinear concomitant

\[
 R(G,H)=\sum_{j=0}^{k-2}(-1)^j
       (d^{k-2-j}G)(d^jH),
\]

whose derivative is g^[p]H+(-1)^(k-2)Gh^[p]. Its intrinsic construction
is C(script-G,script-H)/r!; one need not incorrectly declare each
intermediate derivative separately overconvergent modular.

**Transcription safeguard.** Display (101) in the inspected author PDF
does not visibly include all the contraction sign/factorial factors that
appear in (49) and are restored in (102). For this specialization the
proof uses the raw rho formula after (100) and the two contractions (4).
It does not treat the scalar-looking (101) as an independently normalized
full-cohomology formula.

## 4. Four contributions and the exact operator identity

Put

\[
 P_{gh}(X)=\prod_{u\in\{a,b\},\,v\in\{c,d\}}
                  (1-uvp^{-2k+2}X),
 \qquad P_{uv}(X)=P_{gh}(X)/(1-uvp^{-2k+2}X).
\]

Contraction puts the target in H^1(X)(-r). With a fixed Tate basis its
Frobenius is

\[
 \Phi_{(-r)}=p^r F.                                  \tag{6}
\]

For example the raw rho_(a,c) term after (100) has coefficient
epsilon_DR ac/(2 Delta) and bracket

    script-G tensor (1+cV) omega_(h_c)
      - (1+aV) omega_(g_a) tensor script-H.

Contracting by (4), using (3), and then (5), turns this bracket into
2(-1)^r r! A. Its proper class is therefore

\[
 \Pi\xi_{ac}
 =\epsilon_{\rm DR}(-1)^r r!\frac{ac}{\Delta}
                         P_{ac}(p^rF)A.
\]

The same fixed-denominator convention and alternating signs as
(97)/(103) give the other three contributions. Dividing by P_gh as in
(72) yields

\[
 \Pi\xi(\omega_g,\omega_h)
 =\epsilon_{\rm DR}(-1)^r r!\frac1\Delta
   \left\{\frac{ac}{1-acF/p^k}
          -\frac{ad}{1-adF/p^k}
          -\frac{bc}{1-bcF/p^k}
          +\frac{bd}{1-bdF/p^k}\right\}A.            \tag{7}
\]

The p^k follows from p^(-2k+2) p^(k-2)=p^(-k); omitting the Tate
factor changes this exponent. The polynomial identity

\[
 \frac1{(a-b)(c-d)}
 \sum_{u,v}\epsilon_u\epsilon_v\frac{uv}{1-uvz}
 =\frac{1-abcdz^2}{\prod_{u,v}(1-uvz)}
\]

has epsilon_a=epsilon_c=1 and epsilon_b=epsilon_d=-1. Substituting
z=F/p^k and abcd=chi_f(p)^(-1)p^(2k-2) proves

\[
\boxed{
 \Pi\xi(\omega_g,\omega_h)
 =\epsilon_{\rm DR}(-1)^{k-2}(k-2)!\,
 \frac{1-\chi_f(p)^{-1}F^2/p^2}
 {\displaystyle\prod_{u\in\{a,b\},v\in\{c,d\}}
                 (1-uvF/p^k)}
 \,\Pi[d^{1-k}g^{[p]}h].}                            \tag{8}
\]

With the stated global-sign boundary, this is an identity of proper
cohomology vectors, not just their pairing with the ordinary unit-root
test vector. Its sign-independent, certified content is

\[
\boxed{
 \Pi\xi(\omega_g,\omega_h)
 \ \parallel\ 
 \frac{1-\chi_f(p)^{-1}F^2/p^2}
 {\displaystyle\prod_{u,v}(1-uvF/p^k)}
 \,\Pi[d^{1-k}g^{[p]}h].}                            \tag{8p}
\]

Here parallel means equality up to the stated nonzero scalar, so it also
asserts simultaneous vanishing. At a nonzero specialization it identifies
the actual projective line. Evaluating the operator on the
ordinary modular-form component, where F has eigenvalue beta_f, recovers
the specialization of (102)--(103) / Theorem 3.13 if epsilon_DR=-1 is
used, as printed there. This checks the relative normalization without
purporting to settle the independent overall-sign issue or assuming an
ordinary scalar equality determines a second coordinate.

All denominator factors in (8) are invertible on the proper f-star
component: uv has complex absolute value p^(k-1), an eigenvalue of F has
absolute value sqrt(p), and uvF/p^k consequently has absolute value
p^(-1/2). The numerator is invertible there as well, since its subtracted
term has absolute value p^(-1). These assertions use classical purity at
this fixed weight, not a p-adic unit estimate.

### Residue polynomial required by the source definition

P_gh alone need not annihilate every annular residue target required in
the setup preceding Lemma 3.4. Choose a further polynomial S satisfying
that requirement and invertible on proper cohomology. Use
P=S P_gh in (72), and S(Phi)rho_gh as its primitive. After proper
projection, S(Phi) cancels from

    (S P_gh)(Phi)^(-1) S(Phi) Pi[xi_gh].

This justifies (7) without assuming individual xi_uv have zero residues
or trying to invert a possibly singular polynomial on the residue
quotient. The source's Proposition 3.7 supplies properness of the final
syntomic class; our derivation only inverts polynomials after Pi.

## 5. What normalizations have and have not been transferred

The identity uses the source's full syntomic vector xi and its cycle.
Theorem 3.8 pairs that vector with every permitted weight-two de Rham
test vector. Thus (8p), inserted there, determines the corresponding full
fixed-weight Abel--Jacobi functional projectively. An exact signed
functional still requires the global-sign reconciliation stated above.

A geometric tame trace, degeneracy correspondence or elliptic projector
commuting with F can be applied to both sides. Any scalar normalization
of that map remains on both sides. For example the project's 1/62
normalization is part of its chosen Pi, not an additional factor inserted
into (8). For a raw prime-to-p oldform V_l g one must keep

    d^(1-k)(V_l g) = l^(1-k) V_l(d^(1-k)g).

No factor from changing that raw q-map to a differently normalized
geometric pullback is silently dropped.

The present note makes no identification between this cycle and a
particular normalized Castella--Hsieh / Castella--Do Iwasawa class. Nor
does it insert a Hida congruence period, an ordinary f-stabilization
factor, a Bloch--Kato comparison, or a Perrin--Riou regulator factor.
Those factors belong to the separate arithmetic comparison and must be
specified there. The ordinary scalar formula alone does not fix them as
operators on both coordinates.

## 6. Exact location of the weight-one problem

Write

\[
 q_k=p^{k-1},\quad b=\chi_g(p)q_k/a,\quad
 d=\chi_h(p)q_k/c,\quad
 N(F)=1-\chi_f(p)^{-1}F^2/p^2.
\]

Here q_k is a scalar, unrelated to the modular q-expansion parameter.
Let

\[
 C(F)=\left(1-\frac{a\chi_h(p)}{cp}F\right)
       \left(1-\frac{\chi_g(p)c}{ap}F\right),
\]

and

\[
 S_k(F)=\left(1-\frac{p q_k}{ac}F^{-1}\right)
         \left(1-\frac{\chi_f(p)^{-1}q_k}{p ac}F\right).
\]

An exact factorization of the denominator in (8) is

\[
 D_k(F)=-\frac{ac}{p q_k}F\, S_k(F)\, C(F).          \tag{9}
\]

Consequently (8) can also be written

\[
 \Pi\xi_k=-\epsilon_{\rm DR}(-1)^{k-2}(k-2)!\,
       \frac{p^k}{ac}\,
       S_k(F)^{-1} C(F)^{-1}F^{-1}N(F) A_k.           \tag{10}
\]

This is a fixed-integer identity. There are three separate issues before
it becomes a weight-one statement:

1. p^(k-1) has no analytic extension on a weight disk with the indicated
   classical values. Along k_n=1+(p-1)p^n, it tends to 0 although its
   literal value at k=1 is 1. In particular one cannot substitute k=1
   into S_k or into the nonunit Hecke-root formula.
2. (k-2)! has no literal value at k=1 and its classical valuations grow
   along that sequence. It cannot be replaced by a guessed p-adic gamma
   factor without a normalization theorem.
3. The Tate twists and syntomic Abel--Jacobi vectors at different k must
   first be identified with specializations of an actual arithmetic
   family. Equation (8) alone constructs no such identification.

For **projective** identities the nonzero scalar
(-epsilon_DR)(-1)^(k-2)(k-2)! p^k/(ac) cancels at every classical weight. The two
operator factors in S_k do not cancel this way. They satisfy
S_k=I+O(p^(k-2)) along the sequence above, and their exact treatment is
what remains before a projective family comparison can be asserted.

`PROJECTIVE_INTERPOLATION.md` proves the precise conditional continuation:
if a full analytic arithmetic de Rham vector is projectively identified
with these syntomic vectors at all those classical weights, the factors
S_k can be removed from the analytic projective comparison. Its proof is
a wedge-product vanishing-order argument, not substitution at k=1. The
existence and required identification of that arithmetic family remain
explicit premises.

The companion `check_identity.py` verifies the polynomial numerator in
(7)--(8), the Tate/root normalization of that numerator, and the exact
denominator factorization (9) in a Laurent polynomial ring over the
rationals. It is a checker for these algebraic manipulations; it does not
verify the cited geometric theorems or establish the missing arithmetic
interpolation.
