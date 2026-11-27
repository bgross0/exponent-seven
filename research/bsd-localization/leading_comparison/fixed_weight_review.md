# Independent review: full fixed-weight Frobenius comparison

Date: 2026-11-27. Scope: read-only mathematical review of
`fixed_weight_syntomic/README.md`; no changes to that note or its checker.

## Verdict

The **projective** identity is supported by the argument, under the stated
geometric setup, genuine overconvergence, proper projection, and fixed
classical-weight hypotheses. In the notation of the reviewed note, put

\[
 A_k=\Pi[d^{1-k}g^{[p]}h],\qquad
 R_k(F)=\frac{1-\chi_f(p)^{-1}F^2/p^2}
 {\prod_{u\in\{a,b\},v\in\{c,d\}}(1-uvF/p^k)}.
\]

At every fixed integer \(k\ge2\), the supported conclusion is

\[
 \Pi\xi_k\wedge R_k(F)A_k=0.
\]

The primitive calculation supplies a nonzero proportionality scalar, of
absolute normalization \((k-2)!\) in the source's contraction conventions,
with an unresolved overall sign. Consequently either vector vanishes if
and only if the other does. When they are nonzero, this is the equality
of projective lines

\[
 [\Pi\xi_k]=[R_k(F)A_k].
\]

This is more information than the ordinary scalar formula alone. It
does **not** identify a weight-one Perrin--Riou regulator or prove an
arithmetic family interpolating these full vectors.

## 1. Genuine overconvergence is available here

The use of \(G=d^{1-k}g^{[p]}\) is justified by the source's actual
overconvergent \(\mathcal L_r\)-valued primitive, with \(r=k-2\).
Projecting that primitive through the algebraic Hodge quotient

\[
 \mathcal L_r/\operatorname{Fil}^1\mathcal L_r\simeq\omega^{-r}
\]

gives a genuine overconvergent section. Equations (47), (98), and (99)
give its Fourier expansion as \((-1)^r r!G\). The nonzero scalar can be
divided out at each fixed weight. This argument does not appeal to a
finite Fourier fit, and does not assume that arbitrary intermediate
derivatives of a negative-weight form remain modular.

The same applies to \(H=d^{1-k}h^{[p]}\). Each finite list of their
products with \(V^j g,V^j h\) is defined on a common smaller strict
neighborhood. The cusp-form hypotheses ensure the resulting weight-two
differentials are regular at the cusps.

## 2. The discarded terms vanish before ordinary projection

The identity

\[
 U(J\,VK)=(UJ)K
\]

holds for the stated Fourier normalizations. Since \(UG=UH=0\), the
products \(GV^jh\) and \((V^jg)H\), for \(j\ge1\), are killed by \(U\).
On weight-two rigid cohomology the source gives

\[
 F=pV=pU^{-1}.
\]

Thus their cohomology classes are zero. This is an argument in the full
rigid group, and entails zero residues as well. It justifies all four
replacements in Section 2 of the reviewed note; no information is lost
by an ordinary projection at this step.

One should cite the **proof** of DR Lemma 2.2 for this operator relation.
Its statement concerns the ordinary comparison and is not itself a
general statement that arbitrary overconvergent forms have a single
Frobenius slope.

## 3. Relative contraction sign and factorial

Calibrating the contraction by DR (49) gives

\[
 C(\mathcal G,\omega_h)=(-1)^r r!Gh,\qquad
 C(\omega_g,\mathcal H)=r!gH.
\]

The second expression differs because reversing the alternating fiber
pairing in each of the \(r\) factors contributes \((-1)^r\).
Horizontality of the pairing therefore implies

\[
 dC(\mathcal G,\mathcal H)
 =r!\bigl(g^{[p]}H+(-1)^rGh^{[p]}\bigr)dq/q.
\]

Using Section 2, the exactness yields

\[
 \Pi[gH]=(-1)^{r+1}\Pi[Gh].
\]

Accordingly, the two terms in the raw primitive bracket combine to
\(2(-1)^r r!A_k\). The relative sign and factorial in this conclusion
are checked. The ambiguity below is the **overall** sign of the raw
primitive, not this relative calculation.

## 4. Tate twist, Euler numerator, and invertibility

The contraction takes values in \(H^1(-r)\). Fixing a Tate basis gives
\(\Phi_{(-r)}=p^rF\). The original factor

\[
 1-uvp^{-2k+2}\Phi_{(-r)}
\]

therefore becomes \(1-uvF/p^k\). Omitting \(p^r\) would give the wrong
operator on the second Frobenius coordinate.

The four-term partial-fraction identity has numerator
\(1-abcdz^2\). With
\(abcd=\chi_f(p)^{-1}p^{2k-2}\) and \(z=F/p^k\), it is exactly
\(1-\chi_f(p)^{-1}F^2/p^2\).

On the proper elliptic summand the complex absolute values of the
eigenvalues of \(uvF/p^k\) and
\(\chi_f(p)^{-1}F^2/p^2\) are respectively \(p^{-1/2}\) and \(p^{-1}\).
All denominator factors and the numerator are consequently invertible.
This is a purity argument at a fixed classical weight, not an assertion
that these operators have integral inverses for a selected \(p\)-adic
lattice.

The reviewed checker was rerun successfully. Its exact polynomial
checks support these algebraic manipulations; they do not independently
check the geometric input or the unresolved global sign.

## 5. Proper projection and the cusp basepoint

Keeping \(\Pi\) is essential. The unprojected class of \(Gh\) need not
be proper. The canonical Frobenius-equivariant retraction onto proper
cohomology is legitimate because the proper and residue spectra have
different complex weights. Besser's Section 2 describes this retraction
explicitly.

Multiplying \(P_{gh}\) by a residue-annihilating polynomial \(S\) repairs
the source's condition (ii) before Lemma 3.4. Taking
\(S(\Phi)\rho\), projecting to the proper summand, and only then
cancelling \(S(\Phi)\) is valid: the roots of \(S\) can be confined to
the residue spectrum and hence avoid the proper spectrum. There is no
need to invert \(S\) on the entire open rigid cohomology group.

At \(k=2\), the infinity-cusp basepoint and the zero-constant primitives
must be retained. Besser Remark 4.3 explicitly states that this
basepoint assumption is implicit in DR (95); changing the basepoint can
add Abel--Jacobi terms. The current draft includes the necessary
condition.

## 6. The overall sign is not independently settled

The author PDF states in (91)--(93) that \(d\rho_{ac}=\theta_{ac}\),
but (94) puts a minus before the primitive bracket. With the standard
left-factor-first tensor differential,

\[
 d\bigl(G\otimes\omega_h-\omega_g\otimes H\bigr)
 =g^{[p]}\otimes\omega_h+\omega_g\otimes h^{[p]}.
\]

Thus the displayed leading minus would differentiate to
\(-\theta_{ac}\). This is present also in the publisher's version,
equations (3.30)--(3.33), printed pages 818--819; it is not a lone text
extraction artifact. DR Lemma 3.4 uses the ordered wedge
\(\omega_2\wedge\omega_3\). A different tensor/Kunneth convention
could account for the sign, but this review did not locate an explicit
convention resolving the discrepancy.

The ordinary theorem consistently retains the minus. Merely matching
that printed scalar formula is therefore not an independent audit of
the signed full Abel--Jacobi normalization. Besser's positive-looking
formula likewise cannot be substituted without comparing its cup and
cycle conventions.

The revised note correctly retains a symbolic sign and claims the
projective operator identity. The sign can even be allowed to depend on
\(k\); constancy of that sign is unnecessary for the projective
conclusion. The published formulas do not have to be declared wrong in
order to keep this unresolved convention explicit.

## 7. Conditional superflat continuation

There is a useful abstract consequence **if** full arithmetic
specializations are subsequently supplied. Let \(Z(W)\) and \(Y(W)\)
be analytic vectors in one fixed two-dimensional space on a disk about
zero. Let \(W_n\to0\), with \(v_p(W_n)=n+O(1)\), and suppose

\[
 Z(W_n)\wedge S_n^{-1}Y(W_n)=0,\qquad
 v_p(S_n-I)\ge c p^n-C
\]

for some positive \(c\) and bounded \(C\). For large \(n\),
\(S_n^{-1}\) is uniformly bounded and obeys the same error bound.
Analytic vectors are bounded on a smaller closed disk, so

\[
 v_p\bigl(Z(W_n)\wedge Y(W_n)\bigr)\ge c p^n-C'.
\]

If the analytic scalar \(D(W)=Z(W)\wedge Y(W)\) were nonzero with
order \(m\) at zero, its leading term would instead give
\(v_p(D(W_n))=m n+O(1)\) for large \(n\). This is impossible. Hence
\(D\equiv0\). No bound on a separate projective proportionality scalar
is needed: the wedge identity eliminates that scalar directly.

For \(k_n=1+(p-1)p^n\), the factors called \(S_k(F)\) in the reviewed
note have this superflat behavior. The analytic operator with the
remaining unit-root factors can be used to define \(Y\), provided its
denominators are invertible near the center. But constructing an
analytic arithmetic \(Z\) whose **full vectors** have those classical
specializations is still a hypothesis. An ordinary scalar reciprocity
law alone does not supply it. A projective identity also does not by
itself specify the first nonzero jet when either vector vanishes at the
center; their individual orders must be tracked or factored out.

## Primary references inspected

- Darmon--Rotger, *Diagonal cycles and Euler systems I*,
  [47-page author PDF](https://web.mat.upc.edu/victor.rotger/docs/DR1.pdf):
  proof of Lemma 2.2; Proposition 2.9 and (47)--(49); Lemma 3.4 and
  Proposition 3.7; Theorem 3.8; (91)--(103).
- [Publisher PDF, Ann. Sci. ENS 47 (2014), 779--832](https://smf.emath.fr/system/files/2017-08/ens_ann-sc_47_779-832.pdf):
  (3.30)--(3.35), (3.37)--(3.42), Theorem 3.13. Checked separately for
  the overall-sign issue.
- Besser, *On the regulator formulas of Bertolini, Darmon and Rotger*
  (2016), [published article](https://link.springer.com/article/10.1186/s40687-016-0073-x):
  Section 2, Theorem 4.2, and Remark 4.3.
