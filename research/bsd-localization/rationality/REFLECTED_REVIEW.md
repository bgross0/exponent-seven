# Independent review of the reflected relaxed-class construction

Date: 2026-11-27. Scope: review of Section 6 of `../derived_global/DERIVED_CLASSES.md`. No pilot computation was repeated. The conclusion is the existence of a **possibly zero** Selmer class; this note makes no nonzero-logarithm claim.

## Verdict

The construction is valid under the actual Castella–Hsieh setup and augmentation order at least two. Global division can be performed in their original bounded-coefficient Iwasawa module. Their Theorem 4.5 establishes the specialized finite condition, without assuming that the quotient already specializes to a Selmer class. No new away-from-p rational local-condition hypothesis is needed.

## Precise proposition

Use the hypotheses and test vectors of Castella–Hsieh, Section 5 and Corollary 3.7. Let \(L/\mathbf Q_p\) contain the required coefficients, let \(V_L=V_pE\otimes_{\mathbf Q_p}L\), and let

\[
M=\widehat H^1(K_\infty,V_L),\qquad
\Lambda_L=\mathcal O_L[[\Gamma]][1/p],\qquad T=\gamma-1.
\]

Let \(c\) be natural complex conjugation on this inverse system, acting trivially on the external coefficient field \(L\) and semilinearly on \(\Lambda_L\): \(c(az)=\iota(a)c(z)\), where \(\iota(\gamma)=\gamma^{-1}\). Write \(\kappa\in M\) for the one-sided relaxed class, and suppose \(\operatorname{ord}_J\Theta\ge2\). Put

\[
t=\frac{\gamma-\gamma^{-1}}2,
\qquad Z=\kappa-c\kappa.
\]

Then there is a unique \(x\in M\) with \(tx=Z\). It satisfies \(cx=x\), and its specialization descends to

\[
x_{\mathbf Q}\in\operatorname{Sel}(\mathbf Q,V_L).
\]

Neither \(x\)'s specialization nor its finite logarithm is asserted to be nonzero.

## Proof and audit of the identifications

**1. The specialized numerator is zero.** The specialized diagonal class belongs to the finite Selmer group. The auxiliary quadratic twist has zero Selmer group under the rank-zero hypothesis in the CH setup. Thus the specialization of the E-block in \(H^1(K,V_L)\) is in the plus eigenspace of complex conjugation. This proves \(\operatorname{sp}(Z)=0\), even if the original specialization is itself zero. Do not identify \(c\) with conjugation of the coefficient values of the auxiliary character; it is the natural action on the projected E-Iwasawa module.

**2. Division is in the original module.** Choose a finite set of primes stable under conjugation containing p and all ramified primes of the construction, and use the corresponding global Galois cohomology. Let \(\mathbf T\) be the universal inverse-character coefficient module \(T_pE\otimes\mathcal O_L[[\Gamma]]\). Its short exact sequence

\[
0\longrightarrow\mathbf T\xrightarrow{T}\mathbf T
\longrightarrow T_pE\otimes\mathcal O_L\longrightarrow0
\]

and continuous Shapiro give, after inverting p, the exact segment

\[
H^0(K,V_L)\longrightarrow M\xrightarrow{T}M
\xrightarrow{\operatorname{sp}}H^1(K,V_L).
\]

Here \(H^0(K,V_L)=0\), because the p-primary torsion of \(E(K)\) is finite. Consequently specialization has kernel \(TM\), and multiplication by T is injective. Since

\[
t=T\frac{2+T}{2(1+T)}
\]

is T times a unit already in \(\mathcal O_L[[T]]\), the unique quotient exists in \(M\). There is no enlargement to arbitrary formal power series \(L[[T]]\), and no loss of bounded denominators. One can work integrally first by clearing p-denominators and then killing the finite torsion specialization. Cohomology remains unramified outside the chosen finite set by construction.

The relevant source identifications are CH's lattice-inverse-limit definition on printed p. 13 and its global Shapiro decomposition (3.12) on printed p. 16. This is the same ambient module as its class, not a newly assumed Selmer module.

**3. Reflection gives descent.** Since \(cZ=-Z\) and \(ct=-t\), injectivity of t gives \(cx=x\). Therefore \(x_0\) is invariant under \(\operatorname{Gal}(K/\mathbf Q)\). Restriction identifies \(H^1(\mathbf Q,V_L)\) with these invariants; its inverse is half corestriction. This is degree-two Galois descent, not a conjectural rationality assertion about points.

**4. The finite local condition is a conclusion of CH 4.5.** Choose the fixed Coleman map at the prime where the original class has its nonzero theta regulator, and denote its global composition by F. At this prime, \(\operatorname{Loc}(c\kappa)=0\), because conjugation exchanges the two primes. Consequently

\[
F(Z)=F(\kappa),\qquad F(cZ)=-F(Z).
\]

This uses no comparison between differently normalized Coleman maps. The reciprocity formula gives \(F(Z)\in J^2\). Linearity then gives \(F(x)\in J\), and \(cx=x\) gives the same condition on the conjugate input. CH Theorem 4.5 with r = 1 therefore implies \(x_0\in S_p^{(1)}(E/K)=\operatorname{Sel}(K,V_L)\). Its hypothesis is ambient global Iwasawa cohomology, not prior Selmer membership. Finite scalar extension of the theorem is legitimate because the cohomology, local conditions and maps extend linearly.

**5. Away-from-p conditions cause no extra base obstruction.** For every finite local extension \(F_v/\mathbf Q_\ell\), \(\ell\ne p\), the group \(E(F_v)[p^\infty]\) is finite. Hence \(H^0(F_v,V_pE)=0\). Weil self-duality and local Tate duality give \(H^2(F_v,V_pE)=0\), and the local Euler characteristic gives \(H^1(F_v,V_pE)=0\). Thus the specialized rational class is zero locally away from p. This does not claim that all integral Iwasawa local quotients are torsion-free. The archimedean condition is automatic for odd p. The finite conditions descend from K to \(\mathbf Q\), completing the proposition.

## What remains unproved

If \(F(Z)\) has exact order two, its regularity gives \(1\le\operatorname{ord}_t Z\le2\). Order one means that \(x_0\ne0\); its finite logarithm may still vanish. Order two means that \(x_0=0\); the next quotient specializes into the minus part of **relaxed** global cohomology. Vanishing of the twist Selmer group excludes no such singular relaxed class.

The second Coleman term in CH's height formula carries the Iwasawa involution. For invariant x, its odd first-order terms cancel. Omitting this involution produces a false contradiction and cannot establish nonvanishing.

Finally, \(x_{\mathbf Q}\) may be L-valued. A nonzero finite logarithm over L would supply a \(\mathbf Q_p\)-valued witness by choosing \(a\in L\) for which \(\operatorname{Tr}_{L/\mathbf Q_p}(a\ell(x_{\mathbf Q}))\ne0\) and taking the corresponding coefficient trace of the class. Its existence follows from the nondegenerate field-trace pairing. This does not assert a canonical descent of its coefficient normalization.

## Primary source

F. Castella and M.-L. Hsieh, *On the nonvanishing of generalised Kato classes for elliptic curves of rank 2*, Forum of Mathematics, Sigma 10 (2022), e12. Printed pp. 13, 16–18, 24–28; especially (3.12), Corollary 3.7 and Theorem 4.5. [Published author PDF](https://web.math.ucsb.edu/~castella/Kato-print.pdf).

The global exact-sequence, descent and away-from-p arguments above are supplied explicitly so that the conclusion does not rest on an unspecified cohomological control assumption.
