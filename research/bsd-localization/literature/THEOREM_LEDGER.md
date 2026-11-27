# BSD rank two: theorem and hypothesis ledger

Reviewed against primary sources on 2026-11-27. This is a research audit, not a proof of BSD or a Lean verification. Page numbers refer to the linked PDF version.

## 1. Castella–Hsieh: the precise starting result

**Source CH22:** Francesc Castella and Ming-Lun Hsieh, *On the nonvanishing of generalised Kato classes for elliptic curves of rank 2*, Forum of Mathematics, Sigma **10** (2022), e12, 1–32. [Published PDF](https://web.math.ucsb.edu/~castella/Kato-print.pdf), [publisher / DOI](https://doi.org/10.1017/fms.2021.85).

Setup, §1.2, p. 4; Theorems A and B, p. 5:

- $E/\mathbf Q$, $p>3$ good ordinary; imaginary quadratic $K$ with discriminant coprime to $N_E$, and $p$ split.
- A ray class character $\psi$ of conductor coprime to $pN_E$; $g=\theta_\psi$, $\chi=\psi/\psi^\tau$, with $\chi(\mathfrak p)\ne1$.
- $w(E)=+1$, $L(E,1)=0$, and $L(E^K,1)L(E/K,\chi,1)\ne0$.
- $E[p]$ irreducible; the inert conductor factor $N^-$ is squarefree with an odd number of prime factors; $E[p]$ ramifies at each of them.

Writing $S=\operatorname{Sel}(\mathbf Q,V_pE)$, Theorem A gives

\[
\kappa\ne0\Longrightarrow\dim_{\mathbf Q_p}S=2,
\qquad
(\dim S=2\ \land\ \operatorname{loc}_p|_S\ne0)\Longrightarrow\kappa\ne0.
\]

Theorem B adds positive rational rank and obtains

\[
\operatorname{ord}_T\Theta_{f/K}=2\Longrightarrow\kappa\ne0.
\]

Its proof, §5.6, p. 28, uses positive rational rank precisely to obtain nonzero localization. The leading-term identity is Theorem 5.3, p. 27. These conclusions concern Selmer dimension, not automatically Mordell–Weil rank.

## 2. The subsequent theorem keeps the localization obstruction

**Source C26:** Francesc Castella, *Nonvanishing of generalised Kato classes and Iwasawa main conjectures*. [Author PDF](https://web.math.ucsb.edu/~castella/GKC-IMC.pdf). The [author's publication list](https://web.math.ucsb.edu/~castella/) lists Springer Proceedings in Mathematics & Statistics **527** (2026), 23–50. The author PDF has 21 pages.

Theorem A, pp. 2–3; equivalent detailed statement Theorem 5.2.3, p. 16:

- $p>3$, good ordinary; $E[p]$ absolutely irreducible.
- Some $q\Vert N_E$; if $q\equiv\pm1\pmod p$, require ramification at $q$.
- Either $p>5$, or the residual image contains a conjugate of $\operatorname{SL}_2(\mathbf F_p)$.
- Positive even analytic order, and an auxiliary pair from Choice 5.2.1.

It proves $\kappa\ne0\Rightarrow\dim S=2$. **Assuming $\dim S=2$**, it proves

\[
\kappa\ne0\iff\operatorname{loc}_p|_S\ne0,
\qquad
\mathbf Q_p\kappa=\ker(\operatorname{loc}_p|_S)
\quad\text{when nonzero}.
\]

Choice 5.2.1, p. 16, uses a prime $\ell\nmid6pN_E$, split in $K$ and ordinary for $E$; $q$ is inert, other conductor primes split; $\chi$ has $\ell$-power conductor, is nontrivial at $K_{\mathfrak p}$, and both auxiliary central values are nonzero. Split $p$ is part of the preceding setup. Remark 5.1.4, p. 15, establishes strict localization of $\kappa$.

## 3. What the proposed missing lemma would actually accomplish

The following deductions are this audit's logical analysis of the displayed statements.

Replacing positive rational rank by nonzero localization in CH22 Theorem B is a valid proof-level strengthening, since the identified use of the original assumption supplies exactly that condition. It does not establish this new condition from analytic rank two.

Even after this replacement and a theta certificate, the conclusion is initially only

\[
\dim S=2.
\]

The defining Kummer sequence distinguishes this from rational rank:

\[
0\longrightarrow E(\mathbf Q)\otimes\mathbf Q_p
\longrightarrow S
\longrightarrow V_p\Sha(E/\mathbf Q)
\longrightarrow0.
\]

In particular, dimensions $0+2=2$ are not excluded by the dimension equation. Nonzero localization on the entire Selmer group must not be silently identified with a nonzero rational point.

There are two distinct missing bridges in a universal program:

1. Complex analytic order two must lead to an eligible auxiliary construction with the required **anticyclotomic** theta order and localization. A cyclotomic or complex second derivative is not that theta coefficient by definition.
2. Selmer classes must be shown to arise from rational points, or the $V_p\Sha$ quotient must be eliminated.

A particularly sharp sufficient statement is: construct a **nonzero generalized Kato class in the global Kummer image**. Its strict localization then rules out rational rank one: on a one-dimensional Mordell–Weil space the $p$-adic logarithm of a nontorsion point is nonzero. CH's Selmer upper bound supplies rational rank at most two, so rational rank is exactly two and $\Sha[p^\infty]$ is finite. This would be a substantive rationality theorem, not a consequence of a finite theta computation alone.

The generalized Kato class cannot itself be the desired nonzero-localization witness: the theorem places it in the localization kernel.

The multiplicative-prime hypotheses also mean these sources do not by themselves cover every elliptic curve. A universal argument must handle curves without a prime $q\Vert N_E$, as well as the separate CM setting.

## 4. Applicability to the proposed pilot

The companion arithmetic audit concerns $E=389.a1$, $K=\mathbf Q(\sqrt{-71})$, $p=29$. It computes $a_{29}=-6$, discriminant $389$, splitting of $29$, inertness of $389$, and $h_K=7$. These are independently computed local inputs; consult that audit for its certificates.

The companion eligibility package now certifies the arithmetic inputs for absolute residual irreducibility and ramification, and gives an exact positive interval for $L(E^K,1)$:

\[
0.9360088537803042525901954783264223920549
\le L(E^K,1)\le
0.9360088573972690020870684844656754102100.
\]

Its standard arithmetic and analytic theorem inputs are documented there. The remaining pilot obligations are an eligible auxiliary $\psi$ with $L(E/K,\chi,1)\ne0$ and the identification and order of the computed theta element.

Exact $L(E,1)=0$ follows from the certified nontorsion rational point by contrapositive of the rank-zero theorem. A precise primary source is **Kato**, [*p-adic Hodge theory and values of zeta functions of modular forms*](https://archive.numdam.org/item/AST_2004__295__117_0.pdf), Astérisque **295** (2004), Corollary 14.3(2): a modular abelian variety with nonzero central value has finite rational-point group. Take $A=E$, the trivial character, and the base field $\mathbf Q$. This is a theorem-based deduction, not a numerical zero test. Together with the certified root number $+1$, it gives positive even analytic order. It does not alone certify that the analytic order is exactly two.

A finite theta certificate is useful even though this pilot already has accessible rational points; it tests the certificate machinery, not the universal positive-rank gap.

There is a promising simplification specific to $h_K=7$. All six nontrivial unramified class characters have order seven. If $\psi$ is one of them, $\chi=\psi^2$ is nontrivial. A prime above $29$ is nonprincipal: the norm equation

\[
x^2+xy+18y^2=29
\]

has no integer solutions. Indeed $|y|\le1$, and the resulting quadratic discriminant is $45$ for $|y|=1$. Therefore $\chi(\mathfrak p_{29})\ne1$. Since $29\equiv1\pmod7$, the character values lie in $\mathbf Q_{29}$. **A nonzero conductor-one toric period in one of these character components would supply the remaining auxiliary central-value condition for the original CH22 setup.** This proposed shortcut has not yet been certified. It should not be forced into C26's more specialized auxiliary-choice statement.

### Exact primary formula for that auxiliary shortcut

**Gross:** *Heights and the Special Values of L-series*, CMS Proceedings **7**, 115–187. [Scanned primary paper](https://wstein.org/papers/bib/Gross-Heights_and_the_Special_Values_of_L-series.pdf), Theorem 11.5, printed p. 170 (PDF page index 55). For prime level $N$ inert in the imaginary quadratic field and a class character $A$, it identifies

\[
L(f,A,1)=\frac{(f,f)}{u^2\sqrt d}\langle e_{f,A},e_{f,A}\rangle.
\]

Here $e_A$ is the character-weighted sum of the $h_K$ Gross points, and $e_{f,A}$ its orthogonal projection to the $f$-eigenspace; definitions appear on pp. 167–169. For $N=389,d=71$, this is an exact nonvanishing equivalence with a positive scalar. The evaluator must use actual toric eigenfunction values, or correctly weighted pairings with Gross points: arbitrary Brandt-vector coordinates need not be those values. The formula with trivial character gives $L(E,1)L(E^K,1)$, so vanishing of that product cannot replace the separate positive twist-value certificate.

## 5. Current-source checks and limits

- **CM result:** [Castella, *Generalised Kato classes on CM elliptic curves of rank 2*](https://web.math.ucsb.edu/~castella/Kato-Schoen.pdf), Theorem B, p. 5, gives the analogous Selmer/localization equivalence for its CM construction. The author's list says American Journal of Mathematics, to appear. It does not apply to the non-CM pilot or remove the rationality issue.
- **Recent refined conjectures:** [Castella–Sano, *On the equivariant Heegner point main conjecture and refined conjectures of Birch–Swinnerton-Dyer type*](https://web.math.ucsb.edu/~castella/Darmon.pdf), Theorem 2.6, p. 10. Its setup assumes finite $\Sha(E/K)$ on p. 9; Remark 2.7 permits assuming finite $p$-primary part instead. Its Heegner setup requires all conductor primes split. It cannot be used as a proof of those missing hypotheses for the present inert-conductor pilot.
- **New November preprint:** [Calonge Fabregat, arXiv:2611.09192v1](https://arxiv.org/abs/2611.09192v1), submitted 2026-11-06, starts with rank-two curves $y^2=x^3-Dx$ and studies a $p$-adic leading-term quotient. Its stated hypotheses already assume rank two and restrict to a CM family.
- **OpenAI low-corank work:** the [October 7 primary theorem source](https://github.com/openai/math/blob/main/preprints/Exact-Birch-Swinnerton-Dyer-Formula-from-Low-Selmer-Corank-October-7-2026/build/sections/01-introduction.tex) assumes $s_q(E)\in\{0,1\}$. Its advertised theorem does not cover Selmer corank two. No validation of that preprint's proof is asserted here.
- **A claimed complete proof found in search is not a usable closure:** [Wang/Xiong's March 2026 self-posted manuscript](https://www.researchgate.net/publication/401385931_The_Birch_and_Swinnerton-Dyer_Conjecture_for_Analytic_Rank_Two_A_Complete_Proof_via_Definite_Anticyclotomic_Iwasawa_Theory), Theorem 17.4, Step 3, infers $r=2,s=0$ from $2=r+s$, $r\le2$, $s\ge0$. The numerical possibility $r=0,s=2$ directly disproves that inference. This audit does not treat the manuscript as an established result.

The primary sources inspected do not establish unrestricted analytic-rank-two BSD or remove the localization/rationality gaps identified above. This is a scoped literature finding, not a claim of exhaustive knowledge of every manuscript.

## 6. Brief search for the authors' computation files

The Castella and Hsieh publication pages and the publisher's article page were checked, together with targeted searches for the paper, Sage, Brandt modules, code, and $389a1$. The appendix identifies Sage's Brandt-module package, but no author-linked script, quaternionic eigenvector, or Gross-point data file was found in these inspected sources. This is a bounded search result, not proof that no such file exists. The $K=-7,p=29$ printed coefficient fixture is recorded in `THETA_CONVENTIONS.md`; it has not been independently reproduced.
