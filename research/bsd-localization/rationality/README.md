# A geometric target after the nonzero-localization construction

Date: 2026-11-27. This note proves linear-algebra and descent statements, checks relevant hypotheses in primary literature, and identifies a precise remaining geometric comparison. It does not prove a new nonvanishing or BSD theorem. It complements `../logic/AUDIT.md`; it does not repeat the shared package's `research/localization-obstruction.md`.

## Result and proposed next target

Once a construction supplies a global finite Selmer class with nonzero localization, the rank-two generalized Kato class determines a **canonical exterior class**

\[
\eta_\kappa=\frac{\kappa\wedge z}{\ell(z)}.
\tag{1}
\]

The expression is independent of the localization witness \(z\). A concrete sufficient geometric target is to realize the restriction of \(\eta_\kappa\), over a finite extension \(F/\mathbf Q\), in the exterior square of the Kummer image of \(E(F)\). Point traces then descend it and prove rank two and finiteness of the p-primary part of Sha.

This target concerns degree-one arithmetic cycles or points. An invariant wedge of two nontrivial ring-class eigenspaces, a Selmer-complex determinant, or a local regulator equality does not establish it. In particular, the order-seven character used in the computational pilot creates a specific invariant-wedge trap, proved in Section 4.

## 1. Setup and canonical exterior class

Let \(E/\mathbf Q\) be an elliptic curve and let \(p\) be a good prime. Put

\[
S=\operatorname{Sel}(\mathbf Q,V_pE),\qquad
M=E(\mathbf Q)\otimes\mathbf Q_p\subset S,\qquad
\ell=\log_{\omega_E}\circ\operatorname{loc}_p.
\]

Assume that preceding work has established

\[
\dim_{\mathbf Q_p}S=2,\quad \ell\ne0,\quad
0\ne\kappa\in\ker\ell.
\tag{2}
\]

These are explicit hypotheses of this note. The construction of \(z\) with \(\ell(z)\ne0\), and the arithmetic theorem supplying (2), remain separate obligations.

**Proposition 1.** Formula (1) defines a nonzero element of \(\bigwedge^2S\), independent of \(z\). For the contraction convention

\[
c_\ell(u\wedge v)=\ell(v)u-\ell(u)v,
\]

one has \(c_\ell(\eta_\kappa)=\kappa\). In fact \(c_\ell:\bigwedge^2S\to\ker\ell\) is an isomorphism.

**Proof.** If \(z,z'\) both have nonzero localization, then

\[
\ell\left(\frac z{\ell(z)}-\frac {z'}{\ell(z')}\right)=0.
\]

The parenthesized difference is a scalar multiple of \(\kappa\), since \(\ker\ell\) is one-dimensional. Wedging it with \(\kappa\) proves independence. The vectors \(\kappa,z\) are independent, so their wedge is nonzero. The contraction identity follows by direct substitution. Both spaces in the final assertion are one-dimensional. QED.

If a rational-point basis \((P,Q)\) eventually becomes available and

\[
\kappa=\lambda\bigl(\ell(Q)P-\ell(P)Q\bigr),
\]

then \(\eta_\kappa=\lambda P\wedge Q\). For a basis change of determinant \(d\), both the enhanced regulator and \(P\wedge Q\) change by \(d\). Thus (1) packages the normalization without choosing a transverse Selmer basis or mistaking that basis for rational points.

The class still depends on the specified normalization of \(\kappa\) and \(\ell\). Scaling \(\kappa\) scales \(\eta_\kappa\); scaling \(\ell\) rescales it inversely. Independence here concerns only the choice of \(z\).

## 2. Exactly what the exterior membership statement would prove

Under (2), the following conditions are equivalent:

1. \(\kappa\in M\).
2. \(\eta_\kappa\in\bigwedge^2M\), with the latter viewed inside \(\bigwedge^2S\).
3. \(M=S\).
4. \(\Sha(E/\mathbf Q)[p^\infty]\) is finite.

**Proof.** A nonzero rational point modulo torsion has nonzero local logarithm. Indeed, a nonzero integer multiple enters a sufficiently small formal neighborhood where logarithm is injective; zero logarithm would make that multiple, and hence the point, torsion. Consequently, if \(\dim M=1\), the restriction of \(\ell\) to \(M\) is injective. Condition 1 therefore forces \(\dim M\ge2\), and (2) forces \(M=S\). Condition 2 likewise forces \(\dim M\ge2\), because \(\eta_\kappa\ne0\). Condition 3 plainly implies both 1 and 2.

Finally the Kummer exact sequence is

\[
0\longrightarrow M\longrightarrow S\longrightarrow
T_p\Sha(E/\mathbf Q)\otimes\mathbf Q_p\longrightarrow0.
\]

The p-primary Sha group is cofinitely generated over \(\mathbf Z_p\), as a quotient of the p-primary Selmer group. Its rational Tate module vanishes precisely when its divisible corank is zero, which is precisely finiteness. This proves 3 equivalent to 4. QED.

Thus a theorem placing this one strict class in the Kummer image does not, under (2), provide an arithmetically weaker conclusion than p-primary finiteness: the statements are equivalent. Its value is that it presents a specific class to construct geometrically. A new \(z\) with nonzero localization addresses the preceding nonvanishing problem; it does not by itself settle any of these four equivalent conditions.

## 3. A finite-extension geometric descent criterion

The desired construction need not produce rational points over \(\mathbf Q\) immediately.

**Proposition 2.** Let \(F/\mathbf Q\) be finite of degree \(d\). If

\[
(\bigwedge^2\operatorname{res}_{F/\mathbf Q})(\eta_\kappa)
\in
\bigwedge^2\delta_F\bigl(E(F)\otimes\mathbf Q_p\bigr),
\tag{3}
\]

then \(\eta_\kappa\in\bigwedge^2M\). Consequently (2) and (3) imply rank two and finite \(\Sha[p^\infty]\).

**Proof.** Write a preimage of the left side of (3) as

\[
\Xi=\sum_i a_i R_i\wedge T_i,
\qquad R_i,T_i\in E(F)\otimes\mathbf Q_p.
\]

Restriction and corestriction on \(H^1\) satisfy \(\operatorname{cor}\operatorname{res}=d\), and Kummer maps commute with the point trace \(\operatorname{Tr}_{F/\mathbf Q}\). Applying the **exterior square of corestriction** gives

\[
d^2\eta_\kappa
=\bigwedge^2\delta_{\mathbf Q}
\left(\sum_i a_i\operatorname{Tr}(R_i)\wedge\operatorname{Tr}(T_i)\right).
\tag{4}
\]

Division by the nonzero scalar \(d^2\) proves the assertion. No assumption \(p\nmid d\) is needed over \(\mathbf Q_p\). QED.

The analogous class-level criterion is also valid: if \(\operatorname{res}\kappa\) is in the Kummer image over \(F\), then \(d\kappa\) is in the Kummer image over \(\mathbf Q\), hence so is \(\kappa\). These criteria require no finiteness assertion about Sha over \(F\).

**Construction brief.** A possible proof should specify actual degree-zero divisor classes on a curve over \(F\), a homomorphism from its Jacobian to \(E\), and a global cohomological comparison yielding (3), or its class-level analogue. It is enough to construct the relevant combination of divisor classes; individual points need not be rational over \(\mathbf Q\). Merely knowing that the original family arose from cycles on higher-dimensional Kuga–Sato varieties does not supply the necessary degree-one realization at its weight-one specialization.

If coefficients are extended to a finite field \(L/\mathbf Q_p\), the proof works over \(L\). Membership for a class originally defined over \(\mathbf Q_p\) descends because scalar extension of vector spaces is faithful.

## 4. Ring-class trap: invariant wedge does not mean descending wedge

For a finite Galois extension with group \(G\), in general

\[
\bigwedge^2(U^G)\ne(\bigwedge^2U)^G.
\tag{5}
\]

Take \(G=C_7=\langle\sigma\rangle\), a coefficient field containing a primitive seventh root \(\zeta\), and a two-dimensional representation with

\[
\sigma P=\zeta P,\qquad \sigma Q=\zeta^{-1}Q.
\]

The individual invariants are zero, while \(P\wedge Q\) is invariant. The point trace kills both factors:

\[
\operatorname{Tr}P=\operatorname{Tr}Q=0,
\qquad
(\bigwedge^2\operatorname{Tr})(P\wedge Q)=0.
\]

In contrast the diagonal norm on the wedge gives

\[
\sum_{g\in G}g(P\wedge Q)=7P\wedge Q.
\]

These are different operations. Proposition 2 uses the first, and a nonzero invariant obtained by the second does not satisfy its hypothesis. The same phenomenon already occurs for \(C_2\) acting as \(-1\) on both factors, so it is not caused by a large coefficient field.

This matters directly when attempting to pair points in the \(\chi\) and \(\chi^{-1}\) ring-class components. Their invariant wedge alone does not give rational points or a Mordell–Weil exterior class over \(\mathbf Q\). One must identify the wedge with the restriction of the actual global \(\eta_\kappa\), or prove the corresponding comparison after projecting **each factor** to the appropriate global component. Equation (4) then makes the nonzero trace requirement explicit.

The checker in this directory verifies the C7 identities exactly in \(\mathbf Q[X]/(1+X+\cdots+X^6)\), together with the canonical-class and basis-change identities. These are algebraic checks, not arithmetic counterexamples to BSD.

## 5. Why algebraic-coordinate reconstruction is the wrong target

Assume here that \(E\) is non-CM. Fuchs–Pham [FP, Theorem 2.2, printed p. 338] implies that logarithms of independent algebraic points are linearly independent over \(\overline{\mathbf Q}\). To apply it, multiply the points by a common integer into the exponential domain. Independence over \(\operatorname{End}_{\overline{\mathbf Q}}E=\mathbf Z\) follows from independence modulo torsion; on the one-dimensional Lie algebra its endomorphism ring is \(\overline{\mathbf Q}\).

For independent rational points \(P,Q\), therefore,

\[
\frac{\ell(P)}{\ell(Q)}\notin\overline{\mathbf Q},
\qquad
\ker(\ell|_M)
=\mathbf Q_p\bigl(\ell(Q)P-\ell(P)Q\bigr)
\quad\text{if rank }E(\mathbf Q)=2.
\]

The ratio of the two coefficients of every nonzero vector on this strict line is transcendental. No common scaling makes both coefficients algebraic. This does not assert injectivity over \(\mathbf Q_p\): dependence over \(\mathbf Q_p\) and independence over \(\overline{\mathbf Q}\) are compatible. The potentially algebraic object is a normalization of \(P\wedge Q\), not the coefficients introduced by contracting it with \(\ell\).

## 6. What the relevant primary literature does and does not provide

### Enhanced-regulator rationality and exceptional stabilization

Bertolini–Seveso–Venerucci [BSV26, Conjecture 3.4, author pp. 19–20] assumes Mordell–Weil dimension two and predicts an enhanced-regulator identity up to a nonzero algebraic scalar. Remarks 3.5(2)–(3) explicitly assume equality of the Mordell–Weil and Selmer dimensions before isolating that scalar. These statements cannot first establish the equality they assume. Their Theorem 3.2 supplies a height/logarithm identity, not a new nonzero-localization witness.

The improved mixed-stabilization class of Remark 3.5(6) addresses the exceptional relation \(\alpha_f=\beta_g\alpha_h\). Remark 1.2(1) and Section 3 assumption (27) show this exceptionality is excluded at good ordinary primes. Thus it does not automatically treat the Castella–Hsieh off-diagonal vanishing in the good ordinary p = 5 pilot. A weight derivative there needs its own global divisibility, local-condition and reciprocity arguments.

Darmon–Rotger [DR, Section 3.3 and Conjecture 3.12] formulates the related enhanced-regulator comparison. This gives a natural conceptual home for (1), but the conjectural comparison is not an unconditional point-construction theorem.

### The available diagonal-class/Heegner-point comparison

The direct point comparison in [BSV22, Assumption 1.1 and Theorem A] requires multiplicative reduction at p and p inert in the quadratic field. It also requires \(\epsilon_K(-N_f^-)=+1\) when the conductor is \(N_fp\).

For the conductor-389 pilot, p = 5 or 29 fails multiplicative reduction. Switching to p = 389 gives \(N_f=N_f^-=1\); an imaginary quadratic field then has \(\epsilon_K(-1)=-1\), contrary to the required sign. The real-quadratic version concerns Stark–Heegner local points and does not make their global rationality automatic. This specific theorem therefore does not discharge (3) for the pilot.

### Why an ordinary Heegner trace cannot replace the missing construction

The classical Gross–Zagier formula [GZ, I.§6] identifies the relevant Heegner-point height with a first derivative. If \(L(E,s)\) has a double zero at 1, then for every quadratic \(K\),

\[
L(E/K,s)=L(E,s)L(E^K,s)
\quad\Longrightarrow\quad L'(E/K,1)=0.
\]

Where the formula applies to the trivial-character Heegner point, positive definiteness of canonical height makes that point torsion. Nontrivial ring-class eigenspaces can contain non-torsion Heegner points, but their trace to the trivial component vanishes. A derived cycle or regulator comparison is required; ordinary Heegner traces do not circumvent the double zero.

## 7. Deliverable and remaining theorem

The useful conditional theorem is Proposition 2: a finite-extension realization of the canonical exterior class implies the missing arithmetic conclusion. It does not assume Mordell–Weil rank or finite Sha in order to define the required equality. The unresolved work is to construct its right-hand side and prove equality **globally**, with the appropriate point-trace projection; a local logarithm computation alone cannot prove that equality.

The current candidate is the reflected relaxed-class construction in `../derived_global/DERIVED_CLASSES.md`, independently reviewed in `REFLECTED_REVIEW.md`. Under the actual Castella–Hsieh setup and theta order at least two, it supplies a possibly zero class in the Selmer group over \(\mathbf Q\). Its global division and finite local condition need not be assumed. The remaining obligations are:

1. Prove a nonzero finite logarithm for the reflected class, or supply another global localization witness. Exact theta order two alone does not establish this.
2. Apply the existing nonvanishing and Selmer-dimension argument to obtain (2), with all coefficient and auxiliary hypotheses retained.
3. Establish the finite-extension Kummer/exterior comparison (3), or independently construct two rational points.

The finite p = 5 certificate helps with the specified analytic leading term. None of the propositions here reinterpret that certificate as completion of step 3.

Run the exact algebra check with:

```sh
python research/bsd-localization/rationality/check_exterior_descent.py
```

## Primary references

- **[FP]** C. Fuchs and D. H. Pham, *Some applications of the p-adic analytic subgroup theorem*, Glasnik Matematički 51 (2016), 335–343, Theorem 2.2. [Journal PDF](https://web.math.pmf.unizg.hr/glasnik/51.2/51%282%29-04.pdf).
- **[BSV26]** M. Bertolini, M. A. Seveso and R. Venerucci, *On p-adic analogues of the Birch and Swinnerton-Dyer conjecture for Garrett L-functions*, Annales de l'Institut Fourier 76 (2026), no. 3, 945–981; DOI 10.5802/aif.3726. References above use the numbered pages of the [26-page author PDF](https://www.esaga.uni-due.de/f/massimo.bertolini/publications/BSV-TPR.pdf).
- **[DR]** H. Darmon and V. Rotger, *Elliptic curves of rank two and generalized Kato classes*, Research in the Mathematical Sciences 3 (2016), article 27. [Author PDF](https://web.mat.upc.edu/victor.rotger/docs/DR2b.pdf).
- **[BSV22]** M. Bertolini, M. A. Seveso and R. Venerucci, *Balanced diagonal classes and rational points on elliptic curves*, Astérisque 434 (2022), 175–201. [Author PDF](https://www.esaga.uni-due.de/f/massimo.bertolini/publications/Ast-BSV2.pdf).
- **[GZ]** B. H. Gross and D. B. Zagier, *Heegner points and derivatives of L-series*, Inventiones Mathematicae 84 (1986), 225–320, I.§6. [Author-hosted published PDF](https://people.mpim-bonn.mpg.de/zagier/files/doi/10.1007/BF01388809/fulltext.pdf).

For the Selmer/Kummer setup and the precise Castella–Hsieh hypotheses, see `../logic/AUDIT.md` and its primary references. No additional global theorem is inferred from the finite-dimensional toy checks.
