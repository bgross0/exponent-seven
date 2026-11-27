# An exact theta certificate for 389a1 over Q(sqrt(-71)) at p = 5

Status: independently audited computational argument, 27 November 2026. The finite arithmetic has reproducible exact checks, including a separate PARI/GP implementation and rigorous FLINT/Arb reconstruction of the class polynomials. The classical CM, Jacquet–Langlands, special-value, and Iwasawa-theoretic bridges are stated explicitly below. They are mathematical dependencies, not an end-to-end Lean formalization.

## 1. Result and scope

Let

\[
E: y^2+y=x^3+x^2-2x,\qquad K=\mathbf Q(\sqrt{-71}),\qquad p=5.
\]

The conductor of E is q = 389. The prime q is the supersingular reduction prime in this computation; it is distinct from the ordinary Iwasawa prime p.

The certificate proves the following, using the classical identifications specified in this note:

1. For every nontrivial character χ of the order-seven group Cl(O_K), the central value L(E/K, χ, 1) is nonzero.
2. For the ordinary anticyclotomic theta element Θ associated with E/K on the trivial tame branch, the exact constant and linear coefficients vanish, while its quadratic coefficient is a 5-adic unit. Consequently ord_T Θ = 2. With a primitive integral quaternionic normalization, Θ = T²U for a unit U in Z_5[[T]].

The second conclusion supplies the theta hypothesis in Castella–Hsieh's Theorem B. Applying that theorem also requires its other hypotheses, including positive Mordell–Weil rank and the auxiliary-character conditions. Those checks belong to the separate arithmetic audit. Nothing here removes the positive-rank hypothesis, proves BSD generally, or identifies a generalized Kato class with an explicitly constructed rational point.

The coordinate-dependent residue produced by the present cycle ordering is 4 after the Chida–Hsieh regularization described below. The invariant assertion is that the quadratic coefficient is a unit. A different primitive eigenfunction, Gross-point origin, reciprocity convention, or topological generator can change the displayed residue by a unit.

## 2. Reproducible evidence

The discovery inputs are:

- `data/supersingular-389.json`: supersingular vertices, exact Brandt matrix, primitive eigenfunction, and the seven conductor-one CM reductions.
- `data/H-minus44375-coeffs.json`: ascending coefficients of the ring class polynomial of discriminant -44375 = -71·25².
- `data/CM-minus44375-lifts32.json`: 140 approximate roots in Q_389(u), with u² = 2.
- `data/cm-jet-p5.json`: the certified CM cycle and the resulting finite group-ring coefficients.

The main verifier `verify_certificate.py` reconstructs both class polynomials using FLINT/Arb, then checks the finite-field, Hensel, graph, and moment calculations with integers. Its recorded result is `evidence/certificate-verification.json`.

The independent checker `scripts/cm_independent_audit.gp` does not import either Python discovery script. It uses PARI's built-in modular polynomial, finite fields, exact quadratic-field arithmetic, matrix algebra, class groups, and a fresh class-polynomial computation. Its run is recorded in `evidence/cm-independent-gp.log`. The matching receipt, `evidence/cm-independent-gp-receipt.json`, records the command, exit status, an explicit PASS marker, and SHA256 hashes of the checker, inputs, and output. Run it from the repository root with:

```sh
gp -fq -s 256M scripts/cm_independent_audit.gp
```

The independent run returned:

```text
PASS supersingular Brandt module: 33 vertices; dim T2=-2 is 1;
CM values [-1, -1, 0, 1, 1, 0, 0]
PASS CM polynomial / lifts: 140 roots; min v(H)=32; max v(H')=12
PASS CM graph: connected 140-cycle;
raw Gamma1 coefficients [5, -1, -1, 5, -8]; jet mod5 [0, 0, 1]
CM_INDEPENDENT_AUDIT_PASS PARI=[2, 19, 1]
```

The GP comparison against `polclass` is an independent computational check, not the sole justification of class-polynomial provenance. The rigorous enclosure reconstruction is the additional verification described next.

## 3. Class-polynomial provenance

For D = -71 and D = -44375, the main verifier enumerates every primitive reduced positive definite form (a,b,c) with b²-4ac = D, using the bound a ≤ sqrt(|D|/3) and the usual boundary identifications. It encloses

\[
\tau_{a,b,c}=\frac{-b+i\sqrt{|D|}}{2a}
\]

and then j(τ) with complex ball arithmetic at 16,384-bit working precision. Multiplying the factors X-j(τ) produces an enclosure of the complete ring class polynomial. The CM integrality theorem says that this polynomial has integer coefficients. The `unique_fmpz_poly` check succeeds only when the coefficient balls isolate one integer polynomial; the resulting coefficients are compared against the stored arrays.

The recorded degrees are 7 and 140, and both comparisons pass. This is a proof by rigorous enclosures conditional on the correctness of the FLINT/Arb implementation and the classical CM theorem. It is not a nearest-integer guess from floating-point approximations. The official FLINT documentation explains both the class-polynomial product and the unique-integer extraction criterion [FLINT].

## 4. The Brandt module and its weight convention

Work over F_389² = F_389[u]/(u²-2). The integer 2 is a quadratic nonresidue modulo 389. The data contain 33 distinct supersingular j-invariants. The Python verifier obtains them from all 194 roots of the Deuring polynomial of degree 194. Independently, GP checks supersingularity of all 33 curves and checks the mass

\[
\sum_i \frac1{w_i}=\frac{389-1}{12},
\qquad w_i=\frac{|\operatorname{Aut}(E_i)|}{2}.
\]

There is one vertex with w_i = 3, namely j = 0; all other vertices have weight one. The mass equality verifies completeness after supersingularity and distinctness have been checked.

Let A_ij count cyclic order-two subgroups of E_i whose quotient has j-invariant j_j. This is an **outgoing** adjacency convention. Exact factorization of Φ_2(j_i,Y) verifies each row and its multiplicities; all rows sum to three. The correspondence between this matrix and the supersingular Hecke action is described in Jordan–Ribet–Scholl, §2.2, equation (2.2.3) and Theorem 2.4 [JRS].

The data satisfy

\[
w_jA_{ij}=w_iA_{ji},\qquad Av=-2v,
\qquad \dim_{\mathbf Q}\ker(A+2I)=1,
\qquad \gcd(v_i)=1.
\]

The curve has a_2(E) = -2. Modularity and Jacquet–Langlands put its quaternionic eigensystem in this eigenspace. Since the eigenspace is one-dimensional, v is its quaternionic eigenfunction up to scalar. This identifies the complete eigensystem, not merely a numerical match at one prime: the actual eigensystem exists in the space, and the relevant one-prime eigenspace already has dimension one.

The distinction between a function and divisor coordinates matters. Put W = diag(w_i). On the basis of supersingular divisors, the Hecke matrix for the outgoing convention is Aᵗ. Weighted self-adjointness gives

\[
A^tW^{-1}=W^{-1}A.
\]

Thus the corresponding divisor eigenvector is

\[
d=\sum_i \frac{v_i}{w_i}e_i.
\]

For the pairing ⟨e_i,e_j⟩ = w_iδ_ij, its pairing with a CM character divisor is exactly a sum of the function values v_i. There is no additional division by w_i in the function-value sum:

\[
\left\langle d,\sum_a\chi(a)e_{i(a)}\right\rangle
=\sum_a\chi(a)v_{i(a)}
\]

up to conjugating χ according to the Hermitian convention. This derivation also explains the w-factor in Liu–Masri–Young, §2, equation (2.2) [LMY].

The eigenfunction is primitive over Z and therefore primitive over Z_5. Chida–Hsieh's p-adic normalization in §4.1 is the choice of a generator of this integral eigenline [ChH]. A different such generator differs by a 5-adic unit.

Frobenius acts by j = a+bu ↦ a-bu, and the recorded v is invariant. This agrees with a_389(E) = +1. In these conventions T_389 is Frobenius and T_389 = -W_389; confusing the Frobenius sign with the Atkin–Lehner sign would give an incorrect check. The global root number is +1.

## 5. Exact auxiliary-character nonvanishing

The field discriminant -71 is fundamental, its class number is seven, and 389 is inert. At a fixed prime above 389, the CM elliptic curves for O_K reduce to supersingular curves. The seven roots of H_-71 remain distinct modulo 389. Exact factorization identifies their reductions with seven recorded vertices, on which

\[
\{v(j_a):a\in\operatorname{Cl}(O_K)\}
=\{-1,-1,0,1,1,0,0\}
\]

as a multiset. They all have supersingular automorphism weight one.

Fixing a CM embedding orientation gives a class-group orbit. The reduction construction and its interpretation as Gross points are recalled in [LMY, Introduction and §2]. Changing origin translates the orbit; changing the orientation conjugates it. Neither affects the following argument.

Let C_7 = ⟨c⟩ and let χ be nontrivial. Write r_i = v(j_{c^i}). If

\[
\sum_{i=0}^{6} r_i\chi(c)^i=0,
\]

then the polynomial R(X) = Σr_iX^i, of degree at most six, vanishes at a primitive seventh root of unity. Its rational coefficients force R to be a multiple of Φ_7(X) = 1+X+⋯+X^6. All its coefficients would therefore be equal, contradicting the displayed multiset. Every nontrivial character period is nonzero. This conclusion does not require recovering the labeling of these seven roots.

Gross's special-value formula identifies the central L-value with a nonzero positive scalar times the squared absolute value of the corresponding projected period. The precise divisor form is Gross, Proposition 11.2; [LMY, §2, equations (2.1)–(2.2)] states the formula with both divisor and function conventions [Gross, LMY]. Hence L(E/K,χ,1) ≠ 0 for every nontrivial χ.

For a primitive order-seven class character ψ, complex conjugation acts by inversion, so ψ/ψ^τ = ψ² is again nontrivial. This supplies the Rankin factor for the auxiliary CM theta series g = θ_ψ. The other factor L(E^-71,1) must be checked separately. The arithmetic audit obtains a nonzero exact quadratic-twist modular-symbol sum, -4; the trivial CM period above is zero and cannot establish that twist's nonvanishing on its own.

## 6. Why conductor 25 is the first wild level

Write O_c = Z+cO_K. Since 5 splits in K and O_K has only the units ±1, the ring class number formula gives

\[
|\operatorname{Pic}(O_5)|=7(5-1)=28,
\qquad |\operatorname{Pic}(O_{25})|=7\cdot5(5-1)=140.
\]

The first group has no 5-primary part. At conductor 25 the first quotient of order five appears. Thus the first nontrivial anticyclotomic quotient Γ_1 ≅ C_5 is obtained from Pic(O_25), not from Pic(O_5).

The calculation identifies Pic(O_25) ≅ C_140, generated by the norm-two ideal class represented by (2,1,5547). PARI independently returns this group and generator. The CM cycle below also certifies generation: the horizontal action has a single orbit containing all 140 CM classes.

The projection to Γ_1 is the unique quotient of order five. With a cyclic enumeration j_i = [\mathfrak l]^i j_0, it sends i to i modulo five, up to changing the generator of Γ_1. Summing the 28 weights in each residue class is consequently the projection of the full ring class theta element. Using an average over the tame group instead would multiply by 28^-1, a 5-adic unit; no division by five occurs.

## 7. Hensel certification and the 140-cycle

Let H = H_-44375 and F = Q_389(u), u² = 2. Its ring of integers has the basis 1,u over Z_389, so

\[
v_{389}(a+bu)=\min(v_{389}(a),v_{389}(b)).
\]

For every stored approximate root r, put s = v_389(H′(r)) and h = v_389(H(r)). Both verifiers check

\[
h>2s,\qquad h-s\ge4.
\]

Strong Hensel lifting therefore produces an actual root ρ with ρ ≡ r modulo 389^4. All 140 residue pairs modulo 389^4 are distinct. Since H is monic of degree 140, these are all its roots. This argument allows H′(r) to be divisible by 389; requiring simple reduction modulo 389 would incorrectly discard many roots.

The independent GP audit evaluates H and H′ in the exact field Q[u]/(u²-2), not through the discovery script's modular arithmetic. It finds min h = 32 and max s = 12, and verifies the required inequality for every individual root. The main receipt records min(h-s) = 32.

For two certified roots, define a candidate edge by

\[
\Phi_2(r_i,r_j)\equiv0\pmod{389^4}.
\]

The exact congruence graph has exactly two neighbors at every vertex and is one cycle of length 140. A modular-polynomial congruence alone would not prove an exact isogeny: it might be a spurious near-zero. The CM argument eliminates this possibility here.

Indeed, 2 splits in K and is prime to the conductor 25. Each characteristic-zero CM curve with endomorphism ring O_25 has precisely two horizontal 2-isogenies, corresponding to the two ideals above 2. Their targets belong to the same CM root set; the two target classes are distinct because the norm-two ideal class has order 140. These exact edges must occur among the congruence candidates, since the certified roots are correct modulo 389^4. There are exactly two candidates, so they are exactly the two horizontal neighbors. The class-group interpretation of horizontal edges is described in Sutherland, §3 [Sutherland].

Walking the cycle without immediately reversing an edge labels the CM classes by successive powers of one fixed ideal above 2, up to inversion and origin. The descending 2-isogeny leaves this order and therefore contributes no additional horizontal root. This proof uses characteristic-zero CM curves; it does not incorrectly apply an ordinary finite-field volcano theorem to the supersingular reduction graph.

Reducing the 140 roots modulo 389 and evaluating v gives the complete function values in this cyclic order. Grouping by the exponent modulo five gives

\[
(b_0,b_1,b_2,b_3,b_4)=(5,-1,-1,5,-8).
\tag{1}
\]

## 8. Ordinary regularization cannot remove the quadratic residue

Let α be the 5-adic unit root of X²-a_5X+5. Here a_5 = -3, so α ≡ 2 modulo five. The other root is not a unit.

Use the full ring class construction of [ChH, §4.2, Definition 4.1 and Lemma 4.2], rather than treating the class-number-one parametrization in the Castella–Hsieh appendix as applicable to K. For p not dividing N the regularized Gross point is

\[
P_n^\dagger=\alpha^{-n}P_n-\alpha^{-n-1}P_{n-1}.
\]

At conductor 25, n = 2. Put G_2 = Pic(O_25), G_1 = Pic(O_5), and let π:G_2→Γ_1. The raw full-orbit sum projects to

\[
B(\gamma)=5-\gamma-\gamma^2+5\gamma^3-8\gamma^4.
\]

The lower-conductor summand factors through G_1. The kernel C = ker(G_2→G_1) has order five, and π restricts to an isomorphism C→Γ_1. For each element of G_1, summing its five preimages therefore produces a multiple of

\[
N_{\Gamma_1}=1+\gamma+\gamma^2+\gamma^3+\gamma^4.
\]

Consequently the projected regularized element has the form

\[
\alpha^{-2}B(\gamma)-\alpha^{-3}S N_{\Gamma_1}
\tag{2}
\]

for an integral lower-level sum S. Any Gross-point translations can be absorbed into translations of the displayed terms. No assumed coherence of the independently chosen lower and upper root orderings is needed for the following jet argument.

Set γ = 1+T. In characteristic five,

\[
N_{\Gamma_1}=\frac{(1+T)^5-1}{T}=T^4.
\]

The lower-conductor correction has zero coefficients in degrees zero through three modulo five, regardless of S. Thus it cannot cancel the quadratic coefficient. The separate arithmetic audit additionally finds S = 0 exactly, but that stronger computation is unnecessary for this conclusion.

The exact first three moments of B are

\[
\sum b_j=0,\qquad \sum jb_j=-20,
\qquad \sum\binom j2b_j=-34.
\]

Their residues are (0,0,1). Therefore the quadratic coefficient of (2) is α^-2 ≡ 4 modulo five in this normalization. Inverting the character convention, changing origin, averaging over tame torsion, or choosing another primitive quaternionic generator only changes the relevant leading coefficient by a unit.

## 9. From a finite jet to exact order two

The first quotient of the Iwasawa algebra has relation

\[
\omega_1(T)=(1+T)^5-1
=5T+10T^2+10T^3+5T^4+T^5
\in(5,T^5).
\]

Hence the finite Γ_1 calculation determines the coefficients of the infinite theta element modulo five through degree four. In particular its nonzero quadratic residue is a valid certificate for a nonzero infinite quadratic coefficient. It does not, by itself, prove exact vanishing of earlier coefficients.

Those exact vanishing statements come from separate arithmetic and theory:

- The exact plus modular symbol for {∞,0} is zero. After identifying the eigenform, the standard modular-symbol special-value formula gives L(E,1) = 0. This exact calculation is in the arithmetic audit.
- At the trivial character, the interpolation formula [ChH, Theorem A] expresses Θ(0)² as a finite scalar times L(E/K,1). Since L(E/K,1) = L(E,1)L(E^-71,1), it follows that Θ(0) = 0 in characteristic zero.
- Here N^+ = 1, the root number of E is +1, and the good local root number at five is +1. The functional equation [ChH, Theorem B] is Θ* = Θ in its distinguished normalization, where T* = (1+T)^-1-1 = -T+O(T²). Comparing linear coefficients gives c_1 = -c_1, hence c_1 = 0. After a translation the equation may acquire a group-like factor with constant term one; the same conclusion holds because c_0 = 0.

We have therefore proved exact c_0 = c_1 = 0 and c_2 a unit. This establishes ord_T Θ = 2. It would be invalid to replace the two exact-zero arguments by the fact that the finite moments are merely zero modulo five.

## 10. Application and remaining boundary

Castella–Hsieh's Theorem B applies to their ordinary, residual, ramification, auxiliary-field, and auxiliary-character setting when E(Q) has positive rank. It turns ord_T Θ = 2 into nonvanishing of the two stated generalized Kato classes [CaH, Theorem B and §5.6].

For this benchmark, the completed separate arithmetic audit supplies the exact modular-form identification, residual hypotheses at p = 5, ramification at 389, the p-regular CM auxiliary form, a non-torsion rational point, and the nonzero quadratic-twist factor. Section 5 above supplies the other auxiliary L-value factor; Sections 6–9 supply the theta order. Applying the published Theorems B and A gives nonzero diagonal generalized Kato classes over the permitted coefficient extension and a two-dimensional rational 5-adic Selmer group. These conclusions use the existing theorem and the now-checked hypotheses.

This is a finite, reproducible application of established theorems. It is not a proof of the rank-two BSD leading-coefficient formula, finiteness of the full Tate–Shafarevich group, or a general criterion eliminating the positive-rank assumption. The separate note `research/localization-obstruction.md` explains why an abstract characteristic-ideal or derived-height calculation cannot silently supply that missing assumption.

## Primary references

- **[Gross]** B. H. Gross, *Heights and the special values of L-series*, 1987, especially Proposition 11.2. [Scanned paper](https://wstein.org/papers/bib/Gross-Heights_and_the_Special_Values_of_L-series.pdf).
- **[LMY]** S.-C. Liu, R. Masri, M. P. Young, *Rankin–Selberg L-functions and the reduction of CM elliptic curves*, 2015. Introduction and §2, especially equations (2.1) and (2.2). [Author PDF](https://sites.math.rutgers.edu/~mpy4/ReductionFinalVersion.pdf).
- **[JRS]** B. W. Jordan, K. A. Ribet, A. J. Scholl, *Modular curves and Néron models of generalized Jacobians*, 2024. §2.2, equation (2.2.3), Theorem 2.4. [Published paper](https://www.cambridge.org/core/journals/compositio-mathematica/article/modular-curves-and-neron-models-of-generalized-jacobians/60031C6B9CE3CA2E79A834EB241978CF).
- **[Sutherland]** A. V. Sutherland, *Isogeny volcanoes*, 2013. §3, the ideal-class action and horizontal isogenies. [Published paper](https://msp.org/obs/2013/1-1/obs-v1-n1-p25-s.pdf).
- **[ChH]** M. Chida, M.-L. Hsieh, *Special values of anticyclotomic L-functions for modular forms*. Theorems A and B, §4.1, Definition 4.1, Lemma 4.2. [Author PDF](https://www.math.ntu.edu.tw/~mlhsieh/research/central.pdf).
- **[CaH]** F. Castella, M.-L. Hsieh, *On the nonvanishing of generalised Kato classes for elliptic curves of rank 2*, Forum of Mathematics, Sigma 10 (2022), e12. Theorem B and §5.6; the class-number-one appendix does not directly cover the field used here. [Published paper](https://doi.org/10.1017/fms.2021.85), [author PDF](https://web.math.ucsb.edu/~castella/Kato.pdf).
- **[FLINT]** Official FLINT documentation: [Hilbert class polynomials](https://flintlib.org/doc/acb_modular/class-polynomials.html), [complex ball polynomial arithmetic](https://flintlib.org/doc/acb_poly/index.html), and [unique integer polynomial extraction](https://flintlib.org/doc/acb_poly.html).
