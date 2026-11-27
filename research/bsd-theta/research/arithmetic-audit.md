# Arithmetic audit: 389a1 over Q(sqrt(-71)), at p = 29 and p = 5

Date: 27 November 2026. This audit checks the hypotheses of the published Castella–Hsieh rank-two generalized Kato-class criterion. It preserves the original p = 29 candidate and validates p = 5 as a substantially cheaper computational choice. It does not claim a new general theorem about BSD.

The exact computations are reproducible with `scripts/arithmetic_audit.gp`; their output is `data/arithmetic-audit.json`. The conductor-25 root and theta-jet computation is a separate artifact, `data/cm-jet-p5.json`. The finite arithmetic below uses rational numbers, integers, finite fields, and explicitly truncated p-adic arithmetic. No inference of a zero or a nonzero central L-value is made from an approximate decimal value.

## 1. Result and status matrix

Put

\[
E:\quad y^2+y=x^3+x^2-2x,\qquad
K=\mathbf Q(\sqrt{-71}),\qquad
\omega=(1+\sqrt{-71})/2.
\]

Write \(\mathfrak c=[(29,\omega-13)]\in\operatorname{Pic}(\mathcal O_K)\). This class generates the cyclic class group of order seven. Fix the unramified class character \(\psi(\mathfrak c)=\zeta_7\), and put \(\chi=\psi/\psi^\tau=\psi^2\). Take the auxiliary weight-one CM form \(g=\theta_\psi\), with level 71 and nebentype the quadratic character of K.

| Requirement | Exact witness | Status |
| --- | --- | --- |
| Good ordinary p > 3 | p = 29: a_p = −6; p = 5: a_p = −3; neither divides conductor 389 | Checked for both primes |
| p splits in K | Kronecker symbols (−71/29) = (−71/5) = +1 | Checked |
| Discriminant and auxiliary conductor coprime to Np | D_K = −71; conductor of ψ is 1; N = 389 | Checked |
| N-minus squarefree, odd number of inert prime factors | N-minus = 389; (−71/389) = −1; N-plus = 1 | Checked |
| E[p] irreducible | Frobenius at 3 has polynomial X² + 2X + 3, with nonsquare discriminant modulo either prime | Checked |
| E[p] ramified at every prime dividing N-minus | Minimal Δ = 389, c4 = 112; split multiplicative reduction with v389(Δ) = 1 | Checked |
| Absolute irreducibility after extending coefficients | Irreducibility plus a nontrivial unipotent inertia element | Proved below |
| Root number +1 and L(E,1) = 0 | Exact local reduction/root-number computation and zero plus modular symbol | Checked |
| L(E^(−71),1) ≠ 0 | Exact quadratic-twist modular-symbol sum = −4 | Checked |
| L(E/K,χ,1) ≠ 0 | CM period has seven rational coefficients [−1,−1,0,1,1,0,0], which are not all equal | Checked with the cited Gross period identity |
| Distinct weight-one stabilizations | At 29: ζ7, ζ7^−1. At 5: ζ7³, ζ7^−3 | Checked, also after reduction modulo p |
| Positive Mordell–Weil rank | (0,0) lies on E, while reduction orders 6 at 3 and 13 at 7 force trivial rational torsion | Checked |
| Exact constant and linear theta terms zero | Interpolation at the trivial character and the theta functional equation | Proved below |
| Nonzero quadratic theta term at p = 5 | Separate conductor-25 certificate gives raw jet [0,0,1] modulo 5; ordinary correction is zero | Finite arithmetic supplied separately; normalization explained below |
| Nonzero quadratic theta term at p = 29 | No computation attempted after selecting p = 5 | Open in this audit |

The identification of the conductor-25 CM orbit with the finite theta element is supplied in `research/theta-certificate.md`, using the standard CM/Gross-point correspondence and the normalization in §7. Together with that proof, the mod-5 unit coefficient proves order exactly two and the published Castella–Hsieh implication applies. This is an explicit instance of the published theorem; its positive-rank hypothesis is verified for this curve.

## 2. Curve, residual representations, and positive rank

The model has discriminant 389 and c4 = 112. It is therefore minimal, has good reduction outside 389, and has multiplicative reduction of type I1 at 389. The conductor is 389. The reduction is split, and the global root number is +1. These values are computed directly, not inferred from a database label.

The useful good-prime point counts are

\[
\#E(\mathbf F_3)=6,\quad
\#E(\mathbf F_5)=9,\quad
\#E(\mathbf F_7)=13,\quad
\#E(\mathbf F_{29})=36.
\]

Consequently a3 = −2, a5 = −3, a7 = −5 and a29 = −6. The characteristic polynomial of Frobenius at 3 is

\[
X^2-a_3X+3=X^2+2X+3.
\]

Its discriminant −8 is 21 modulo 29 and 2 modulo 5; both are nonsquares. A Galois-stable line over the residue field would be stable under this Frobenius and would force its characteristic polynomial to split. Thus E[29] and E[5] are irreducible.

At 389, Tate uniformization expresses the inertia action through an upper-triangular unipotent matrix whose off-diagonal tame parameter is controlled by v389(Δ) = 1. Since neither 5 nor 29 divides this valuation, the residual inertia action is nontrivial. This verifies the ramification hypothesis in [CH, Theorem A].

It also upgrades the preceding irreducibility to absolute irreducibility. A nonidentity unipotent 2 × 2 matrix has exactly one invariant line over an algebraic closure, and that line is defined over the original finite field. If the entire representation acquired an invariant line after a field extension, it would have to be this line, contradicting irreducibility over the original field.

For positive rank, the point P = (0,0) is visibly rational and is not the identity. Rational torsion injects under good reduction at the odd primes 3 and 7; the two target group orders are 6 and 13, with gcd 1. Hence E(Q) has trivial torsion, and P has infinite order. This is enough for the positive-rank hypothesis of [CH, Theorem B]; no rank-two assumption is used here.

## 3. The auxiliary character and p = 5 coefficient field

The ring of integers is Z[ω], where ω² − ω + 18 = 0. The reduced powers of the prime-29 class are

\[
\begin{array}{c|rrrrrrr}
i&1&2&3&4&5&6&7\\\hline
\mathfrak c^i&(3,1,6)&(2,-1,9)&(4,-3,5)&(4,3,5)&(2,1,9)&(3,-1,6)&(1,1,18).
\end{array}
\]

These are all seven reduced classes. Complex conjugation acts by inversion, so ψ^τ = ψ^−1 and χ = ψ² has exact order seven. In particular g = θψ is cuspidal: ψ is not equal to its conjugate.

Our ideal convention associates the form (a,b,c) with the ideal (a,(−b + √D)/2). Thus the form (29,25,6) gives (29,ω−13). The form (5,3,4) gives (5,ω−2), and reduces to (4,−3,5) = c³. This fixes the character convention:

\[
\psi(\mathfrak p_{29})=\zeta_7,\qquad
\psi(\mathfrak p_5)=\zeta_7^3,\qquad
\chi(\mathfrak p_5)=\zeta_7^6\ne1.
\]

Choosing the conjugate prime in either case inverts these values and leaves regularity unchanged.

At p = 29, μ7 lies in Q29; for example 16 modulo 29 has order seven. At p = 5, take L = Q5(ζ7). This is the unramified extension of degree six, since 5 has order six in (Z/7Z)×, equivalently Φ7 is irreducible modulo 5. Prime-to-5 roots of unity retain their orders under reduction, so ζ7³ and ζ7^−3 are distinct even in the residue field. The weight-one form is p-regular.

The introductory discussion in [CH, §1.1] assumes Qp-valued Hecke fields only for simplicity. The construction in [CH, §2.1] explicitly uses O, the integers of a finite extension L/Qp; §2.4 similarly permits ring-class characters valued in O. The coefficient extension is therefore allowed. For p = 5 one should write the relevant projected generalized Kato class in

\[
\operatorname{Sel}(\mathbf Q,V_5E)\otimes_{\mathbf Q_5}L.
\]

Dimension and nonvanishing statements descend through faithful scalar extension. This does not assert that an arbitrarily normalized individual class is literally Q5-rational.

The ordinary unit roots for f are

\[
\alpha_{29}\equiv139\pmod{29^2},\qquad
\alpha_5\equiv7\pmod{25}.
\]

In particular α5 ≡ 2 modulo 5. These are the unit roots, not the other roots returned by a generic root solver. There is no p ≥ 11 hypothesis in the main theorem: it assumes p > 3. The p ≥ 11 remark supplies an automatic criterion in certain examples, and the paper's appendix itself includes p = 5 examples.

## 4. Exact modular-symbol nonvanishing and vanishing

PARI constructs the weight-two rational modular-symbol spaces at level 389 with signs ±. Their dimensions are 32 and 33 respectively. In each sign, the conditions

\[
T_2=-2,\quad T_3=-2,\quad T_5=-3,\quad T_7=-5
\]

isolate a one-dimensional rational eigenspace. The chosen vectors are primitive integral vectors; they are checked to satisfy the modular-symbol relations. The script also verifies every prime Hecke eigenvalue through the Sturm bound

\[
\left\lfloor\frac{2}{12}[\operatorname{SL}_2(\mathbf Z):\Gamma_0(389)]\right\rfloor
=\lfloor390/6\rfloor=65.
\]

The eigenvalues agree with the exact finite-field traces of E. Hecke multiplicativity and the prime-power recurrences then give agreement through the full bound. Modularity, Eichler–Shimura, and the Sturm theorem identify the eigensymbols with f_E. The non-Eisenstein T2 eigenvalue excludes the Eisenstein component of the plus space.

For the plus symbol, the exact result is

\[
\varphi^+(\{\infty,0\})=0,
\]

which gives L(E,1) = 0. For the minus symbol, the exact result is

\[
S_{-71}:=\sum_{a=1}^{70}\left(\frac{-71}{a}\right)
\varphi^-(\{\infty,a/71\})=-4.
\]

The usual twisting identity comes directly from the Fourier expansion of the integral of f and the Gauss sum of the primitive quadratic character modulo 71. It identifies this sum with a nonzero period/Gauss-sum multiple of L(E^(−71),1). The Gauss sum and the period are nonzero, so the exact integer −4 proves that central L-value is nonzero.

The integer −4 is **not** asserted to be L(E^(−71),1) divided by the minimal real period. The primitive rational eigensymbol has an arbitrary nonzero scaling. Only nonvanishing is needed, and that is insensitive to this scaling. The full symbol vectors, 70 cusp values, and 70 character weights are saved in the JSON evidence.

## 5. Independent supersingular and toric-period audit

The script uses PARI's classical modular polynomial Φ2 to reconstruct the outgoing 2-isogeny matrix on all 33 supersingular j-invariants in F389² = F389[u]/(u²−2). It checks that the listed j-values are distinct and supersingular and that every row has degree three. The known supersingular count is 33, so the list is complete.

The resulting matrix has exactly the same characteristic polynomial as T2 on the plus modular-symbol space. Its eigenvalue −2 has multiplicity one, and its primitive eigenfunction φ agrees, up to sign, with the independently produced supersingular computation. This eigenline is the Jacquet–Langlands line for E.

PARI independently computes H_−71. Its seven roots modulo 389 are distinct and lie among those supersingular j-values. The φ-values at the roots, in the saved j-order, are

\[
[-1,-1,0,1,1,0,0].
\]

The induced norm-two graph is a seven-cycle. Every relevant automorphism weight w_j is one for these seven points. More generally, for the outgoing function matrix the adjoint divisor has coefficients φ_j/w_j, so the Gross period is the unweighted sum of the function values, not an extra multiplication by automorphism weights. [LMY, §2, equations (2.1)–(2.2)] gives this pairing convention and the central L-value identity.

For any nontrivial class character χ, order the class group cyclically and form F(X) = Σ_{i=0}^6 b_i X^i from the corresponding φ-values. If the toric sum F(ζ7) vanished, irreducibility of

\[
\Phi_7(X)=1+X+\cdots+X^6
\]

would imply F is a rational multiple of Φ7. All seven b_i would then be equal. They are not. Thus every nontrivial order-seven class character has a nonzero period, including the selected χ = ψ². No choice of orientation or cyclic starting point can alter this conclusion. The Gross/Waldspurger identity in the cited source therefore gives L(E/K,χ,1) ≠ 0.

This step uses the classical CM reduction/Gross-point correspondence and the period formula as mathematical theorems. The scripts certify their finite arithmetic inputs; they are not formal proofs of those background theorems.

## 6. The class-number-seven correction

The appendix of [CH] assumes class number one. Its single local-orbit formula must not be copied unchanged for K. The main theorems have no such class-number-one assumption, and [CH18, §4.2] supplies the general definition over

\[
G_m=\operatorname{Pic}(\mathbf Z+p^m\mathcal O_K).
\]

Here, for m ≥ 1,

\[
|G_m|=7(p-1)p^{m-1}.
\]

For p = 29 the tame quotient has order 196 and the first wild level, conductor 29², has 5,684 classes. Conductor 29³ has 164,836 classes. For p = 5 the corresponding orders are 28, 140, and 700. This is the reason for selecting p = 5.

The trivial tame branch is obtained by summing over the entire prime-to-p torsion subgroup. All seven ideal-class cosets and all p−1 local tame classes must occur. Multiplying one principal-class orbit by seven would generally be wrong. At finite level, projection to the p-primary quotient must use the group law; a raw arbitrary indexing of coset representatives does not determine it.

For conductor 25, PARI independently verifies that the form (2,1,5547) of discriminant −44,375 has exact order 140. Its 140th power is principal, and its powers at exponents 70, 28 and 20 are nonprincipal. Together with class number 140, this proves G2 is cyclic and the norm-two class generates it. Consequently, after choosing a cyclic origin and orientation, the map to its order-five quotient is exactly cycle index modulo five. Translations and reversal only change the theta element by a group element or the involution; they preserve the order of vanishing and nonvanishing of the leading term.

## 7. Ordinary regularization at conductor 25

For p not dividing N, [CH18, §4.2, Definition 4.1] defines the regularized Gross point and theta element by

\[
P_m^\dagger=\alpha_p^{-m}P_m-\alpha_p^{-m-1}P_{m-1},\qquad
\widetilde\Theta_m=\sum_{\sigma\in G_m}\varphi(\sigma P_m^\dagger)\sigma.
\]

Its natural projections are compatible by [CH18, Lemma 4.2]. Let Γ1 be the order-five quotient of G2 at conductor 25, with generator γ. The raw first summand projects to

\[
A(\gamma)=5-\gamma-\gamma^2+5\gamma^3-8\gamma^4
\]

in the separately saved conductor-25 computation. Expanding γ = 1 + T gives

\[
A(1+T)\equiv T^2\pmod{(5,T^3)},
\]

because its first three integer coefficients are 0, −20, and −34.

The correction term uses the conductor-five classes G1, of order 28. Since |G1| and |Γ1| are coprime, G2 maps isomorphically to G1 × Γ1. Therefore the correction after projection is

\[
\left(\sum_{\sigma\in G_1}\varphi(\sigma P_1)\right)
(1+\gamma+\gamma^2+\gamma^3+\gamma^4).
\]

The script independently factors the exact class polynomial H_−1775 over F389². It retains all root multiplicities, which sum to 28, and computes

\[
\sum_{\sigma\in G_1}\varphi(\sigma P_1)=0
\]

exactly. Thus the projected ordinary correction is zero. Even without this stronger check, its quadratic jet would be zero modulo 5, since 1 + γ + ⋯ + γ⁴ = (γ−1)⁴ in F5[Γ1].

With the displayed primitive φ normalization, regularization therefore multiplies the raw quadratic coefficient by α5^−2. Since α5 ≡ 2 modulo 5,

\[
[T^2]\Theta_{f/K}\equiv 2^{-2}\cdot1=4\pmod5
\]

in this normalization. A different primitive sign, a unit normalization, a Gross-point translation, or a choice of topological generator can alter the displayed unit; none alters its nonvanishing. An averaged rather than summed tame projection also changes the result by a unit because 5 does not divide 28.

## 8. Exact lower zeros and the conclusion supplied by the published theorem

The lower terms require a theorem, not an observation that their residues happen to vanish. At the trivial character the interpolation identity gives

\[
\Theta_{f/K}(0)^2=C\,L(E/K,1)=
C\,L(E,1)L(E^{(-71)},1)=0,
\]

for the finite period/Euler-factor normalization C. Thus Θ(0) = 0 exactly.

The theta functional equation [CH18, Theorem B, or Theorem 4.8] is

\[
\Theta^*=\epsilon_p(f)\epsilon(f)\Theta\,\sigma_{N^+}^{-1}.
\]

Here p is good, so εp(f) = +1; ε(f) = +1; and N-plus = 1. Thus Θ* = Θ. In power-series coordinates, the involution sends T to (1+T)^−1−1 = −T + T² − ⋯. Comparing linear coefficients gives −c1 = c1, hence c1 = 0 in characteristic zero. This proves

\[
\operatorname{ord}_T\Theta_{f/K}\ge2
\]

without relying on finite precision. The normalized nonzero quadratic coefficient then proves equality. At this finite level, the relation (1+T)^5−1 is T⁵ modulo 5, so a coefficient of degree two is well-defined.

With the finite-orbit identification in §7, all hypotheses of [CH, Theorem B] are satisfied at p = 5. It gives nonvanishing of the corresponding diagonal generalized Kato class; [CH, Theorem A] then gives

\[
\dim_{\mathbf Q_5}\operatorname{Sel}(\mathbf Q,V_5E)=2.
\]

This conclusion concerns a rational 5-adic Selmer group and a published nonvanishing criterion. It does not prove the complete BSD leading-coefficient formula, determine the order of the full Tate–Shafarevich group, or establish a general rank-two BSD implication. The positive-rank hypothesis is discharged for this curve by a rational point; it has not been removed from the theorem.

## 9. Reproduction and trust boundary

Run from the project directory:

```sh
/workspace/scratch/a5e8474eb180/deps/pari/gp -fq scripts/arithmetic_audit.gp > data/arithmetic-audit.json
```

PARI/GP version: 2.19.1. The official source archive has SHA-256 `419553b11ff8c3ecb8e9031b7d91d7cee003a5d721e685fcb499565c96fe2943`, checked before the local build. The audit program stops on any failed assertion and emits JSON only on success, including the unique string `PARI_ARITHMETIC_AUDIT_PASS` in its `result` field. It does not append to the data file. Two consecutive fresh runs produced identical valid JSON, exit code zero, and empty standard error. The complete log and replay receipt are `evidence/arithmetic-audit.log` and `evidence/arithmetic-audit-receipt.json`.

Final arithmetic script SHA-256: `bbb5eb508aee7d7055036548270c2c8dd955b07953a50170f62b553a1f57cfdb`. Data/log SHA-256: `3db7f2a91081df0bea5bad013649119625f0b2f9489768eff56e3e16d7303b26`. Its explicit computations are fast; the separate conductor-25 lifting certificate is the larger calculation.

The trust boundary includes PARI's implementation of finite-field, modular-symbol and class-polynomial algorithms, the curve modularity theorem, Eichler–Shimura/Jacquet–Langlands, the Sturm bound, CM reduction, the Gross period identity, and the cited theta construction and functional equation. The project also has a separate checker, `verify_certificate.py`, which reconstructs H_−71 and H_−44375 with rigorous FLINT/Arb balls, complete reduced-form enumeration, and unique-integer coefficient checks, then verifies the saved roots, graph, and moments. The conductor-five zero-sum crosscheck is useful but not required for the mod-five quadratic conclusion, which also follows from the norm-element argument in §7. No end-to-end Lean or other small-kernel proof of the arithmetic theorem is claimed here.

## Sources

- **[CH]** Francesc Castella and Ming-Lun Hsieh, *On the non-vanishing of generalized Kato classes for elliptic curves of rank two*, Forum of Mathematics, Sigma 10 (2022). [Author manuscript](https://web.math.ucsb.edu/~castella/Kato.pdf). Theorems A/B: pp. 4–5; coefficient field: §2.1; theta interpolation: Theorem 2.3; general hypotheses: §5; class-number-one appendix: §6.
- **[CH18]** Masataka Chida and Ming-Lun Hsieh, *Special values of anticyclotomic L-functions for modular forms*, Journal für die reine und angewandte Mathematik 741 (2018), 87–131. [Author manuscript](https://www.math.ntu.edu.tw/~mlhsieh/research/central.pdf). Theorem B: pp. 2–3; regularization and compatibility: §4.2, pp. 19–20; functional equation: Theorem 4.8, pp. 22–23. Page references here follow the author manuscript.
- **[LMY]** Sheng-Chi Liu, Riad Masri, and Matthew P. Young, *Rankin–Selberg L-functions and the reduction of CM elliptic curves*. [Author-hosted manuscript](https://sites.math.rutgers.edu/~mpy4/ReductionFinalVersion.pdf). CM reduction in the introduction; the supersingular pairing, divisor/function convention, and Gross period formula in §2, equations (2.1)–(2.2), printed pp. 7–9.
- **[PARI-MS]** PARI/GP official documentation, [Modular symbols](https://pari.math.u-bordeaux.fr/dochtml/ref/Modular_symbols.html): `msinit`, `msfromhecke`, `mshecke`, `mseval`, and the period convention described under `msfromell`.
- **[PARI]** PARI/GP official [download and release page](https://pari.math.u-bordeaux.fr/download.html) and [function reference](https://pari.math.u-bordeaux.fr/dochtml/html/).
- **[LMFDB]** [389.a1 curve page](https://www.lmfdb.org/EllipticCurve/Q/389/a/1), useful for identification and comparison. The arithmetic witnesses in this audit are recomputed rather than accepted from the database.
