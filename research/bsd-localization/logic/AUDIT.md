# Rank-two BSD route: localization and rationality audit

Date: 2026-11-27. Scope: independent mathematical audit, plus exact rational arithmetic. No Lean proof is claimed. This work does not implement the theta coefficient computation being developed elsewhere.

## Conclusion

The Castella–Hsieh route can certify a **two-dimensional p-adic Selmer group** from a correctly identified theta element of order two and a nonzero localization map. That is a useful theorem, but it does not by itself prove that the Mordell–Weil group has rank two. The quotient between these two objects is the p-adic Tate module of Sha.

There are two separate targets:

1. Construct a second Selmer class whose localization is nonzero. The generalized Kato class itself has zero localization.
2. Prove enough global rationality to place a nonzero strict-localization class in the Kummer image of rational points, or supply two independent rational points by another argument.

For the example E389.a1 at p = 29, the first target is already discharged by the explicit rational point P = (0,0). We independently computed

\[
\log_{\omega_E,29}(P)\equiv29\pmod{29^2},
\qquad \omega_E=dx/(2y+1).
\]

This does not remove the positive-rank input uniformly for arbitrary analytic-rank-two curves. It supplies that input, without numerical approximation, for this particular example.

## 1. Notation and the exact sequence

Write

\[
M=E(\mathbf Q)\otimes_{\mathbf Z}\mathbf Q_p,
\qquad S=\operatorname{Sel}(\mathbf Q,V_pE),
\qquad A=T_p\Sha(E/\mathbf Q)\otimes_{\mathbf Z_p}\mathbf Q_p.
\]

The Kummer exact sequence is

\[
0\longrightarrow M\longrightarrow S\longrightarrow A\longrightarrow0.
\]

Therefore

\[
\dim S=\operatorname{rank}E(\mathbf Q)+\dim A.
\]

Let

\[
\ell:S\xrightarrow{\operatorname{loc}_p}
 E(\mathbf Q_p)\widehat\otimes\mathbf Q_p
 \xrightarrow{\log_{\omega_E}}\mathbf Q_p.
\]

At a good prime the local logarithm is an isomorphism after tensoring with Q_p, so the kernels of loc_p and ell agree. This is a one-dimensional local target. A nonzero global Selmer element can have zero localization.

Reference: Castella–Hsieh [CH22], introduction, Kummer exact sequence, and Remark 1.5. These are the actual Selmer and class-group objects in the paper; no identification S = M is available without another argument.

## 2. Precisely what the literature supplies

Use the hypotheses of [CH22, Theorem A]: p > 3 good ordinary; the specified split imaginary quadratic auxiliary field and weight-one theta series; sign +1 and L(E,1) = 0; the nonvanishing auxiliary L-values; residual irreducibility; the required squarefree inert part of the conductor and residual ramification. The eligibility and literature audits track those hypotheses separately.

Theorem A supplies

\[
\kappa\ne0\quad\Longrightarrow\quad\dim_{\mathbf Q_p}S=2.
\]

Theorem B assumes positive Mordell–Weil rank and proves

\[
\operatorname{ord}_T\Theta_{f/K}=2\quad\Longrightarrow\quad\kappa\ne0.
\]

Inspecting its proof, the positive-rank assumption is used only to produce an x in S with ell(x) nonzero. Thus the following is a valid reformulation of that argument, under the same remaining hypotheses:

\[
\operatorname{ord}_T\Theta_{f/K}=2,
\quad\ell\ne0
\quad\Longrightarrow\quad\kappa\ne0
\quad\Longrightarrow\quad\dim S=2.
\]

The reason is explicit. In the setting of the paper, the first derived-height filtration satisfies S^(2) = S. The leading-term formula specializes to

\[
h^{(2)}(\kappa,x)=c\,\Theta^{(2)}\ell(x)
\]

with c nonzero. If Theta has order two and ell(x) is nonzero, the right side is nonzero; hence kappa is nonzero. This is an inference from [CH22, Theorem 5.3 and Section 5.6], not a new general theorem eliminating localization.

The later paper [C26, Theorem A / Theorem 5.2.3] sharpens the relation: when dim S = 2, kappa is nonzero if and only if loc_p is nonzero, and then kappa spans ker(loc_p). In particular, it does **not** prove that nonzero localization always holds in analytic rank two.

### The class that cannot provide the localization witness

In this rank-(2,0) setting,

\[
\operatorname{loc}_p(\kappa)=0.
\]

This is stated explicitly in [C26, Remark 5.1.4] and reflected in [CH22, Remark 1.6]. A strategy asking the same generalized Kato class to have nonzero localization is incompatible with its local condition. A successful localization witness must be another class.

### A common circular step

The formula expressing kappa as a multiple of

\[
\log_p(Q)P-\log_p(P)Q
\]

is not automatically a construction of rational points P and Q. In [C26] they may be a basis of S, not a basis of rational points. In [CH22, Section 5.7 / Theorem 5.5], the identification with E(Q) tensor Q_p is made **after adding finiteness of Sha[p^infinity]**. Using that identification to prove the missing finiteness or rationality would be circular.

## 3. Explicit countermodels to the insufficient inference

These are countermodels to a proposed inference from linear algebra and an exact sequence. They are **not elliptic curves**, are not counterexamples to BSD, and make no claim that the indicated Sha behavior occurs for an actual curve.

Take S = Q^2, with

\[
\ell(x,y)=x,\qquad\kappa=(0,1),
\qquad h((a,b),(c,d))=bc-ad.
\]

Then dim S = 2; ell is nonzero; kappa is nonzero and spans ker(ell); h is nondegenerate and alternating; and

\[
h(\kappa,x)=\ell(x)
\]

for every x in S. Thus even the elementary shape of the leading-term formula is present.

* Model 0: M = 0, A = Q^2, and S to A is the identity. All the preceding assertions hold, but dim M = 0.
* Model 1: M = Q(1,0), A = Q, and S to A is (x,y) maps to y. Again all assertions hold, but dim M = 1. The localization is nonzero even on M.

Both models remain valid after extending scalars to Q_p. They demonstrate that neither Selmer dimension two, nor a nonzero localization map, nor even a positive-rank Kummer subspace and the displayed height identity, alone forces M to have dimension two.

Do not use a parity statement about the p-infinity Selmer corank as though it were an unconditional parity statement about the Mordell–Weil rank: the Tate-module contribution of Sha is exactly what this proposed route must address.

## 4. A useful sufficient proposition with a smaller arithmetic target

**Proposition (a nonzero strict class in the Kummer image).** Let E/Q be an elliptic curve, let p be an odd good prime, and suppose dim S is at most two. If

\[
0\ne\kappa\in M\subseteq S,
\qquad\operatorname{loc}_p(\kappa)=0,
\]

then rank E(Q) = 2 and Sha(E/Q)[p^infinity] is finite.

**Proof.** Nonzero kappa in M excludes rank zero. If rank were one, M would be spanned over Q_p by a non-torsion rational point P. Such a point has nonzero p-adic logarithm: after multiplication by a nonzero integer it enters the formal subgroup, on which the logarithm is injective; a zero logarithm would therefore make P torsion. Thus localization is injective on the one-dimensional M, contradicting the existence of kappa. Consequently dim M is at least two. The injection M into S and dim S at most two give M = S and dim M = 2. Hence V_p Sha = 0. The p-primary Sha group is cofinitely generated over Z_p, being a quotient of the p-infinity Selmer group; zero divisible corank therefore makes it finite. QED.

Under Castella–Hsieh's hypotheses, their nonvanishing theorem supplies dim S = 2 once kappa is nonzero. The remaining hypothesis in this proposition is the **geometricity of this particular strict Selmer class**:

\[
\kappa\mapsto0\text{ in }V_p\Sha.
\]

This is weaker as a stated input than assuming all of Sha[p^infinity] finite, but proving it is a serious arithmetic problem. It is not established by the finite theta coefficient computation.

An alternative sufficient input is two independent rational points. Then dim S = 2 implies rank two and finiteness of Sha[p^infinity] directly. The neighboring eligibility audit supplies an elementary finite-field independence certificate for (0,0) and (1,0) on E389.a1.

Neither conclusion proves finiteness of all of Sha, the BSD leading-term formula, or the implication for every elliptic curve of analytic rank two.

## 5. Independent finite localization certificate for E389.a1

Use the integral model

\[
E:y^2+y=x^3+x^2-2x,
\qquad P=(0,0).
\]

Its discriminant is 389, so 29 is a good prime. Exact enumeration gives #E(F_29) = 36 and a_29 = -6, so the reduction is ordinary. Exact rational addition computes R = [36]P. With z(R) = -x(R)/y(R), the results are

\[
v_{29}(z(R))=1,
\qquad z(R)\equiv203=7\cdot29\pmod{841}.
\]

Because R reduces to the identity, it belongs to the formal subgroup. Write the invariant differential in its integral local parameter as

\[
\omega_E=(1+\sum_{j\ge1}b_jz^j)dz,
\qquad b_j\in\mathbf Z_{29}.
\]

Then

\[
\log_{\omega_E}(R)=z(R)+
 \sum_{n\ge2}\frac{b_{n-1}}n z(R)^n.
\]

For n at least two, n - v_29(n) is at least two, so every displayed remainder term is divisible by 29 squared. Thus log(R) = 203 modulo 841. Since 36 is a 29-adic unit and 36 times 29 is 203 modulo 841,

\[
\log_{\omega_E}(P)\equiv29\pmod{841}\ne0.
\]

This certifies a nonzero localization of the global Kummer class of P and, independently, shows P is non-torsion. The computation uses only Python integers and exact fractions. The formal-group argument is supplied above; it is not formalized in the program.

The eligibility agent independently replicated z(R) = 203 modulo 841 using a separately written rational group law. Its separate reduction argument at 3 and 7 also rules out rational torsion.

Run from the repository root:

```sh
python research/bsd-localization/logic/verify_logic.py
```

The script prints the exact arithmetic results, verifies the two abstract countermodels, and checks the finite-precision examples below. It imports no numerical, elliptic-curve, or theta libraries.

## 6. What a finite theta certificate must actually imply

Let Theta(T) = sum a_j T^j be the correctly normalized infinite theta element.

* A certified a_2 nonzero modulo p^m proves a_2 is nonzero in Q_p, hence ord_T Theta is at most two.
* It does not prove a_0 = a_1 = 0. For any m, the three series T^2, p^m + T^2, and p^m T + T^2 have identical reductions modulo p^m but orders two, zero, and one respectively.
* One needs exact lower-order vanishing from a separate theorem. A clean sufficient route is Theta(0) = 0 and a functional equation Theta((1+T)^(-1)-1) = u(T)Theta(T), with u(0) = +1. Comparing the first nonzero coefficient gives (-1)^r = 1, so a nonzero series vanishing at zero has even order at least two. The exact functional-equation sign must be checked in the normalization used.
* For the quotient by (1+T)^(p^n)-1, coefficients through degree two are unambiguous modulo p^m when n is at least m and p is odd: the coefficients of T and T^2 in the quotient relation are divisible by p^n. Modulo p alone the quotient is F_p[T]/(T^(p^n)).
* A unit change of topological generator scales the first nonzero degree-two coefficient by a unit square; multiplication of Theta by an integral unit also preserves its nonvanishing. This does not justify an arbitrary change of p-stabilization, trace, or interpolation normalization.
* K = Q(sqrt(-71)) has class number seven, whereas the simplified [CH22] appendix formula is presented for class number one. The full ideal-class sum/projection must be accounted for in the finite-to-infinite identification.

The literature audit identified an unresolved dictionary issue between the forward-neighbor expression in the [CH22] appendix and the usual backward-neighbor p-stabilized Gross-point formula. Do not treat a raw finite sum as the published Theta until its norm compatibility and identification have been proved. This audit does not resolve that normalization issue or assert a typographical error in the paper.

## 7. Acceptance criteria for the next step

For a valid example-level conclusion, independently establish:

1. The theorem's arithmetic/auxiliary hypotheses, including nonzero auxiliary complex L-values, without interpreting database analytic Sha as a theorem.
2. Identification of the finite theta object with the infinite theta element in the theorem, with the exact projection, p-stabilization, and level convention.
3. An exact lower bound of two for its T-adic order, and a finite certificate of nonzero degree-two coefficient.
4. A nonzero localization witness distinct from kappa. For E389.a1 this audit already supplies it.
5. Two independent rational points, or the geometricity proposition's Kummer-membership input, if the desired conclusion concerns Mordell–Weil rank and Sha[p^infinity].

For a uniform theorem from analytic rank two, steps 2–5 must be replaced by general implications, not a finite list of successful examples.

## Primary references

* **[CH22]** F. Castella and M.-L. Hsieh, *On the nonvanishing of generalised Kato classes for elliptic curves of rank 2*, Forum of Mathematics, Sigma 10 (2022), e12. Theorems A/B; Remarks 1.5/1.6; Theorem 5.3; Sections 5.6 and 5.7; appendix. [Published HTML](https://www.cambridge.org/core/journals/forum-of-mathematics-sigma/article/on-the-nonvanishing-of-generalised-kato-classes-for-elliptic-curves-of-rank-2/72ED842AB428A7ED619B1B84287A6864), [author's published PDF](https://web.math.ucsb.edu/~castella/Kato-print.pdf), [author's preprint](https://web.math.ucsb.edu/~castella/Kato.pdf).
* **[C26]** F. Castella, *Nonvanishing of generalised Kato classes and Iwasawa main conjectures*, Springer Proceedings in Mathematics & Statistics 527 (2026), 23–50; author's PDF dated June 20, 2024. Theorem A; Remark 5.1.4; Theorem 5.2.3. [Author's PDF](https://web.math.ucsb.edu/~castella/GKC-IMC.pdf), [publication listing](https://web.math.ucsb.edu/~castella/).
* **[CH18]** M. Chida and M.-L. Hsieh, *Special values of anticyclotomic L-functions for modular forms*, J. Reine Angew. Math. 741 (2018), 87–131. Theorem B, Section 4.2, Lemma 4.2, Theorem 4.8. [Author's PDF](https://www.math.ntu.edu.tw/~mlhsieh/research/central.pdf).
* **LMFDB**, curve 389.a1, used to verify the model and to distinguish recorded rank from analytic Sha. [Curve record](https://www.lmfdb.org/EllipticCurve/Q/389/a/1), [raw data](https://www.lmfdb.org/EllipticCurve/Q/data/389.a1). The exact arithmetic in this audit does not assume its rank or Sha entries.
