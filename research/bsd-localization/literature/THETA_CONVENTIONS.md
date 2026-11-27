# Theta certificates: group projection, conductor indexing, and normalization

Audit date: 2026-11-27. This note separates the source definition from elementary deductions needed by a finite certificate. No theta coefficient for $K=\mathbf Q(\sqrt{-71})$ is asserted to have been computed here.

## Primary definition

**Chida–Hsieh**, *Special values of anticyclotomic L-functions for modular forms*, Journal für die reine und angewandte Mathematik **741** (2018), 87–131. [Author PDF, dated 2016-01-05](https://www.math.ntu.edu.tw/~mlhsieh/research/central.pdf), [arXiv record](https://arxiv.org/abs/1204.2427), [published DOI](https://doi.org/10.1515/crelle-2015-0072).

The linked author's PDF has 34 pages. Section 4.2, Definition 4.1, p. 19, defines theta elements using all of

\[
G_m=\operatorname{Pic}(\mathbf Z+p^m\mathcal O_K),\qquad m\ge1.
\]

For weight two and good ordinary $p$, the regularized Gross point is

\[
P_m^\dagger=\alpha^{-m}P_m-\alpha^{-(m+1)}P_{m-1},
\quad
\widetilde\Theta_m=\sum_{\sigma\in G_m}\phi(\sigma P_m^\dagger)[\sigma].
\]

Lemma 4.2, p. 20, supplies compatibility under $G_{m+1}\to G_m$. Section 4.3, p. 22, takes the quotient by the finite torsion subgroup $\Delta\subset G_\infty$, then the chosen character of $\Delta$. The trivial character sends every $\delta$ to one. Hence this projection **sums coefficients over each torsion fiber**; it does not divide by $|\Delta|$. The functional equation is Theorem 4.8, pp. 22–23.

## Elementary group calculation for −71 at 29

Put $\omega=(1+\sqrt{-71})/2$, so $\omega^2-\omega+18=0$. The units are $\{\pm1\}$. The standard ideal-class exact sequence gives

\[
1\to(\mathcal O_K/29^m)^\times/(\mathbf Z/29^m)^\times
\to G_m\to\operatorname{Cl}(\mathcal O_K)\to1.
\]

Because $29$ splits, the kernel is the ratio of the two local coordinates, isomorphic to $(\mathbf Z/29^m)^\times$. Using $h_K=7$,

\[
|G_m|=7\cdot28\cdot29^{m-1}=196\cdot29^{m-1}.
\]

Its prime-to-$29$ subgroup has order $196$, and its wild quotient has order $29^{m-1}$. The finite subgroup need not be guessed to be $C_7\times C_{28}$.

In fact there is an explicit cyclicity test. For $\mathfrak a=(2,\omega)$, the relation

\[
\mathfrak a^7=(10+\omega),\qquad N(10+\omega)=128
\]

gives a local ratio. Its values, calculated here by integer Hensel lifting, are:

| $m$ | $\omega$ at the first prime | conjugate root | $(10+\omega)/(10+\bar\omega)\pmod{29^m}$ |
|---:|---:|---:|---:|
| 1 | 13 | 17 | 3 |
| 2 | 477 | 365 | 322 |
| 3 | 20661 | 3729 | 18824 |
| 4 | 288940 | 418342 | 677327 |

The value $3$ has order $28$ modulo $29$, and

\[
322^{28}\equiv610=1+21\cdot29\pmod{29^2}.
\]

Consequently this ratio generates $(\mathbf Z/29^m)^\times$ for every $m$, by the elementary lifting argument for odd primes. Once the global ideal relation and class-group presentation are certified, a lift of $\mathfrak a$ therefore generates $G_m$, which is cyclic of order $196\cdot29^{m-1}$. Inverting the reciprocity convention inverts the ratio but does not alter this conclusion. The neighboring projection note proves the global ideal presentation and the all-level claim; its code checks the finite arithmetic premises. These mathematical arguments have not been formalized in Lean.

## Canonical projection and its normalization

For an abelian group of order $196\cdot29^n$, let $e$ satisfy

\[
e\equiv0\pmod{196},\qquad e\equiv1\pmod{29^n}.
\]

Then $g\mapsto g^e$ is the canonical projection to the $29$-primary subgroup. It kills every prime-to-$29$ element and fixes every $29$-power-order element. This avoids assuming that arbitrarily chosen lifts of the seven ordinary ideal classes have zero wild coordinate.

If $g=\delta\gamma^i$ and $\widetilde\Theta=\sum_g a_g[g]$, the trivial-branch pushforward is

\[
\Theta=\sum_i\left(\sum_{\delta\in\Delta}a_{\delta\gamma^i}\right)[\gamma^i].
\]

An implementation that instead takes an average over the $196$ elements obtains $\Theta/196$, a unit multiple in $\mathbf Z_{29}$. Such averaging preserves nonvanishing and order, but changes benchmark coefficients. The idempotent $e_\Delta=196^{-1}\sum_\delta[\delta]$ is compatible with the **sum** normalization under the identification $e_\Delta[\gamma^i]\mapsto[\gamma^i]$; taking a single coefficient of $e_\Delta\widetilde\Theta$ is a different operation.

## Conductor index versus wild-layer index

Reserve $m$ for the conductor exponent in $29^m$, and $n=m-1$ for the wild layer of order $29^n$. With $\gamma\mapsto1+T$, that layer has relation

\[
\omega_n(T)=(1+T)^{29^n}-1.
\]

For $n\ge1$ and every $1\le j<29$, the coefficient $\binom{29^n}{j}$ has $29$-adic valuation $n$. Thus a compatible level-$n$ element determines all coefficients of degree below $29$ modulo $29^k$ whenever $n\ge k$.

| Required coefficient precision | Minimum wild layer $n$ | Conductor exponent $m$ | $|G_m|$ | wild quotient size |
|---|---:|---:|---:|---:|
| modulo $29$ | 1 | 2 | 5684 | 29 |
| modulo $29^2=841$ | 2 | 3 | 164836 | 841 |
| modulo $29^3$ | 3 | 4 | 4780244 | 24389 |

This is an indexing calculation, not an assertion that these levels suffice for every desired valuation: if the quadratic coefficient vanishes to higher $29$-adic order, precision must increase.

The first useful attempt is therefore **modulo $29$**, at conductor exponent $m=2$, using the $5684$ full group values and a $29$-element wild quotient. If the quadratic coefficient is nonzero, that precision already certifies its nonvanishing. Escalate to modulo $841$ and $m=3$ with $164836$ full group values only if the first test vanishes or exact comparison with the published modulo-$841$ fixture is desired. No full expanded polynomial is needed to accumulate the constant, linear, and quadratic coefficients.

## Published regression fixture and unresolved dictionary

**Castella–Hsieh 2022**, [published PDF](https://web.math.ucsb.edu/~castella/Kato-print.pdf), Table 1, p. 30, includes

\[
E=389.a1,\quad K=\mathbf Q(\sqrt{-7}),\quad p=29,
\qquad
\Theta\equiv148T^2+31T^3+O(T^4)\pmod{(841,T^{29})}.
\]

This fixture is sourced, **not independently recomputed**. It is not a fixture for $K=\mathbf Q(\sqrt{-71})$. The appendix assumes class number one, a primitive quaternionic eigenfunction modulo $p$, $u=1+p$, and the displayed Gross-point representatives. Scaling the eigenfunction, changing the chosen generator, or translating the initial Gross point can change the coefficients.

There is an unresolved normalization dictionary: that appendix prints

\[
\alpha^{-(n+1)}\sum_{i=0}^{p^n-1}\sum_{a\in\mu_{p-1}}
\bigl(\alpha\phi(P_n^{au^i})-\phi(P_{n+1}^{au^i})\bigr)(1+T)^i,
\]

with $P_n^a$ built from $\begin{psmallmatrix}1&ap^{-n}\\0&1\end{psmallmatrix}$. This is not obtained from the preceding regularization by merely substituting $m=n+1$. Two independent audit agents found the same mismatch under the usual raw-point trace convention. We have **not** proved that the published formula is erroneous; different point conventions must first be reconciled. A certificate must explicitly check its distribution relation and its match to a primary theta definition before claiming theorem-level theta nonvanishing.

## Exact lower-order vanishing is a separate proof obligation

Zeros of the constant and linear coefficients modulo $841$ do not prove that those coefficients vanish in $\mathbf Z_{29}$. For this pilot, an available exact route is:

1. The interpolation formula and $L(E,1)=0$ give $\Theta(0)=0$.
2. In the Chida–Hsieh normalization, the positive functional-equation sign gives $\Theta(T)=\Theta((1+T)^{-1}-1)$ when $N^+=1$, hence $a_1=-a_1$, so $a_1=0$. Translating the initial point can insert a group unit with constant term one into this equation; with $a_0=0$, the same conclusion about $a_1$ follows. The precise cubic coefficient is sensitive to this distinction.
3. A certified nonzero quadratic coefficient modulo $29^k$ then proves $\operatorname{ord}_T\Theta=2$.

Every arrow requires the same branch, normalization, and generator conventions. Only the final finite nonzero-coefficient check is supplied by a theta jet computation.
