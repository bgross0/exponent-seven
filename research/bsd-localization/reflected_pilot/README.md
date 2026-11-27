# Executable CM weight jets for the reflected-class pilot

Date: 2026-11-27. Curve (E=389.a1), field (K=\mathbf Q(\sqrt{-71})), prime (p=5).

## Result and its precise scope

The new executable computes the first **two** CM weight coefficients, not just the weight-one eigenforms. The saved dataset contains every q-coefficient through (q^{4096}), modulo (5^{12}=244140625), in the unramified coefficient ring

\[
 (\mathbf Z/5^{12}\mathbf Z)[\zeta_7]
 = (\mathbf Z/5^{12}\mathbf Z)[X]/(1+X+\cdots+X^6).
\]

It covers both embeddings (\omega\equiv2,4\pmod5), where (\omega^2-\omega+18=0). It also supplies the ordinary and slope-one refinements of the elliptic eigenform, raw iterated-integral inputs, and raw **second-order weight-two de Rham inputs** with the necessary oldforms at 389. Generation took 5.676 seconds in this environment using only Python's standard library.

This is independently usable analytic input. It does **not** compute the diagonal class, its local cohomology jet, its projected de Rham regulator, or the finite logarithm of the reflected class. None of those quantities is renamed or substituted by a q-expansion coefficient.

Files:

- `cm_weight_jets.py`: exact generator and finite arithmetic checks.
- `cm-weight-jets.json.gz`: complete coefficients and conventions, deterministically compressed.
- `result.json`: checks, data hash, precision comparison, and a full-space workload estimate.

The supplied upstream package is identified by archive SHA256 `f4d0332acbe087da2dda53a9a380f41c75d3ec63c5ad59441f2a5785ef21531a`. Its 140 CM points and Lean build were not recomputed.

## 1. A compact ideal description removes the need for CM point arithmetic

Put

\[
 \mathfrak a=(2,\omega),\qquad \eta=10+\omega.
\]

Then \(N(\eta)=128\) and \(\mathfrak a^7=(\eta)\). For example, the root of \(X^2-X+18\) modulo 128 selecting \(\mathfrak a\) is 118, so \(10+\omega\) belongs to \(\mathfrak a^7\); equality follows by comparing norms. There is no element of norm 2, so \(\mathfrak a\) is nonprincipal. The exact reduced-form enumeration has seven elements; consequently its seven powers represent all ideal classes.

For (0\le k<7), write

\[
 \mathfrak a^k=(2^k,\omega-r_k),\qquad
 \alpha=2^k x+(\omega-r_k)y,
 \qquad \mathfrak b=(\alpha)/\mathfrak a^k.
\]

Every nonzero integral ideal \(\mathfrak b\) occurs exactly once with \(y>0\), or with \(y=0,x>0\). This removes the only unit ambiguity, \(\{\pm1\}\). The exact identity

\[
 4\cdot2^k N(\mathfrak b)
 =\bigl(2^{k+1}x+(1-2r_k)y\bigr)^2+71y^2
\]

gives finite integer bounds for the enumeration. The code uses integer square roots and verifies each norm identity. For the branch specified by \(\iota_p(\omega)\equiv2\) or 4, the condition \(\mathfrak p\nmid\mathfrak b\) is exactly that \(\iota_p(\alpha)\) is a 5-adic unit, since \(\mathfrak a\) is prime to 5.

No generators of huge seventh powers need to be searched for: the fixed identity \(\mathfrak a^7=(10+\omega)\) handles every class.

## 2. The weight coordinate and the exact jet

Choose \(\psi(\mathfrak a)=\zeta_7\). For the ideal above, \(\psi(\mathfrak b)=\zeta_7^{-k}\). Define

\[
 L_p(\mathfrak b)=
 \frac{\log_5\iota_p(\alpha)-\frac{k}{7}\log_5\iota_p(\eta)}{\log_5 6}
 \in\mathbf Z_5.
\]

This is independent of the choice of generator \(\alpha\), because \(\log_5(-1)=0\). It is additive under multiplication of ideals. The class-representative correction by \(k/7\) is essential.

Write \(s=\kappa-1\) and **\(W=6^s-1\)**. The ordinary CM family in this convention has q-expansion

\[
 g_W(q)=
 \sum_{\substack{\mathfrak b\subset\mathcal O_K\\\mathfrak p\nmid\mathfrak b}}
 \psi(\mathfrak b)(1+W)^{L_p(\mathfrak b)}q^{N\mathfrak b}.
\]

On classical weights \(\kappa\equiv1\pmod4\), this is the theta series of the corresponding Hecke character of infinity type \((\kappa-1,0)\), with its ordinary stabilization. Therefore each ideal contributes

\[
 \zeta_7^{-k}\left(1+L_p(\mathfrak b)W+
 \binom{L_p(\mathfrak b)}2W^2\right)\pmod{W^3}.
\]

The second entry is the coefficient of \(W^2\), **one half of the second derivative in W**. It is not a second derivative in the numerical weight \(\kappa\).

For the branch \(\omega\equiv2\pmod5\), the first useful small fixture is

\[
 [q^2]g_W\equiv
 \zeta_7+\zeta_7^{-1}+2\zeta_7W+\zeta_7W^2
 \pmod{5,W^3}.
\]

The \(U_5\) eigenvalue at the base is \(\zeta_7^2\), and its logarithmic W derivative is

\[
 \frac{\alpha_g'(0)}{\alpha_g(0)}
 \equiv 74800148\pmod{5^{12}},
 \qquad\equiv3\pmod5.
\]

The other branch has base eigenvalue \(\zeta_7^5\) and the same logarithmic derivative. The family \(h_W\) attached to \(\psi^{-1}\) is obtained by applying \(\zeta_7\mapsto\zeta_7^{-1}\) to every coefficient. The base field has degree six because \(\operatorname{ord}_7(5)=6\); no embedding of these individual character values in \(\mathbf Q_5\) is made.

The upstream package uses the generator \(c=\mathfrak a^4\). To match a convention \(\psi(c)=\zeta_{\rm upstream}\), substitute **\(\zeta_7=\zeta_{\rm upstream}^2\)** in this dataset. The present weight coordinate and ideal reciprocity convention are explicit; identifying them with CH's chosen \(\gamma\) still requires the corresponding character-coordinate comparison.

### Precision proof

The implementation computes \(\log_5 u=\frac14\log(u^4)\). If \(z=u^4-1\), then \(v_5(z)\ge1\), and the term \(z^n/n\) has valuation at least \(n-v_5(n)\ge n/2\). Thus omitting terms \(n\ge2N\) gives the logarithm modulo \(5^N\). Guard digits allow exact division by the 5-part of \(n\), followed by inversion of its unit part.

To produce \(L_p(\mathfrak b)\) modulo \(5^{12}\), the code computes the logarithms modulo \(5^{13}\), divides their known factor 5, and inverts the unit \(\log_5(6)/5\). Division by 7 and by 2 introduces no loss. Hensel lifts of \(\omega\) are computed to the required precision.

## 3. The finite checks go beyond comparing saved output

For each branch, the generator checks 9,515 Hecke relations **at each of orders 0, 1, and 2**. For \(\ell\ne5,71\), these are the coefficients of

\[
 a_{\ell n}(W)=a_\ell(W)a_n(W)
 -\chi_{-71}(\ell)(1+W)^{\log_5\ell/\log_5 6}a_{n/\ell}(W),
\]

where the last term is zero unless \(\ell\mid n\). The checks at 5 and 71 use the appropriate degree-one Euler factor. They verify the differentiated ordinary eigenvalue relation as well as the base eigenform.

An independent algebraic specialization checks all 4,096 coefficients at weight 5 modulo 125. It uses a Hensel seventh root of \(\iota_p(\eta)\), integer fourth powers of \(\iota_p(\alpha)\), and **no logarithms**. Since \(W=6^4-1\) has valuation one, omitted integral terms of order \(W^3\) vanish modulo 125.

Other checks verify classical theta conjugation symmetry, p-stabilization, the relation between the two CM types, the ordinary and critical-slope elliptic \(U_5\) equations, and initial packed-convolution coefficients by direct summation. A separate run to 13 digits through \(q^{500}\) agreed after reduction on 17,034 cyclotomic coefficient vectors.

These are exact Python calculations with mathematical error bounds, not additional Lean theorems.

## 4. A concrete input for the missing full de Rham calculation

Darmon–Lauder construct a de Rham-valued family by taking the cohomology class of the weight-two overconvergent form obtained from \((d^{1-\kappa}g_\kappa)h_\kappa\), with the indicated Dirichlet twist/depletion, and projecting to the elliptic factor. Their numerical work retains both slope zero and slope one components. The base-value theorem is proved; the stated arithmetic derivative formula is Conjecture 3.2. Their paper does not supply the needed identity with the full varying regulator of the particular CH class. [DL, Sections 1, 3, 4]

Our actual raw input is explicitly

\[
 \Xi_{a,b}(W)=
 d^{-s}\bigl((V_a g_W)^{[5]}\bigr)\,V_bh_W,
 \qquad(a,b)=(1,389),(389,1).
\]

Here (V_aF(q)=F(q^a)). At a q-index (n) prime to 5, the factor supplied by (d^{-s}) is

\[
 (1+W)^{-\log_5(n)/\log_5 6}.
\]

The code stores \([W^j]\Xi_{a,b}\), for \(j=0,1,2\), under `raw_de_rham_input_cross_oldforms`. In particular the correction at an index \(389n\) includes \(\log_5(389)\); shifting first and differentiating afterwards is necessary. Simply shifting a previously differentiated unraised input would miss this term.

The two cross oldforms are a useful reduction. Both native CM forms have tame level 71. Their unraised product, including its weight derivatives, has zero projection to the new eigensystem of conductor 389. Raising both forms by \(V_{389}\) is again a degeneracy image from level 71 and contributes no new 389 component. Only the two cross pairs can contribute at common level \(71\cdot389=27619\). Their exact linear combination and normalization must match the chosen global test vector.

The dataset separately stores the variant in which (h) is also 5-depleted. These are different raw inputs; no Euler-factor equality is assumed. In particular an “h-only depleted” family cannot be created by silently using (n^{-s}) at indices divisible by 5: the factor (5^{-s}) does not vary analytically in the weight coordinate. The relationship between the displayed formulas in DL Sections 1 and 4 must be tracked with their differential-operator and Euler conventions.

For reference the data also retain
\(d^{-1}(f^{[5]})h_W\), used in the more familiar weight-one iterated-integral projection, and both elliptic refinements

\[
 f_\alpha=f-\beta_fV_5f,\qquad
 f_\beta=f-\alpha_fV_5f,
 \qquad \alpha_f\beta_f=5.
\]

The slope-one refinement is not ordinary, so applying the ordinary projector to it destroys precisely that component.

### What must be supplied before this computes the reflected logarithm

The target in the companion reciprocity note is a calibrated complementary component of the **full local regulator of the same class**. Raw q-jets alone do not identify it. The remaining inputs are:

1. The precise oldform test vectors and the comparison of the ordinary-family, anticyclotomic, and odd reflection coordinates.
2. A certified de Rham reduction and projection retaining both elliptic Frobenius slopes, with denominators and error bounds.
3. An identity between this analytic vector family and the full Perrin–Riou regulator of CH's relaxed class, including the depletion and period factors. The scalar theta reciprocity law does not provide this identity.
4. The calibration of the divided finite component against the local formal logarithm.

The separate Frobenius computation for (E) provides useful data for items 2 and 4. It does not manufacture the projected modular-form class or settle item 3. A nonzero raw q-coefficient, including a second weight coefficient, proves none of those missing steps.

## 5. Feasibility and the next computation worth allocating

Lauder's Katz-expansion algorithm is a genuine polynomial-precision route to ordinary projections, including weight one by a weight shift. The coefficient-extension case is permitted. Its slope-one extension is used by Darmon–Lauder, who point to the eigenprojection method in Loeffler–Skinner–Zerbes, Section 6.3. This is more pertinent to the missing de Rham coordinate than a single cyclotomic modular-symbol L-value. [La, Algorithm 2.1 and Sections 2.2.5, 2.3; DL, Section 4; LSZ, Section 6.3]

The basic whole-space implementation is expensive at this pilot's common level. For a weight-two computation at \(N=27619\), \([\mathrm{SL}_2(\mathbf Z):\Gamma_0(N)]=28080\) and the genus is 2339. Lauder's basic parameters at 12 digits give \(n=19\), maximum classical weight 78, dimension 180182, Sturm bound 182520, and input q-precision 912600. One dense 180182-square matrix takes about 130 GB with four-byte residues, or 260 GB at the stated 16-digit working precision using eight-byte residues. These are bare array sizes for the basic method, not a lower bound for a targeted algorithm or a measured runtime.

Accordingly, the useful next computational step is an **elliptic Hecke-component projection that retains both slopes**, exploiting the two cross oldforms before building a general full-level Katz matrix. A larger unstructured q-expansion run would not resolve the theorem comparison. The 4096-term dataset is a reproducible input and normalization fixture; it is not sufficient q-precision for the basic full-space projection just estimated.

### A further exact reduction: two tame traces to level 389

There is a stronger route around the large common-level matrix. Let
\(\pi_1,\pi_2:X_0(71\cdot389)\to X_0(389)\) be the two standard degeneracy maps, forgetting and quotienting the 71-subgroup. Each has degree 72. On de Rham cohomology their pullbacks and traces satisfy

\[
 \begin{pmatrix}\pi_{1*}\\\pi_{2*}\end{pmatrix}
 (\pi_1^*,\pi_2^*)
 =\begin{pmatrix}72&T_{71}\\T_{71}&72\end{pmatrix}.
\]

The diagonal entries follow from push-pull by the degree of a finite map; the two off-diagonal correspondences are exactly the 71-Hecke correspondence. On the \(E\)-factor, the exact point count gives \(a_{71}(E)=-10\), so this becomes

\[
 G=\begin{pmatrix}72&-10\\-10&72\end{pmatrix},
 \qquad\det G=5084\equiv4\pmod5.
\]

Consequently **both traces recover the entire \(E\)-old component with no 5-adic precision loss from this recovery**. The inverse is \(5084^{-1}\begin{pmatrix}72&10\\10&72\end{pmatrix}\), and the code checks the inverse modulo \(5^{12}\). A single trace could annihilate an oldform combination; retaining both removes that problem. This statement is about cohomological degeneracy pullbacks, so no raw-q oldform normalization factor is silently dropped.

The tame trace commutes with \(U_5\), with Frobenius, and with the de Rham differential, as the relevant prime-to-5 correspondences commute. It must be applied to the **whole product** \(\Xi_{a,b}\); it is not the product of traces of its two weight-one factors. Computing the trace requires expansions at the 72 relevant cosets/cusps, or an equivalent modular-symbol/cohomological representation. An infinity q-expansion alone has not performed that operation. This factor-recovery reduction is proved at the correspondence level, but the traced q-jets have **not** been computed here.

A finite-precision Katz implementation must also track the Hasse/Eisenstein trivialization for **each** map. The second degeneracy map pulls back the lower-level \(E_4\) differently from the first. A termwise trace of coefficients in one shared Katz basis cannot simply be commuted past division by powers of \(E_4\); the pullback factors and their precision must be included. The favorable matrix bounds below are conditional on implementing these two traces in a controlled, bounded-precision overconvergent model.

At target level 389 the genus is 32, the index is 390, and there are two order-two elliptic points, no order-three elliptic points, and two cusps. The weight-78 modular-form dimension is

\[
 (78-1)(32-1)+2\lfloor78/4\rfloor+2(78/2)=2503.
\]

Thus the same basic 12-digit Katz setup would have Sturm bound 2535 and input q-precision 12675, a factor **72** smaller than the common-level q bound. A 2503-square matrix takes **25,060,036 bytes** at four bytes per entry, or **50,120,072 bytes** at eight bytes per entry, about **5182 times** less dense storage. These illustrative workspace bounds replace the common-level matrix estimate after the two traces have actually been constructed; they are not observed runtimes. They exclude cusp-expansion work, additional matrices, eigenprojection denominators and the arithmetic comparison theorem. This is a concrete reduction worth implementing on the next node; it does not depend on the unresolved nonvanishing of the reflected class.

The present environment has Python, NumPy and SymPy; it does not have Sage, Magma, PARI/GP, python-flint or Lean. No large toolchain was installed. A computation on a node with Sage or Magma should first demonstrate the targeted slope-one projection and its precision loss at small precision, with a known low-level regression example, before increasing this pilot's bound.

Ordinary overconvergent modular symbols compute an elliptic eigenform's cyclotomic L-function. Critical-slope symbols require the additional eigenlifting conditions discussed by Pollack–Stevens. Neither output is automatically the complementary regulator of the generalized Kato class. [PS]

## Reproduce or consume

From the repository root:

```sh
python research/bsd-localization/reflected_pilot/cm_weight_jets.py --check
```

Change `--bound`, `--digits` and `--output` to generate a different finite dataset. The default output is overwritten only when `--check` is absent. Each cyclotomic coefficient is a six-entry list in the order \(1,\zeta_7,\ldots,\zeta_7^5\); q-index zero is present and zero.

An output name ending in `.gz` uses gzip with timestamp zero and no embedded filename. The checker reads either compressed or plain JSON. For direct use:

```python
import gzip, json
with gzip.open("research/bsd-localization/reflected_pilot/cm-weight-jets.json.gz", "rt") as f:
    data = json.load(f)
second_q2 = data["branches"]["2"]["g_weight_coefficient_2"][2]
```

## Primary sources

- **La:** Alan Lauder, *Efficient Computation of Rankin p-Adic L-Functions*, Algorithm 2.1; Notes 2.2(3)–(5); Sections 2.2.5 and 2.3. [Author PDF](https://people.maths.ox.ac.uk/lauder/papers/AgbLauderFINAL.pdf).
- **DL:** Henri Darmon and Alan Lauder, *Stark points on elliptic curves via Perrin-Riou's philosophy*, Sections 1, 2.3, 3 and 4. [Author PDF](https://people.maths.ox.ac.uk/lauder/papers/DL.pdf).
- **DLR:** Henri Darmon, Alan Lauder and Victor Rotger, *Stark points and p-adic iterated integrals attached to modular forms of weight one*, Lemma 3.2 and Theorem 3.3. The split-CM rank-(2,0) case has vanishing usual base iterated integrals. [Author-corrected PDF](https://web.mat.upc.edu/victor.rotger/docs/DLR1.pdf).
- **LSZ:** David Loeffler, Christopher Skinner and Sarah Livia Zerbes, *Syntomic regulators of Asai–Flach classes*, Section 6.3, for certified eigenprojection precision via elementary divisors. [Accepted manuscript](https://discovery.ucl.ac.uk/id/eprint/10067174/1/asai_regulator.pdf).
- **PS:** Robert Pollack and Glenn Stevens, *Overconvergent modular symbols and p-adic L-functions*, Theorems 1.1 and 5.14; and *Critical slope p-adic L-functions*. [First paper](https://math.bu.edu/people/rpollack/Papers/Overconvergent_modular_symbols_and_padic_Lfunctions.pdf), [second paper](https://rpollack9974.github.io/web/Papers/Critical_slope_padic_Lfunctions.pdf).
- **CH:** Francesc Castella and Ming-Lun Hsieh, *On the nonvanishing of generalised Kato classes for elliptic curves of rank 2*, Section 2.4, Corollary 3.7 and Section 5. [Published author PDF](https://web.math.ucsb.edu/~castella/Kato-print.pdf).
