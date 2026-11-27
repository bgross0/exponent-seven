# The localization obstruction in the rank-two Castella–Hsieh route

Status: mathematical obstruction analysis, 27 November 2026. This note proves elementary logical limitations and states an arithmetic research obligation. It does **not** prove a new nonvanishing theorem, exhibit an elliptic-curve counterexample, or remove a hypothesis from Castella–Hsieh.

## 1. The exact obligation

Let

\[
V=V_pE,\qquad S=\operatorname{Sel}(\mathbf Q,V),\qquad
\ell=\log_{\omega_E}\circ\operatorname{Loc}_p:S\longrightarrow\mathbf Q_p.
\]

Use the precise ordinary, residual, ramification, auxiliary-field, and auxiliary-character hypotheses of Castella–Hsieh, rather than replacing them with an informal assertion that the curve is ordinary. The proposed strengthening of their Theorem B requires proving

\[
\operatorname{ord}_{s=1}L(E,s)=2,
\quad \operatorname{ord}_T\Theta_{f/K}=2
\quad\Longrightarrow\quad \ell\ne0
\]

under those remaining hypotheses.

In [CH, Theorem B and §5.6], positive Mordell–Weil rank is used to obtain this nonzero localization. Their leading-term formula [CH, Theorem 5.3] has the relevant shape

\[
h^{(2)}(x,\kappa)=c\,\Theta_2\,\ell(x),
\qquad c\ne0,\quad\Theta_2=[T^2]\Theta_{f/K}\ne0.
\tag{1}
\]

Here the statement is schematic only in its nonzero normalization factor; implementing it requires the paper's exact fields, differentials, Euler factors, and height target. The proof uses the second derived Selmer stage, identified with the full Selmer group in its setting. Equation (1) makes a nonzero value of \(\ell\) sufficient for \(\kappa\ne0\). It supplies no such value by itself.

## 2. A proved linear-algebra obstruction

**Proposition.** A two-dimensional Selmer-shaped vector space, a nondegenerate second derived-height-shaped alternating pairing, a nonzero quadratic theta coefficient, and identity (1) do not logically imply nonzero localization.

**Proof.** Take a field \(k\) of characteristic zero and set

\[
S=k^2,\qquad
h((a,b),(c,d))=ad-bc,\qquad
\ell=0,\qquad\kappa=0.
\]

The pairing is alternating and nondegenerate. For any \(c,\Theta_2\in k^\times\), both sides of (1) vanish for every \(x\). All the listed inputs hold and \(\ell\ne0\) fails. ∎

This is an **abstract consistency model**, not a Galois representation, a Selmer group known to come from an elliptic curve, or a counterexample to BSD. Its precise purpose is to reject a proof that uses only the listed algebraic inputs.

If the pairing in (1) is nondegenerate on all of \(S\), then (1) actually gives

\[
\kappa=0\quad\Longleftrightarrow\quad\ell=0.
\]

It identifies the obstruction rather than eliminating it.

## 3. Why a main-conjecture determinant is not enough

An equality of characteristic ideals constrains a module; it does not determine an additional localization morphism out of its specialization. The following model makes the distinction explicit.

Let \(R=k[[T]]\) and

\[
X=(R/(T^2))^{\oplus2},\qquad \Theta=T^2.
\]

Then

\[
\operatorname{char}_R(X)=(T^4)=(\Theta^2),
\qquad X/TX\simeq k^2.
\]

Put the preceding nondegenerate alternating form on \(X/TX\), and choose its localization-shaped functional to be zero. This realizes the characteristic-ideal identity and the desired specialization dimension without a nonzero localization functional.

Again, this is a module-level model. We have not shown it is realizable by arithmetic, carries every structure of an actual Selmer complex, or satisfies every theorem about one. Its use is narrower: a characteristic ideal, dimension count, and alternating regulator do not, as abstract data, specify localization.

A nonzero determinant of \(h^{(2)}\) does not help: that determinant is already nonzero in the model. A stronger determinant identity *could* help if it involves the actual localization map and identifies a mixed regulator with an independently nonzero arithmetic quantity. Proving that identity and its nonvanishing would be the new arithmetic input. It cannot be inferred by calling the existing height determinant an enhanced regulator.

When applying any strict/relaxed main conjecture, record precisely which Selmer complex it concerns, whether its specialization is exact, and the local Euler or exceptional-zero factors. An equality for one local condition is not automatically an equality for another.

## 4. What global duality can and cannot say

To explain the dimensional issue without asserting an unverified arithmetic exact sequence, consider the following **comparison template**:

\[
0\to S_{\mathrm{str}}\to S
\xrightarrow{\ell}L
\to S_{\mathrm{rel}}^\vee
\to S^\vee\to0.
\tag{2}
\]

In applications this template is suggested by Poitou–Tate comparison for nested Selmer structures: strict condition \(0\) versus ordinary/Bloch–Kato finite condition at \(p\), with dual local conditions full versus the annihilator finite condition. It is **not asserted here as an unconditional exact sequence for the selected elliptic curve**. A rigorous use must fix coefficients (finite, integral, or rational), the set of allowed ramification, conditions at every place, the duality convention, and all terminal or invariant terms. Over rational coefficients one must justify the passage from finite or integral duality and any completion or dual involved.

Even if (2) is established exactly and \(\dim L=1\), it does not force \(\ell\ne0\). The dimensions

\[
\dim S_{\mathrm{str}}=2,\quad \dim S=2,
\quad\dim L=1,\quad\dim S_{\mathrm{rel}}=3
\]

are compatible with an exact sequence having \(\ell=0\). Explicitly, take the first map to be the identity, inject \(L\) as the first summand of \(L\oplus S^\vee\), and use projection to \(S^\vee\) as the last map.

If \(\ell\) is surjective, the alternative dimensions are \(\dim S_{\mathrm{str}}=1\) and \(\dim S_{\mathrm{rel}}=2\). Thus a theorem excluding the extra relaxed direction would suffice, **after** proving the exact comparison sequence. Duality alone accommodates both alternatives.

## 5. The Mordell–Weil versus divisible-Shafarevich–Tate distinction

The ordinary rational Selmer group fits into

\[
0\to E(\mathbf Q)\otimes_{\mathbf Z}\mathbf Q_p
\to S
\to T_p\Sha(E/\mathbf Q)\otimes_{\mathbf Z_p}\mathbf Q_p
\to0.
\tag{3}
\]

Here

\[
T_p\Sha=\varprojlim_r\Sha[p^r]
\]

uses the multiplication-by-\(p\) transition maps. See [CH, Introduction, the exact sequence defining its rational \(p\)-adic Selmer group]. The last term concerns compatible \(p\)-divisibility, not the size of a finite \(\Sha[p]\) group. A finite \(p\)-primary subgroup contributes zero to this Tate module.

Consequently \(\dim S=2\) alone permits the structural possibility

\[
\operatorname{rank}E(\mathbf Q)=0,
\qquad
\dim_{\mathbf Q_p}(T_p\Sha\otimes\mathbf Q_p)=2.
\]

An even-dimensional contribution is not excluded by a parity statement. We assert no known curve with this behavior.

For the good-reduction local situation at issue, a non-torsion rational point has nonzero local logarithm: the kernel of the extended elliptic logarithm on \(E(\mathbf Q_p)\) is torsion, and an embedded rational point cannot become a torsion point without having been torsion already. Therefore \(\ell=0\) forces the rational Mordell–Weil rank to be zero. The converse is **not** asserted: (3) does not identify the localization map on its quotient with zero.

Assuming finite \(\Sha[p^\infty]\) together with \(\dim S=2\) would give rank two and hence nonzero localization. That is a sufficient hypothesis, but it would bypass rather than solve the desired arithmetic gap. Finite \(\Sha[p^\infty]\) must also not be confused with finiteness of the entire Tate–Shafarevich group.

## 6. Finite-level classes require a lifting proof

A class \(c_m\in\operatorname{Sel}_{p^m}(E/\mathbf Q)\), even with a nonzero local image, need not certify a nonzero rational Selmer localization. It may be torsion, fail to lift through the inverse system, or carry local finite-coefficient information that disappears after tensoring with \(\mathbf Q_p\).

A valid certificate of the desired conclusion can instead start with an actual class

\[
z\in\operatorname{Sel}(\mathbf Q,T_pE)
\]

whose compatible global construction is proved. If, in a fixed integral normalization with certified precision, the local logarithm of \(z\) has a nonzero residue modulo \(p^m\), then its rational localization is nonzero. The finite computation certifies the logarithm; the global construction and compatibility certify that it belongs to the correct Selmer group.

One cannot substitute success in lifting through finitely many levels for a theorem producing compatible lifts at every level.

## 7. The strongest noncircular sufficient arithmetic input

The most direct target is:

> Construct, under the stated curve/prime/auxiliary hypotheses, a global ordinary Selmer class \(z\) together with an explicit local reciprocity law whose right-hand side is independently proved nonzero. In particular prove \(\ell(z)\ne0\), without assuming positive Mordell–Weil rank, finiteness of \(\Sha[p^\infty]\), or nonvanishing of the generalized Kato class being sought.

Equivalent structural targets, when their comparison sequences are fully established, are \(S_{\mathrm{str}}\ne S\), or the absence of the extra relaxed Selmer direction. None follows from the preceding abstract inputs.

For a particular curve, an explicit rational point proved to be non-torsion supplies a sound certificate. This discharges the published theorem's hypothesis for that curve; it does not remove the hypothesis uniformly. Explicit descent can also provide arithmetic information, but finite-coefficient outputs need the lifting check just described.

### A concrete research test for a derived-class construction

If attempting a new proof via an Iwasawa cohomology family and its Bockstein/augmentation derivatives, require these separate lemmas:

1. **Global divisibility or lift.** Prove the needed division by \(T\) or \(T^2\) in the correct global cohomology module, or construct an equivalent derived global class. Vanishing of a Coleman-map image to order two proves only a statement about that image, not global divisibility.
2. **Correct local condition after specialization.** Prove the derived class lands in the ordinary/Bloch–Kato finite Selmer group. A nonzero image in a relaxed or singular local quotient is not the desired nonzero finite localization.
3. **Nonzero logarithm.** Prove a reciprocity law connecting this class's finite local logarithm to certified nonzero arithmetic data, including every Euler factor and normalization.

The point of this test is to locate where the obstruction lives. It is not a claim that these lemmas hold for a proposed family. If the only available specialization yields the original zero-logarithm generalized Kato direction, it does not solve the transversality problem.

## 8. Decision rule for the current project

Proceed with finite theta certificates and exact checks of the published theorem's hypotheses. Keep the hypothesis-removal target as a separate open theorem.

Do not describe a proof as removing positive rank if it assumes a non-torsion point, finite \(\Sha[p^\infty]\), a nonzero localization, or an equivalent strict/relaxed codimension statement without proving it from independent arithmetic input. Do not report a characteristic-ideal calculation or nondegenerate derived-height determinant as proof of that missing codimension.

## Primary reference

[CH] Francesc Castella and Ming-Lun Hsieh, *On the nonvanishing of generalised Kato classes for elliptic curves of rank 2*, Forum of Mathematics, Sigma 10 (2022), e12. [Published article](https://doi.org/10.1017/fms.2021.85), [author's PDF](https://web.math.ucsb.edu/~castella/Kato.pdf). Relevant locations: Theorems A and B, Remark 1.5, Theorem 4.1, Theorem 5.3, and §§5.4–5.6. The paper supplies the arithmetic framework; the elementary consistency models and proposed research tests in this note are our own analysis.
