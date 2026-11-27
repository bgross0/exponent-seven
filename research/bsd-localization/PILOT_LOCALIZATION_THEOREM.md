# Nonzero localization of the reflected class: the E389 pilot

Date: 2026-11-27. Research branch: `bsd-arithmetic-comparison`.
Continues the projection package at commit `260370b`, retaining its
precision binding and witness replay update to the frozen mathematical
snapshot `9364a14`.

## Statement and proof status

For

\[
 E:y^2+y=x^3+x^2-2x,\qquad K=\mathbf Q(\sqrt{-71}),\qquad p=5,
\]

the arguments below establish the following pilot result from the
identified theta certificate, the published arithmetic theorems, and the
geometric and analytic deductions documented in this repository.

Let `kappa_CH` be the variable component of the Castella--Hsieh family
with the good test vectors of its theta reciprocity law. Fix the selected
prime of `K` by `omega=2 mod5`, where `omega^2-omega+18=0`, and let
`c` denote complex conjugation. Put

\[
 t=(\gamma-\gamma^{-1})/2,\qquad
 x=\frac{\kappa_{\rm CH}-c\kappa_{\rm CH}}{t}.
\]

**Pilot theorem.** The quotient is a well-defined global Iwasawa
cohomology class. Its base specialization descends to a class

\[
 z\in\operatorname{Sel}(\mathbf Q,V_5E\otimes L),
 \qquad L=\mathbf Q_5(\zeta_7),
\]

and

\[
 \boxed{\log_{\omega_E}(\operatorname{loc}_5 z)\ne0.}
\]

The proof does not use either of the known independent rational points
on this curve, its known Mordell--Weil rank, or finiteness of its
Tate--Shafarevich group. Its output is a Selmer class with nonzero finite
localization, not an identification of that class with a rational point.
Taking a suitable `Q5`-linear coefficient functional also supplies a
`Q5`-valued Selmer witness with nonzero localization; no canonical
coefficient functional is asserted.

This is a **written computer-assisted mathematical proof draft**. The
new finite algebra has executable certificates and independent review.
The geometric comparison, local Galois complexes, and published source
theorems are not new Lean-checked results. In particular, the argument
retains the repository's proved rational projected-edge extension and
its source-based infinite Katz comparison as mathematical inputs. It
does not represent a completed formalization of those arguments.

## 1. The input ledger

The proof uses the following inputs with their actual scope.

| Input | Evidence and role |
|---|---|
| Exact order two of the primitive integral theta series | The other research thread's supplied p=5 certificate: exact constant and linear zeros, unit quadratic coefficient; accepted input as recorded in the package README |
| CH arithmetic hypotheses and auxiliary nonvanishing | The supplied arithmetic audit, the exact cyclic toric-period calculations in `p5/`, and the separate twist check; these justify the named CH family and reciprocity law |
| Big five-adic image | `galois_image/README.md`: Tate inertia, exhaustive residual matrix certificate, and the stated closed-subgroup lifting theorem |
| Reflected global division and base finite Selmer condition | `derived_global/DERIVED_CLASSES.md`, Section 6, and `rationality/REFLECTED_REVIEW.md` |
| Analytic CM vector, including exact lower zeros | `analytic_target_audit/`, `weight_reflection/`, and `leading_comparison/` |
| Certified quadratic coefficient balls | Actual Sage CM projection and independent replay in `projection_backend/`; the infinite bound is `INFINITE_KATZ_BRIDGE.md`, with the pinned Sage geometric provenance stated there |
| Full fixed-weight syntomic vector | `fixed_weight_syntomic/README.md`, retaining both elliptic coordinates |
| The full geometric class at weights `(2,k,k)` | Rational projected-edge proposition in `leading_comparison/ARITHMETIC_SPECIALIZATION.md`; it extends the inspected moment/localization diagram rather than misquoting a higher-weight theorem |
| Same generic global Selmer line | New `global_class_comparison/README.md`, using Castella--Do's rank-one theorem and full strict local conditions |
| Fully normalized local comparison | New `normalized_local_comparison/README.md`, using syntomic/etale compatibility and both tests in CH Theorem 3.4 |
| One-way nonvanishing criterion | New `comparison_logic_audit/README.md`; no simple-determinant or calibrated-logarithm theorem is assumed |

The source-based Katz provenance is material. The finite witnesses replay
the actual matrix and CM fit; the infinite theorem additionally uses the
documented saturated-basis and coordinate-tail argument for the inspected
pinned Sage implementation. Those are distinct verification layers.

## 2. The reflected class exists before any local division

Write `M=H1_Iw(K_infinity,V5E tensor L)`. Complex conjugation is
semilinear for `gamma -> gamma^-1` and fixes the external coefficients.
The CH base specialization is Selmer. Vanishing of the quadratic-twist
Selmer group makes it conjugation-invariant. Therefore

\[
 \kappa_{\rm CH}-c\kappa_{\rm CH}
\]

has zero **global** specialization. The universal-character cohomology
exact sequence makes it divisible by `gamma-1` in `M`. There is no
ambiguity because the relevant global `H0` is zero. Since `t` is
`gamma-1` times a unit and `c(t)=-t`, the displayed quotient `x` exists
uniquely and satisfies `c(x)=x`.

The full localization of `kappa_CH` at the conjugate prime is zero.
The fixed ordinary Coleman image at the selected prime is `u*Theta`,
with `u(0)!=0`. Its order at least two implies that both Coleman
images of `x` vanish at the base. CH Theorem 4.5, with `r=1`, puts
`x0` in the finite Selmer group. Its conjugation invariance gives
descent to `z` over `Q`. The rational local cohomology away from five
vanishes; no extra specialized local condition is being omitted.

Let

\[
 y=\operatorname{loc}_{\mathfrak p}\kappa_{\rm CH},
 \qquad x_{\mathfrak p}=\operatorname{loc}_{\mathfrak p}x.
\]

Full strictness of the conjugate class gives

\[
                         y=t x_{\mathfrak p}.                 \tag{1}
\]

In particular, `(x_p)0` is already finite before the numerical direction
test is used. This is division of an actual global class, not division
of a scalar power series followed by an assumed global lift.

## 3. The exact local nonvanishing criterion

Let `P` be the full normalized CH regulator, with both elliptic test
coordinates. Both belong to a common space of analytic distribution
germs. Choose a common complete overfield `Omega` of `L`, for example
`C5`, containing the normalized unramified period coefficients. Write
`D_Omega=H1_dR(E) tensor Omega` and use the fixed alternating Weil/cup
identification. We do not assert that the normalized output itself
descends to `L`. With `F^2+3F+5=0`, its base image is contained in

\[
 \Omega\zeta,\qquad \zeta=\frac{20-13F}{45}\omega_E.
\]

Thus the constant functional `lambda(v)=<v,zeta>` satisfies

\[
                        \lambda P_0=0                       \tag{2}
\]

on all local inputs. This follows from the **normalized** CH
interpolation formula, not from replacing its averaging by a trace.
Moreover `P0` kills finite local classes. By (1),

\[
             P(y)=tP(x_{\mathfrak p})\in t^2D_\Omega[[t]].    \tag{3}
\]

The independent ordinary reciprocity identity has exact order two, so
the full vector in (3) has exact order two. Set

\[
                    v_2=[t^2]P(y)\ne0.                       \tag{4}
\]

The crucial implication is elementary:

\[
 \lambda(v_2)\ne0
       \ \Longrightarrow\ (x_{\mathfrak p})_0\ne0
       \ \Longrightarrow\ \log_{\omega_E}((x_{\mathfrak p})_0)\ne0.
                                                                    \tag{5}
\]

For the first implication, suppose instead that the local specialization
were zero. The local universal-character exact sequence gives
`x_p=t w` for some local Iwasawa class `w`. Then `y=t^2 w`, and (2)
forces `lambda P(y)` to lie in `t^3`, contrary to the hypothesis.
For the second, the Bloch--Kato logarithm is injective on the finite
one-dimensional elliptic local space. The same reasoning works after
restriction to the finite unramified field used in the regulator:
rational restriction is injective and the logarithm is compatible.
The Selmer class itself remains defined over the finite coefficient
field `L`; extending the regulator target to `Omega` neither changes
that fact nor converts a zero local class into a nonzero one.

No assertion that the regulator determinant has a simple zero is used.
We do not compute an absolute scalar relating (4) to a normalized
logarithm. Such a scalar is unnecessary for the nonvanishing in (5).

## 4. Why the computed direction belongs to this class

Let `kappa_DR` denote the variable component of the DR22 family with
the specified projected classical specialization. The following
comparison concerns full classes and full vectors.

**Global comparison.** Both classes have the same anticyclotomic
coefficient representation and the same full relaxed/strict local
condition. DR22 Proposition 5.8 gives the image of local cohomology of
the balanced subrepresentation. On the variable CM block, that
subrepresentation is full `V5E` at one prime and zero at the other.
Away from five, perfect local cohomology and derived base change make
the ambient local complexes acyclic at the augmentation germ.

The proof of Castella--Do Theorem 5.6.1, via Theorem 3.3.3, gives rank
one for precisely this Selmer module. Its big-image hypothesis is
verified independently in `galois_image/`. Both classes are nontorsion.
For the geometric class this can be seen directly from its full
classical syntomic specializations: the analytic vector is nonzero at
all sufficiently close nonzero classical weights, and the fixed-weight
Euler operators and projective scalars are nonzero. This proves
nonvanishing of the **variable** component without requiring an
auxiliary scalar-regulator identification.

Consequently, in full global cohomology over the Iwasawa fraction field,

\[
                    \kappa_{\rm DR}=f(T)\kappa_{\rm CH},
                    \qquad f\ne0.                            \tag{6}
\]

The scalar may have a zero or pole. Equation (6) transports the
projective regulator direction; the independent argument (3)--(4)
supplies the order of the actual CH vector. Reflection is still
performed on the actual CH class, not on an arbitrary rescaling.

**Local comparison.** At each classical weight `(2,k,k)`, the
holomorphic CM test tensor annihilates the auxiliary component and
detects the full selected rank-two variable component. The projected
syntomic/etale Abel--Jacobi comparison identifies its syntomic vector
with the Bloch--Kato logarithm of the same DR specialization, up to a
nonzero rank-one CM period scalar. The general rational comparison
has no restriction `p` prime to `phi(71*389)`; the older integral
family construction with that restriction is not used.

CH Theorem 3.4 already interpolates its normalized Frobenius-averaged
map. Using both independent elliptic test eigenvectors determines the
full adjoint operator. At `s=k-1`, `j=-s`, it is

\[
 K_s(F)=(1-5^{-s-1}F)(1-5^sF^{-1})^{-1}.
\]

The ordinary stabilization and tame degeneracy maps act on multiplicity
spaces of the globally absolutely irreducible elliptic representation;
their nonzero restrictions act by one scalar on both elliptic
coordinates. They do not introduce an unidentified second matrix.

After the fixed-weight cancellation and analytic wedge argument, (6)
therefore gives

\[
                 v_2\ \parallel\ K_{\rm lead}\mathcal A_2,   \tag{7}
\]

where `A2` is the computed quadratic vector and

\[
 K_{\rm lead}=\frac{3[(5\tau+11)+2(\tau+1)F]}{5\tau^2+18\tau+25},
 \qquad \tau=1-\xi-\xi^2,\quad \xi=\zeta_7+\zeta_7^{-1}.
                                                                    \tag{8}
\]

This leading matrix is denoted `K0=C(0)^(-1)N` in the component notes.
It is **not** obtained by substituting `s=0` into `K_s`: it is obtained
after fixed-integer-weight cancellation and the analytic wedge argument.
No analytic continuation of `5^s` or a factorial is used.

The analytic CM and anticyclotomic parameters differ by a change with
nonzero derivative. That only rescales the first nonzero vector.
Likewise the scalar in (6) need not be an augmentation unit for (7).

## 5. The finite certificate excludes the base line

Use the specified elliptic stabilization basis `(f_alpha,f_beta)`.
The independently replayed projection and infinite comparison give

\[
 \mathcal A_2=a_2f_\alpha+b_2f_\beta,
 \qquad v_5(a_2)=-1,\quad v_5(b_2)=-2,
\]

\[
           5b_2/a_2=109+75\xi+106\xi^2\pmod{125}.              \tag{9}
\]

Here `xi^3+xi^2-2xi-1=0`. The Frobenius eigenvalue on `f_alpha` is
`beta`, and on `f_beta` it is `alpha`. Modulo125, `alpha=32` and
`beta=90`. The common scalar in (8) cancels from the ratio, so the
correction multiplier is

\[
 \frac{(5\tau+11)+2(\tau+1)\alpha}
      {(5\tau+11)+2(\tau+1)\beta}
       =79+\xi+91\xi^2\pmod{125}.                             \tag{10}
\]

Exact arithmetic in the unramified cubic ring gives

\[
 (79+\xi+91\xi^2)(109+75\xi+106\xi^2)=21\pmod{125}.          \tag{11}
\]

In the same stabilization basis the base line has the separately
certified representative

\[
       \zeta=(19330,67476)\pmod{5^7},
       \qquad 5\zeta_2/\zeta_1=86\pmod{125}.                 \tag{12}
\]

Its first coordinate has valuation one, so the scaled quotient in
(12) is legitimate at the stated precision. Both ratios in (11)--(12)
are integral after scaling. Their difference is

\[
                     21-86=60\pmod{125}.                     \tag{13}
\]

Since 60 has valuation one, (13) cannot be zero in the p-adic field.
Thus `K_lead A2` is not parallel to `zeta`, and its alternating pairing
with `zeta` is nonzero. Equations (7) and (5) now prove the theorem.

The cancellation to a rational residue in (11) is observed only at the
available precision. No exact coefficient-field descent is inferred
from that cancellation. Three scaled digits suffice for the nonzero
test, and no additional large geometry computation is needed for it.

## 6. Consequences and remaining research

This completes the proposed nonzero-localization test for the named
reflected class in the pilot, subject to the explicit arithmetic and
geometric input ledger. It also isolates a reusable sufficient
criterion: an order-two theta identity, the common full projective
comparison, and separation from the base image line imply nonzero
finite localization of the reflected derivative.

The proof is not a general rank-two BSD theorem. Its Selmer output does
not by itself produce a rational point or remove a divisible
Tate--Shafarevich contribution. The pilot's rank-two/finite-5-primary-Sha
corollary in `p5/` separately uses two independently verified rational
points. Those points are deliberately absent from this theorem's
dependency chain.

The next useful work is to expose the general hypotheses of this
criterion, independently review the projected-edge and analytic
comparisons as mathematics, and test a second eligible curve. A later
Selmer-to-point construction must carry its own proof; it cannot be
deduced by relabeling the class constructed here.

## Reproduction

Run the compact certificate suite from this directory:

```sh
python verify_all.py --receipt verification.json
```

The new exact components are:

```sh
python galois_image/check_image.py --check
python normalized_local_comparison/check_linear_algebra.py
python comparison_logic_audit/check_logic.py --check
```

The first checks the finite big-image arithmetic, the second checks the
full-coordinate selection and adjoints, and the third checks the
nonvanishing algebra and the actual corrected ratio. Their outputs do
not claim to mechanically verify the published theorems or the full
geometric proof above. Large Sage geometry and CM-projection witnesses
retain their separate completed replay receipts.

## Primary references

* Castella--Hsieh, *On the nonvanishing of generalised Kato classes for
  elliptic curves of rank 2*, [author PDF](https://web.math.ucsb.edu/~castella/Kato-print.pdf):
  Definition 3.3, (3.9), Theorem 3.4, Theorem 3.6, Corollary 3.7,
  Theorem 4.5, and Lemma 5.1.
* Castella--Do, *Diagonal cycles and anticyclotomic Iwasawa theory of
  modular forms*, [author PDF](https://kimtuando.github.io/website/Schoen_CM.pdf):
  Notation 3.3.2, Theorem 3.3.3, and the proof of Theorem 5.6.1 with
  the hypotheses of Theorem 5.5.1.
* Darmon--Rotger, *p-adic families of diagonal cycles*,
  [arXiv:2207.01314](https://arxiv.org/abs/2207.01314): the construction,
  projected specialization diagrams, and Proposition 5.8.
* Darmon--Rotger, *Diagonal cycles and Euler systems I*,
  [author PDF](https://www.math.mcgill.ca/darmon/pub/Articles/Research/62.DR-Diagonal1/paper.pdf):
  the cusp-corrected cycle and full Theorem 3.8.
* Nekovar--Niziol, *Syntomic cohomology and p-adic regulators for
  varieties over p-adic fields*,
  [published PDF](https://msp.org/ant/2016/10-8/ant-v10-n8-p04-p.pdf):
  Theorem A(4), (6), (7), and Proposition 1.1.
