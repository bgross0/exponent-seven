# Adversarial audit of the weight-two specialization

Date: 2026-11-27. This note audits the geometric input to the pilot
localization argument. It changes no finite computation and introduces no
new numerical experiment.

## Result and scope

The original rational edge proof in
[ARITHMETIC_SPECIALIZATION.md](../leading_comparison/ARITHMETIC_SPECIALIZATION.md)
has an unproved step: it identifies the specialization of a **normalized,
dually constructed ordinary extension** with the extension obtained by a
raw sheaf moment. Null-homology and the existence of degree-zero moments
do not establish that identification. The literal finite sheaf
identification used in DR22's proof cannot be read as an isomorphism of
stalks. Section 5 isolates the missing assertion without claiming that the
published DR22 theorem is false.

The required research input has a different route. Use the **BSV balanced
diagonal family** and its actual dual ordinary control maps. BSV Theorem
8.1 already includes weights `(2,k,k)`. Its remaining tame-level comparison,
Proposition 8.3, is printed for all weights at least three, but its entire
finite pushforward proof extends to first coefficient exponent zero.
Sections 1--3 prove that extension and give the resulting four nonzero
Euler factors. Section 4 explains the remaining geometric identification;
the complete companion argument is in
[BSV_REPAIR.md](../general_criterion/BSV_REPAIR.md).

This repairs the **full projective geometric-specialization input for the
BSV family**. It is not an assertion that the old DR22 proof has been
completed. Transfer to the named CH class uses the separately audited
global Selmer comparison. The local adjoint operator and the full CM
projection in
[normalized_local_comparison/README.md](../normalized_local_comparison/README.md)
then apply with this BSV input; no new elliptic matrix appears.

All statements here concern rational coefficients. A nonzero scalar at
each fixed classical weight is sufficient. No integral unit, uniform
valuation bound, or analytic interpolation of that scalar is claimed.
The argument is a source-based mathematical proof, not a Lean
formalization of the source theorems.

## Sources and exact locations

Page numbers are the printed page numbers of these author files.

| Source | Locations used |
|---|---|
| [BSV, *Reciprocity laws for balanced diagonal classes*](https://www.esaga.uni-due.de/f/massimo.bertolini/publications/Ast-BSV1.pdf) | p. 3: `p >= 5` and the classical-weight congruence; pp. 11--14: coefficient maps (16)--(22); pp. 17--20: (39)--(48), including nonnegative exponents; pp. 24--27: geometric comparison and Proposition 3.7; pp. 59--65: Theorem 8.1 and normalized dual control; pp. 65--70: (169), Proposition 8.3, and its Steps 1--3. |
| [BSV erratum](https://www.esaga.uni-due.de/f/massimo.bertolini/publications/Errata-AstBSV1.pdf) | pp. 1--2: the corrected perfect-duality statement explicitly retains the ordinary slope `h=0` case used here. |
| [DR22, *p-adic families of diagonal cycles*](https://arxiv.org/pdf/2207.01314) | pp. 8--10: (1.17)--(1.22); pp. 18--24: modified cycles, hermitian duality, and extensions (2.17)--(2.25); pp. 25--27: positivity restriction, Lemma 3.2, diagrams (3.5)--(3.6), and the finite sheaf-identification step; pp. 28--33: degeneracy maps and the later positivity restriction. |
| [DR I, *Diagonal cycles and Euler systems I*](https://www.math.mcgill.ca/darmon/pub/Articles/Research/62.DR-Diagonal1/paper.pdf) | Definition 3.2: the explicit `(2,k,k)` cusp correction; the Abel--Jacobi extension around (66); Theorem 3.8 and its proof: the full fixed-weight syntomic functional, including arbitrary first-factor test class at this edge. |

The symbols `>=` and `>` were checked visually where relevant. In
particular BSV permits **`p=5`**. A text-extraction rendering of its prime
restriction as `p>5` is incorrect.

## 1. BSV supplies the normalized full class at the edge

Fix a tame level `N` prime to `p`, three ordinary cuspidal forms with
weights `(2,k,k)`, `k>2`, trivial first nebentype, and nebentypes whose
product is one. Use the ordinary stabilizations at level `Np`. Put

\[
\mathbf r=(0,m,m),\qquad m=k-2,\qquad
r=(r_1+r_2+r_3)/2=m.
\]

The determinant section in BSV (41) is exactly

\[
\operatorname{Det}_{\mathbf r}
 =(y_1z_2-y_2z_1)^m.
\tag{1}
\]

It is independent of the first vector, but it is a nonzero invariant
with the required determinant twist. BSV Assumption 3.1 expressly
allows all `r_i >= 0`. Its diagonal class is

\[
\widetilde\kappa_{N,\mathbf r}
 =\operatorname{HS}\,d_*\operatorname{Det}_{\mathbf r},
\qquad
\kappa_{N,\mathbf r}=s_{\mathbf r*}
  \widetilde\kappa_{N,\mathbf r}.
\tag{2}
\]

Here the base is the **affine** modular curve `Y_1(N)`. Over an
algebraic closure, a smooth affine curve has cohomological dimension
one for the rational lisse sheaves used here. Therefore

\[
H^4(Y_1(N)^3,\mathcal S^{[\mathbf r]})=0,
\qquad
H^3(Y_1(N)^3,\mathcal S^{[\mathbf r]})
=\bigotimes_{i=1}^3 H^1(Y_1(N),\mathcal S_{r_i}).
\tag{3}
\]

The constant first sheaf has nonzero `H^0`; it creates no extra
degree-three or degree-four term in (3). Thus (2) is a full triple
cohomology class before any scalar regulator pairing.

The normalized duality matters. In BSV's proof of Theorem 8.1, the
maps `c_u`, `s_{u,0}`, and `comp_u` satisfy (165)

\[
\operatorname{comp}_u\circ s_{u,0}\circ c_u
       =(p-1)^{-1}s_{u*}.
\tag{4}
\]

The source explicitly defines these maps for **nonnegative** `u`.
At `u=0`, the finite coefficient pairing is the pairing on the
constant polynomial `1`, so `s_0` is the identity. The proof uses
ordinary slope zero throughout. The BSV erratum proves that the
necessary perfect duality remains valid precisely in this case;
its correction for arbitrary finite slope is not an obstruction here.

With the notation of BSV Theorem 8.1, its conclusion is

\[
(p-1)\alpha_f\,\rho_{(2,k,k)}\kappa_{\rm BSV}
 =\left(1-\frac{\alpha_f\beta_g\beta_h}{p^k}\right)
   \kappa^\dagger(f_\alpha,g_\alpha,h_\alpha).
\tag{5}
\]

This is a Galois-cohomology identity. It includes both elliptic
coordinates. In particular (4)--(5) are the controlled ordinary
normalizations which the raw DR22 argument did not supply.

## 2. Direct extension of BSV Proposition 8.3

This section is a deduction from the published proof, not a quotation
of a statement whose printed hypotheses already include weight two.

### 2.1 Coefficient maps at exponent zero

BSV (16)--(22) constructs the pullbacks and traces from finite covers
of modular curves and from symmetric powers of the relative
degree-one cohomology maps of an elliptic isogeny. In the polynomial
realization, (173) reads

\[
\lambda^u_{p*}(P)=
 \begin{pmatrix}1&0\\0&p\end{pmatrix}P,
\qquad
\lambda_p^{u*}(P)=
 \begin{pmatrix}p&0\\0&1\end{pmatrix}P.
\tag{6}
\]

For `u=0` both coefficient maps are the identity. In particular

\[
\lambda_p^{0*}\lambda^0_{p*}=1=p^0.
\tag{7}
\]

One must not replace `Sym^0` of the degree-one isogeny map by the
degree-`p` trace on degree-zero cohomology of the elliptic fibre.
The degrees of the **base** covers still occur in the maps
`nu_p`, `check nu_p`, and `mu_p`, with degrees `p+1` and `p-1`
as in BSV. The construction in (6)--(7) leaves those degrees intact.

Step 2 of Proposition 8.3 introduces its `pi^u` maps with the phrase
`u >= 1` on p. 68. The same displayed compositions define them at
`u=0`; no inversion or division by `u` occurs. This is the only
new definition required at the edge.

### 2.2 The eight pushforward identities

Write `pr_ijk*` for the product of the three degeneracy pushforwards,
where each of `i,j,k` is `1` or `p`. All coefficients in the following
table multiply the same tame-level class `kappa(f,g,h)`, after the
full `(f,g,h)` projection. Bars on nebentypes denote inverses.
Specializing BSV (174), (176), and (181) to `(r_1,r_2,r_3)=(0,m,m)`
gives:

| Pushforward | Coefficient of `kappa(f,g,h)` |
|---|---|
| `pr_111*` | `p^2-1` |
| `pr_ppp*` | `p^m(p^2-1)` |
| `pr_p11*` | `(p-1) bar chi_f(p) a_p(f)` |
| `pr_1pp*` | `(p-1) p^m a_p(f)` |
| `pr_1p1*` | `(p-1) bar chi_g(p) a_p(g)` |
| `pr_p1p*` | `(p-1) a_p(g)` |
| `pr_11p*` | `(p-1) bar chi_h(p) a_p(h)` |
| `pr_pp1*` | `(p-1) a_p(h)` |

Here is why the proof, rather than just its final formulas, remains
valid.

* **Step 1, (174)--(175):** applying the same matrix to the two
  vectors in (1) multiplies the determinant by `p`. Its `m`th power
  is multiplied by `p^m`. The first tensor factor is constant.
  The two base-cover degrees are unchanged. Functoriality of
  diagonal pushforward and Hochschild--Serre gives the first two
  rows of the table.
* **Step 2, (177)--(180):** replace the non-Galois finite cover by
  the same Galois closure used in the source. Pullback followed by
  trace is the sum of deck transformations on cohomology with
  **any** of these sheaves, including the constant one. The two
  coefficient identities are `lambda_{p*}^{bold r} Det=p^m Det`
  and `lambda_p^{r_1*}lambda_{p*}^{r_1}=p^{r_1}`; at `r_1=0`
  the second is (7). The cancellations in (178)--(180) divide
  only nonzero cover degrees and powers of `p` over the rational
  coefficient field. The remaining six rows follow.
* **Step 3, (182)--(183):** the isomorphisms `s_u` commute with
  the dual Atkin--Lehner operator also at `u=0`. The identities
  `pr_p* w_p'=p^u pr_1*` and `pr_1* w_p'= <p>' pr_p*`
  likewise have a well-defined `u=0` instance. Expanding (169)
  therefore gives the same eight-term expression, with the table
  above. Its factorization uses only
  `alpha_i beta_i=chi_i(p) p^(weight_i-1)`,
  `a_p(i)=alpha_i+beta_i`, and `chi_f chi_g chi_h=1`.
  There is no remaining positivity assumption in this calculation.

Consequently the **edge extension** of Proposition 8.3 is

\[
\begin{aligned}
\Pi^\alpha_*\kappa^\dagger
 ={}&(p-1)\alpha_f
 \left(1-\frac{\beta_f\alpha_g\beta_h}{p^k}\right)
 \left(1-\frac{\beta_f\beta_g\alpha_h}{p^k}\right)\\
 &\hspace{20mm}\cdot
 \left(1-\frac{\beta_f\beta_g\beta_h}{p^k}\right)
 \kappa(f,g,h),
\end{aligned}
\tag{8}
\]

where the actual full Galois map is

\[
\Pi^\alpha_*=
 \left(\mathrm{pr}_{1*}-\frac{\beta_f}{p}\mathrm{pr}_{p*}\right)
 \otimes
 \left(\mathrm{pr}_{1*}-\frac{\beta_g}{p^{k-1}}\mathrm{pr}_{p*}\right)
 \otimes
 \left(\mathrm{pr}_{1*}-\frac{\beta_h}{p^{k-1}}\mathrm{pr}_{p*}\right).
\tag{9}
\]

No one-coordinate ordinary logarithm is used in this proof.

## 3. All Euler factors and the prime-five hypotheses

Combining (5) and (8), with the same source normalizations, gives

\[
\boxed{\quad
\Pi^\alpha_*\rho_{(2,k,k)}\kappa_{\rm BSV}
 =E_0E_1E_2E_3\,\kappa(f,g,h).
\quad}
\tag{10}
\]

The four factors are

\[
\begin{array}{ll}
E_0=1-\alpha_f\beta_g\beta_h/p^k,
 &E_1=1-\beta_f\alpha_g\beta_h/p^k,\\
E_2=1-\beta_f\beta_g\alpha_h/p^k,
 &E_3=1-\beta_f\beta_g\beta_h/p^k.
\end{array}
\tag{11}
\]

At a prime not dividing the tame conductors, the two roots of a
cuspidal weight-`w` Hecke polynomial have complex absolute value
`p^((w-1)/2)`. Thus every numerator in (11), at weights `(2,k,k)`,
has complex absolute value

\[
p^{1/2+(k-1)/2+(k-1)/2}=p^{k-1/2}.
\]

Each ratio has complex absolute value `p^(-1/2)`, so none equals
one. All four Euler factors are nonzero. This argument concerns
algebraic Hecke roots at each classical weight; it makes no claim
that these ratios have bounded `p`-adic valuations as the weight
varies. The prefactors cancelled between (5) and (8) are nonzero
because `p-1 != 0` and `alpha_f` is an ordinary unit. The distinct
ordinary/nonordinary roots have different `p`-adic valuations, so
the stabilization maps do not acquire a repeated-root denominator.

The BSV standing setup requires `p >= 5` and tame levels prime to
`p`. Sections 3, 4, and 8, and the ordinary-duality correction in
the erratum, introduce no assumption `p does not divide phi(N)`
for the construction and specialization used above. The proof is
over rational coefficients and uses the full-level curves directly.
It does not invoke DR II Section 1.6, whose integral restriction
would be unsuitable for this pilot. The other BSV hypotheses,
including its conditions on weight-one Hida centers and the chosen
tame test vectors, remain part of the global-family input; they
are not removed by this local audit.

BSV chooses classical integer weights congruent to their centers
modulo `2(p-1)`. On the line through `(2,1,1)`, use

\[
s_n=2(p-1)p^n=8\cdot5^n,
\qquad k_n=1+s_n,
\tag{12}
\]

for sufficiently large `n` in the chosen weight discs. These are
balanced triples `(2,k_n,k_n)` and accumulate at `(2,1,1)`.
Replacing a previously used sequence `4*5^n` by (12) changes no
analytic germ or nonzero-Jacobian character-coordinate comparison.

## 4. From the affine invariant to the DR I cycle

BSV Proposition 3.7 compares (2) with the geometric diagonal using
relative Leray, proper pushforward, and the fibre calculation
(60)--(63). At the edge set `A=empty` and
`B=C={1,...,m}`. The fibre calculation is simply the product of
`m` copies of the alternating diagonal tensor. Projection to the
two symmetric powers gives (1), up to the common sign convention.
Thus the relevant morphism of cohomology classes is available; one
does not infer it from null-homology alone.

There is a small preliminary statement in that proof which must
also be adjusted at the edge. Before Proposition 3.7 the text
claims the product Scholl projector kills every geometric degree
except `2r+3`. With a constant first factor, degree `2r+2` can
also occur on the affine product. What the proof needs remains
true: degree `2r+4` vanishes and degree `2r+3` identifies with
the full tensor of three `H^1` groups. A first-factor cuspidal
projection kills the extra `H^0` term as well.

For the proper Kuga--Sato realization use the first-factor
correspondence

\[
R_f=\frac{q+1-T_q}{q+1-a_q(f)}.
\tag{13}
\]

It kills the trivial first-factor `H^0` and `H^2` and is identity
on the selected `f` summand. If the point `o` in DR I Definition
3.2 is a cusp, Manin--Drinfeld gives

\[
R_f[o]=0\quad\text{in }\mathrm{CH}_0(X)_\mathbf Q.
\tag{14}
\]

Indeed `T_q[o]-(q+1)[o]` is a degree-zero cuspidal divisor and is
torsion. Therefore the actual cusp-supported correction in the
DR I edge cycle vanishes after this rational projection, not just
after taking its geometric cohomology class. At the pilot one
may use `q=3`, giving `R_f=(4-T_3)/6`.

Restriction to the affine curve is an isomorphism on the specified
cuspidal cohomology summands; boundary terms are Eisenstein.
Functoriality of the cycle class, Leray, and Hochschild--Serre maps,
together with (14), then identifies the projected BSV geometric
class with the projected DR I Abel--Jacobi class. The companion
[BSV_REPAIR.md](../general_criterion/BSV_REPAIR.md) records this
identification and its use in the global CM Selmer decomposition.

The tame and `p`-old maps here act on full Galois representations.
After fixing the global modular realization of the irreducible
elliptic representation, an oldspace is `V_E tensor M`; a
Galois-equivariant map of copies is `id_{V_E} tensor ell`, up to
one scalar on the selected copy. It is not projection onto an
elliptic crystalline eigenline. Thus substituting the BSV family
does not add a hidden polynomial in elliptic Frobenius to the
previously derived local `K_s`. Euler factors are already in
(10), and CM period choices remain common nonzero scalars.

## 5. What is wrong with the old DR22 argument

### 5.1 The literal finite sheaf identification is insufficient

DR22 (1.17) gives, on the smooth open locus,

\[
\mathcal L_n^*|_{(A,P)}
 =\mathbf Z_p[A[p^n]_{\langle P\rangle}],
\qquad
A[p^n]_{\langle P\rangle}=
 \{Q:p^{n-1}Q=P\}.
\]

This stalk has rank `p^(2(n-1))`. Taking the character quotient
for the free principal diamond action leaves rank `p^(n-1)`
over `Z/p^n`; it does not leave rank `u+1`, the rank of
`TSym^u H_n`. Already for `n=1` the source stalk has rank one,
whereas a positive symmetric power has larger rank. Consequently
the displayed equality on DR22 p. 27 cannot literally identify
these coefficient sheaves. Ordinary cohomology control can
identify appropriate quotients of cohomology without making the
underlying sheaves isomorphic.

The source theorem may use this line as shorthand for an ordinary
duality/control argument. The original repository deduction did
not supply that argument. Its application of moments to (3.6)
therefore does not by itself produce the asserted morphism of
normalized localization extensions.

### 5.2 Raw residue moments display the missing normalization

This is an exact diagnostic calculation, not a counterexample to
the source theorem. A lifted diagonal component has, over a fixed
smooth base point, the orbit

\[
K_n=\ker(\mathrm{SL}_2(\mathbf Z/p^n)
                 \longrightarrow\mathrm{SL}_2(\mathbf F_p)),
\qquad |K_n|=p^{3(n-1)}.
\]

The raw edge moment is an orbit sum

\[
S_n=\sum_{M\in K_n}(v_2M)^{[m]}\otimes(v_3M)^{[m]}.
\tag{15}
\]

For `n>=2`, the lifts of `M_0` can be written
`M_0(1+p^(n-1)A)` with `A` in the three-dimensional trace-zero
matrix space over `F_p`. Expanding the integral polynomial in
(15) modulo `p^n`, the quadratic terms vanish and the sum of
linear terms vanishes. The constant terms give

\[
S_n\equiv p^3 S_{n-1}\pmod{p^n},
\qquad S_n\equiv0\pmod{p^n}\quad(n\ge2).
\tag{16}
\]

The unnormalized residue generators themselves push down with
degree `p^3` at each step, consistently with DR22 Lemma 2.4.
They are not the norm-compatible normalized dual family.
DR22 uses the hermitian dualities and extension construction in
(2.17), (2.23), and (2.25); a naive covariant orbit moment omits
that normalization.

In particular a congruence such as (16) does **not** disprove
proportionality by a nonzero rational scalar. That scalar is
allowed arbitrary positive `p`-adic valuation at every fixed
weight, and the actual dual construction has not been replaced
by (15). The diagnostic establishes that the missing normalized
map cannot be silently treated as the raw residue map.

If one insists on the DR22 family, the exact remaining obligation
is to construct a morphism of its **normalized dual ordinary
localization extensions**, whose left map is the desired full
cohomology specialization and whose residue map sends the source
generator to

\[
c_m\,\theta_q\operatorname{CG}_{0,m,m},
\qquad c_m\in L^\times.
\tag{17}
\]

Neither a stalk isomorphism nor flat specialization is required.
But some proof of (17), compatible with the actual ordinary
duality, is required. The BSV replacement avoids this outstanding
DR22-specific obligation by using its proved (4)--(5).

### 5.3 The missing preceding support group can be repaired

For completeness, the leading zero in the repository's compact
localization sequence needs justification. Let `X` be a smooth
compact curve, let each coefficient factor be the ordinary
extension `j_*L_i` of a rational lisse sheaf on its open modular
curve, and put `F=boxtimes_i j_*L_i` on `X^3`. Let `Z` be the
finite union of diagonal and Hecke-translate curves used for the
modified cycle.

At a point of a curve, the localization triangle and the inertia
cohomology description show that the costalk of `j_*L_i` is
concentrated in degree two: the degree-zero map to inertia
invariants is an isomorphism and the remaining inertia
coinvariants contribute in degree two. At a point of `X^3`,
external-product compatibility puts the costalk of `F` in degree
six. Remove the finitely many cusp points, singular points, and
intersections of the curves in `Z`. On the remainder, purity for
a smooth codimension-two support and a lisse sheaf gives no
support cohomology below degree four. Excision at the removed
points therefore gives

\[
                         H_Z^3(X^3,F)=0.
\tag{18}
\]

This supplies the injection at the left of the localization
segment. At the other end one should retain `H_Z^4` and its map
to `H^4(X^3,F)`, and pull back along a residue whose boundary
vanishes. It is not necessary to make the whole last group
zero. Nor should one automatically identify `H_Z^4` across the
cusps with ordinary `H^0` of the naive pullback of `F`: extending
an external tensor and extending its pullback along the diagonal
can have different invariant spaces. The support formulation
avoids that ambiguity.

The cusp filter, the repaired localization sequence, and the
existence of degree-zero moment maps are therefore sound tools.
They do not fill the normalized extension-comparison gap in
(17). The BSV route supplies the needed arithmetic input without
relying on that gap.

## Final dependency status

| Item | Status after this audit |
|---|---|
| Raw DR22 projected-edge proof as previously written | Incomplete at normalized dual moment/residue compatibility; not used by the replacement. |
| Missing preceding `H_Z^3` in the compact sequence | Vanishes by the argument in (18). |
| Rational cusp correction | Killed in Chow after the stated first-factor cuspidal filter. |
| BSV normalized full specialization at `(2,k,k)` | Theorem 8.1 applies directly; ordinary dual control survives the erratum. |
| BSV tame-level comparison at first exponent zero | Proved above by extending every map and Steps 1--3 of Proposition 8.3. |
| Four Euler factors | Nonzero at every required classical weight by (11). |
| Prime `p=5` | Within BSV's standing prime range. No imported `p`-prime-to-`phi(N)` hypothesis. |
| Full fixed-weight local operator | Unchanged, after the stated global geometric realization and projective scalar convention. |
| CH global comparison and final localization implication | Separate audited inputs; not proved anew here. |

