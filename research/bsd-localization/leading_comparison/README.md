# The ordinary second coordinate, a projective target, and its missing line comparison

Pilot: E389.a1, K=Q(sqrt(-71)), p=5. Date: 2026-11-27.

This continuation proves a useful reduction, conditional on the existing
package's exact theta identification and its analytic cohomology construction:
**the ordinary coefficient of the second de Rham weight jet is already
known to be nonzero.** The large computation is needed to determine its
direction, especially its critical-slope component, rather than merely to
discover whether the vector vanishes.

It also makes the nonvanishing comparison target smaller: identify one
line in the analytic de Rham space, then show that the second vector is
not on that line. The absolute period and coordinate scale need not be
known to decide this. The arithmetic identification of that line is still
unproved. The numerical line below is a precisely stated candidate, not
an established reciprocity law.

## 1. A source that permits conductor one

The published Castella--Hsieh Proposition 2.5 is introduced using an
auxiliary character of conductor ell^m with m>0. The present pilot uses
class-group characters of conductor one, so that wording should not be
silently broadened.

Castella--Do, *Diagonal cycles and anticyclotomic Iwasawa theory of modular
forms*, author version dated August 4, 2025, gives the needed broader
factorization in Proposition 5.2.1. Section 5.2 allows ray class characters
of arbitrary prime-to-p conductor, including one. For inverse characters
xi1=psi, xi2=psi^-1 on the same weight diagonal it specializes to

    Lp^f(test vectors; W) = u(W)*Theta(E/K; W)*Theta(E/K,psi^2;0)*C_f,

where u is regular and nonzero at the base and C_f is a nonzero
congruence/period factor. Nonzero here is over the coefficient field; this
does not assert that every factor is a 5-adic integral unit.

The hypotheses used in this specialization are:

| Published hypothesis | Pilot input |
|---|---|
| p does not divide 6Nf | p=5, Nf=389 |
| ordinary at p | a5=-3, unit root alpha=2 mod5 |
| p split in K | omega^2-omega+18 has distinct roots 2 and4 mod5 |
| p does not divide hK | hK=7 |
| self-duality of the two finite characters | psi and psi^-1 |
| inverse-character theta families are cuspidal | psi has order7 and psi!=psi^c |
| N^- squarefree with an odd number of factors | N^-=389, inert in K |
| f residually irreducible and p-distinguished | supplied arithmetic audit; the package retains its provenance |
| gcd of the three tame levels squarefree | gcd(389,71,71)=1 |

The accompanying source's Section 5.2 derives its local-sign requirement
for these CM pairs. The auxiliary theta value is nonzero by its Theorem
5.1.1 and the supplied nonzero auxiliary central value. Its p-Euler
factors are nonzero: alpha reduces to an order-four element2, while the
finite CM eigenvalues have order7.

This is a theorem-based use of the supplied theta and arithmetic inputs.
The Python checker does not prove the automorphic factorization.

## 2. All minimal-level test vectors use the same analytic output

Put N=389 and retain the definitions

    A_s=d^-s(g_s^[5])*V_N h_s,
    B_s=d^-s((V_N g_s)^[5])*h_s,
    D_s=d^-s(g_s^[5])*h_s.

The two CM forms have native tame level71; their test-vector spaces at
level71*N are spanned by (g,V_Ng) and (h,V_Nh). This is the test-vector
definition in CH Section2.2 and Castella--Do Section4.1.3. For analytic
coefficients a,b,c,d,

    gcheck=a*g+b*V_Ng,       hcheck=c*h+d*V_Nh,

their inverse-Bol product is

    ac*D_s + ad*A_s + bc*B_s + bd*<N>^-s*V_N D_s.

The first and last terms come from level71. Their proper E-new projection
at389 is zero, because the conductor389 automorphic representation does
not occur at level71. The preceding analytic audit proves
Pi_E(A_s)=Pi_E(B_s). Hence

    Pi_E(d^-s(gcheck^[5])*hcheck)=(ad+bc)*L(s),

where L(s)=Pi_E(A_s) in the symmetric oldspace coordinate.

The f test vector lies in the two-dimensional oldspace at71. Acting on
the Fricke71-plus input reduces its two degeneracy coordinates to one
scalar functional, by the earlier trace matrix calculation. On the
ordinary elliptic direction this scalar is fixed after specializing f
to weight2. The extra second-factor depletion remains cohomologically
invisible.

Thus the scalar triple-product function for the good minimal-level test
vectors has the form

    Lp^f(test vectors;W)=q(W)*a_E(W),                 (1)

with q regular, where

    L(W)=a_E(W)*[f_alpha]+b_E(W)*[f_beta].

Regularity here is an essential source hypothesis, not a consequence of
the finite-dimensional oldspace calculation. Castella--Do Remark4.1.2
(printed page35) places the scalar for arbitrary test vectors in
Frac(I_f) tensor I_g tensor I_h: possible meromorphic denominators occur
in the f variable. Section5.2 then specializes f and explicitly places
the resulting scalar in L_P tensor O[[Z1,Z2]]. Thus the fixed-f diagonal
used here has no pole in the CM weight W. The same remark chooses its
good test vectors at the minimal common tame level, which is exactly the
oldspace considered above. We use both facts in (1).

This uses the ordinary projection definition of the triple-product
function. Coleman's identification is compatible with U5 and tame Hecke
correspondences. Exact differentials and residue classes do not create
an extra E-ordinary component. Fixed congruence and pairing factors may
be absorbed into q; no numerical value for them is claimed.

## 3. Exact order two follows without computing the critical component

The preceding analytic audit proves L(0)=L'(0)=0. In particular,
ord_W(a_E)>=2. The supplied theta result and the factorization in Section1
prove ord_W(Lp^f)=2. The coordinate changes involved have nonzero linear
term, as checked explicitly below.

Since q in (1) is regular,

    2=ord_W(q)+ord_W(a_E),       ord_W(q)>=0, ord_W(a_E)>=2.

Therefore

    ord_W(q)=0,       ord_W(a_E)=2,
    a2=[W^2]a_E(W)!=0.                              (2)

Consequently the full vector L2=[W^2]L(W) is nonzero. This proves neither
that its critical coordinate b2 is nonzero nor that the reflected global
class has nonzero localization. It also does not identify the 5-adic
valuation of a2: the unknown period/congruence scale can affect it.

The theorem's dependency is the supplied exact theta identification,
auxiliary nonvanishing, eligibility, and the analytic constructions in
the existing package. It adds no new assumption of finite Sha.

## 4. Explicit coordinate transport for the norm-two generator

Use omega^2-omega+18=0, the embedding omega=2 mod5, and the ideal
a=(2,omega). We have

    a^7=(10+omega),       N(10+omega)=128.

In the CM q-series normalization, the varying anticyclotomic character
rho_s/rho_s^c takes a to

    (1+W)^delta,       W=6^s-1,

where

    delta=(log5(10+omega)-log5(11-omega))/(7*log5(6)).

The exact logarithm calculation gives

    delta=52766382 mod5^12,       delta=2 mod5.       (3)

Thus the pro-5 image of the norm-two ideal is a topological generator.
The opposite norm-two ideal or the inverse Artin convention changes its
sign; delta^2 is unchanged. With T_a the parameter for this norm-two
generator, evaluation along the CM weight character makes

    T_a=(1+W)^delta-1,
    t_a=((1+T_a)-(1+T_a)^-1)/2
       =delta*W-(delta/2)*W^2+O(W^3).

In particular the leading-order scale for the odd parameter is delta,
not a silently assumed1. After choosing the canonical generator dual to
the character rho_s/rho_s^c itself, the scale is1. Castella--Do
Section2.4.3 uses gamma_minus=gamma_p^(1/2)*gamma_pbar^(-1/2), which
explains why a factor2 must not be inserted by replacing this with the
unhalved product. Its weight2-centered variable is Z=6^-1(1+W)-1;
the Proposition5.2.1 variables become W1=W and W2=0 on our diagonal.

The supplied raw norm-two finite element has quadratic residue1 mod5.
Its ordinary regularization contributes alpha^-2=4 mod5, so the
regularized theta coefficient in T_a is4. Substitution above multiplies
the quadratic coefficient by delta^2=4, giving residue1 in W. This last
residue retains the supplied primitive quaternionic sign and no new
global period normalization. In particular it is not a numerical value
for a2 in (2).

The checker verifies (3) at two successive precisions, checks the
principal ideal relation, and transports the finite coefficient. Its
logarithm routine has the explicit truncation bound documented in the
earlier CM input package.

## 5. The nonvanishing question is projective

By (2), define

    r_E=b2/a2 in Q5(zeta7+zeta7^-1).                 (4)

This ratio is unchanged by multiplying the analytic family by any
regular scalar unit. A regular coordinate change with nonzero linear
coefficient multiplies both a2 and b2 by the same square, so also leaves
(4) unchanged. This can eliminate absolute period normalization from
the desired nonvanishing test.

To state precisely what still must be proved, use the local regulator
model in finite_log_reciprocity/. Let P have a simple determinant zero,
with ker(P0)=H_f, and let

    I0=im(P0),       y=t*x,       x0 in H_f.

The divided-regulator argument there proves

    log(x0)!=0  iff  [t^2]P(y) is not in I0.         (5)

Suppose an arithmetic comparison modulo weight degree3 has the form

    L(W)=M(W)*P(y(t(W))),       M(0) invertible.

Then it is enough to identify the single line

    B=M(0)*I0

in the analytic de Rham space. Equation(5) becomes

    log(x0)!=0  iff  L2 is not in B.                 (6)

If the known scalar reciprocity law is matched to the ordinary row, B
has a nonzero ordinary coordinate. It is then described by one ratio
r_bad, and (6) is exactly r_E!=r_bad. No value of the absolute period,
the finite-log scale c_P, or the coordinate scale delta is needed for
this nonvanishing decision. An equality or a numerical logarithm still
needs those normalizations.

This is a reduction of the arithmetic comparison, not its proof. One
must prove that this particular analytic L2 is the image of the actual
CH localization and that the indicated base line is B. A matrix merely
chosen to fit the computed vector does not meet that obligation.

## 6. A computable candidate line from DL's Euler operator

Let F be the existing geometric Frobenius on H1_dR(E), so
F^2+3F+5=0. At the chosen CM embedding the four products of the two CM
Frobenius roots are 1,1,zeta7^3,zeta7^4. Put

    tau=zeta7^3+zeta7^4=1-xi-xi^2,
    E(F)=(1-F)^2*(1-tau*F+F^2).

DL Theorem3.1 says that its base analytic vector, after multiplication
by (1-F^2)/E(F), lies on the Hodge line span(omega). Thus the natural
candidate for B is

    B_DL=span(H(F)*omega),
    H(F)=E(F)/(1-F^2)
        =((-2-10*tau)+(11+tau)*F)/3.                 (7)

The polynomial reduction is exact. The denominators are units at5, and
the Euler factors are invertible. Using our calibrated (f_alpha,f_beta)
basis, the slope of this candidate line is

    r_DL=15070+68205*xi+21655*xi^2 mod5^7,
    r_DL=0 mod5.                                   (8)

Equation(8) is a numerical target for a conjectural line comparison. It
is not a computed value of r_E, and it is not a proved r_bad.

The PR annihilator zeta=((20I-13F)/45)omega has omega,eta coordinates
(13133,32916) mod5^7, hence line(3,1) mod5. In contrast, H(F)omega has
line(1,0) mod5. The two lines cannot be identified just because both
are written in a two-dimensional crystalline space: one is in regulator
coordinates, and the other in analytic coordinates. The missing
comparison has mathematical content even at the base line.

### Why the base-value theorem does not already prove the line comparison

Here L(0)=0, so the DL base-value Hodge-line assertion is vacuous for
calibrating M(0). The same is true for every minimal-level test vector,
since all are scalar multiples after projection. Knowing the first
ordinary row does not fix the other row.

An explicit exact model illustrates the remaining freedom. Put

    P=diag(1,t),       y_B=(t^2,B*t),
    M_B=[[1,0],[r-B,1]].

For every B, the same analytic vector is

    M_B*P(y_B)=t^2*(1,r).

It has zero constant and first terms, is even, and has the same known
ordinary scalar component. But the image of P0 is carried to
span(1,r-B), while the finite logarithm is B. It may be zero or nonzero.
This model also fixes determinant(M_B)=1 and the entire ordinary row.
It shows that the stated scalar law and base-value theorem alone cannot
force (7) to be the true bad line. These are abstract local models, not
claimed arithmetic realizations.

## 7. Next theorem and next numerical output

The useful numerical output is r_E, retaining both slopes with a
certified error bound. The useful arithmetic theorem is the line-level
reciprocity assertion B=B_DL, or another explicit description of B.
Proving that assertion and certifying r_E!=r_bad would imply the desired
nonzero reflected logarithm through (5)--(6). A full vector reciprocity
law would suffice but is stronger than this nonvanishing target needs.

Neither this note nor the cited first-order theorems proves that line
comparison. The available ordinary laws factor through the quotient
that misses the finite direction. The prior source ledger's restrictions
on exceptional-zero, CM-elliptic-curve, and changed-refinement results
therefore remain in force.

Run the exact coordinate check with:

```sh
python research/bsd-localization/leading_comparison/check_leading.py --check
```

## Sources and dependency boundaries

* Castella--Do, *Diagonal cycles and anticyclotomic Iwasawa theory of
  modular forms*, author version August4,2025: Section2.4.1 and
  Section2.4.3 for coordinates; Section4.1.3 for test vectors;
  Theorem5.1.1 and Proposition5.2.1 for the scalar factorization.
  https://kimtuando.github.io/website/Schoen_CM.pdf
  Published record: https://doi.org/10.4171/jems/1735
* Castella--Hsieh, *On the nonvanishing of generalised Kato classes for
  elliptic curves of rank2*, Section2.2 and Proposition2.5. The latter's
  introductory conductor restriction is why Castella--Do is used above.
  https://web.math.ucsb.edu/~castella/Kato-print.pdf
* Darmon--Lauder, *Stark points on elliptic curves via Perrin-Riou's
  philosophy*, Section1 and Theorem3.1. Conjecture3.2 is not treated as
  a proved derivative comparison.
  https://people.maths.ox.ac.uk/lauder/papers/DL.pdf
* The supplied theta-certificate package supplies the primitive
  norm-two cyclic ordering, regularization alpha^-2, exact lower zeros,
  and unit quadratic theta coefficient. Its archive hash is recorded
  in ../p5/inputs.json. The calculations here use that identified
  mathematical input; they do not rebuild its CM class polynomials.
