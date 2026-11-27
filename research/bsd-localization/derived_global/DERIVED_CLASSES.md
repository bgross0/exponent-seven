# Derived global classes: a definite obstruction and a precise escape condition

Date: 2026-11-27. This note advances the localization-obstruction analysis in
the supplied rank-two package. It does not repeat the pilot computation and
does not claim a new arithmetic nonvanishing theorem. The algebraic results
below are proved here; their application to a proposed cohomology family has
the explicitly stated hypotheses.

**Evidence levels.** Sections 2--4 are elementary module/cohomology
arguments. Section 1 uses published CH results. Section 5 proves the
character and local-line calculations and states the full-family
cohomological comparison conditionally. Section 6 proves a reflected-class
consequence of specified CH inputs, using division in the original
Iwasawa module. No claim of nonzero localization or novelty is made, and
the proposition has not been formalized in Lean. The accompanying
computation verifies algebraic fixtures, not an arithmetic nonvanishing
theorem.

## 1. A whole family-construction strategy is excluded

Use the anticyclotomic tower and local conditions of Castella--Hsieh [CH22].
Theorem 4.1(b), printed p.20, identifies the intersection of the derived Selmer
filtration with universal norms. Immediately before Theorem 5.3, printed p.26,
the paper states that this intersection is zero in its definite setting,
using Cornut--Vatsal and the assumption that N^- has an odd number of factors.

Consequently a class obtained as the base specialization of a compatible
Selmer system in **that same anticyclotomic tower** is zero. This conclusion
does not require positive rational rank, nonzero localization, nonzero kappa,
or an already known Selmer dimension of two.

This also excludes the following proposed workaround. Suppose a big Selmer
class z can be divided by T^r **inside the big Selmer module**, and call the
quotient x. Then x is itself a compatible Selmer family. Its base
specialization is again a universal norm, and hence zero. Division inside
the same Selmer module does not create the missing transverse direction.

The qualification about the same deformation and local conditions is
essential. This is not a statement about every Galois-cohomology family,
every Hida deformation, or every relaxed Selmer structure.

### A weaker exclusion that already follows from the leading-term formula

Suppose theta has exact order two, and write CH's leading-term identity as

    h2(kappa,x) = c * Theta2 * ell(x),

with the nonzero constants interpreted in the paper's coefficient field.
For x in the third derived stage, the left side is zero: that stage is the
radical of h2, and h2 is alternating. Thus ell(x)=0. In particular, any
universally liftable class has zero logarithm even without using the stronger
vanishing of the whole universal-norm space. This inference assumes the
leading-term identity, but does not assume ell is already nonzero.

## 2. The correct algebra for dividing a relaxed family

Let R be a commutative ring, t an element of R, M and Q R-modules, and
F:M->Q an R-linear map. Think of M as global cohomology with relaxed local
conditions, Q as the quotient recording the disallowed local components,
and S=ker(F) as the desired big Selmer module.

### Proposition A: exact obstruction to saturation

There is a natural isomorphism

    {x in M : t^r*x in S}/S  ~=  (im(F))[t^r],

induced by x |-> F(x). Its kernel is exactly S, and an element of im(F) is
annihilated by t^r exactly when one of its preimages belongs to the numerator.
Thus division of a Selmer element in ambient global cohomology preserves
the Selmer condition if the relevant local quotient has no t^r-torsion.

**Counterexample.** Take R=Q[[t]], M=R, Q=R/(t), and F the quotient map.
Then S=tR. The element z=t is Selmer, but z/t=1 is not. The obstruction is
the nonzero element 1 in Q[t].

### Proposition B: one extra order of local vanishing suffices at the base

Assume multiplication by t^r on Q is injective. Suppose

    z=t^r*x,                 F(z)=t^(r+1)*q.

Then F(x)=t*q, because cancellation of t^r is valid in Q. Hence the image
of x in M/tM satisfies the specialized local condition ker(F mod t).

This permits a useful construction that Proposition A alone would miss:
the big family need not be Selmer. Its local defect must vanish one order
more deeply than the global class being divided. It remains necessary to
identify ker(F mod t) with the actual Bloch--Kato/ordinary local condition;
naive specialization of a quotient is not always the correct control map.

### Proposition C: a separate nonzero finite logarithm is required

Let L:M->R be a linear functional whose specialization is the desired
finite local logarithm. If z=t^r*x and L(z) has exact order r, then
L(x) mod t is nonzero, so the specialized global class is nonzero.

Together, B and C give a sufficient construction template:

    global order at least r;
    disallowed local component order at least r+1;
    permitted local logarithm order exactly r.

The two local maps must genuinely be different in the required sense. If
L factors through F by an R-linear map Q->R, the second condition forces
L(z) to have order at least r+1, contradicting the third. An explicit
reciprocity law on a singular quotient cannot simply be relabeled as a
finite logarithm. Removing an exceptional factor from a regulator requires
its own integral-domain and specialization argument.

### A constructive abstract model

Take R=Q[[t]], M=R^2 and F=t^2*J, where

    J = [[0,1],[-1,0]].

The big kernel is zero, while F mod t=0, so the specialized kernel is Q^2.
For z=t^r*(1,0), division gives x=(1,0). Its local defect is t^2*Jx,
which vanishes at the base but not as a family. The functional
L(x1,x2)=x1 detects x. This realizes the shape needed to escape the
universal-norm obstruction, without asserting that these modules arise
from an elliptic curve or that an arithmetic reciprocity law exists.

## 3. Finite lifts and the Bockstein obstruction

For a two-term complex C=[R^a --D(t)--> R^b], write

    D(t)=D0+tD1+t^2D2+...,
    x(t)=x0+tx1+t^2x2+... .

The condition D(t)x(t)=0 modulo t^n is the finite exact linear system

    sum(Di*x_(k-i), i=0..k)=0,       0<=k<n.

For x0 in ker(D0), the first obstruction is the class of D1*x0 in
coker(D0). It vanishes precisely when some x1 solves
D0*x1=-D1*x0. Higher obstructions depend on the earlier choices and must
be taken in the appropriate derived quotient; repeatedly using the same
unmodified cokernel is incorrect.

The accompanying `bockstein_lifts.py` implements the finite block linear
system over exact rational numbers. It computes the subspace of constant
terms that lift to each specified order. The actual run completed with all
checks passing; `bockstein-results.json` stores the results. It checks these
models:

| Differential | Liftable constants mod t | mod t^2 | mod t^3 | mod t^4 |
|---|---:|---:|---:|---:|
| diag(t,t^2) | 2 | 1 | 0 | 0 |
| diag(t^2,0) | 2 | 2 | 1 | 1 |
| t^2 J, J alternating and invertible | 2 | 2 | 0 | 0 |
| [[1,t],[0,t^2]] | 1 | 1 | 0 | 0 |

Thus a two-dimensional specialized cohomology space need not contain any
nonzero class liftable to a full compatible family. Even a vanishing first
Bockstein does not guarantee a lift past the next stage.

The identification of derived stages with images of finite lifts is made
explicit in Macias Castillo--Sano [MCS26], Appendix A, especially Remark A.6.
Its derived and generalized Bockstein maps are distinguished in Definitions
A.1 and A.3. Sano [S23], Section 2, supplies the corresponding descent
formalism. These sources justify the language; the finite matrix algorithm
and examples here are direct algebraic calculations.

## 4. Why a vanishing regulator image is insufficient for global division

Already with M=N=R and Col(x)=t^2*x, Col is injective and Col(1)=t^2,
yet 1 is not divisible by t. The defect is the t-torsion in coker(Col).
Injectivity of a Coleman map is therefore insufficient to transfer its
order of vanishing to the global class. A saturated image, or a genuine
global specialization/divisibility theorem, is needed.

There is a clean global source of divisibility when the **class itself**
specializes to zero. For a complex C and principal regular parameter t,
the derived exact triangle

    C --t--> C --> C tensor^L R/(t)

gives

    H1(C) --t--> H1(C) --> H1(C tensor^L R/(t)).

Exactness says that a class with zero derived specialization is divisible
by t in H1(C). Its quotient is unique if H1(C)[t]=0. The neighboring
H0 term governs this torsion. To use this for a Galois representation,
the derived specialization must be identified with the claimed ordinary
specialization; a vanishing projection to one summand alone is insufficient
unless the whole family is first projected to a regular summand.

## 5. Mixed stabilizations: a tempting tangent and its further obstruction

CH Proposition 5.2 proves that the mixed-stabilization classes vanish. Its
proof restricts the two CM weights to the anti-diagonal (ell,2-ell), where
the E-block is an anticyclotomic family with ordinary local conditions;
this is exactly the universal-norm obstruction above.

A first thought is to differentiate transversely to this line. That does
not follow from Proposition 5.2 alone, and the full CM decomposition is
decisive. Here is the character calculation. Let a=ell-1 and b=m-1. Let
Psi be the varying CM character of one fixed p-adic CM type, normalized so
that Psi*Psi^tau=N on the chosen weight branch, with N the cyclotomic/norm
character in that convention. The two inducing characters in the mixed
stabilization are psi*Psi^a and psi^(-tau)*Psi^b. The critical twist removes
N^((a+b)/2), leaving the two induced characters

    Psi^a*(Psi^tau)^b*N^(-(a+b)/2),
    chi*Psi^(a+b)*N^(-(a+b)/2),       chi=psi/psi^tau.

Set A=Psi*N^(-1/2), so A^tau=A^(-1). These are exactly A^(a-b) and
chi*A^(a+b). Equivalently, the critically normalized inducing characters
can be written

    psi*A^a       and       psi^(-tau)*A^b,

where A is the normalized anticyclotomic character. The tensor-induction
identity gives two blocks:

    V_E tensor Ind(A^(a-b)),
    V_E tensor Ind(chi*A^(a+b)),       chi=psi/psi^tau.

At odd p, t=a-b and u=a+b are independent formal parameters. The first
block is the same anticyclotomic E-family pulled back from t; u is an
additional scalar parameter. The second block carries the auxiliary
character. In multiplicative weight coordinates q2 and q3, the precise
change uses q_minus=(q2/q3)^(1/2) and q_plus=(q2*q3)^(1/2), with inverse
q2=q_plus*q_minus, q3=q_plus/q_minus. These half-powers are defined in the
completed weight algebra because 2 is a unit. The anti-diagonal fixes
q_plus=1; a transverse CM direction only moves the other block.

The tensor-induction projectors themselves require no division by
differences of eigencharacters. Choose the standard induced bases
e0,e1 and f0,f1. The spans of {e0*f0,e1*f1} and {e0*f1,e1*f0} are stable
under G_K and under the coset involution, which swaps each pair. Projection
onto these complementary spans is defined over the coefficient ring.
At the base, splitting Ind(1)=1+epsilon_K requires division only by 2.

In the mixed stabilization, the two E-block terms are g+ tensor h- and
g- tensor h+. Each has exactly one of the two CM plus-lines. The balanced
local condition therefore requires F+V_E in both terms. This follows from
the balanced module

    F++ = F+f*F+g*Vh + F+f*Vg*F+h + Vf*F+g*F+h.

Each mixed tensor line occurs in exactly one of the first two terms and
not in the third. Hence its f-factor is F+f. This calculation is valid
before specialization, at both p-adic primes, throughout the two-weight
chart; one must match the family's chosen ordinary summands to these CM
lines.

**Conditional two-weight no-go.** If these block decompositions and local
conditions extend over the completed weight algebra, and the relevant
global Selmer complex satisfies flat base change from R=L[[t]] to
R[[u]], then the E-block of the mixed class is zero whenever the compact
anticyclotomic Selmer module is zero. Indeed,

    H1(C_ac tensor_R R[[u]]) = H1(C_ac) tensor_R R[[u]] = 0.

All its u- and t-derivatives projected to E are then zero. Merely adding a
second CM-weight coordinate does not evade the obstruction. A proof of
the indicated family decomposition, regular projectors, flat base change,
and the precise zero compact module is required before calling this an
arithmetic theorem for the full family; this note has not supplied that
entire cohomological comparison.

Varying the f-weight changes the E-representation itself and is not covered
by this fixed-E argument. Deforming a weight-one form away from its CM
component is another genuinely different possibility. Neither is asserted
to produce a nonzero class: the local projector and reciprocity derivative
still have to be identified, and a more general universal-norm obstruction
could remain. Changing only a topological generator of the same
anticyclotomic tower does not change the obstruction.

## 6. A more concrete candidate: reflected relaxed classes

The following construction was suggested by the parent research thread.
It avoids the problem above because its family has relaxed local
conditions at both primes over p, although its base derivative is finite.
The claims here separate formal algebra, available CH inputs, and the
remaining nonvanishing theorem.

### Proposition: a reflected derivative in the rational Selmer group

Assume the setup of CH Section 5: E/Q has good ordinary reduction at
p>3, the imaginary quadratic field K has p split and discriminant prime
to p*N_E, the inert part N^- is a squarefree product of an odd number
of primes, and E[p] is irreducible and ramified at every prime dividing
N^-, as in CH Theorem A. Choose an auxiliary ray class character psi of
conductor prime to p*N_E and set chi=psi/psi^tau. Assume
chi(mathfrak_p)!=1 for a chosen prime mathfrak_p of K above p, and
assume

    L(E,1)=0 with root number +1,
    L(E^K,1)!=0,       L(E/K,chi,1)!=0.

Let L be a finite p-adic coefficient field containing the necessary
character values, let V=V_pE tensor_Qp L, and let kappa_plus be the
projected Iwasawa class of CH equation (3.12), using the test vectors
of Corollary 3.7. This is a class in the original module

    M = H1_Iw(K_infinity,V),       R=O_L[[Gamma]][1/p].

Write gamma=1+T for a topological generator. Complex conjugation c acts
L-linearly on the external coefficient field and iota-semilinearly on
R, with iota(gamma)=gamma^(-1). Suppose additionally that theta has
augmentation order at least two.

Then there is a **unique** x in M such that

    ((gamma-gamma^(-1))/2)*x = kappa_plus-c(kappa_plus).

It satisfies c(x)=x. Its base specialization x_0 is the restriction
of a class in Sel(Q,V). This class is allowed to be zero, and the
proposition does not assert nonzero localization.
The Iwasawa class x itself is nonzero when theta is nonzero, since its
Coleman image is u*theta/t. Nonvanishing of that family is different
from nonvanishing of its base specialization or base finite logarithm.

The published inputs can equivalently be separated into the three
properties actually used: kappa_0 is Selmer with vanishing minus
Selmer eigenspace; kappa_plus is **strict at one p-adic prime**, meaning
its full localization is identically zero; and at the other prime its
fixed Coleman image is a regular unit/nonzero scalar times theta.
These are supplied by CH Lemma 5.1, the nonzero quadratic-twist L-value,
and Corollary 3.7. CH Theorem 4.5 supplies the base local condition.
Sections 6.1--6.2 give the proof. This is a consequence of those inputs
and exact cohomology sequences; no claim of novelty or Lean
formalization is made.

### 6.1 The reflection and global division are canonical

Let M be global Iwasawa cohomology for the anticyclotomic tower, with
R=O[[T]][1/p] and gamma=1+T, where O is the coefficient ring of integers.
Complex conjugation c acts on the inverse system of cohomology groups.
It fixes L and is semilinear over the Iwasawa ring:

    c(r*z)=iota(r)*c(z),       iota(gamma)=gamma^(-1),       c^2=1.

This construction does not require choosing an identification between
unrelated Galois representations. In the equivalent universal-character
description, conjugation switches the character with its inverse and
the coefficient involution makes the same identification.

Let kappa_plus be the one-sided relaxed class supplied by CH. Its base
specialization belongs to Sel(K,V). If the quadratic-twist Selmer group
is zero, this specialization is c-invariant. Therefore

    Z = kappa_plus - c(kappa_plus)

has zero global specialization. To justify division in the original
Iwasawa module, use its standard Shapiro description by the universal
coefficient module boldT and the sequence

    0 -> boldT --T--> boldT -> T_E -> 0.

After rationalizing, its cohomology exact sequence gives

    H0(K,V) -> M --T--> M --specialize--> H1(K,V).

Thus Z=T*X. This uses vanishing of the actual specialized class, not
just vanishing of a regulator. Here H0(K,V)=0, since E(K)[p^infinity]
is finite, so there is no T-torsion ambiguity. CH equation (3.12),
printed p.16, explicitly identifies its projected class with this
Iwasawa module and its usual specialization. No division in the larger
formal ring L[[T]] is needed. If one
starts integrally, one first clears p-denominators and then kills the
finite torsion specialization; division followed by rationalization
gives the same result.

For a particularly clean parameter, put

    t = (gamma-gamma^(-1))/2 = T*(2+T)/(2*(1+T)).

It is T times a unit, and c(t)=-t. Thus x=Z/t exists; the torsion-free
division just established gives c(x)=x. With
the original coordinate T the corresponding identity is
c(X)=(1+T)*X, which also makes X_0 c-invariant. The invariant base class
descends from K to Q by restriction/corestriction, since 2 is invertible.
Neither the construction nor its descent assumes kappa_0 is nonzero.
The descended class is L-valued. Descent of its coefficients to Q_p is
not canonical. If it has nonzero localization, an appropriate Q_p-linear
coefficient functional on L produces a Q_p-valued Selmer witness with
nonzero localization.

### 6.2 The base local condition follows without unsafe cancellation

Choose the fixed Coleman map F at the prime where Corollary 3.7 gives
F(kappa_plus)=u*theta, with u a regular unit/nonzero scalar. The full
localization of kappa_plus at the conjugate prime is zero. Reflection
swaps the primes, so F(c(kappa_plus))=0. Hence

    F(Z)=F(kappa_plus)=u*theta,       F(c(Z))=-u*theta.

No comparison between two independently normalized Coleman maps is
needed. If theta has order at least two, R-linearity gives F(x) in J.
Since c(x)=x, its other Coleman input is also in J. The class x is in
the actual ambient Iwasawa cohomology by Section 6.1, so CH
Theorem 4.5, printed p.24, with r=1 puts x_0 in the
ordinary/Bloch--Kato Selmer group. This is a direct use of their theorem.
It does not infer literal divisibility of a singular local cohomology
class merely from divisibility of its Coleman image.

There is no additional rational away-from-p condition to assume for
V=V_pE: at any finite extension F_v/Q_l with l!=p, the group
E(F_v)[p^infinity] is finite, so H0(F_v,V)=0. Weil self-duality and local
Tate duality give H2(F_v,V)=0. The local Euler characteristic is zero,
so H1(F_v,V)=0. Thus every specialized global V-class has zero local
cohomology class away from p. Integral local quotients in the tower can
still have torsion; that is different from this rational base condition.

The printed height formula in Theorem 4.5 has an Iwasawa involution on
the second Coleman expression. For c(x)=x, its first-order terms are
F(t)+F(-t), so they cancel. Forgetting this involution incorrectly turns
the odd-height parity into a contradiction.

### 6.3 Exact theta order two leaves a sharp dichotomy

Suppose the relevant Coleman image of Z has exact order two and its
regulator is R-linear and regular. Global divisibility gives ord_t(Z)>=1,
while the regulator gives ord_t(Z)<=2. Thus there are two possibilities:

1. ord_t(Z)=1: x_0 is a nonzero rational Selmer class. Its finite
   logarithm may still be zero, so nonzero localization requires another
   argument.
2. ord_t(Z)=2: x_0=0. The next quotient Z/t^2 specializes to a
   c-anti-invariant relaxed class with a nonzero singular component
   when the nonzero specialization factor in CH Theorem 3.4 is used. The
   vanishing of the quadratic-twist *Selmer* group does not exclude such
   a relaxed class.

The second possibility explains precisely why a nonzero theta coefficient
alone does not prove the desired first derivative is nonzero.

An exact algebraic countermodel is included in the script. Take M=R^2,
c(e+)=e+, c(e-)=-e-, c(t)=-t, F_p(a,b)=t^2*a+b, and

    kappa=(a(t), -t^2*a(t)).

Then F_p(kappa)=0 and F_p(c(kappa))=2*t^2*a(-t). The choices a(t)=1
and a(t)=1+t have the same exact order-two leading defect, but their
reflected derivatives specialize respectively to 0 and 2*e+. This is
an algebraic insufficiency example, not a model satisfying every
arithmetic hypothesis of CH or a claim about the finite logarithm.

### 6.4 Nonzero localization survives unit-normalization ambiguities

Replace kappa by u(t)*kappa, where u is a regular unit. At the base,

    x'_0 = u(0)*x_0 + 2*u'(0)*kappa_0.

Indeed u*kappa-iota(u)*c(kappa)
=u*Z+(u-iota(u))*c(kappa), and (u-iota(u))/t has constant term 2*u'(0).
The base class kappa_0 has zero localization at one prime by Corollary
3.7; its c-invariance then makes its localization zero at the other.
Therefore

    log_p(x'_0)=u(0)*log_p(x_0).

The derived class depends on normalization modulo the strict kappa-line,
but the property of having nonzero localization does not. Replacing t
by another anti-invariant uniformizer also only rescales the base
logarithm by a nonzero constant.

This produces a well-defined candidate and narrows the new arithmetic
task to the nonvanishing of its permitted local logarithm. It does not
claim that nonvanishing follows from the theta leading coefficient.

## 7. A concrete next theorem to seek

For a proposed new direction s, with relaxed global class Z(s), the next
task is to establish all of the following for the **same regular E-block**:

1. Zero specialization of Z, yielding a global derivative by the exact
   triangle, together with uniqueness or an explicitly controlled ambiguity.
2. A local quotient Q with the required s-torsion-freeness, and an extra
   order of vanishing of the forbidden local component.
3. A reciprocity derivative whose specialization is the finite E-logarithm,
   rather than the auxiliary-character or singular component.
4. An arithmetic nonvanishing theorem for that derivative which does not
   already assume positive rank, finite Sha, or nonzero localization.

The new reduction here is that an everywhere-Selmer anticyclotomic family
is the wrong source, and even a transverse second CM weight may be a
scalar extension of that wrong source. A relaxed local defect or a
genuinely different representation deformation must do real work.

## Primary references

* [CH22] Castella--Hsieh, *On the nonvanishing of generalised Kato classes
  for elliptic curves of rank 2*, Forum of Mathematics, Sigma 10 (2022), e12.
  Theorem 4.1, Proposition 5.2, the paragraph before Theorem 5.3, and
  Theorem 5.3. https://web.math.ucsb.edu/~castella/Kato-print.pdf
* [MCS26] Macias Castillo--Sano, *On Selmer complexes, Stark systems and
  derived p-adic heights*, arXiv:2603.23978v1 (2026). Appendix A and
  Section4. https://arxiv.org/pdf/2603.23978
* [S23] Sano, *Derived Bockstein regulators and anticyclotomic p-adic
  Birch and Swinnerton-Dyer conjectures*, arXiv:2308.08875v1 (2023).
  Section 2. https://arxiv.org/pdf/2308.08875
* [BKS24] Burns--Kurihara--Sano, *On derivatives of Kato's Euler system for
  elliptic curves*, J. Math. Soc. Japan 76 (2024), 855--919.
  https://doi.org/10.2969/jmsj/90699069 . Its derivative constructions do
  not automatically provide the missing analytic-rank-two implication;
  the displayed BSD-element comparison has its own algebraic-rank and
  Sha hypotheses. Preprint: https://arxiv.org/pdf/1910.07404
