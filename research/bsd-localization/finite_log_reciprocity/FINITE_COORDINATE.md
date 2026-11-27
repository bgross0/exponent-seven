# The finite logarithm of the reflected class

Date: 2026-11-27. This continues `derived_global/DERIVED_CLASSES.md` and
`rationality/REFLECTED_REVIEW.md`. The reflected Selmer-class existence
proposition is taken as established under its stated Castella--Hsieh (CH)
hypotheses. Nothing here asserts that its finite logarithm is nonzero.

## 1. The exact local quantity to compute

Let c be complex conjugation on anticyclotomic Iwasawa cohomology,
gamma=1+T, and

    t=(gamma-gamma^(-1))/2,       x=(kappa-c(kappa))/t.

Choose the prime v over p where the CH Coleman image is nonzero. At the
conjugate prime the **full localization** of kappa is identically zero.
Consequently loc_v(c(kappa))=0 and, writing y=loc_v(kappa),

    loc_v(x)=y/t.

The specialized class kappa_0 is invariant under c and strict at one
prime; it is therefore strict at both primes. Thus y_0=0. The quantity
we need is precisely

    ell(x_0)=log_{omega_E}(sp(y/t)).                 (1)

There is no factor of two in (1). A factor of two occurs in a different
identity when kappa itself is globally divisible by t, but at this fixed
prime its reflected localization is zero.

The existing reciprocity law supplies

    F(y)=u(t)*Theta(t),                            (2)

where F is CH's scalar Coleman map, u is regular and nonzero at the base,
and Theta has order at least two. F specializes to a nonzero scalar times
the singular dual exponential. Equation (2) supplies the finite local
condition for sp(y/t); it does not supply its finite logarithm.

## 2. A formal lemma identifying the missing coordinate

Let A=L[[t]], let M be a free A-module of rank two, and identify M/tM
with a two-dimensional local cohomology space H. This completion is used
only to discuss local jets; the global divided class already exists in
the original bounded Iwasawa module. Suppose

* F:M->A is linear and F_0 is a nonzero functional on H;
* H_f=ker(F_0) is the finite local line;
* ell:H_f->L is the chosen Bloch--Kato logarithm;
* G:M->A is any regular linear map with G_0|H_f=ell.

**Finite-coordinate lemma.** If y is in tM and F(y) is in t^2 A, then

    x_loc=y/t,       sp(x_loc) in H_f,
    ell(sp(x_loc))=[t]G(y).                        (3)

Here [t] denotes the coefficient of t, not an unnormalized weight
derivative. The proof is just cancellation: F(x_loc) lies in tA, while
G(y)=tG(x_loc). Taking constant terms proves (3).

**Independence from the regular lift.** Suppose G' is another regular
functional with G'_0|H_f=ell. Since H/H_f is one-dimensional,

    G'-G=a(t)F+tH

for some regular scalar a and regular functional H. Therefore

    (G'-G)(y) in t^2 A,

and the coefficient in (3) is independent of G. To see the decomposition,
first choose a(0) so that (G'-G)_0=a(0)F_0. Subtract this multiple of F;
each coordinate of the remaining functional is divisible by t because M
is free. No Selmer-rank hypothesis is used.

The same argument shows invariance under a different splitting of the
ordinary local exact sequence. What is missing is not a canonical
choice among regular lifts of the finite logarithm: the coefficient of
interest is canonical among all of them. What is missing is an arithmetic
formula evaluating one such lift on the actual class y.

### A normal form

If w generates ker(F), w_0 spans H_f, and n satisfies F(n)=1, then
M=A*w+A*n. Normalize w so that ell(w_0)=1. We can write

    y=t*a(t)*w+t^2*b(t)*n.

Equation (2) determines t^2*b(t). The target is a(0). Replacing
n by n+h(t)w changes the w-coordinate of y by a multiple of t^2, so
does not change a(0).

This normal form requires the specified freeness, kernel and local
specialization identifications. The finite-coordinate lemma itself only
requires the weaker hypotheses stated before (3).

### Exact insufficiency of even the entire scalar theta series

In M=A^2, take F(a,b)=b, H_f=L*(1,0), ell(a,0)=a, and

    y_B=(B*t, t^2),       B in L.

Every y_B has the **same entire scalar image** F(y_B)=t^2, while

    ell(sp(y_B/t))=B.

Thus no manipulation of the scalar theta series alone can recover the
finite logarithm without additional information about the global class
or another local coordinate. This is a local algebraic example; it does
not assert that all these choices occur as actual global diagonal classes.

## 3. Calibration from CH's finite local norm

CH constructs a finite local universal norm w_eta using the big
exponential. Its Lemma 4.4, printed p.23, gives

    sp_F(w_eta)=exp_{F,V}(((1-p^(-1)*phi^(-1))/(1-phi))*eta).

In the normalization of CH (3.14), printed p.18,

    phi(eta)=(alpha/p)*eta,
    <eta,omega_E tensor t_cris^(-1)>_dR=1.

Thus the logarithm at F is

    (1-alpha^(-1))/(1-alpha/p).

The vector used after local corestriction to Q_p has logarithm

    c_E=d*(1-alpha^(-1))/(1-alpha/p),       d=[F:Q_p].       (4)

This also follows by inverting the logarithm normalization appearing in
the proof of CH Theorem 4.5, printed p.24. Both numerator and denominator
are nonzero for an elliptic curve of good ordinary reduction at p>3.
One may divide the norm vector by c_E to obtain ell(w_0)=1 over L.

For the pilot E389, p=5, K=Q(sqrt(-71)), and conductor c=1, d=7.
Indeed the Hilbert class group has order seven, and a prime above five
is not principal: the norm equation a^2+ab+18b^2=5 has no integer
solution. Its ideal class therefore has order seven, which is the local
residue degree in the Hilbert class field. The factor in (4) is

    7*(1-alpha^(-1))/(1-alpha/5).

This calibrates the **local finite direction**. It does not determine
the coefficient a(0) of the diagonal class. A Frobenius matrix on
H^1_dR(E) must also be converted to CH's V_pE convention: CH's eta is
the Tate-twisted unit-root eigenline, of eigenvalue alpha/p, with its
scale fixed by the displayed pairing. A choice of eigenline alone does
not fix the scale or the pairing sign.

## 4. What a full vector Perrin--Riou regulator could supply

Here is a second exact algebraic criterion. Let

    P:M -> A^2

be a regular rank-two regulator, with P(0) of rank one and determinant
of exact t-order one. Assume ker(P(0))=H_f. Choose a nonzero output
functional lambda_0 annihilating im(P(0)), and extend it regularly to
lambda(t). Then lambda(t)P(M) is contained in tA, so

    G_P=lambda(t)P/t : M -> A

is regular. Its restriction to H_f at the base is nonzero. For example,
take a basis w,n with w_0 in H_f and n_0 outside H_f. In the output
basis adapted to im(P(0)), the first nonzero coefficient of the determinant
is a nonzero multiple of (G_P)_0(w_0). Exact determinant order one
therefore forces (G_P)_0(w_0) != 0.

Let c_P be the nonzero scalar defined by

    (G_P)_0|H_f=c_P*ell.

For the same y as in Section 2, this gives the exact extraction rule

    ell(sp(y/t)) = c_P^(-1)*[t^2](lambda(t)P(y)).           (5)

It is a **second coefficient of a divided complementary vector
component**, rather than the second coefficient of CH's scalar F.
Changing lambda by another regular extension with the same base
annihilator affects the expression only through terms already controlled
by Section 2, after consistent normalization.

In fact P(y) itself lies in t^2 A^2: write y=t*x_loc, and use
P(0)(sp(x_loc))=0. Thus changing lambda by t times another functional
changes lambda P(y) only in degree at least three.

### An explicit annihilator from CH's interpolation formula

Put

    A_phi=(1-p^(-1)*phi^(-1))*(1-phi)^(-1).

Let omega_tilde span Fil^0 D(V), with V=V_pE, and define

    zeta=A_phi^(-1)*omega_tilde.                         (6)

CH Theorem 3.4, printed p.16, at j=0 and n=-1 gives

    Col_zeta(z)(1)=<exp^*(z_0),A_phi*zeta>_dR=0

for every local z. The last equality holds because exp^*(z_0) is in
Fil^0 D(V^*) and this annihilates Fil^0 D(V). Although (3.9) is first
stated for eigenvectors to specify growth, it extends linearly to zeta;
the vector map of Definition 3.3 is already defined before that pairing.
Consequently Col_zeta/t is a regular map at the augmentation. To identify
its restriction to H_f as a nonzero multiple c_zeta of ell still requires
the simple-determinant/local-control comparison described below. With
that comparison, the concrete form of (5) is

    ell(x_0)=c_zeta^(-1)*[t^2]Col_zeta(loc_v(kappa)).     (7)

The sign of c_zeta is part of its definition. At the base specialization
in (6) there is no extra Iwasawa involution or sign: zeta is constant.
When expressing the map by a Tate pairing against a divided big
exponential, the involution must be retained; division in the second
argument contributes iota(t)=-t.

For the pilot, write F for crystalline Frobenius on H^1_dR(E), with
F^2+3F+5=0. Under V=H^1_et(E)(1), phi=F/5, and

    zeta=(1-F/5)*(1-F^(-1))^(-1)*omega_tilde
        =((20-13F)/45)*omega_tilde.                    (8)

This identity is exact in Q[F]/(F^2+3F+5). It is checked independently
by the accompanying script. The numerical realization of (8), computed
in the separate `local_crystalline/` workstream, determines the target
crystalline pairing. It does not determine the diagonal class's value
under that pairing.

### Weight coordinates and analytic normalization

Suppose s is a computational weight coordinate and t=a*s+O(s^2),
with a nonzero. Suppose an analytic vector D(s) is proved to satisfy

    D(s)=U(s)*P(y(t(s))) mod s^3,        U(0) invertible. (9)

Because P(y) has order at least two, only U(0) matters at that order.
The extraction rule is then

    ell(x_0)=[s^2](lambda_0*U(0)^(-1)*D(s))/(c_P*a^2). (10)

If one uses the second derivative rather than its power-series
coefficient, the denominator in (10) acquires the factor 2. No
derivative of U and no quadratic term of t(s) is needed. Conversely,
an analytic family with a nonzero constant or first vector coefficient
cannot satisfy (9) for this strict base class. This is a useful early
falsification check on a proposed comparison.

For W=(1+p)^(k-1)-1, the ordinary weight derivative is
log_p(1+p) times the W derivative. CH's variable satisfies
T=v^(-1)(1+S)-1 (Proposition 2.5). An implementation must identify its
CM weight coordinate with this T and its chosen anticyclotomic
generator, rather than silently putting a=1.

### Published support and remaining comparison

For the cyclotomic Perrin--Riou regulator, Lei--Loeffler--Zerbes prove
an elementary-divisor formula in Theorem 4.16, printed p.1124. For
Hodge--Tate weights 0 and 1, its two factors are 1 and

    ell_0=log(1+T)/log_p(chi_cyc(gamma)),

so at the trivial character the nontrivial factor has a simple zero.
Theorem 4.16 is a theorem about their cyclotomic regulator and its stated
coefficient/distribution algebra. It is not by itself an identification
with CH's relative Lubin--Tate regulator along the anticyclotomic local
extension. CH Section 3 constructs a vector Coleman map before pairing
with eta, so a compatible two-component construction is available in
principle. Applying (5) requires verifying its elementary divisors and
specialization normalization in precisely that local extension.

Even after this local comparison, a separate **explicit reciprocity
law for lambda P(y)** is needed to replace the cohomological quantity
in (5) by a computable analytic function. CH's reciprocity law provides
one pairing with eta. It does not provide the second vector component.

## 5. Why the other ordinary triple-product branches do not immediately help

Use a notation independent of the sources' plus-sign conventions. The
balanced local module is Fil^2, of rank four, and the deepest ordinary
line is Fil^3, of rank one. Their associated graded quotient is

    gr^2 = (-++) + (+-+) + (++-),
    Fil^3 = (+++).

The f-, g- and h-dominant ordinary Perrin--Riou maps factor through the
three respective summands of gr^2. In particular they all annihilate
the image of H^1(Fil^3). These definitions are in Darmon--Rotger's
Lemma 5.3 and Proposition 5.7 (their rank-one space is called V^{++},
and their balanced rank-four space V^+), and in BSV's equations
(146)--(147), printed pp.53--54 of the author preprint.

In CH's fixed-f, same-CM-type diagonal specialization the nonzero E
local block has CM signs g+ h+. The full f-factor is allowed there;
its finite ordinary subline is precisely f+g+h+, the deepest line
annihilated by all three quotient maps. The f-dominant branch sees the
singular f- direction and gives theta. The g- and h-dominant branches
see the auxiliary-character blocks, rather than the missing finite
E-coordinate. CH Lemma 3.5 makes the auxiliary global class identically
zero along this diagonal when its auxiliary L-value is nonzero.

Therefore simply changing from L_p^f to L_p^g or L_p^h does not yield
(1). Along this fixed diagonal, derivatives of the identically zero
auxiliary component remain zero. A transverse weight derivative changes
the problem and needs a proved comparison with the same E-coordinate;
it cannot be substituted by formal analogy.

This also explains why varying a tame test vector in the existing
ordinary reciprocity theorem does not authorize replacing its fixed
crystalline pairing with an arbitrary complementary eigenvector. The
theorem specifies its quotient and pairing. A different refinement or
another vector regulator needs its own comparison to the same class.

## 6. Existing derivative and complementary-class formulas: exact scope

### Darmon--Lauder's analytic vector and the second jet

Darmon--Lauder constructs a de Rham valued analytic family from the
weight-two overconvergent product d^(1-k)(g_k^[p])*h_k, followed by
Coleman's cohomological projection and the chosen E projection. Both
ordinary and slope-one components can be computed. Theorem 3.1,
printed p.10, proves a base-value identity after an explicit Frobenius
Euler operator. The derivative comparison is Conjecture 3.2, not a
proved identity with the full regulator of CH's varying class.

Their Section 2.3, Case 1, printed p.8, makes the adjoint rank-(2,0)
Perrin--Riou point regulator zero. A first-derivative point formula
therefore does not provide our missing second-order coordinate. The
second vector jet is a concrete analytic target for (9), with the
cohomological comparison still to be proved. These are different
claims: the analytic family is defined and computable, while the
required interpretation as the finite logarithm of this reflected
class is not established by that paper.

For the raw q-series computation, retain the depletion convention.
Theorem 3.1 uses g^[p]*h. The formula in Section 4 instead writes a
depletion on h; agreement needs its Euler correction. A p-adic exponent
n^(-s) must not be assigned silently to indices divisible by p.

### Rivero and BSV

Rivero's author PDF has standing split-multiplicative reduction at p.
Proposition 3.9 constructs a globally divided class along the direction
wt(f)=wt(g)+1 with h fixed, and Theorem 3.10, printed p.17, identifies
the logarithm of its specified g-projection with an L-invariant times
the g-dominant p-adic L-value. Its proof differentiates an actual Euler
factor zero and a class which is known to vanish. It is a useful model
of the exact proof obligations for (5), but those vanishing Euler
factors are absent at the good-ordinary pilot. Question 5.3, printed
p.24, explicitly asks for a generic non-exceptional second-derivative
reciprocity law. It must not be quoted as a theorem.

BSV's companion paper on rational points assumes multiplicative
reduction and that p is inert in its quadratic field; its Proposition
2.2 and Theorem A belong to that exceptional setup. Our p=5 is good
ordinary and split in K. Their logarithm formulas cannot simply be
transported to the pilot.

### Castella's CM construction

The February 13, 2026 version of `Kato-Schoen.pdf` gives, in Theorem C,
printed p.6, a basis consisting of a generalized Kato class and a derived
elliptic unit. The theorem assumes E has CM, finite Sha(E/Q)[p^infinity],
and the two specified Katz L-functions have orders 2 and 1. It is an
actual construction of the desired kind in its setting, but neither
the CM hypothesis nor the finite-Sha hypothesis may be silently dropped.
The pilot E389 is non-CM. The ordinary scalar theta function in our
construction is not automatically either of the two Katz functions.

### Finite-slope and Eisenstein-degeneration leads

Huang's arXiv:2403.18620v2 (November 9, 2026) proves finite-slope
triple-product Gross--Zagier and reciprocity results. A critical-slope
f-refinement is a possible source of a different crystalline component,
but one must prove that its class compares to the original CH class,
control specialization at weight two, and identify the divided
complementary coordinate. A change of refinement alone proves none of
these comparisons.

Alonso--Omil-Pazos--Rivero, arXiv:2509.07564, compares diagonal and
Beilinson--Flach classes using a CM family specializing to an irregular
weight-one Eisenstein series. This is a genuinely different degeneration
mechanism. It is not the regular cuspidal weight-one CM point of the
pilot, so applying it would require a new comparison, not merely a
different test vector.

## 7. Concrete next arithmetic identity

There are now two precise sufficient data formats:

1. A certified local cohomology jet y modulo t^2, together with a
   regular lift G of the normalized finite logarithm. Then (3) computes
   the target directly.
2. A compatible full vector regulator P and an explicit reciprocity
   law for lambda P(y) modulo t^3, with the nonzero constant c_P
   calibrated. Then (5) computes the target. The concrete pairing
   vector (8) and the analytic comparison format (9)--(10) specify
   exactly which second coefficient and coordinate normalization are
   required.

Computing CM q-expansion weight jets, a local Frobenius eigenline, or
the scalar theta element contributes useful inputs to these tasks.
None of those computations alone supplies the missing class jet or
the missing vector reciprocity value. The accompanying exact check
verifies the finite-coordinate identities and the ordinary-filtration
blind spot; it is not an arithmetic certificate for the reflected class.

Run the check with

    python3 research/bsd-localization/finite_log_reciprocity/check_finite_coordinate.py

The saved output is `finite-coordinate-results.json`. It checks seven
formal identities, including the CH annihilator operator and the
coordinate-change factors; it makes no arithmetic nonvanishing claim.

For source details and theorem hypotheses see `SOURCE_LEDGER.md`.
