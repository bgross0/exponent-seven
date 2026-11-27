# Both tame traces of the CM second-weight jet

Date: 2026-11-27. This note concerns the actual analytic input families
constructed in `reflected_pilot/`, not a conjectural arithmetic
interpretation of their de Rham classes.

## Result

Put r=71, N=389, p=5, s=k-1, and W=6^s-1. Let g_W and h_W be the
two conductor-one CM Hida families for K=Q(sqrt(-71)), with the
ordinary stabilizations and weight coordinate used in the saved data.
Their finite characters may be the order-seven character and its inverse.
Write V_m for the **raw** q-operator F(q) -> F(q^m), and [5] for
depletion of coefficients whose indices are divisible by 5. The two
weight-two input families are

    Xi_A(W)=(d^(-s) g_W^[5]) * V_N h_W,
    Xi_B(W)=d^(-s)((V_N g_W)^[5]) * h_W.

The same conclusions hold with h additionally 5-depleted. These are the
analytic overconvergent weight-two families of the type constructed in
Darmon--Lauder, Section 1, with the specified test vectors. The statements
below apply to their germs, and in particular through W^2.

**Trace formula.** For either family Xi, both geometric degeneracy
traces from tame level rN to N are equal, and

    Tr_1 Xi = Tr_2 Xi = Xi + U_r Xi.                 (1)

Here U_r(sum a_n q^n)=sum a_(rn) q^n. Thus, if
Xi(W)=sum_(j=0)^2 F_j W^j mod W^3, then

    [q^n W^j] Tr_i Xi = [q^n]F_j + [q^(71n)]F_j.  (2)

No derivative correction to (2) is missing. The proof below tracks the
varying weights of the two factors before their product has fixed weight
two. In particular, it does not apply an ordinary complex slash operator
to an arbitrary raw q-series or commute a generic theta operator through
Fricke without justification.

## 1. Slash, oldform and geometric normalizations

For a matrix A=(a b; c d) of positive determinant, use

    (F|_k A)(z)=det(A)^(k/2)*(cz+d)^(-k)*F(Az).     (3)

Central positive scalar matrices act trivially. If D_m=diag(m,1), then

    F|_k D_m=m^(k/2)*V_m F.

In weight two this is the pullback on differentials for z -> mz:
it is m*V_m, not raw V_m. Formula (1) uses geometric traces adjoint to
these geometric pullbacks. For the input factors we retain the raw
V_389 convention of the saved q-series.

Let H=Gamma_0(rN), G=Gamma_0(N), and set

    sigma = (1  0; 389  1),
    T     = (1  1;   0  1),
    W_r   = (71  -23; 27619  -8946).

The determinant of W_r is 71. In fact 71*(-126)-389*(-23)=1.
The matrices 1 and sigma*T^a, 0<=a<71, represent H\G: their bottom
rows modulo 71 represent respectively (0:1) and all (1:b) in P^1(F_71).
Reduction of G modulo 71 is onto, since 389 is invertible modulo 71.
Consequently the trace is the sum of these 72 slashes.

For B_j=(1 j; 0 r), direct multiplication gives

    W_r*B_j/r = sigma*T^(j-23).                     (4)

Hence, at any integer weight k for which these operators act,

    Tr_1 F = F + r^(1-k/2)*U_r(F|_k W_r).           (5)

The factor r^(1-k/2) comes from the r terms of the trace and the
r^(-k/2) in F|_k B_j. It equals 1 at weight two.

The matrix W_r D_r^(-1)=(1 -23;389 -8946) lies in Gamma_0(N), so
the second degeneracy morphism is the first composed with w_r.
Furthermore W_r^2/r lies in H. On the trivial-character weight-two
input, w_r is therefore an involution, and

    Tr_2 F = Tr_1(F|_2 W_r)
           = F|_2 W_r + U_r F.                     (6)

Equations (5)--(6) are general. Formula (1) will follow from Xi|_2 W_r=Xi.

## 2. Fricke symmetry of conductor-one CM forms

Let w_r=(0 -1;r 0), the usual Fricke matrix at native level r. The
native CM specialization at an odd classical weight k is a sum of
harmonic binary theta series. More explicitly, put m=k-1. For ideal
class representatives a, the terms have the form

    C_a * sum_(alpha in a) alpha^m
                 exp(2*pi*i*z*Norm(alpha)/Norm(a)),

with constants C_a depending on the Hecke character. This follows by
writing each integral ideal in its class as (alpha)*a^(-1); the Hecke
character has value alpha^m on principal ideals. The sum over units
accounts for the usual factor 1/2. It does not affect the Fricke action.

Here is the normalization of the theta transformation, including the
higher-weight case. Scale a to the Euclidean lattice
L=sqrt(2/Norm(a))*a in C. Its covolume is sqrt(r), and

    L^* = i*L/sqrt(r).

For the harmonic homogeneous polynomial P(x)=x^m, with m even,
Poisson summation for the Gaussian gives

    theta_(L,P)(-1/(r*z))
       = -i*i^m * r^((m+1)/2)*z^(m+1)*theta_(L,P)(z).

Indeed the Fourier transform contributes the Gaussian factor and
z^m, while passing from L^* to iL/sqrt(r) contributes i^m*r^(-m/2).
Thus under the normalized slash (3),

    theta_(L,P)|_(m+1) w_r = i^(-(m+1))*theta_(L,P).

Every class summand has the same eigenvalue, so the CM form does too.
On our classical branch k=1 mod 4 this eigenvalue is always

    lambda_k=-i.                                  (7)

No class-character or CM-embedding-dependent sign appears. The
weight-one case, in exactly this Fricke convention, is also stated in
Schwagenscheidt--Williams, printed p.2. Mascot's Theorem 2.2.1 gives
an independent newform check: the ramified ideal is principal, its
coefficient is r^((k-1)/2) on this branch, and the quadratic Gauss-sum
factor gives a constant square root of -1. Mascot's chosen matrix has
the opposite odd-weight sign from w_r; the product sign below agrees.

### Raising tame level

For any native-level form f of character chi=chi_(-71), direct matrix
factorization, with the displayed W_r, gives

    f|W_r = chi(N)*(f|w_r),
    (V_N f)|W_r = V_N(f|w_r).                       (8)

For the first identity, W_r*w_r^(-1)=(23 1;8946 389) lies in
Gamma_0(r), with lower-right entry N. For the second, conjugate W_r
by D_N before multiplying by w_r^(-1); its lower-right entry is 1.
These identities include the normalized determinant factors. Passing
between raw V_N and normalized D_N introduces the same scalar on
both sides.

The character values are

    chi(389)=-1,       chi(5)=1.                    (9)

The displayed W_r at tame level rN does **not** normalize the
classical group Gamma_0(rN*25). At a classical specialization with
5-depletion, use a tame Atkin--Lehner lift at that actual level.
Put N'=N*25=9725, choose integers b',d' with r*d'-N'*b'=1, and use

    W'_r=(r b'; r*N' r*d').

For example b'=-35,d'=-4794 works. This is still the operator at the
exact divisor r=71, not full Fricke at rN*25. The same factorization
on a native form raised by V_m has character factor chi(N'/m).
For the terms m=5^j of the unraised factor, 0<=j<=2, this is -1;
for the terms m=389*5^j of the raised factor it is +1, since
chi(5)=1. Consequently every term of the stabilization/depletion
has the same required tame Fricke eigenvalue.

The canonical ordinary component of the p-power-level curve is
identified with the corresponding tame ordinary neighborhood by
selecting the canonical 25-subgroup. A prime-to-5 isogeny carries
that subgroup to the canonical subgroup of its target. Thus W'_r
induces the same tame correspondence as W_r on this component.
This is the identification used to transport the classical identity
to overconvergent tame-level forms. There is no use of the false
claim that the displayed lower-level matrix normalizes the larger
classical group. At the level of the odd-character factors, the
change of lift has extra character value chi(25)=1, also giving
the same normalization.

The trace can alternatively be formed classically at levels rN' and
N' and then restricted to their canonical components; its formula
is still F+U_r(F|W'_r). Thus the trace identity itself is independent
of this lift. For the cusp charts this compatibility is visible
explicitly. The actual-level chart sigma'=(1 0;9725 1) has shift
35, since 9725^(-1)=35 modulo 71. We have
sigma'=h*sigma*T^12 with h in Gamma_0(71*389), and 35=23+12.
Consequently its phase agrees with (16) after that chart change.
The lower-level slash notation in (16) means the canonical tame
chart, not an unjustified classical slash of a p-power-level form.

## 3. The inverse Bol operator at the other cusp

One cannot simply claim that d=q*d/dq preserves overconvergence in
every weight. The needed operator is the specific Bol power at a
classical weight k:

    d^(k-1): M_(2-k)^dagger -> M_k^dagger.          (10)

Coleman constructs this operator geometrically in Proposition 4.3,
printed p.222. Its quotient is the finite-dimensional de Rham
cohomology in Theorem 5.4, printed p.225; U acts there as Ver, which
is invertible by Theorem 5.1, printed p.223.

Let G=g_k^[5]. Since U_5 G=0, its cohomology class is zero. Thus G
has an overconvergent primitive H with d^(k-1)H=G. On q-expansions
all its positive coefficients are a_n/n^(k-1), and U_5 H has only a
constant coefficient. Replacing H by H-U_5H gives a primitive in
ker U_5. It is unique there: a q-series killed by d^(k-1) is
constant, while U_5 fixes a constant. The q-expansion principle then
gives uniqueness as an overconvergent form.

For completeness, the normalized Bol covariance is

    d^(k-1)(H|_(2-k) A)=(d^(k-1)H)|_k A.          (11)

For an integer k>=2 it follows directly by differentiating
(cz+d)^(k-2)*H(Az) k-1 times. All lower derivative terms cancel;
the surviving determinant factor is det(A)^(k-1). Together with
det(A)^((2-k)/2), this is the det(A)^(k/2) on the right. The
geometric operator (10) gives the same identity on overconvergent
sections. This is the special Bol identity, not a covariance claim
for arbitrary individual powers of d.

Tame w_r commutes with U_5 in this character component; the potential
character factor is chi(5)=1. Prime-to-5 isogenies preserve the
canonical 5-subgroup, so the same operators act on a common strict
ordinary neighborhood. Applying (11), the difference

    H|_(2-k)w_r - lambda_k H

is killed both by d^(k-1) and U_5. It is therefore zero. We have
proved

    d^(1-k)(g_k^[5])|_(2-k)w_r
         =lambda_k*d^(1-k)(g_k^[5]).               (12)

There is no residual Eichler-period polynomial or constant in (12).
The ker U_5 condition is what removes the possible integration
ambiguity. At k=1 the operator is the identity and (12) is immediate.

Raw raising satisfies the separately necessary identity

    d^(-s)(V_N G)=N^(-s)*V_N(d^(-s)G).            (13)

For p-adic s, N^(-s) here means <N>^(-s) on the chosen branch.
This is exactly the log_5(389) correction already present in the
second-jet generator. Dropping it would change Xi_B.

## 4. Fricke eigenvalue of the complete product and all its weight jets

At every classical weight k=1 mod 4, combine (7)--(12).
For Xi_A, its first factor has tame Fricke scalar chi(N)*lambda_k
and its raised second factor has scalar lambda_k. For Xi_B the
roles are reversed, and the scalar N^(-s) in (13) commutes with
Fricke. Their product scalar in both cases is

    chi(N)*lambda_k^2=(-1)*(-1)=1.                 (14)

Additional 5-depletion of h changes none of these statements.

The complete product has fixed weight two and trivial tame character.
Thus its Fricke operator is a fixed linear map, independent of W.
Here is the identity principle used to extend (14), including its
domain. Work on a sufficiently small closed disc |W|<=rho<1 about
W=0 on which the analytic modular-form family of Darmon--Lauder is
defined; one can shrink a disc of radius 1/5 further if necessary.
The tame correspondence is independent of W and continuous on the
ordinary Igusa space: its prime-to-5 isogeny preserves the p-divisible
group and multiplies an integral invariant differential by a 5-adic
unit. It therefore acts on analytic families and preserves Hodge-height
ordinary neighborhoods.

For all sufficiently large a, the distinct classical points

    W_a=6^(4*5^a)-1

lie in this disc and tend to its interior point 0. Each q coefficient
of Xi(W)|_2 W_r-Xi(W) is an analytic function of W which vanishes
at all W_a by (14). The rigid analytic identity theorem makes each
coefficient zero; the q-expansion principle then makes the family
zero. Thus

    Xi(W)|_2 W_r=Xi(W),
    F_j|_2 W_r=F_j for j=0,1,2.                    (15)

One can carry out this identity argument first on the ordinary Igusa
space, so it does not require assuming a uniform overconvergence
radius for every weight in a large family. For the three
overconvergent jets under discussion, take the minimum of their
individual radii; the resulting strict neighborhood is stable under
the tame correspondence. Equality on the ordinary locus, or the
q-expansion principle there, gives the same equality on that
neighborhood. This is an analytic-family argument, not an inference
from three sampled classical weights. No arithmetic Stark conjecture
or identification with a diagonal Galois class enters it. Equations
(5), (6), and (15) prove (1)--(2).

## 5. All non-infinity expansions and the differential scale

Putting j=23 in (4) gives sigma=W_r*B_23/r. Therefore (15) gives
the explicit non-infinity cusp expansion

    (F_j|_2 sigma)(z)=71^(-1)*F_j((z+23)/71).      (16)

If F_j=sum a_(n,j) q^n and q_71=exp(2*pi*i*z/71), this is

    sum_n 71^(-1)*zeta_71^(23n)*a_(n,j)*q_71^n.

The other 70 expansions are obtained by z -> z+a. Summing over a
annihilates all indices not divisible by 71 and gives U_71 F_j.
One therefore never needs to adjoin zeta_71 in the implementation:
its complete trace is performed symbolically.

The width factor in the differential operator must be retained. At
this cusp,

    d=q*d/dq = (1/71)*q_71*d/dq_71,

so its inverse s-th power contributes 71^s. Equivalently the scalar
acting at an index n/71 is <n/71>^(-s), not <n>^(-s).
The two slash factors in the cross product are respectively

    71^(-(1-s)/2),       71^(-(1+s)/2),

and their product is exactly 71^(-1). All W derivatives of those
weight factors cancel in the whole product. This explains why (16)
has no hidden log_5(71) terms although the individual factor jets
at this cusp do have such terms.

## 6. Exact finite interface and precision

The interface requires Xi's infinity coefficients for all indices
0<=n<=71B, through W^2, in the coefficient ring modulo 5^M.
For each j=0,1,2 and 0<=n<=B, output

    trace1[j,n] = trace2[j,n] = input[j,n]+input[j,71*n] mod 5^M.

It consists only of coefficient selection and addition. There is no
5-adic precision loss. The full factors can also be contracted
directly at indices n and 71n rather than forming every product
coefficient in between. For Xi_A the convolution condition is
a+389b=n; for Xi_B it is 389a+b=n.

Writing nu(m)=log_5(<m>)/log_5(6), the inverse-differential jet at a
5-adic unit index m is

    (1+W)^(-nu(m))
       =1-nu(m)W+nu(m)*(nu(m)+1)*W^2/2 mod W^3.

Use m=a for Xi_A and m=389a for Xi_B. Multiplying this by the two
CM jets gives the precise finite convolution used by the input
generator. The W^2 entry is a Taylor coefficient, not the second
derivative. Indices divisible by 5 in the differentiated factor
are omitted, so no nonanalytic 5^(-s) is introduced.

The saved q^4096 dataset therefore determines both traces through
q^57, since 71*57=4047. It does not determine q^58. For the previously
estimated lower-level input bound B=12675, the needed raw bound is
899925. Trace reduction reduces the subsequent space dimension;
it does not remove this coefficient-depth requirement.

On the E-old component, the two geometric pullbacks have Gram matrix

    (72  -10; -10  72).

Since (15) puts the component in the plus eigenspace, it has the form
(pi_1^*+pi_2^*)v, where

    v = (72+a_71(E))^(-1)*e_E(Tr_1 Xi)
      = (1/62)*e_E(Tr_1 Xi).                       (17)

Both 62 and the full Gram determinant 5084 are 5-adic units.
Root's separate certified Hecke polynomial projector at level 389
has a universal **one-digit** 5-adic division cost. That cost is
additional to this lossless trace/recovery step; subsequent local
regulator divisions and analytic comparison factors must retain their
own precision accounting.

Formula (17) recovers the complete E-old component, including both
Frobenius slopes. A chosen modular parametrization may take a further
specified linear combination of the two degeneracy coordinates.
This trace theorem neither computes that lower-level de Rham
projection nor proves its identification with CH's complementary
Perrin--Riou coordinate. Those remain separate steps.

## Source and verification status

The matrix/coset identities, harmonic-theta computation, inverse-Bol
argument, and trace formulas are mathematical derivations in this
note. The existing CM input and analytic-family construction are
their declared inputs. They are not Lean-formalized here and no
novelty claim is made. See `SOURCES.md` for exact source locations;
`TRACE_INTERFACE.json` records the finite interface without claiming
that a projected arithmetic class has been evaluated.
