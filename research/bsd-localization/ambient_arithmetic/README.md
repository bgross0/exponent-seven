# The ambient obstruction is a first global Bockstein

Date: 2026-11-27.

## Result and scope

This note gives a conditional arithmetic reduction for the reflected class
constructed in `../derived_global/DERIVED_CLASSES.md`, Section 6. It does
not assert that the remaining arithmetic invariant has been computed.

Let `kappa` be the one-sided relaxed Castella--Hsieh family, let `c` be
complex conjugation, and put

\[
t=(\gamma-\gamma^{-1})/2,\qquad
x=(\kappa-c\kappa)/t,\qquad x_0=\operatorname{sp}(x).
\]

Here `c(t)=-t`, and `c` fixes the constant coefficient field. The existing
construction supplies a possibly zero class
`x0 in Sel(Q,V_L)`, under the CH hypotheses and `ord_t Theta=2`.

**Conditional conclusion.** With the Poitou--Tate identification, local
regulator saturation, and main-conjecture equality specified below,

\[
\boxed{\ell(x_0)\ne0
\quad\Longleftrightarrow\quad
\operatorname{length}_{R}H^2_{\rm Iw}(K_\infty,V_L)_R=1.}
\tag{1}
\]

Here `R=(O_L[[T]][1/p])_(T)` is the augmentation discrete valuation ring,
and `ell` is the finite logarithm at one of the split primes above `p`.
The quotient defining `x` already exists in the original bounded Iwasawa
module; this localization is used to measure an index, not to manufacture
a new global class.

Under the additional pilot facts `dim Sel(K,V_L)=2`, all Selmer classes
are plus, and `ell` is nonzero, the obstruction module has only two
possibilities:

\[
H^2_{\rm Iw}(K_\infty,V_L)_R\simeq R/(t)
\quad\text{or}\quad R/(t^2).
\tag{2}
\]

The first case makes the reflected class transverse to the strict line;
the second forces it into that line. Equivalently, the first case is
detected by a nonzero **global first Bockstein**, which is a cup product
with the anticyclotomic character. This is a new conditional reduction
in this work package, not a claimed new theorem of arithmetic
nonvanishing, and it has not been formalized in Lean.

## 1. Exact hypotheses and identifications

Write

\[
M=H^1_{\rm Iw}(K_\infty,V_L)_R,\qquad
B=H^2_{\rm Iw}(K_\infty,V_L)_R,
\]

and let `Q=Q_p + Q_bar` be the two ordinary local quotient modules. Each
has rank one over `R`. Let `X` be degree-two cohomology of the ordinary
Selmer complex. With the standard duality convention it is the localized
dual of the ordinary discrete Selmer group. An involution on that dual,
if required by the convention, preserves every `t`-length used here.

We use these precise inputs:

1. Global cohomology has derived specialization to `R Gamma(G_K,S,V_L)`;
   its relevant cohomology is in degrees one and two. Global `H0` is
   zero. Thus `M/tM` injects into `H1(K,V_L)`, and `B/tB` identifies with
   `H2(K,V_L)`.
2. The ordinary compact Selmer module is zero, and local quotients have
   no degree-two cohomology after augmentation localization. Consequently
   the Selmer-complex triangle gives the **exact** sequence

   \[
   0\longrightarrow M\xrightarrow{\Phi}Q
   \longrightarrow X\longrightarrow B\longrightarrow0.
   \tag{3}
   \]

3. The chosen scalar Coleman maps identify `Q_p` and `Q_bar` with `R`
   up to units at augmentation. Their kernels are the ordinary local
   lines. Under these identifications, one column of `Phi(kappa)` is
   zero and the other has exact order two; `c(kappa)` has the reversed
   support and the same order. All non-theta factors in the reciprocity
   law have nonzero augmentation.
4. The ordinary anticyclotomic main-conjecture **equality** gives

   \[
   \operatorname{length}_R X
   =2\operatorname{ord}_t\Theta=4.
   \tag{4}

   A one-sided divisibility is not substituted for this equality.
5. The base twist Selmer group is zero, so every base Selmer class over
   `K` is plus. CH's ambient-cohomology specialization criterion applies
   to the original family and its divisible quotients. The base class
   `kappa0` is therefore strict: it is plus and one full localization is
   zero. No nonzero localization is assumed in the proof of (1).

### Why the terminal zero in (3) is justified

The relevant long exact sequence continues with `B -> H2(Q_local)`.
The ordinary quotient at a split `p`-adic place is the cohomology of the
rank-one quotient representation `V^-`. In the good ordinary,
nonexceptional setting its `H0` and `H2` at the base vanish. The latter
also follows from local duality, since the dual twist is the ordinary
plus line and has no invariants. Derived base change and Nakayama then
make the localized local `H2` zero. The full local representation has
`H0=H2=0` as well, so its degree-one specialization is an isomorphism.

At a finite place away from `p`, `H0(F_v,V_pE)=0` because local
`p`-power torsion is finite. Weil self-duality gives `H2=0`, and the
local Euler characteristic gives `H1=0`. The rational localized local
complexes are therefore acyclic. This explains why no omitted tame
term survives in (3). These are statements after inverting `p` and
localizing at augmentation; integral torsion has not been declared zero.

The inverse-limit Poitou--Tate sequence also identifies `B` with the
localized dual fine Selmer module: the intervening local `H2` and global
`H0` terms vanish here. Wuthrich's equations (7.5) and (7.6) record the
specialization and fine-Selmer sequences before this rational
localization. At the base, Poitou--Tate gives the perfect duality

\[
H^2(K,V_L)\simeq S_0^*,\qquad
S_0=\ker\bigl(H^1(K,V_L)\longrightarrow
                 \textstyle\bigoplus_{v\mid p}H^1(K_v,V_L)\bigr).
\tag{5}

In this setting `S0` is precisely the strict Selmer space. This
identification does not assume finiteness of Sha.

### Local saturation is more than regulator injectivity

CH Proposition 4.3 expresses the scalar Coleman map as a local Iwasawa
Tate pairing against a finite local class `w_eta`, times a factor with
nonzero augmentation. Lemma 4.4 gives a nonzero finite specialization
of that class: its logarithm contains the factor
`(1-alpha_p^(-1))/(1-p^(-1) alpha_p)`. Both factors are nonzero in the
good ordinary elliptic-curve setting. After localization, `w_eta` is
primitive. The perfect local pairing then makes its quotient functional
surjective, and the ordinary line is its kernel. This supplies the
saturation needed in input 3, once the indicated local and coefficient
identifications are made.

One may make a faithfully flat extension of the constant coefficient
field to accommodate CH's unramified regulator coefficients. This
preserves `t`-lengths. Alternatively, Castella's Theorem 4.1.1 gives a
rank-one regulator with pseudo-null cokernel, hence an isomorphism at
the augmentation height-one prime; matching the regulator conventions
is still required. Mere injectivity would not suffice.

### Main-conjecture eligibility is a separate gate

Castella, *Nonvanishing of generalised Kato classes and Iwasawa main
conjectures*, Theorem 4.2.1, supplies (4) for a `p`-old weight-two ordinary
form when `N^-` is squarefree with an odd number of prime factors and
Assumption (A) holds: residual absolute irreducibility, ramification at
`q|N^-` with `q=+/-1 mod p`, and either `p>5` or residual image containing
`SL2(F_p)`. It is independent of a chosen auxiliary order-seven CM
character. A theta certificate alone is not a verification of this
theorem's hypotheses.

For the pilot, the available arithmetic offers a short way to check the
extra `p=5` image condition. The Frobenius polynomial at `3` is
`X^2+2X+3`, with nonsquare discriminant `2 mod 5`, excluding an invariant
`F5`-line. Split multiplicative reduction at `389`, with valuation one
of the minimal discriminant, supplies a nontrivial transvection by the
Tate-curve inertia criterion. An irreducible subgroup of `GL2(F5)`
containing a transvection contains `SL2(F5)`: conjugate that transvection
to a distinct fixed line, choose those two fixed lines as a basis, and
take powers to obtain every upper and lower unipotent matrix. These
generate `SL2(F5)`. This arithmetic interpretation is distinct from the
algebraic fixture computation below.

## 2. The determinant identity

Let `N=R kappa + R c(kappa)`. Its two generators are independent because
their nonzero local quotient coordinates have disjoint support.
Equation (3) then makes `M` free of rank two. Input 3 gives

\[
\operatorname{length}_R(Q/\Phi N)=4.
\]

Put `a=length(Q/Phi M)` and `d=length(M/N)`. The inclusions
`Phi N < Phi M < Q` and (3) give, respectively,

\[
a+d=4,\qquad a+\operatorname{length}_R B=4.
\]

Hence

\[
\boxed{\operatorname{length}_R B
       =\operatorname{length}_R(M/N).}
\tag{6}

This expresses the ambient fine-Selmer obstruction as the saturation
index of the two reflected one-sided families. It uses the equality
in (4) exactly once.

## 3. Proof of the localization criterion

First observe a useful vanishing implication:

\[
\kappa_0=0\quad\Longrightarrow\quad\ell(x_0)=0.
\tag{7}

Indeed, global specialization exactness gives `kappa=t eta`. The
original zero full localization stays zero after division because the
local module is `t`-torsion-free. Its opposite Coleman coordinate now
has order one. CH Theorem 4.5 therefore makes `eta0` Selmer. It is plus
by twist-Selmer vanishing, so its other full localization is also zero.
Since `c(t)=-t`, the reflected quotient is `eta+c(eta)`, with base
`2 eta0`, and is strict.

The wedge identity

\[
\kappa\wedge c\kappa=-t\,\kappa\wedge x
\tag{8}

now proves (1). If `length B=1`, (6) and (8) show that `kappa,x` form
an `R`-basis of `M`. Their base classes are independent. On the other
hand, (5) and `B/tB` of dimension one show that the strict Selmer
space is one-dimensional. It contains `kappa0`, so `x0` is not strict.
Because `x0` is plus and finite at both primes, its finite logarithm
is nonzero.

Conversely, if `ell(x0)` is nonzero, (7) gives `kappa0!=0`. The strict
class `kappa0` and the transverse class `x0` are independent. Their
lifts form an `R`-basis by Nakayama, and (8) gives `length(M/N)=1`.
Equation (6) gives `length B=1`.

This proof distinguishes three conclusions: `x` is a nonzero family;
`x0` might nevertheless vanish; and even a nonzero `x0` might be strict.
It does not equate any of them without the stated argument.

## 4. A two-case dichotomy under the established rank-two pilot facts

Now suppose, additionally, that `S=Sel(K,V_L)` is two-dimensional,
`S=S^+`, and its finite localization is nonzero. Then `dim S0=1`,
and (5) implies

\[
B\simeq R/(t^h)\quad(h\ge1).
\]

Global Poitou--Tate and Euler characteristics over `Q`, applied also
to the rank-zero quadratic twist, give

\[
\dim H^1(K,V_L)^+=2,\quad
\dim H^1(K,V_L)^-=1,\quad H^2(K,V_L)=H^2(K,V_L)^+.
\]

In particular `H1(K,V_L)^+=S`. Let `U=im(M/tM -> H1(K,V_L))`.
The quotient `H1/U` is `Tor_1^R(B,L)`. Its conjugation sign is
`(-1)^h`: in a minimal two-term summand `R --t^h--> R`, the target
has plus sign and equivariance forces that sign on the source. The
extra sign of the `t`-resolution must be retained; treating the
connecting map as untwisted would reverse this conclusion.

If `h` is odd, `U` is the entire two-dimensional plus space. Hence
`Phi mod t=0`, so `a=ord det Phi>=2`. From `a+h=4`, odd `h` is at
most two, and therefore `h=1`.

If `h` is even, `U` has plus and minus dimensions one each. The plus
line is Selmer, while the minus line is not, because `S^-=0`. Thus
`Phi mod t` has rank one, giving `a>=1`. Now even `h<=3`, so `h=2`.
This proves (2).

In both cases `kappa0` is nonzero. Otherwise `kappa=t eta` and the
argument proving (7) gives `eta0` plus. Thus `eta` and `c(eta)` have
dependent specializations, so their index in `M` is at least one.
Multiplying both by `t` would give `length(M/N)>=3`, contrary to (2).

Consequently the exact alternatives are:

| Global obstruction | `U` eigendimensions (+,-) | `U intersect S` | Reflected logarithm |
|---|---|---|---|
| `R/(t)` | `(2,0)` | all of `S` | nonzero |
| `R/(t^2)` | `(1,1)` | `S0=L kappa0` | zero |

The table is a conditional consequence of the arithmetic inputs, not a
claim that the first case has been selected for `389.a1`.

## 5. A finite first-jet test, and what must be certified

Let `a_ac:G_K,S -> L` be the anticyclotomic character obtained by
linearizing the Iwasawa action. The coefficient extension modulo `t^2`
gives

\[
\beta_{\rm ac}:H^1(K,V_L)\longrightarrow
H^2(K,V_L)\otimes(t)/(t^2).
\]

Up to the sign from the chosen inverse-character convention,

\[
\beta_{\rm ac}(y)=a_{\rm ac}\cup y.
\tag{9}
\]

Lam--Liu--Sharifi--Wake--Wang, Proposition 2.3.3, states this first
Bockstein/cup-product identity; their Theorem 2.2.4 identifies its
cokernel with `tB/t^2B`. Hence, when `dim(B/tB)=1`,

\[
\beta_{\rm ac}\ne0\ \Longleftrightarrow\ tB=0
\ \Longleftrightarrow\ B\simeq R/(t).
\tag{10}
\]

The first equivalence also follows by Nakayama from `tB/t^2B=0`.
As `a_ac` is minus and `H2` is plus, the map can be nonzero only on
the one-dimensional **minus relaxed** cohomology space. This space
is not the twist Selmer group, which is zero. A rank-zero twist Euler
class is a plausible way to supply a nonzero vector there, but its
cup-product value has not been computed here.

For an actual finite free two-term global complex

\[
C=[R^a\xrightarrow{D(t)}R^b],\quad D(t)=D_0+tD_1+\cdots,
\]

the test is concrete: choose a matrix `K0` whose columns span
`ker D0`. Then

\[
\operatorname{rank}\beta
=\operatorname{rank}[D_0\mid D_1K_0]-\operatorname{rank}D_0.
\tag{11}
\]

Thus a certified presentation through order `t^2`, together with the
one-dimensional `H2` identification, decides the dichotomy. Higher
Taylor coefficients are unnecessary for a nonzero first obstruction.

**The arithmetic certificate must include the global comparison.**
An arbitrary finite Galois quotient, a local cochain jet, or a matrix
with matching dimensions is not yet a model of `R Gamma(G_K,S,V_L)`.
Inflation/comparison and the local-condition maps must be justified.
Likewise a nonzero mod-`p` cohomology class might be integral torsion;
one must control saturation or work in a certified free lattice in
the rational target before using modular arithmetic as a nonzero
certificate. This note supplies a test interface, not that missing
global presentation.

`check_ambient_jet.py` computes (11), determinantal Smith valuations,
the index identity, and the reflected base vector for the two exact
models in `../derived_global/AMBIENT_CONTROL.md`. It also checks
invariance of the Bockstein rank under polynomial unimodular changes
of bases, and distinguishes the ambient Bockstein from the vanishing
first Bockstein of the ordinary Selmer complex. The models are not
asserted to be Galois representations or to satisfy full arithmetic
Poitou--Tate self-duality.

## 6. Why the height observations are consistent

The anticyclotomic fine height on a plus strict line is zero by
conjugation: the character is anti-invariant and both arguments are
invariant. This does **not** force `h>=2` in (2). The entire first
global Bockstein can be nonzero on the minus relaxed direction while
its restriction to the plus strict line is zero. This is exactly the
`h=1` alternative above.

The tempting converse to Wuthrich's fine-height theorem is invalid.
His Proposition 5.3 factors the height through fine invariants, fine
coinvariants, and then global `H1` coinvariants. Even if the first
invariants-to-coinvariants map is an isomorphism, the next map need
not be injective. In the proof of Theorem 6.1, printed p.15, the maps
`c` and `d` are treated separately; equation (7.3) describes `ker d`.
Nondegenerate height implies augmentation order equal to strict rank
**and** injectivity of the particular strict-to-ambient-obstruction
map. The order equality alone does not imply that injectivity.

For a minimal module example of the distinction, take `Y=R/(t)` and
a surjection `D=R+R/(t) -> Y` which reduces the free summand modulo
`t` and kills the torsion summand. Although `Y[t] -> Y/tY` is an
isomorphism, `D[t] -> Y[t]` is zero. Dualizing gives exactly the
failure of an inclusion to remain injective on coinvariants. This
example checks the logical obstruction, not an arithmetic realization.

The separately computed **cyclotomic** height of the pilot's strict
line concerns a different character and a different first Bockstein.
If its nondegeneracy and the fine-height identification are supplied,
Wuthrich's theorem gives order one for the fine characteristic factor
in that cyclotomic extension. It does not determine the order after
restriction to the anticyclotomic extension. Over `Q` it identifies a
transverse ambient cyclotomic norm line; exploiting it through a
derived cyclotomic Kato class would require that family's own global
division, specialization and reciprocity argument. No two-variable
comparison or identification with `x0` is asserted here.

## 7. Functional equations and the actual next target

A full scalar identity `c(kappa)=u kappa` with nonzero `u` is excluded:
apply the fixed Coleman map which vanishes on `c(kappa)` and is
nonzero on `kappa`. The two families are globally independent. This
does not exclude first-order agreement of their projective lines,
which is what the index in (6) detects.

Under the rank-two pilot assumptions of Section 4, so that
`S0=L kappa0`, the reflected base is strict exactly when

\[
c\kappa\equiv u\kappa\pmod {t^2M}
\quad\text{for some }u\in R^\times,\ u(0)=1.
\]

The theta functional equation controls regulator values and does not
by itself imply this stronger cohomological congruence. Replacing
`kappa` by `u(t) kappa` changes `x0` to
`u(0)x0+2u'(0)kappa0`, so the vanishing of its finite logarithm is
unchanged.

The next decisive arithmetic target for this specific construction is
therefore one of these equivalent pieces of information, under the
listed inputs:

* a nonzero value of `a_ac cup y_minus` in the one-dimensional global
  `H2` target;
* a certified first global Bockstein matrix of rank one;
* length one of the augmentation-localized fine/global `H2` module;
* first-order separation of `kappa` and its reflection in the actual
  global Iwasawa module.

A finite local logarithm jet would also prove the desired nonvanishing,
but the existing singular theta coefficient does not provide this
global invariant. No published theorem forcing the invariant to be
zero, or forcing it to be nonzero, has been identified in this review.

## Sources

* Castella--Hsieh, *On the nonvanishing of generalised Kato classes for
  elliptic curves of rank 2*, Forum of Mathematics, Sigma 10 (2022),
  e12: Corollary 3.7, Proposition 4.3, Lemma 4.4, Theorem 4.5,
  Sections 5.3--5.4.
  <https://web.math.ucsb.edu/~castella/Kato-print.pdf>
* Castella, *Nonvanishing of generalised Kato classes and Iwasawa main
  conjectures*, author version dated June 20, 2024: Theorems 4.1.1
  and 4.2.1, Assumption (A).
  <https://web.math.ucsb.edu/~castella/GKC-IMC.pdf>
* Wuthrich, *Iwasawa theory of the fine Selmer group*: Sections 2.1
  and 5.2, Proposition 5.3, Theorem 6.1, equations (7.3), (7.5), (7.6).
  <https://www.maths.nottingham.ac.uk/plp/pmzcw/download/fine.selmer.pdf>
* Lam--Liu--Sharifi--Wake--Wang, *Generalized Bockstein maps and Massey
  products*, Forum of Mathematics, Sigma 11 (2023), e5: Proposition
  2.3.3 and Theorem 2.2.4.
  <https://doi.org/10.1017/fms.2022.103>

The determinant, parity, and localization implications are proved in
this note from the explicit inputs. The cited authors are not being
credited with a claim that the new pilot obstruction has been computed.
