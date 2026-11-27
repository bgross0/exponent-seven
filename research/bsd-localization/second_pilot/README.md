# A second finite theta pilot: E433, K=Q(sqrt(-71)), p=5

Date: 2026-11-27.

## Result and scope

The selected second curve is

\[
 E_{433}:y^2+xy=x^3+1,
 \qquad [a_1,a_2,a_3,a_4,a_6]=[1,0,0,0,1].
\]

Its Cremona and LMFDB labels are `433a1` and `433.a1`. It is the
smallest distinct prime-conductor catalog-rank-two class after the
389 pilot, and it passes the exact ordinary/definite arithmetic screen
with the **same** `K=Q(sqrt(-71))` and `p=5`. Catalog rank is used only
to select a useful test case; the arithmetic implications below do not
use rational points or a known Mordell--Weil rank.

This directory supplies three completed pieces:

* An exact elementary eligibility and residual-image certificate.
* A rigorous rational interval proving `L(E433^(-71),1)>0`.
* Independent small algebraic checks on the separate finite CM/theta
  certificate in `../second_theta/`, together with the precise
  point-free interpretation through Gross's formula.

With that separate CM certificate and the stated classical theorems,
the data establish

\[
 L(E_{433},1)=0,
 \qquad L(E_{433}^{(-71)},1)>0,
 \qquad L(E_{433}/K,\chi,1)\ne0
\]

for every nontrivial class character `chi` of order seven, and the
primitive ordinary theta series has augmentation order two. This does
**not** assert nonzero localization of a reflected global class for
433, or a new BSD theorem. The full analytic-vector computation and
the full geometric comparison are separate requirements. The broader
program now uses the corrected BSV specialization in
`../general_criterion/BSV_REPAIR.md`; that comparison does not enter
these finite theta and central-value arguments.

## 1. Source provenance and selection

The curve coefficients were read from both the primary
[LMFDB curve page](https://www.lmfdb.org/EllipticCurve/Q/433/a/1)
and John Cremona's original `ecdata` repository. The saved complete
prefix contains **every** row of conductor at most 1000, without a
rank filter. Its 5,113 rows end at conductor 999; there is no row at
conductor 1000.

The source is pinned to:

```
repository: JohnCremona/ecdata
commit:     6fedd3ab463a70e52061ebc0b04832ad19fd2e01
file:       allcurves/allcurves.00000-09999
Git blob:   baab5801d7f81e1d5c44f5eb5acf4f1e100bc90b
```

The GitHub file metadata at the pinned commit returned that blob;
the full blob was then read and its complete conductor-at-most-1000
prefix saved in `sources/cremona-through-1000.txt`. The retrieval and
local SHA-256 are recorded in `sources/provenance.json`.

The exact screen of prime-conductor rank-two classes in that prefix is:

| Cremona curve | `a5` | `(-71/N)` | Definite/ordinary screen | Supersingular vertices | Genus of `X0(71N)` |
|---|---:|---:|---|---:|---:|
| 389a1 | -3 | -1 | Original pilot | 33 | 2339 |
| **433a1** | **-4** | **-1** | **Selected** | **36** | **2603** |
| 563a1 | -4 | -1 | Eligible, larger | 48 | 3383 |
| 571b1 | -2 | +1 | Conductor splits in K | 48 | 3431 |
| 643a1 | -2 | +1 | Conductor splits in K | 54 | 3863 |
| 709a1 | -3 | -1 | Eligible, larger | 59 | 4259 |
| 997b1 | -4 | +1 | Conductor splits in K | 83 | 5987 |
| 997c1 | -2 | +1 | Conductor splits in K | 83 | 5987 |

The distinction between labels matters: Cremona `571b1` is LMFDB
`571.a1`. The suggested conductors 571 and 643 cannot reuse the
present definite setup with `K=-71`.

At the common tame level, the exact index is `72*(N+1)` and the genus
is `6*N+5`: there are four cusps and no elliptic points, since 71 is
3 modulo four and 2 modulo three. Moving from 389 to 433 increases
the index by the factor `217/195`, about 11.3%. Squaring or cubing
that ratio gives dimension-based cost proxies, not wall-time
predictions. The finite CM class counts remain 7, 28, and 140 at
conductors 1, 5, and 25. All class-polynomial and CM-character data
depending only on `K` and the conductor are reusable.

## 2. Exact elementary eligibility

The invariant formulas give

\[
 c_4=1,\quad c_6=-865,\quad\Delta=-433,
 \qquad j=-1/433.
\]

The discriminant is a unit away from 433, and has valuation one
there. The model is minimal and has multiplicative type `I1` at
433, so its conductor is 433. The character test on `-c6` gives
split multiplicative reduction. The bad local root number and the
archimedean root number are both -1, giving global root number +1.
The nonintegral rational `j` also excludes complex multiplication.

Direct finite-field enumeration gives:

| q | 2 | 3 | 5 | 7 | 11 | 13 |
|---|---:|---:|---:|---:|---:|---:|
| `#E(Fq)` | 4 | 6 | 10 | 11 | 16 | 19 |
| `a_q` | -1 | -2 | -4 | -3 | -4 | -5 |

The ordinary condition at five is therefore satisfied. The reduced
quadratic forms of discriminant -71 number seven; `X²-X+18` has
roots 2 and 4 modulo five and no root modulo 433. Hence five splits,
433 is inert, `5` does not divide the class number, and
`gcd(5*433,71)=1`. The prime-five ideal has nonprincipal reduced
form `[4,-3,5]`, so its class has order seven. Every nontrivial
class character gives the required distinct CM refinements.

### The residual and five-adic image

Frobenius at three has polynomial `X²+2X+3`, whose discriminant is
2 modulo five. It has no root in `F5`. Multiplicative reduction with
discriminant valuation one supplies an inertia transvection through
Tate uniformization.

In a basis putting that transvection in standard upper-unitriangular
form, there are twenty possible Frobenius matrices with trace -2
and determinant 3. The checker enumerates every one and verifies
that it and the transvection generate all 480 elements of
`GL2(F5)`. Thus no simultaneous-basis assumption is hidden.

The standard closed-subgroup lifting theorem for primes at least
five gives `SL2(Z5)` inside the five-adic image. The precise
mathematical interpretation and primary references are the same as
in `../galois_image/README.md`, Sections 2--4. These are statements
about the actual representation, supported by the finite certificate
and those standard theorems; Python does not compute an infinite
Galois group.

## 3. The anomalous prime is allowed, but affects precision

Here `a5=-4=1 mod5`, so `#E(F5)=10` and the prime is anomalous.
This does not violate the hypotheses being used:

* Castella--Hsieh Theorem A and Sections 3--5 assume good ordinary
  reduction at `p>3`, irreducibility and the stated ramification,
  signs, and auxiliary nonvanishing. They impose no condition
  `a_p != 1 mod p`.
* Chida--Hsieh Theorem A requires the ordinary root to be a unit;
  it does not require that root minus one to be a unit.
* The Castella--Do rank-one application assumes big image and
  `p`-distinguishedness. The latter still holds: the residual ordinary
  inertia characters are the cyclotomic character and the trivial
  character, which are distinct at five.

The ordinary root of `X²+4X+5` satisfies

\[
 \alpha=16\pmod{25},\qquad \alpha=66\pmod{125},
 \qquad v_5(\alpha-1)=1.
\]

It is not exactly one: the polynomial takes value 10 at one.
The factors `1-alpha^-1` and `1-alpha/5` are nonzero, of valuations
1 and -1. The corresponding CH height prefactor has valuation -2.
Such quantities cannot be treated as integral units.

In the existing elliptic de Rham convention the new relation is
`F²+4F+5=0`. Direct exact reduction gives

\[
 A_0=(1-F^{-1})(1-F/5)^{-1}=\frac{38+7F}{25},
 \quad\det A_0=1,
\]

\[
 A_0^{-1}=\frac{10-7F}{25},\qquad
 \zeta_{433}=\frac{10-7F}{25}\omega_E.
\]

The denominator in this displayed operator costs one more five-adic
digit than the analogous 389 formula. This is an operator observation,
not a complete precision budget for a future basis conversion or
geometric projection. The 389 Frobenius polynomial, base line, and
unit assumptions must not be reused unchanged.

The auxiliary factor `1-alpha^-1*chi(p)` is still a unit: `alpha`
reduces to one, while a nontrivial order-seven value stays distinct
from one modulo five in the unramified degree-six coefficient field.

## 4. Rigorous nonvanishing of the quadratic twist

A minimal integral model of the -71 twist is

\[
 y^2+xy=x^3-18x^2-357911.
\]

Its invariants are the original invariants multiplied by
`D²,D³,D⁶`, respectively, where `D=-71`. Its conductor is

\[
                  433\cdot71^2=2182753.
\]

The root number is +1 because `w(E)=+1` and `chi_-71(-433)=+1`.
The program `check_twist_lvalue.py` obtains the Fourier coefficients
from exact finite-field counts and Euler recurrences, then evaluates
the central Mellin/Fricke identity

\[
 L(E^{(-71)},1)=2\sum_{n\ge1}\frac{a_n(E^{(-71)})}{n}
                 \exp\!\left(-\frac{2\pi n}{\sqrt{2182753}}\right).
\]

Every enclosure uses rational arithmetic. Machin's identity bounds
pi; integer squares bound the square root; an alternating Taylor
series bounds the exponential; fixed-point multiplication rounds
outward. The coefficient bound `|a_n|<=2n` bounds the omitted tail
after 6000 terms by `4*r^6001/(1-r)`.

The resulting certified interval is

\[
\begin{split}
1.1502294196396946581943689605252904429375
 &< L(E_{433}^{(-71)},1)\\
 &<1.1502294351856175010472606527965917550173.
\end{split}
\]

The file `twist-lvalue.json` records all prime traces, all coefficients,
the exact interval endpoints, tail bound, and coefficient digest.
This argument assumes modularity and the standard Mellin/Fricke and
Hasse bounds; it uses neither rational points nor an analytic-rank
lookup. It is not a Lean proof of the analytic identity.

## 5. Exact central vanishing and auxiliary nonvanishing without points

The separate `second_theta/certificate.json` records the primitive
Brandt eigenfunction and a certified CM cycle. Its `T2=-1`
eigenspace has dimension one, independently checked here over the
rationals. Since the modular form of `E433` has `a2=-1`, modularity
and Jacquet--Langlands identify this eigenline with the needed
elliptic constituent.

At conductor one its seven CM values, in the certified cycle order,
are

\[
                    (1,1,-1,0,0,0,-1).
\]

There are no supersingular `j=0` or `j=1728` vertices in
characteristic 433, so all automorphism weights are one. The
outgoing function convention therefore gives these unweighted
period coefficients directly. Gross's exact formula applies also
to the trivial class character. The sum of the seven coefficients
is zero, so it gives

\[
 L(E_{433}/K,1)=L(E_{433},1)L(E_{433}^{(-71)},1)=0.
\]

The strictly positive twist interval proves

\[
                         L(E_{433},1)=0
\]

exactly. This replaces a rational-point or modular-symbol argument
for the base central zero.

For a nontrivial order-seven character the period polynomial is

\[
 P(X)=1+X-X^2-X^6.
\]

At a primitive seventh root it satisfies

\[
 P(\zeta_7)=-\zeta_7^{-1}(\zeta_7-1)^2(\zeta_7+1),
 \qquad N_{\mathbf Q(\zeta_7)/\mathbf Q}P(\zeta_7)=49.
\]

The independent checker computes the norm as the determinant of
the six-dimensional multiplication matrix modulo `Phi7`. Every
nontrivial order-seven period is nonzero, and its five-adic value is
a unit. Gross's formula then gives the auxiliary central
nonvanishing for every nontrivial order-seven class character,
including the chosen `chi=psi²`.

The primary source for both character cases is Liu--Masri--Young,
Section 2, equations (2.1)--(2.2), quoting Gross Proposition 11.2.
Their printed page 6 also explicitly states the trivial-character
factorization. Their analytic center `1/2` corresponds to the
arithmetic elliptic center `1` used here.

## 6. What the new finite theta calculation establishes

At conductor 25, all 140 classes are retained. The separate CM
certificate gives the grouped coefficients

\[
                    (b_0,b_1,b_2,b_3,b_4)=(0,1,-2,1,0).
\]

Consequently

\[
 G(\gamma)=\gamma-2\gamma^2+\gamma^3
            =\gamma(\gamma-1)^2,
 \qquad G(1+T)=T^2+T^3.
\]

The independent checker reconstructs these coefficients from the
root reductions, eigenfunction, and the saved order-140 generator
cycle. Verification that these are the complete actual CM roots and
horizontal graph belongs to `second_theta`'s separate certificate
verifier; this small checker does not claim to replace it.

Ordinary regularization changes the upper-level term by
`alpha^-2`, a unit congruent to one modulo five. Its lower-level
term, after projection to the order-five quotient, is a scalar
multiple of

\[
 1+\gamma+\cdots+\gamma^4
       \equiv T^4\pmod5.
\]

It cannot affect the quadratic residue. The quotient relation
`(1+T)^5-1` is in `(5,T^5)`, so the finite calculation determines
the infinite theta coefficient modulo five through degree four.
Thus its quadratic coefficient is a unit, with residue one for the
displayed summed projection and primitive sign.

The exact lower zeros are separate mathematical steps. The
interpolation formula and `L(E433/K,1)=0` give `Theta(0)=0`.
Chida--Hsieh's functional equation has sign
`epsilon_5(f)*epsilon(f)=+1` and `N+=1`, so it is inversion
invariant in the distinguished normalization. Comparing the linear
terms under `T -> (1+T)^-1-1` gives `c1=-c1`, hence `c1=0`.
A translated normalization has a group-like factor with constant
term one and gives the same conclusion because `c0=0`.

Therefore the finite certificate plus these published theta
identities establish

\[
                   \operatorname{ord}_T\Theta_{E_{433}/K,5}=2.
\]

This conclusion does not invoke the positive-rank hypothesis of
Castella--Hsieh Theorem B. Applying that theorem to obtain its
particular Kato-class conclusion would be a different step with
its own hypotheses.

## 7. Reproduction and the next computation

The machine-readable curve configuration is `candidate.json`.
From `research/bsd-localization`, run:

```sh
python second_pilot/screen.py --check
python second_pilot/check_twist_lvalue.py --check second_pilot/twist-lvalue.json
python second_pilot/check_toric_consequences.py --check
```

The final command consumes the separate `second_theta/certificate.json`.
All three commands passed. The root/graph and rigorous class-polynomial
replay commands belong to that directory's own documentation.

The next substantial computation would use level `71*433=30743`
and `F²+4F+5` to determine the full proper quadratic de Rham vector,
with the additional denominator precision identified above. Before
spending that geometry budget, the normalized-moment compatibility
gate from the ongoing source audit should be resolved or kept as an
explicit conditional premise. The central-value and finite theta
work here is complete independently of that gate.

## Primary references

* [Cremona ecdata, pinned file](https://github.com/JohnCremona/ecdata/blob/6fedd3ab463a70e52061ebc0b04832ad19fd2e01/allcurves/allcurves.00000-09999)
  and [database description](https://johncremona.github.io/ecdata/).
* [LMFDB 433.a1](https://www.lmfdb.org/EllipticCurve/Q/433/a/1),
  used for curve identity and candidate selection, not a proof through
  its listed generators or BSD invariants.
* Liu--Masri--Young, *Rankin--Selberg L-functions and the reduction of
  CM elliptic curves*, [author PDF](https://sites.math.rutgers.edu/~mpy4/ReductionFinalVersion.pdf),
  Section 2, especially (2.1)--(2.2), and the trivial-character
  factorization on printed page 6.
* Chida--Hsieh, *Special values of anticyclotomic L-functions for
  modular forms*, [author PDF](https://www.math.ntu.edu.tw/~mlhsieh/research/central.pdf),
  Theorems A and B; Definition 4.1 and Lemma 4.2 for ordinary
  regularization and level compatibility.
* Castella--Hsieh, *On the nonvanishing of generalised Kato classes
  for elliptic curves of rank 2*, [author PDF](https://web.math.ucsb.edu/~castella/Kato-print.pdf),
  Theorem A; Sections 3--5, including the nonzero rational local
  factors in Theorem 4.5.
* Castella--Do, *Diagonal cycles and anticyclotomic Iwasawa theory
  of modular forms*, [author PDF](https://kimtuando.github.io/website/Schoen_CM.pdf),
  Notation 3.3.2, Theorem 3.3.3, and the hypotheses and proof of
  Theorem 5.6.1.
