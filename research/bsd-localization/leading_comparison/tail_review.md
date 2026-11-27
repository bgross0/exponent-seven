# Independent review of the CM tail argument

Date: 2026-11-27. Reviewed `../cm_tail_bound/README.md`, Sections1--6.

**Verdict.** The stated conditional tail inequality is valid in the
specified saturated integral Katz and pole-reduction models. I found no
counterexample or extra loss in the norm, logarithm, tame-map, or trace
steps. The conclusion remains conditional on the precise fixed-weight
Coleman-family realization (CF). Finite q-expansions do not establish
that premise. The final elliptic-vector precision additionally depends
on the actual backend lattice and normalization comparisons.

## 1. Hypotheses used in this review

The fixed-weight forms must have a convergent Katz expansion in the
integral complements stated in the note, with the full q-expansions
integral. The three coefficients of

    F(w)=E4^(-s/4)h_s,       W=25w=6^s-1,

must exist on a common positive-radius strict ordinary neighborhood and
satisfy the infinite equation

    U5(K(w)F(w))=alpha(w)F(w),      K=G^(s/4), G=E4/V5(E4).

Here alpha has integral coefficients through degree2 and unit constant
term. These are the contents of (CF), rather than consequences of the
finite archive. The quoted radius-improvement theorem is applied to
genuine Banach-space elements, with input radius valuation less than1/6.

The relevant published input is Lauder, *Computations with classical and
p-adic modular forms*, Sections2.1--2.3, especially (2.2) and (2.3):

https://people.maths.ox.ac.uk/lauder/papers/LMSLauderMFJune10.pdf

Its definition of the classical integral lattice uses the q-expansion at
infinity, and its Katz complements are integral direct summands. This is
the required meaning of an integral complement here. The review below
deduces the new estimates from those inputs; it does not attribute the
minimum argument or the numerical cutoff to Lauder.

## 2. Integrality and the minimum argument

For a convergent Katz expansion f=sum c_i/E4^i at a positive radius,
v(c_i) tends to infinity. Choose a finite head after which all c_i are
integral. The tail is q-integral since E4 has constant1, so the head is
q-integral too. Multiplying it by E4^n produces a classical integral
form. Its iterated direct-sum decomposition then makes every head c_i
integral. The argument works coefficient by coefficient for the
three-term jet ring. It does not assert an integral radius norm.

At a radius r where F exists and K is an integral multiplier, set

    m=min_(i,j) {v(c_(i,j))-ri}.

The minimum is attained: there are finitely many jets and their normalized
Katz coefficients tend to zero. The high-row estimate for U, followed by
the integral triangular operator alpha^(-1), gives

    v(c_(i,j))-ri >= m+4ri-1.

At a minimizing index this forces i<=floor(1/(4r)). Its unscaled numerator
is integral, hence m>=-r*floor(1/(4r)). Applying the radius-improvement
estimate a second time gives m_(5r)>=m_r-1. No simple-eigenvalue,
finite-matrix isolation, or a priori integral Banach norm is needed.

## 3. Radius bootstrap and multiplier

One can bootstrap the whole jet at once. Start at any common radius
r0>0 supplied by (CF), shrinking below1/6. The three coefficients of K
exist at every r<1/6, whether or not their norms are integral. Thus

    F=alpha^(-1) U5(KF)

extends all three coefficients from r to5r simultaneously. The new forms
agree with the old ones on the overlap by q-expansion injectivity. Iterate,
restrict to input radius4/25 when it has been reached, and apply U once
more. This avoids any assumption that a varying-weight derivative is by
itself a fixed-weight form; precisely F in (CF) is being extended.

The estimate for logG checks. Unscaled coefficients of G-1 have valuation
at least1 by its full q-expansion. The 1-unit assertion at every r<1/6
also gives valuation at least i/6 for pole index i. Consequently

    m_r(G-1)>=1-6r.

At r=4/25 this is1/25, and the logarithm terms have lower bounds
5^a/25-a; their minimum is-1, attained at a=2. The first two coefficients
of s/4 have valuations1 and3 after W=25w. Therefore the three coefficients
of K are integral, including the quadratic term involving (logG)^2/2.
Only this truncated claim is used. General binomial series with a
nonconstant integral exponent need not have all their coefficients
integral; there is no such all-degree inference here.

These facts establish

    m_(4/25)(F)>=-4/25,       m_(4/5)(F)>=-29/25.

## 4. Product, tame oldform map, and trace

The Katz integral lattices are multiplicative. Indeed, a product of two
integral classical numerators can be decomposed into integral Katz
summands at poles at most the sum of their original poles. Passing to a
lower pole introduces an additional nonnegative power of the radius
element and cannot worsen the norm.

At rho=4/5 write R=V389(E4)/E4. The classical numerator V389(E4)-E4 is
divisible by5, so m_rho(R-1)>=1-rho=1/5. Thus R and R^(-1) are integral
units, and logR has norm valuation at least0. The truncated multipliers
R^(s/4) and its inverse are integral. Raw V389 preserves classical
q-integrality and replaces E4^i by E4^i R^i. It is therefore norm
nonincreasing on these lattices. Reflection sends w to -w+25w^2 modulo
w^3, which also preserves the jet norm. The two product factors thus
give the bound -58/25 claimed in the note.

Forgetting the tame level71 subgroup commutes with the level-one E4
section. Its geometric trace takes integral classical numerators to
integral numerators, so it preserves this bound. In terms of geometric
lattices, q-integrality gives integrality by the q-expansion principle on
the connected smooth tame modular models at5. This geometric trace
statement is the needed fact; a generic linear operation on a chosen
finite q-expansion basis would not suffice. The separate tame Fricke
calculation identifies this trace as Q+U71(Q) and introduces no division
by5. Averaging coefficient conjugates divides by2, also a unit.

## 5. The cutoff and its limits

Returning from w to W loses2j digits in jet j. The coefficients lie in
the original unramified field, even if the radius element was temporarily
adjoined. Hence their valuations are integers and ceiling is legitimate:

    a_(i,j)=max(0,ceil((20i-58)/25)-2j).

The extra zero bound again comes from full q-integrality and the first
argument in this review. Combining it with the supplied saturated
pole-reduction loss floor(log_5(i-1)) is valid termwise; the bounds tend
to infinity, so the reduced infinite tail converges.

For the quadratic coefficient and cutoff17, the first discarded pole is
i=18. Its numerator valuation is at least9 and its reduction loses at
most1, leaving8 digits. The following logarithmic breakpoint i=26 has a
strictly larger bound, as do subsequent complete blocks. The other
tabulated cutoffs satisfy the same calculation.

This proves eight tail digits in the stated model under (CF). It does
not prove eight digits in a backend's arbitrary coordinates, certify the
backend's finite fit, or identify the resulting vector with an arithmetic
Perrin--Riou regulator. Those are distinct remaining obligations.
