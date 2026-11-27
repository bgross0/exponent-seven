# A second exact theta certificate: E433 over Q(sqrt(-71))

For

\[
E=433.a1:\quad y^2+xy=x^3+1,\qquad
K=\mathbf Q(\sqrt{-71}),\qquad p=5,
\]

the finite CM computation gives

\[
(b_0,b_1,b_2,b_3,b_4)=(0,1,-2,1,0),
\qquad
G(\gamma)=\gamma-2\gamma^2+\gamma^3
          =\gamma(\gamma-1)^2.
\]

Thus, with `gamma=1+T`,

\[
                         G(1+T)=T^2+T^3.
\]

The accompanying arithmetic argument identifies this witness with the
ordinary anticyclotomic theta series and establishes

\[
              \boxed{\Theta_{E/K,5}=T^2U(T),\quad U(0)\in\mathbf Z_5^\times.}
\]

This is a second concrete application of the published theta construction.
The exact finite witness and the written arithmetic interpretation have
different verification scopes, set out below. In particular, this result
does not depend on the projected weight-two specialization used in the
E389 localization argument.

## 1. What was computed

We work in the quadratic field `F_433[u]/(u^2-5)`. The Deuring polynomial
has 216 distinct roots, giving the complete set of 36 supersingular
`j`-invariants. The modular polynomial `Phi_2` gives an outgoing Brandt
matrix `B2`. Its eigenvalue `-1=a_2(E)` has a one-dimensional rational
eigenspace: `rank(B2+I)=35`, certified by reduction modulo 101 together
with the displayed exact kernel vector. The primitive integer eigenfunction
is unique up to sign. Since `433=1 mod12`, neither exceptional
automorphism weight occurs; all vertex weights are one.

The class polynomials for discriminants `-71` and `-44375=-71*25^2`
are reconstructed with rigorous FLINT/Arb complex balls at 16,384-bit
working precision. Every coefficient is uniquely isolated as an integer.
The generator uses a product-from-roots routine; the verifier multiplies
the linear factors successively. Both use the same underlying FLINT/Arb
implementation, so this is an independent computation path, not an
independent implementation of complex ball arithmetic.

The saved root approximations then certify all 7 and 140 roots in the
unramified quadratic extension of `Q_433`. For each approximation `a`,
the verifier checks

\[
h=v_{433}(H(a))>2s=2v_{433}(H'(a)),\qquad h-s\ge4.
\]

The strong Hensel lemma gives a root in each stated residue ball modulo
`433^4`; these balls are pairwise disjoint and their number is the degree
of `H`. This handles the collisions in the reduction of `H_-44375`, where
the maximum derivative valuation is seven.

For each root, exactly two root balls can satisfy the degree-two modular
polynomial. Complex multiplication theory supplies two horizontal
norm-two isogenies at these conductors, because 2 splits in `K` and is
coprime to the conductor. The two candidates therefore exhaust the actual
horizontal neighbors. They are distinct: the norm-two ideal is nonprincipal
in the class group of discriminant `-71`, of order seven, so its lifts
at conductor 25 also have order divisible by seven. Both graphs are
single cycles. The norm-two ideal
class generates the cyclic groups of orders 7 and 140; reduction of the
140-cycle index modulo five is the anticyclotomic quotient of order five.

The reduction of every CM root is a listed supersingular vertex. Evaluating
the primitive eigenfunction and summing in the five quotient fibers yields
the displayed vector. A different initial CM point, inverse generator,
or primitive eigenfunction sign changes the expected choices of group
coordinate and unit normalization. Exact order two and a unit leading
coefficient are invariant under these choices.

## 2. How the finite witness gives the infinite theta order

The arithmetic details, source hypotheses, and independent checks are in
[the second-pilot audit](../second_pilot/README.md). Three separate steps
are required.

**Exact constant term.** At conductor one the CM values, in the saved
norm-two cycle order, are

\[
                         [1,1,-1,0,0,0,-1].
\]

Their sum is exactly zero. Gross's special-value formula then gives
`L(E/K,1)=0`. The independently certified positive interval for
`L(E^(-71),1)` in `second_pilot/twist-lvalue.json`, together with the
quadratic base-change factorization, gives `L(E,1)=0`. No rational point
or database rank is used in this argument. The theta interpolation
formula gives exact vanishing of its constant term.

**Exact linear term.** The theta functional equation has sign `+1` in
this setup. Its involution is `T -> (1+T)^(-1)-1=-T+O(T^2)`.
Once the constant term is zero, the linear coefficient equals its
negative, so it is zero in characteristic zero. This is an argument
about the infinite theta series. Exact zeros in the displayed finite
polynomial, by themselves, would not prove infinite exact vanishing.

**Unit quadratic term.** The ordinary regularization of the conductor-25
element differs from `alpha^(-2) G` by a scalar multiple of the norm
element

\[
             1+\gamma+\gamma^2+\gamma^3+\gamma^4
                        \equiv T^4\pmod5.
\]

It therefore contributes nothing in degree two modulo five. The unit
root of `X^2+4X+5` satisfies `alpha=1 mod5`, so the surviving quadratic
coefficient is a unit. Finally

\[
                  (1+T)^5-1\in(5,T^5)
\]

shows that the order-five quotient preserves coefficients modulo five
through degree four. The quadratic unit is consequently a property of
the infinite theta series.

The conductor-one auxiliary polynomial is

\[
P(X)=1+X-X^2-X^6.
\]

For a primitive seventh root `zeta`,

\[
P(\zeta)=-\zeta^{-1}(\zeta-1)^2(\zeta+1),
\qquad N_{\mathbf Q(\zeta)/\mathbf Q}P(\zeta)=49.
\]

The independent consequences checker verifies this norm by the determinant
of multiplication in `Z[X]/Phi_7`. Thus every nontrivial order-seven
toric period is nonzero and is a five-adic unit.

## 3. Files and reproduction

| File | Purpose |
|---|---|
| `compute_theta.py` | Discovers the finite-field eigenfunction and CM root/cycle witnesses |
| `certificate.json` | Complete saved finite certificate, including all root lifts, adjacency rows and CM values |
| `verify_theta.py` | Reconstructs the class polynomials and independently verifies the certificate without importing the generator |
| `verification.json` | Deterministic successful verification receipt |
| `test_rejection.py`, `rejection.json` | Eleven targeted corruptions rejected at the certificate trust boundary |
| `../second_pilot/check_toric_consequences.py` | Independently checks the eigenline, moments and cyclotomic norm |

From `research/bsd-localization`:

```sh
python -m pip install -r requirements.txt
python second_theta/verify_theta.py --check second_theta/verification.json
python second_theta/test_rejection.py --check second_theta/rejection.json
python second_pilot/check_toric_consequences.py --check
```

To rediscover the witness in a separate file:

```sh
python second_theta/compute_theta.py --output /tmp/e433-theta-certificate.json
python second_theta/verify_theta.py --certificate /tmp/e433-theta-certificate.json
```

The discovery run took 1.29 seconds in the available Python 3.12.14
environment with `python-flint==0.9.0` and `sympy==1.14.0`.
This is one observed local timing, not a scaling estimate or a measure
of the much larger two-coordinate CM projection.

Certificate SHA-256:

```text
5e533e6f0ea31a2c59293448a5f2f8077de512b9e3c50e7420f6eafd2a699898
```

The canonical JSON coefficient hashes reconstructed by the verifier are:

```text
H_-71:    69e90f79dbe3718af1ff052322e14631d03cffe5ff2bc52b4e62f0b151ade1e5
H_-44375: 5881a397aa9161a92629db2f92e00711c2f8152fad0871828dd5e958decb46c6
```

## 4. Scope of the new milestone

The executable checks certify finite arithmetic and rigorous class-polynomial
reconstruction. The link to the modular form, CM class action, ordinary
theta series and its functional equation uses the published theorems
identified in the second-pilot audit. This branch adds no new Lean
theorems and makes no claim of a second completed localization computation.

The prime five is anomalous for this curve: `a_5=-4=1 mod5`. It is still
good ordinary, and the theta construction applies. However, denominators
in the regulator comparison differ from the E389 case. A second
two-coordinate projection must use a new precision budget before it can
test the nonzero-localization criterion. The primitive direction of the
base regulator line is proportional to `(10-7F) omega`, with
`F^2+4F+5=0`; the complete normalized annihilator is
`(10-7F) omega/25`. This is a target for the next computation, not its result.

## Primary sources

- [LMFDB, 433.a1](https://www.lmfdb.org/EllipticCurve/Q/433/a/1), used to
  identify the candidate; exact arithmetic is recomputed in `second_pilot`.
- [Gross, *Heights and the Special Values of L-series*, Proposition 11.2](https://wstein.org/papers/bib/Gross-Heights_and_the_Special_Values_of_L-series.pdf),
  for the toric special-value formula, with the trivial-character
  applicability detailed in the arithmetic audit.
- [Chida--Hsieh, *Special Values of Anticyclotomic L-functions for Modular Forms*](https://www.math.ntu.edu.tw/~mlhsieh/research/central.pdf),
  Theorems A and B and Section 4.1, for interpolation, functional equation
  and the ordinary regularization.
- [Castella--Hsieh, *On the nonvanishing of generalised Kato classes for elliptic curves of rank 2*](https://web.math.ucsb.edu/~castella/Kato-print.pdf),
  for the separate Selmer-theoretic application. The theta computation
  alone does not identify a Selmer class with a rational point.
