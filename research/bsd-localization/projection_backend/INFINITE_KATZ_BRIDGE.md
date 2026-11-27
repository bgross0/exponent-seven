# A bounded infinite dual from the actual finite Katz certificate

This note states the analytic comparison precisely. The finite checks are
in `actual-katz-replay.json` and `actual-cm-finite-projection.json`; the
CM input estimate is in `../cm_tail_bound/README.md`. The argument below
does not assume that a finite eigenvector extends to a bounded infinite
functional. It constructs that extension from explicit operator blocks.

The geometric provenance premise is stated in Section1. The final section
separates the source-based justification of that premise from the narrower
artifact-only verifier. Arithmetic regulator and global-class comparisons
remain separate from this analytic calculation.

## 1. Geometric model and the premise to identify

Let O be the unramified coefficient ring, and choose saturated integral
Katz complements in weight2 and tame level389:

    M_(2+4i)(O) = E4*M_(2+4(i-1))(O) direct_sum W_i.

Each W_i may have many basis elements. The index i below always denotes
the pole level, not the ordinal number of an individual row. Choose an
integral basis w_(i,t) of each W_i and put

    e_(i,t) = 5^floor(i/6) * w_(i,t)/E4^i.

Let L be the c0 coefficient lattice in this basis: its elements have
integral coefficients tending to zero. Its scalar extension is a Banach
space. The head H consists of i<=10 and has dimension1333; T is its tail.

**Head provenance premise.** The saved E is the q-expansion modulo5^8 of
a basis obtained from these head elements by a matrix in GL_1333(Z5).
Its entries through q6829 have the saved residues. This premise includes
the modular-form identity of the selected products and the saturated
complement ranks. It is stronger than merely recognizing a rectangular
matrix of q-coefficients.

The head change acts only within H. It preserves coordinate minima and
all head/tail block bounds below. The tail remains the original scaled
Katz basis. The coefficient evaluation minor in the actual certificate
has inverse norm5, because its verified guard is1.

We use the published Katz-radius estimate already specified in the tail
note:

    5 U5 M_k(O,r) subset M_k(O,5r),       0<r<1/6.

The ordinary and critical classical stabilizations f_alpha,f_beta are
nonzero overconvergent eigenforms, with eigenvalue valuations h=0,1.
Their positive-radius existence and exact U equations suffice to put
them in the present Banach space: applying lambda^-1 U repeatedly extends
the radius, and one can pass beyond1/6. Multiplication by lambda^-1
changes a finite norm constant but does not obstruct this continuation.

## 2. Uniform output-column bounds

The radius-r norm valuation of an input e_(i,t) is

    floor(i/6)-ri >= -5/6.

If c_j is an unscaled pole-j numerator in its U image, the radius estimate
gives v(c_j)>=5rj-11/6. Let r increase to1/6 and use integral valuations.
After dividing the output by5^floor(j/6), every output-pole-j matrix
column has valuation at least

    g(j) = ceil((5j-11)/6)-floor(j/6).

Writing j=6k+s with0<=s<6 makes this explicit:

    g(j)=4k+(-1,-1,0,1,2,3)[s].

In particular g(j)>=7 for j>=11, and g(j) tends to infinity. This also
justifies the required convergence of infinite sums. The limiting argument
is coefficientwise; it does not assume that the radius theorem is stated
at its excluded endpoint.

There is a separate useful bound for tail input and head output. The full
q-expansion of U(e_(i,t))/5^floor(i/6) is integral. The saturated Katz
integrality lemma in the tail note implies that every unscaled numerator
of this form is integral. Therefore its output coordinate at pole j has
valuation at least

    floor(i/6)-floor(j/6).

For i>=11 and j<=10 this is nonnegative. With row coefficient convention
x -> x U, write the infinite operator as

    U = [[A, B],
         [C, D]].

Thus B maps head input to tail output, and C maps tail input to head
output. The established estimates are

    B in5^7,       D in5^7,       C integral.             (1)

They remain true after the GL(Z5) head change. The finite matrix will
identify A to the stated precision below. In fact the entire scaled U
matrix is integral already: g(j)>=0 for j>=2, while at j=0,1 the separate
q-integrality bound is at least floor(i/6)>=0. Thus no integrality of an
unknown head block is assumed while comparing it with finite residues.

## 3. Identifying the head matrix and constructing the infinite dual

Every tail basis row has q-expansion divisible by5. By(1), the omitted
tail of U applied to a head basis element has q-expansion divisible by5^8.
The exact finite fit modulo5^8 and the evaluation-minor guard1 therefore
give

    A = A_fit + O(5^7).                                  (2)

Here A_fit is the integral lift in the matrix sidecar. Thus A reduces to
the released six-digit matrix. This use of the
full residual and inverse minor is necessary: a few pivot coefficients
alone would not identify the matrix.

For lambda=alpha or beta, let h=v(lambda), equal to0 or1. Since D is
divisible by5^7, the Neumann inverse

    (lambda I-D)^(-1)

exists on the tail and its continuous dual, with norm at most5^h. The
finite Schur matrix is

    S_lambda = A+B(lambda I-D)^(-1)C.

Its correction to A has valuation at least7-h, hence

    S_lambda = A_saved mod5^6.                           (3)

The exact classical left eigenvector supplies a nonzero left kernel of
S_lambda-lambda I. Its head cannot vanish, since otherwise the tail would
be a lambda-eigenvector of D, contrary to v(D)>=7>h. The measured finite
complementary-minor guards are c_alpha=1 and c_beta=2. The inverse-minor
lemma, applied using(3), proves that the exact head right kernel is one
dimensional. Its vector u, normalized by the saved coordinate u_j=1,
is integral and satisfies

    u_alpha = uhat_alpha mod5^5,
    u_beta  = uhat_beta  mod5^4.                          (4)

Define its tail by

    v=(lambda I-D)^(-1) C u.

This yields an actual right eigenfunctional w=(u,v) for the infinite row
operator. Its tail is bounded, with valuation at least-h. A bounded tail
column pairs continuously with c0 input coordinates, so the pairing is
well-defined. We have proved, rather than assumed,

    v(w_alpha)>=0,             v(w_beta)>=-1.            (5)

The finite normalization pairings below are nonzero to certified
precision. Thus the corresponding exact classical eigenline also pairs
nontrivially with w. This excludes a Jordan-chain obstruction to the
normalized rank-one coefficient functional. Uniqueness and this nonzero
pairing identify it with the actual lambda-spectral coefficient on the
Banach space. Its de Rham interpretation additionally uses the specified
U-equivariant proper cohomology map and the nonzero stabilization classes
in `../de_rham_strategy/README.md`; it does not follow from the Banach
eigenline alone.

## 4. The actual CM input is fitted after applying U

Let Q be the actual traced cubic-average W^2 coefficient of the undepleted
product. The tail note proves, for its unscaled pole-i numerator,

    a_i=max(0,ceil((20i-58)/25)-4).

Its scaled Katz coordinate valuation is at least

    t_i=a_i-floor(i/6).

The global minimum is-1, attained at i=6,7; the minimum for i>=11 is2.
These are infinite-range statements: after the linear branch begins,
t_(i+30)=t_i+19, so a single finite block verifies the asserted minima.
In particular Q lies in5^-1 L and its tail lies in5^2 L_T.

The program fits Y=UQ, not Q. By(1), the actual tail of Y has coordinate
valuation at least6. Its q-expansion is therefore divisible by5^7.
The saved input has more than eight coefficient digits; the full finite
fit and its evaluation guard1 give

    Y_H = Yhat mod5^6.                                  (6)

The actual fitted head columns have coordinate valuation0. Thus their
true head lifts are integral as well. Pairing the tail directly with(5)
costs at most h and gives a numerator-tail error of valuation at least6-h.

## 5. Normalization precision is also controlled

Put R_lambda=U f_lambda, and let rhat be its fitted integral head row.
The exact left eigen-equation gives

    R_T=R_H B(lambda I-D)^(-1).

Write nu=v(R_H). Then v(R_T)>=nu+7-h, and its q-tail is divisible to
valuation at least nu+8-h. The finite evaluation minor implies

    v(R_H-rhat)>=min(7,nu+7-h).                          (7)

If nu<0, the left side equals nu because rhat is integral, whereas the
right side is strictly larger. Hence nu>=0. Equation(7) then identifies
the observed head valuations rho_alpha=0,rho_beta=1, since its error is
at least6. Substituting these improved valuations gives

    R_T in5^7 L_T,              R_H=rhat mod5^7.         (8)

This argument avoids assuming an integral norm for a classical critical
stabilization merely from its integral q-expansion.

Let N=Y w, D_lambda=R_lambda w. From(4),(6),(8), the exact numerator and
denominator precisions are at least

    a=min(6, K+eta, 6-h),
    b=min(7, K+rho, 7-h),

where K is5 or4 and the observed input-head valuation eta is0. The
resulting table is:

| Direction | h | K | rho | numerator a | denominator b | v(D_lambda) |
|---|---:|---:|---:|---:|---:|---:|
| alpha | 0 | 5 | 0 | 5 | 5 | 1 |
| beta | 1 | 4 | 1 | 4 | 5 | 2 |

These are exactly the precisions used in the finite certificate. The
denominator valuations are certified, because b exceeds each valuation.
For the quadratic input the numerator valuations are0 and1 in the cubic
field. The quotient formula

    min(a-v(D), b+v(N)-2v(D))

therefore gives three absolute digits on the undepleted alpha coefficient
and two on the undepleted beta coefficient. The fixed Euler transfer
preserves the former and costs one digit on the latter. Under the stated
geometric provenance, the existing depleted output balls survive intact:

    a2=(418+150xi+83xi^2)/5  + O(5^3),
    b2=(14+27xi+124xi^2)/25 + O(5).

In particular v(a2)=-1 and v(b2)=-2. Their ratio satisfies

    5*b2/a2 = 109+75xi+106xi^2 mod125.

The independent cubic checker proves this precision is sharp from these
balls: replacing b2 by b2+5 remains admissible and changes the scaled
ratio at valuation3. The analytic comparison does not supply a fourth
digit for that ratio. Lower-jet zero balls likewise remain zero balls;
exact lower-order vanishing must come from its separate analytic theorem.

## 6. What discharges the head provenance premise?

The pinned Sage10.10 source used in the successful run is
[`src/sage/modular/overconvergent/hecke_series.py` at tag10.10](https://github.com/sagemath/sage/blob/10.10/src/sage/modular/overconvergent/hecke_series.py).
Its SHA256, independently matched to the actual capsule's runtime-source
metadata, is

    6292ef3c2e20c2456058fdac25ecb1576e9abdace4c47a3aae13b1469f58703a

The inspected local copy is byte-identical to this runtime source. An
extra trailing newline introduced when saving the download was removed
before making that comparison. The pinned source supplies a source-based
mathematical justification of the algorithmic invariant:

1. `complementary_spaces_modp` builds products of the proven low-weight
   forms. Each product has the required classical weight. The loop accepts
   a product only after its q-expansion increases rank modulo5.
2. The complete classical dimension is reached at each weight. The saved
   q-depth exceeds every required Sturm bound. Since E4=1 modulo5 as a
   q-series, the prior rows represent multiplication of the prior spaces
   by the required E4 powers. The q-expansion principle and Nakayama's
   lemma therefore give saturated integral complements W_i.
3. `higher_level_katz_exp` constructs exactly
   5^floor(i/6) w_(i,t)/E4^i. The supplied long low-weight expansions match
   their short exact provenance, with guarded divisions by5.
4. `ech_form` swaps rows, scales a row only by the inverse of its unit
   part, and adds integral multiples of other rows. All operations lift
   to GL(Z5). It never divides an entire row by a nonunit.

The successful run, pinned source hash, and checks of the supplied bases
support this premise at the usual level of trust in Sage's modular-form
construction and exact arithmetic. There is no additional unknown Banach
norm constant in that source-based argument. The GL head change preserves
(1), while the independently checked inverse guard controls q-evaluation.

The artifact-only Python verifier currently checks the finite matrices,
the inverse witnesses, the short product provenance, and the fixtures.
It does not reconstruct every higher-weight complement choice or every
echelon row operation. An entirely self-contained geometric certificate
would also save `CompSpacesCode`, the complete rank witnesses, and the
head row operations, then replay those. A lightweight instrumented replay
can export them; the distinction is about independently replayable
provenance, not an asserted vanishing of an unbounded infinite tail.

Consequently the source-based analytic interpretation and the
artifact-only finite result should be labeled separately. Neither one
alone identifies the computed line with a Perrin--Riou bad line, proves
a common global-class comparison, fixes its period normalization, or
proves nonzero global localization.

## 7. Exact arithmetic receipts

`check_infinite_bounds.py --check` instantiates the period6 column bound,
the period30 CM-coordinate bound, and the complete precision table using
the actual projection receipt. Its saved output is
`infinite-katz-bounds.json`. It checks the arithmetic in this proof and
does not turn geometric premises into consequences of a finite test.

`check_cubic_ratio.py --check` independently reduces polynomials in the
cubic field and verifies the ratio, its inverse witness, and the sharp
precision counterexample. Its output is `cubic-ratio-result.json`. That
receipt also checks a supplied provisional local line as an explicitly
labeled normalization diagnostic; it does not identify an arithmetic bad
line.
