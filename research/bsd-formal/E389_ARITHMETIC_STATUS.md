# Original BSD pilot: arithmetic proof status

Date: 2026-11-28. This branch extends the 266-theorem formalization at
`72e9f63708fbe3b48342de296a60979e32bb8c31` with 54 theorems, bringing the
package to 320. The new work closes concrete arithmetic obligations, but
does not complete the arithmetic theta identification or the terminal
rank-and-Sha theorem.

## 1. The fixed endpoint

The original coordinated pilot is

\[
E_{389}:y^2+y=x^3+x^2-2x,\qquad
K=\mathbb Q(\sqrt{-71}),\qquad p=5.
\]

Its desired terminal conclusion is

\[
\operatorname{rank}E_{389}(\mathbb Q)=2,
\qquad \Sha(E_{389}/\mathbb Q)[5^\infty]\text{ finite}.
\]

This is the endpoint in the
[shared handoff at cf84450](https://github.com/bgross0/exponent-seven/blob/cf84450fb80b673c9b32c5abb71d7e26d4e87957/research/bsd-coordination/README.md).
It does not include the full complex BSD formula, the leading coefficient,
or all primary components of Sha.

The secondary curve `E433 : y²+xy=x³+1` has different finite eigenfunction
values and a different ordinary root. The preceding assembled theorem was
for that secondary curve. This extension supplies an explicitly separate
E389 interface. It never substitutes E433 theta evidence into the E389
rank-and-Sha argument.

## 2. New unconditional arithmetic proofs

### The actual E389 rational-point group contains two independent points

`BSDRationalPoints.E` is definitionally `BSDOrdinary.curve389 ℚ`, with
Weierstrass coefficients `[0,1,1,-2,0]`. Both membership and the group
operations are Mathlib's actual elliptic-curve definitions.

The main proved declarations are:

```lean
points_linearIndependent : LinearIndependent ℤ ![P, Q]

pointCombination_injective :
  Function.Injective (fun c : ℤ × ℤ => c.1 • P + c.2 • Q)

rank_at_least_two : 2 ≤ Module.rank ℤ E.Point

P_infinite_order : ¬ IsOfFinAddOrder P
```

Here `P=(0,0)` and `Q=(1,0)`. `Module.rank` is cardinal-valued; no
Mordell–Weil finite-generation assumption is inserted. These statements
have no arithmetic premises.

The duplication formula has numerator and denominator

\[
N(x)=x^4+4x^2-2x+3,\qquad
D(x)=4x^3+4x^2-8x+1.
\]

The three equations `N(x)-kD(x)=0`, for `k=0,1,-2`, are monic quartics
with no root modulo eleven. Monic rational-root integrality therefore
rules out rational halves of P, Q and P+Q. A separate monic cubic modulo
four rules out rational two-torsion. Every integral relation is then
divisible by every power of two, forcing both coefficients to vanish.

This proves the positive-rank input needed by the published criterion,
and the rank lower bound needed at the endpoint. It does not prove the
rank upper bound or any Sha finiteness statement.

### The seven existing roots have an exact polynomial seven-cycle

`BSDHorizontal71` proves, for the seven previously constructed roots in
the completed quadratic order and their certified cyclic ordering,

\[
\Phi_2(r_i,r_j)=0
\quad\Longleftrightarrow\quad
j=i+1\text{ or }i=j+1\quad(i,j\in\mathbb Z/7\mathbb Z).
\]

This upgrades the old congruences modulo `433^4` to exact equalities
between actual roots of the full degree-seven polynomial. Both directions
are proved: the 14 directed edges vanish, and all 35 nonedges give units.

Two full integer polynomial identities give the bridge:

\[
D^2\Phi_2(X,Y)=Q(X,Y)L(X,Y)+H(X)R_\Phi(X,Y),
\]
\[
D^2H(Y)=Q(X,Y)S(X,Y)+H(X)R_H(X,Y).
\]

Here Q has degree two in Y and the explicit clearing denominator D is a
proved unit in the completion. Hensel lifting of Q and simple-root
uniqueness for H identify the lifted neighbor with the already constructed
root. The proof needs no domain instance for the completion.

The candidate polynomial H is shared by the pilots; this particular root
realization is at 433. The theorem does not identify E433 eigenfunction
values with E389 values. It also does not identify H analytically as a
Hilbert class polynomial or prove that the literal Phi_2 relation represents
the required geometric isogenies.

The 140-root family has nonunit derivatives, so the simple-root uniqueness
proof cannot be reused there without additional work.

## 3. A smaller, correctly targeted finite theta obligation

`BSDE389Theta` imports all 140 original supplied integer values from the
coordinated pilot and checks their quotient sums in the kernel:

\[
(5,-1,-1,5,-8).
\]

The shifted polynomial is exactly

\[
-20T-34T^2-27T^3-8T^4.
\]

For ordinary scale u and trace correction c, the quadratic coefficient
after regularization is `-34u-10c`, congruent to u modulo five. The scale
is the proved unit `alpha389^(-2)`, constructed from the actual E389 point
count at five.

The new theorem `e389_certificate_of_finite_tower` only requires the
first-level quadratic congruence. It no longer asks for all five low-degree
coefficient congruences. Its remaining inputs are:

1. A finite polynomial family G with the successive cyclic distribution
   relation at every level.
2. Its finite inversion symmetries at every level, with augmentation-one
   origin multipliers.
3. Exact zero level-zero augmentation.
4. The single quadratic congruence with the regularized E389 data.

From these inputs it constructs the series and proves `F=T²V` with V(0)
a unit. The actual arithmetic CM family G is still to be defined and proved
to satisfy the inputs. The raw coefficient -20 is never promoted from a
modulo-five zero to an exact zero.

## 4. What still prevents the end-to-end theorem

| Obligation | Current formal status | Required arithmetic content |
| --- | --- | --- |
| Positive rank and rank at least two | Proved for actual E389 points | Closed by `BSDRationalPoints` |
| Actual ordinary parameter at five | Proved from actual point count | Its occurrence in the arithmetic normalization still needs identification |
| Exact degree-seven polynomial graph | Proved for actual constructed roots | CM interpretation and geometric isogeny interpretation remain |
| Conductor-25 finite evaluations | Exact supplied E389 sums proved; stronger E433 finite data also proved | Identify the actual CM classes, eigenfunction and anticyclotomic projection |
| Infinite theta construction | Limit and order theorem proved from finite inputs | Define the actual arithmetic tower and prove its all-level relations |
| Curve/eigenform identification | Not proved here | Brandt module and Jacquet–Langlands identification for the specified curve |
| Theta-to-Selmer theorem | Not formalized here | Published arithmetic criterion, including its actual cohomological objects and hypotheses |
| Rank upper bound and finite 5-primary Sha | Not proved here | Actual Kummer exact sequence and Selmer/Sha arithmetic, applied to the proved bound |

The pinned Mathlib has useful elliptic-curve point, height, polynomial,
completion and modular-form theory. It does not provide ready-to-import
versions of the required CM/Jacquet–Langlands/elliptic-Selmer machinery.
The similarly named Dedekind-domain Selmer module concerns multiplicative
`K(S,n)`, not the elliptic Selmer space used in this pilot. The detailed
source audit is in `review/arithmetic-scope-audit.md`.

[Castella–Hsieh, Theorems A and B](https://web.math.ucsb.edu/~castella/Kato-print.pdf)
provide the published theta-to-Selmer route. Theorem B requires positive
rational rank, which the new actual point theorem supplies. This pilot
does not need a new general theorem removing that positive-rank hypothesis.
Formalizing the published arithmetic route remains substantial work.

For zero augmentation alone, the actual Hecke distribution relation may
shorten the dependencies: the full raw CM sums satisfy the first boundary
relations `S1=(a5-2)S0`, `S2=a5*S1-4*S0`, followed by the recurrence with
coefficient five. Since S0=0 for the supplied conductor-one values, their
actual CM interpretation plus those relations would give zero at every
level. The initial coefficient four is essential. This is a prospective
arithmetic shortcut, not a formalization already completed here. See
[Chida–Hsieh, Section 4.2](https://www.math.ntu.edu.tw/~mlhsieh/research/central.pdf).

A direct certified 5-descent is a possible alternative for the terminal
rank-and-Sha statement. It would require a genuine elliptic Selmer computation
and its soundness theorem. A 2-descent alone would not prove the required
5-primary Sha conclusion.

The next focused reuse step is documented in
[`review/reusable-exponent-seven.md`](review/reusable-exponent-seven.md).
The existing exponent-seven code already proves actual maximal-order class
group facts for K. Combining its sharp generation bound with `Norm(omega)=18`
offers a short route to the actual norm-two generator and class number seven.
The explicit principal-power witness `(2,omega)^7=(10+omega)` then supplies
the local ratio 3 modulo 25 needed for a prospective all-level ring-class
generator proof. The nonmaximal-order Picard and CM-action bridges remain
explicit; the two projects' different Lean pins also need reconciliation.

## 5. Verification and completion criterion

`verification/receipt.json` records the pinned build, every theorem's axiom
dependencies, separate kernel replay of all 18 project modules, and exact
source/object/log hashes. The unchanged original 15 theorems remain preserved.
All 320 theorem declarations are audited; accepted axioms are only `propext`,
`Classical.choice`, and `Quot.sound`. Independent statement reviews are stored
under `review/`.

A completed pilot must end in a theorem about the fixed E389 model and the
actual arithmetic objects, with no assumed CM identification, arithmetic
tower relation, Selmer-dimension bound, Kummer comparison, or desired Sha
conclusion. A consistent abstract tower, a literature citation, and a
successful numerical computation are useful inputs to the project, but none
substitutes for those missing Lean proofs.
