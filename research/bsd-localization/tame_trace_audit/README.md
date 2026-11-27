# Independent audit of the two tame traces

Date: 2026-11-27. Pilot: `E=389.a1`, `p=5`, `K=Q(sqrt(-71))`.

## Findings

The proposed reduction from tame level `71*389` to `389` is valid on
the full elliptic de Rham factor, including both Frobenius slopes.
For the particular two cross products there is a stronger simplification:
their normalized Fricke-71 sign is `+1`, and therefore their two
geometric traces coincide. After projection at level 389, recovery of
the old component uses the scalar `1/62`, a 5-adic unit.

This conclusion concerns the analytic vector defined by the actual
overconvergent construction. It does not identify that vector with the
full regulator of the global Castella--Hsieh class. It also does not
remove the de Rham reduction or its denominator accounting.

The trace shortcut does remove the need to compute 72 independent cusp
expansions for these cross products. It does **not** reduce the raw
infinity expansion bound by the same factor: extracting `U71` requires
coefficients through 71 times the desired traced bound.

## 1. Geometric normalization and recovery

Set `N=389`, `r=71`, `Y=X0(Nr)`, `X=X0(N)`. The two degeneracy maps
`pi1,pi2:Y->X` have degree `r+1`. Their pullbacks `i1,i2` and geometric
traces `tau1,tau2` on de Rham cohomology satisfy

\[
\begin{pmatrix}\tau_1\\\tau_2\end{pmatrix}(i_1,i_2)
=\begin{pmatrix}r+1&T_r\\T_r&r+1\end{pmatrix}.
\tag{1}
\]

The off-diagonal maps are the two orientations of the Hecke
correspondence; they coincide on the trivial-character weight-two
factor. On the elliptic factor `D_E`, `T71=-10`, giving

\[
G=\begin{pmatrix}72&-10\\-10&72\end{pmatrix},\qquad
\det G=5084\equiv4\pmod5.
\]

For an arbitrary class `y`, first project each lower-level trace to
the exact `E` Hecke eigensystem. Then

\[
\Pi_{E,\mathrm{old}}y
=(i_1,i_2)G^{-1}
\begin{pmatrix}\Pi_E\tau_1y\\\Pi_E\tau_2y\end{pmatrix}.
\tag{2}
\]

Both traces are needed for a general old vector. For example the
nonzero old-coordinate vector `(10,72)` has first trace zero and
second trace `5084`.

Equation (1) uses pullbacks of **differentials**. With
`omega_f=f(q)dq/q`, the second pullback is

\[
i_2(\omega_f)=r f(q^r)dq/q.
\]

Thus replacing its second column by the raw oldform `V_r f=f(q^r)`
changes the trace matrix to

\[
\begin{pmatrix}72&-10/71\\-10&72/71\end{pmatrix}.
\tag{3}
\]

There is no contradiction between (1) and a nonsymmetric matrix in
a raw-q basis. Mixing these conventions would give the wrong recovery.

The action is `G tensor Id_(D_E)`: the two-by-two matrix operates on
oldform multiplicity, not on the two Frobenius directions inside `D_E`.
Its unit determinant proves that this recovery step has no 5-adic
precision loss in compatible lattices. It says nothing about possible
denominators in the separate level-389 Hecke projection.

## 2. Why the overconvergent class and its jets survive

The input is

\[
\Xi_{a,b}(W)=d^{-s}((V_a g_W)^{[5]})\,V_bh_W,
\qquad (a,b)=(1,389),(389,1),\quad k=1+s.
\]

At a classical weight, inverse Bol changes the first factor from
weight `k` to weight `2-k`; the product has weight **two**. The
nebentypes cancel. On the selected branch `k=1 mod4`, the finite
Teichmueller correction in the Darmon--Lauder definition is trivial
on 5-adic units, with depletion still required at multiples of 5.

Darmon--Lauder, Section 1, equations (5)--(6), places this family in
the fixed weight-two overconvergent space and maps it to proper de
Rham cohomology by the canonical Frobenius splitting of the
supersingular-residue exact sequence. Prime-to-5 degeneracy
correspondences preserve ordinary neighborhoods and commute with
Frobenius, the differential, and residues. Their induced maps
therefore commute with that splitting. This proves the compatibility
with the proper cohomology used in (1)--(2), including the residue
correction rather than silently discarding it.

Consequently, for an actual family on a common strict neighborhood,

\[
[W^j]\tau_i\Xi(W)=\tau_i([W^j]\Xi(W))\quad(j=0,1,2).
\]

The trace operator has fixed weight two; it contributes no derivative
of a changing weight slash factor. Individual derivatives of `g_W`
or `h_W` need not be ordinary modular forms of weight one. Their
correct combination in the constant-total-weight family is essential.

Proper de Rham traces preserve the Hodge filtration. This does not
mean that every derivative of `Xi` lies in `Fil1`. A computation only
in classical `S2(389)` retains the holomorphic line in each elliptic
factor and is insufficient for the full vector. One needs de Rham
cohomology, or an equivalent overconvergent reduction retaining
ordinary and slope-one components. At level 389, the proper space has
dimension 64, while `S2` has dimension 32.

## 3. Independent check of the Fricke shortcut

We use normalized slash

\[
(F|_kA)(z)=\det(A)^{k/2}(cz+d)^{-k}F(Az).
\]

At level 71 the native CM newforms have the same Fricke eigenvalue
`lambda`, with `lambda^2=-1`, for every classical weight `k=1 mod4`.
One direct primary-source check is Mascot, Theorem 2.2.1. Its
pseudo-eigenvalue formula specializes to

\[
\lambda=71^{k/2-1}\frac{\tau(\chi_{-71})}{a_{71}}.
\]

The ramified prime ideal is `(sqrt(-71))`, so the conductor-one CM
Hecke character gives

\[
a_{71}=(\sqrt{-71})^{k-1}=71^{(k-1)/2}
\quad(k=1\bmod4).
\]

The finite order-seven character is trivial on this principal ideal.
Thus `lambda=tau(chi_-71)/sqrt(71)` is constant, independent of the
finite CM character or the selected CM embedding. The CM coefficients
are real under complex conjugation, as conjugation pairs the two
ideals of each split norm. Hence the pseudo-eigenform is the same
newform. Mascot's chosen matrix has upper-right entry `+1 mod71`,
whereas the usual Fricke matrix has `-1`; this can reverse the
individual odd-weight eigenvalue. The product sign below is unchanged.

Mascot's Theorem 2.4.1, in the raw `V_d` convention, gives

\[
(V_{389}g)|W_{71}
=\chi_{-71}(389)V_{389}(g|W_{71})
=-\lambda V_{389}g.
\tag{4}
\]

The corresponding factor at 5 is `chi_-71(5)=1`, so ordinary
5-stabilization and 5-depletion preserve the Fricke sign.

### Inverse Bol does not introduce an unaccounted period polynomial

For integer `k>=5`, let `eta=d^(1-k)(g^[5])` in the actual
overconvergent space. Normalized-slash Bol covariance gives

\[
d^{k-1}(\eta|_{2-k}W_{71})
=(d^{k-1}\eta)|_kW_{71}.
\]

Thus `eta|W71-lambda eta` is killed by `d^(k-1)`. It is also killed
by `U5`, because `eta` is depleted and the prime-to-5 Fricke operator
commutes with `U5` here. Its q-series is therefore both constant and
`U5`-killed, so it is zero. This is an argument for the depleted
overconvergent Bol primitive, not for a complex Eichler integral with
its period-polynomial ambiguity. Coleman's Gauss--Manin construction
of the Bol map and cohomological quotient supplies the required
functorial interpretation.

Each cross product therefore has sign
`lambda*(-lambda)=+1`. Since the product's weight is fixed, the
identity extends to the analytic family from classical weights
accumulating at weight one, and hence to every coefficient jet. Explicitly,
the weights `k=1+4*5^n` have `W=6^(4*5^n)-1 -> 0`. The identity theorem
is applied to the actual fixed-weight overconvergent family (or to each
of its q-expansion coefficients), not inferred from finitely many
specialization checks.

With the standard geometric trace convention this yields

\[
\boxed{\tau_1\Xi_j=\Xi_j+U_{71}\Xi_j,
\qquad\tau_2\Xi_j=\tau_1\Xi_j.}
\tag{5}
\]

For an explicit matrix check, set

\[
\sigma=\begin{pmatrix}1&0\\389&1\end{pmatrix},\quad
W=\begin{pmatrix}71&-23\\27619&-8946\end{pmatrix}.
\]

Then `det W=71` and
`W [[1,23],[0,71]]/71=sigma`. The nonidentity cosets can be taken
as `sigma T^a`, `0<=a<71`. For a Fricke-plus weight-two form,
the cusp expansion is `71^(-1) F((z+23)/71)`. Summing translations
selects indices divisible by 71, proving (5) without adjoining a
71st root of unity in the final calculation.

The Fricke-plus part of the old elliptic factor is
`(i1+i2)D_E`, so (2) simplifies further to

\[
\Pi_{E,\mathrm{old}}\Xi_j
=(i_1+i_2)\left(\frac1{62}\Pi_E\tau_1\Xi_j\right).
\tag{6}
\]

The plus sign here refers to Fricke-71, not to complex conjugation.
It leaves a two-dimensional de Rham factor. Matching a particular
modular parametrization or global test vector still requires its
specified linear combination of the two traces; an antisymmetric
combination would annihilate this particular input.

## 4. What the trace reduction saves

If input coefficients are available through `q^B`, (5) guarantees
traced coefficients only through `q^floor(B/71)`. Thus 4,096 terms
give 57 traced terms, fewer than the level-389 classical weight-two
Sturm bound 65. The illustrative lower-level Katz input bound 12,675
requires raw input through 899,925 before coefficient extraction.

This does not undo the large matrix reduction: the lower-level Katz
or cohomology basis is still much smaller. It separates that saving
from raw q-series generation and convolution. Nor is a classical
Sturm bound a general certification bound for arbitrary
overconvergent forms: those bounds require the finite Katz model and
its tail/precision proof.

## 5. Optional exact low-weight specialization route

At weight five, the required specialization is

\[
d^{-4}(g_5^{[5]})h_5.
\]

It is a weight-two overconvergent form, not the classical weight-ten
product `g5*h5`. Modular symbols for the classical factors give useful
Hecke and normalization data but do not perform the inverse Bol
operation, multiplication, and de Rham projection. An identification
with a suitable cohomological product would be additional work.

Nevertheless small positive weights can give a log-free independent
jet computation. The following interpolation statement is exact.

Let `F(W)` have integral Taylor coefficients in a fixed finite free
5-adic module. Set `a_j=6^(4j)-1`. For a desired modulus `5^m`,
interpolate `F` at `a_0,...,a_(m+1)` by a polynomial `P` of degree
at most `m+1`. Then

\[
[W^2]P\equiv[W^2]F\pmod{5^m}.
\tag{7}
\]

**Proof.** The polynomial with these interpolation nodes has roots
in `5 Z5`. The coefficient of `W^i` in the remainder of `W^n`
modulo that polynomial is homogeneous of degree `n-i` in its roots,
so its valuation is at least `n-i`. Terms through degree `m+1`
interpolate exactly. For all remaining terms `n>=m+2`, the error in
the `W^2` coefficient is divisible by `5^(n-2)`, hence by `5^m`.

For `m=12`, this uses the fourteen classical CM weights
`1,5,...,53`. The exact Lagrange coefficient weights lose at most
four digits, so sixteen-digit values suffice for (7). This is a
bound for the indicated integral module. A denominator bound from
de Rham reduction, Hecke projection, or period normalization must be
added if that module is an output lattice instead of the integral
raw-q input lattice. In particular, integrality of q-expansions does
not alone certify integrality in an arbitrary cohomology basis.

One weight-five check is insufficient for a second jet even at
infinite numerical precision. The polynomial `W(W-a_1)` vanishes
at the weight-one and weight-five nodes but has second coefficient
one. Adding the weight-nine node identifies the second coefficient
modulo 5, not modulo 25: `W(W-a_1)(W-a_2)` vanishes at all three
nodes and has second coefficient `-(a_1+a_2)` of valuation exactly
one. These supply exact counterexamples to overinterpreting a
low-weight specialization regression.

## 6. Executable checks and remaining work

`check_trace_audit.py` uses only Python's standard library. It checks
the exact curve count at 71, geometric and raw-q Gram matrices,
Fricke-plus recovery, the matrix/coset identity, the two low-weight
counterexamples, and interpolation weights for 1, 2, 5 and 12 digits.
The output includes all fourteen rational coefficient weights for
the twelve-digit interpolation. Finite monomial tests accompany the
general error proof above.

Default execution prints stable JSON without writing files; use
`--check PATH` or `--output PATH` explicitly. These checks do not
compute the actual elliptic projection of any new trace jet.

The next computational gate is the bounded-precision, full de Rham
projection at level 389. The next arithmetic gate remains the
comparison of that analytic vector with the specified global class
and its calibrated finite logarithm. The tame-trace reduction is
compatible with both goals and establishes neither by itself.

## Primary sources

* Darmon--Lauder, *Stark points on elliptic curves via Perrin-Riou's
  philosophy*, Section 1, equations (5)--(6), and Section 4.
  <https://people.maths.ox.ac.uk/lauder/papers/DL.pdf>
* Coleman, *Classical and Overconvergent Modular Forms*, Proposition
  4.3 and Theorems 5.1, 5.4, for the Bol/Gauss--Manin construction.
  <https://www.math.uchicago.edu/~fcale/Files/Cole1.pdf>
* Mascot, *Companion forms and explicit computation of PGL2 number
  fields with very little ramification*, Sections 2.1--2.2 and
  Theorem 2.4.1, for normalized Fricke and raw-oldform conventions.
  <https://warwick.ac.uk/fac/sci/maths/people/staff/mascot/companion.pdf>
* Lauder, *Efficient Computation of Rankin p-Adic L-Functions*,
  Section 2.3.1, for the depleted inverse-Bol overconvergence and
  the distinction from direct classical computation.
  <https://people.maths.ox.ac.uk/lauder/papers/AgbLauderFINAL.pdf>

The interpolation lemma and its error accounting are proved here.
The Fricke/coset calculation was independently checked alongside the
parallel `tame_trace_compute` and geometric workstreams; its source
and normalization arguments are included to make this audit standalone.
