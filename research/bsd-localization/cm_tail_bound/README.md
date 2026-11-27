# A quantitative CM-jet tail bound and an undepleted representative

Date: 2026-11-27. Pilot: level 389, K=Q(sqrt(-71)), p=5.

This note proves an explicit tail inequality under the fixed-weight
Coleman-family realization specified in Section 1. The bound is for an
**undepleted product representative Q**, related to the existing input by
a fixed elliptic Euler operator. It is not a bound obtained by fitting
finitely many q-coefficients. It does not assert that the Sage reduction,
its integral lattice comparison, or the global regulator comparison has
been executed.

The computationally useful conclusions are:

* A q-integral unit eigen-jet has an explicit norm bound from Wan's
  high-row estimate; a separate finite-head eigenline isolation is not
  required for this norm argument.
* If i denotes the E4 pole index, the second W coefficient of the traced
  undepleted product has an integral Katz numerator with valuation at least

  `max(0, ceil((20*i-58)/25)-4)`.

* After the saturated pole reduction from `../de_rham_strategy/`, discard
  pole indices i>17 only with an error divisible by 5^8 in that model.
  The old Hecke projector and the undepleted-to-original Euler correction
  can each cost one further digit. Any additional lattice/normalization
  loss still has to be measured; this is not a final six-digit output.
* For the embedding omega=2 mod5, the undepleted Euler constant is
  `c=zeta7^3`; for omega=4 it is `zeta7^4`.

The executable checker verifies the exact valuation arithmetic and the
Euler identity against the saved CM q-expansions at all three jet orders.
The analytic hypotheses and proofs are in this note, not inferred from
those finite checks.

The saved run passed 9840 raw vector identities through q819 and144
trace identities through q11, in both embeddings and both placements,
modulo5^12. Replacing the correct Euler root by a different seventh root
was rejected in2442 coefficient comparisons. The tail arithmetic includes
255 cutoff regressions against longer finite ranges; the infinite-range
justification is the monotonic block argument in Section6.

## 1. Exact scope: the analytic input

Fix integral Katz complements for weight one and character chi_-71:

    M_(1+4i)(71,O) = E4*M_(1+4(i-1))(71,O) direct_sum W_i.

They are the standard integral complements in Lauder's Section 2.1. Work
over the unramified coefficient extension containing zeta7, extending it
further to contain the chosen radius element when necessary.

Write `s=k-1`, `W=6^s-1`, `W=25*w`, and

\[
 j(w)=s/4=\frac{\log(1+25w)}{4\log6}.
\]

Let h_s be the actual normalized ordinary CM Hida family used by the
package. The analytic realization required here is:

**(CF)** The truncated formal q-series

\[
 F(w)=E_4^{-j(w)}h_s\pmod{w^3}
\]

is realized by three overconvergent forms of fixed weight one on some
common positive-radius ordinary neighborhood. It satisfies Coleman's
fixed-weight eigen-equation

\[
 U_5\bigl(G^{j(w)}F(w)\bigr)=\alpha(w)F(w),
 \qquad G=E_4/V_5E_4,                                  \tag{1}
\]

where alpha(w) is the CM ordinary eigenvalue and is a unit of
O[[w]]/(w^3). This is the usual Coleman realization of the normalized CM
family: integer weights give (1) by U(Va*b)=a*U(b), and the family identity
is its analytic continuation. The ordinary CM family is p-distinguished
here (zeta7^2 and zeta7^5 are distinct modulo5). Darmon--Lauder Section1
records the applicable local weight coordinate and the Hida-family
realization; Lauder Section2.2 records this fixed-weight operator.

We retain (CF) as an explicit analytic input. The code does not verify an
infinite Banach-family realization from the finite archive. A reader using
a different family trivialization must establish its comparison with (CF).
No assertion that a varying-weight derivative by itself is a fixed-weight
overconvergent form is used.

The follow-up [source review](CF_REVIEW.md) supplies (CF) for this actual
normalized CM family using Bellaiche--Dimitrov's etale branch and
Coleman's perfect Hecke pairing, with an explicit conversion to the E4
chart. This is a theorem-based analytic argument, separate from the
executable finite checks and from the numerical backend's lattice audit.

The other inputs are the published Katz splitting, the 1-unit property
of G for every radius valuation r<1/6, and

\[
 5U_5 M_k(O,r)\subset M_k(O,5r),\quad 0<r<1/6.          \tag{2}
\]

Here r is the valuation of the radius element, and M_k(O,r) denotes its
integral Banach lattice. Thus larger r is the larger strict neighborhood.
In an orthonormal Katz basis the output pole-i row of U5, or U5 composed
with an integral multiplication operator, has valuation at least 4ri-1.

The coefficients of F are q-integral. Indeed h has integral W coefficients
by its ideal-sum construction. Also log(E4) belongs to 5*O[[q]], while
the first two coefficients of j(w) have valuations1 and3. Expanding
exp(-j(w)*log(E4)) through w^2 therefore has integral q-coefficients.
This verifies the normalization premise needed below without asserting
an integral Banach norm in advance.

## 2. q-integrality implies unscaled Katz-coefficient integrality

Suppose an overconvergent fixed-weight form is written uniquely as

\[
 f=\sum_{i\ge0}\frac{c_i}{E_4^i},\qquad c_i\in W_i\otimes K.
\]

If its full q-expansion is integral, then every c_i is integral.

**Proof.** Overconvergence makes v(c_i) tend to infinity. Choose n so all
tail numerators i>n are integral; their q-expansions, divided by E4^i,
remain integral because E4 has q-constant1. The finite head is therefore
q-integral. Multiplying that head by E4^n gives a classical modular form
whose q-expansion is integral. By the definition of the classical integral
lattice and its iterated direct-sum splitting, every component
E4^(n-i)*c_i is integral in its summand. Hence every head c_i is integral.
Together with the tail this proves the claim. The same argument works
coefficientwise in O[w]/(w^3), and after division by any fixed power of5.

This proves integrality of the *unscaled* coefficients. It does not say
v(c_i)>=r*i, which is the stronger integral radius assertion.

## 3. A minimum-norm argument for unit eigen-jets

Use the radius-normalized coefficients c_i/radius^i and define

\[
 m_r(F)=\min_i\{v(c_i)-ri\},
\]

taking the minimum over the three jet coefficients as well. The minimum
exists because F is in the Banach space and the normalized coefficients
tend to zero. Assume the multiplier K(w)=G^j and alpha(w)^(-1) are integral
operators in this jet norm. Equation(1) and (2) give

\[
 v(c_i)-ri\ge m_r(F)+4ri-1.
\]

If i is an index attaining m_r(F), then 4ri<=1. The preceding integrality
lemma gives v(c_i)>=0, whence

\[
 \boxed{m_r(F)\ge-r\left\lfloor\frac1{4r}\right\rfloor.}     \tag{3}
\]

Applying (1),(2) once more yields the larger-radius bound

\[
 \boxed{m_{5r}(F)\ge-1-r\left\lfloor\frac1{4r}\right\rfloor.} \tag{4}
\]

This argument uses neither a simple eigenvalue of a finite U matrix nor
a finite approximation to an eigenline. Unit alpha and the exact
infinite eigen-equation suffice. Those are properties of the CM input,
not of the elliptic slope-one output we eventually want to extract.

### Why an initially unspecified positive radius suffices

The jet form in (CF) initially exists at some radius. Restrict that radius
below1/6. All three coefficients of K=G^j exist there over the coefficient
field, even before their integral norm is bounded. Hence the entire jet
alpha^(-1)U(KF) extends from r to5r by (2). Its q-expansion equals F by
(1), so q-expansion injectivity supplies the continuation of all three
coefficients together. Iterate while the input radius is below1/6,
restrict to4/25 once it is reached, and apply U once more. This is analytic
continuation from (CF), not continuation of finite q-data.

## 4. Explicit constants at r=4/25

We need an integral multiplication operator through the second jet.
The following estimate supplies it without assuming G-1 is 5-divisible
in a Banach lattice at the chosen radius.

The full q-expansion of G-1 is divisible by5. Section2 gives v(c_i)>=1
for its unscaled Katz coefficients. Its 1-unit property at every r<1/6
also gives v(c_i)>=i/6 by taking the limit r to1/6. Hence

\[
 m_r(G-1)\ge\inf_i\{\max(1,i/6)-ri\}=1-6r.             \tag{5}
\]

At r=4/25 this is delta=1/25. For any element u with v(u)>=delta,

\[
 v(\log(1+u))\ge\min_{a\ge0}(5^a\delta-a).             \tag{6}
\]

To see this, write each logarithm summation index as n=5^a*m with
5 not dividing m; n*delta-v5(n)>=5^a*delta-a. For delta=1/25 the minimum
is -1, attained at a=2; the later values strictly increase.

The coefficients of j(w) through order two have valuations1 and3.
Consequently the coefficients of

\[
 G^{j(w)}=1+j_1\log(G)w+
 (j_2\log(G)+j_1^2\log(G)^2/2)w^2
\]

have valuations at least0 at all three orders. The use of the truncated
jet ring is intentional: no convergence of this exponential on a full
unit w-disk is inferred at the limiting norm zero.

Since floor(1/(4r))=1, equations(3),(4) now give

\[
 m_{4/25}(F)\ge-4/25,\qquad
 \boxed{m_{4/5}(F)\ge-29/25.}                           \tag{7}
\]

## 5. The undepleted product and its trace

Define

\[
 Q_A(s)=h_{-s}\,V_{389}h_s,\qquad
 Q_B(s)=\langle389\rangle^{-s}(V_{389}h_{-s})h_s.        \tag{8}
\]

These are fixed weight-two products. To compare their trivializations,
put R=V389(E4)/E4. Since V389(E4)-E4 is divisible by5 in the integral
classical weight-four space, at rho=4/5 we have

\[
 m_\rho(R-1)\ge1-\rho=1/5,\qquad m_\rho(\log R)\ge0.
\]

Thus R^j and R^(-j) have integral truncated w-jets. The prime-to-5 map
V389 preserves the same norm: on a pole-i term its denominator changes
by R^i, a unit, while its classical numerator remains integral. In the
fixed-weight model

\[
 Q_A=F(-s)\,V_{389}F(s)\,R^{j(s)}.
\]

The reflected parameter is w -> -w+25w^2 modulo w^3, so reflection
preserves the jet Gauss norm. Both products in (8) therefore satisfy

\[
 \boxed{m_{4/5}(Q_A),m_{4/5}(Q_B)\ge-58/25.}           \tag{9}
\]

Forgetting the level-71 subgroup commutes with E4 and its pole filtration.
Its integral geometric trace preserves the integral numerator lattices,
so (9) also holds for the traced forms. The native CM families have the
same tame Fricke-71 scalar as in `../tame_trace_theory/`; hence each Q
is tame-Fricke71 plus and its trace is Q+U71 Q. This argument has no
weight derivative of the trace scalar: the products have fixed weight2.

Coefficient conjugation and averaging by (1+sigma)/2 preserve the bound.
The cubic averaged representative constructed in the companion Euler
work therefore has the same bound.

## 6. From (9) to an explicit discarded-tail certificate

Changing back from w to W costs2j digits for coefficient W^j. The
coefficient field is unramified, so valuations of the unscaled numerators
are integers. If B_(i,j) is its pole-i numerator, (9) gives

\[
 v_5(B_{i,j})\ge
 a_{i,j}:=\max\left(0,\left\lceil\frac{20i-58}{25}\right\rceil-2j\right).
                                                               \tag{10}
\]

The zero lower bound uses q-integrality of the untrivialized product and
its integral trace, followed by Section2 at fixed weight2. It remains
valid for the cubic average. For the second coefficient set a_i=a_(i,2).

The saturated integral pole reduction from `../de_rham_strategy/` reduces
a pole-i term to poles at most2 with loss at most floor(log_5(i-1)). Thus
discarding all i>N, where N>=2, produces an error with valuation at least

\[
 \boxed{\min_{i>N}\{a_i-\lfloor\log_5(i-1)\rfloor\}.}   \tag{11}
\]

The infinite minimum has a finite check. Within every interval
5^k<=i-1<5^(k+1), the expression is nondecreasing. From k=1 onward its
full-block minima strictly increase: check i=6 to26 directly, after
which the numerator's linear branch has slope4/5 and
(4/5)*(5^(k+1)-5^k)>1. The initial block k=0 is covered by its first
following breakpoint i=6. Consequently only the first discarded i and
the first following power-of-five breakpoint need be checked.

| Largest retained pole index N | Error after saturated pole reduction |
|---|---:|
| 10 | at least 2 digits |
| 12 | at least 4 digits |
| 15 | at least 6 digits |
| 17 | at least 8 digits |
| 20 | at least 10 digits |
| 22 | at least 12 digits |

These are digits in the specified pole/cohomology model. Subtract the
actual subsequent lattice, Hecke, Euler, and normalization losses before
claiming precision for a final elliptic vector. In particular a nominal
six-digit Katz matrix with pole cutoff10 does not, by this argument,
automatically give six certified vector digits.

## 7. Exact Euler transfer to the original input

Let A_s=h_-s^[5] V389(h_s), using the already-proved CM inverse-Bol
identity. The ordinary eigenvalues satisfy

\[
 \alpha_h(-s)\alpha_h(s)=c,
 \quad c=\begin{cases}\zeta_7^3&\omega\equiv2\pmod5,\\
                         \zeta_7^4&\omega\equiv4\pmod5.
       \end{cases}
\]

Their varying exponents cancel. From U(F*V5G)=U(F)*G and commuting U5
with V389 we get the exact raw identity

\[
 \boxed{U_5A_s=(U_5-c)Q_A(s).}                         \tag{12}
\]

The B placement has the same identity with Q_B, including the scalar
<389>^-s in (8). Tame trace commutes with U5, so the identities survive
both traces and all weight coefficients. On the elliptic factor U is
invertible and equals5F^-1, giving

\[
 \boxed{\Pi_E A=(I-cF/5)\Pi_E Q_A.}                   \tag{13}
\]

Here Pi_E includes the canonical proper projection. The oldspace
coordinate still divides by62, a unit at5. The correction matrix is
constant in weight, so no Euler-factor derivative is missing.

For completeness, writing d=c^2+3c+5,

\[
 (I-cF/5)^{-1}=\frac{(5+3c)I+cF}{d}.
\]

The denominator d is a unit: modulo5 it is c(c+3), and a nontrivial
seventh root of unity cannot equal2 in characteristic5. The forward map
loses at most one digit in an F-stable integral lattice; its inverse is
integral. The companion cubic Euler construction averages the two
conjugate Q inputs and gives the corresponding degree-three transfer.

## Reproduction and source scope

```sh
python research/bsd-localization/cm_tail_bound/check_bound.py --check
```

The checker proves finite identities and rational/integer inequalities.
Its PASS status does not formalize (CF), the published Banach theorems,
or the geometric integral-lattice identifications.

Primary sources:

* Lauder, *Computations with classical and p-adic modular forms*,
  Sections2.1--2.3: integral Katz complements, Coleman weight change,
  the 1-unit assertion, and the pU radius estimate.
  https://people.maths.ox.ac.uk/lauder/papers/LMSLauderMFJune10.pdf
* Darmon--Lauder, *Stark points and Perrin-Riou's philosophy*, Section1
  and the weight-one deformation discussion: the actual overconvergent
  Hida-family setting and its weight coordinate.
  https://people.maths.ox.ac.uk/lauder/papers/DL.pdf
* Lauder, *Efficient Computation of Rankin p-Adic L-Functions*,
  Note2.3(1): the integral-radius issue this specialized argument addresses.
  https://people.maths.ox.ac.uk/lauder/papers/AgbLauderFINAL.pdf

Equations(3)--(13), their proof organization, and the numerical cutoff
certificate are deductions in this note. They are not attributed as
verbatim statements of those papers, and no novelty or Lean-verification
claim is made.
