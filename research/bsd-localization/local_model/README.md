# A 30-digit local benchmark for the reflected-class problem

For the pilot

\[
E:\ y^2+y=x^3+x^2-2x,\quad P=(0,0),\quad Q=(1,0),\quad p=5,
\]

we compute the logarithms for the differential \(\omega_E=dx/(2y+1)\).
Both have valuation one. The exact finite-precision result is

\[
\begin{aligned}
\log_5(P)/5&\equiv439539435537114752261,\\
\log_5(Q)/5&\equiv226464719373794906613
\end{aligned}
\qquad\pmod{5^{30}},
\]

where \(5^{30}=931322574615478515625\). Therefore

\[
r:=\frac{\log_5(Q)}{\log_5(P)}
\equiv281099199846294196408\pmod{5^{30}}.
\]

The strict line in the rational-point span has normalized generator
\(rP-Q\), interpreted in \(E(\mathbf Q)\otimes\mathbf Q_5\).
The finite residue displayed above approximates its coordinate; it is not
an assertion that an integer multiple of P equals Q.

| Precision | log(P)/5 | log(Q)/5 | log(Q)/log(P) |
|---|---:|---:|---:|
| modulo 5 | 1 | 3 | 3 |
| modulo 25 | 11 | 13 | 8 |
| modulo 5^5 | 2261 | 363 | 2658 |
| modulo 5^10 | 5377261 | 5844113 | 5133908 |

The complete residues, precision metadata, and exact formal parameters are
in `result.json`. The point-independence proof is in the preceding
`../eligibility/arithmetic/README.md`; it uses finite reductions and does
not assume the rank recorded by a curve database.

## Exact differential calculation

Put \(t=-x/y\), \(w=-1/y\), and \(w=t^3v(t)\). Substitution in the curve
equation gives

\[
w=t^3+t^2w+(1-2t)w^2,\qquad
v=1+t^2v+t^3(1-2t)v^2.
\]

The second equation uniquely determines \(v\in\mathbf Z[[t]]\), with
constant coefficient one. Its coefficients are computed by

\[
v_n=\mathbf1_{n=0}+v_{n-2}
+\sum_{i+j=n-3}v_iv_j-2\sum_{i+j=n-4}v_iv_j,
\]

where a term with a negative index is zero. All terms on the right use
previous coefficients. Direct differentiation of \(x=t^{-2}/v\) yields

\[
\frac{dx}{2y+1}
=\frac{2v+tv'}{v(2-t^3v)}\,dt
=\left(\sum_{j\ge0}c_jt^j\right)dt.
\]

The denominator has constant term two, a unit in \(\mathbf Z_5\).
Consequently every \(c_j\) is 5-adically integral. Independent implicit
differentiation gives the equivalent expression

\[
\frac{dx}{2y+1}=\frac{dt}{1-t^2-2t^3v+4t^4v},
\]

whose denominator has constant term one. This proves the stronger
integrality \(c_j\in\mathbf Z\) and justifies the recurrence's exact
integer divisions by two. The first twelve
coefficients, obtained by exact integer recurrence, are

\[
(1,0,1,2,-3,6,-5,-12,31,-80,51,50).
\]

Thus the formal logarithm is

\[
\log(t)=\sum_{n\ge1}\frac{c_{n-1}}n t^n.
\]

The script verifies the curve and differential identities to its working
degree. The infinite identities and integrality follow from the equations
above; checking a finite initial segment alone would not establish the tail
estimate.

## Precision proof, including nonunit denominators

The finite group has \(\#E(\mathbf F_5)=9\). The multiples \([9]P,[9]Q\)
are in the formal subgroup, and exact rational addition gives

\[
t([9]P)=\frac{1869740440020}{6362164375021},\qquad
t([9]Q)=\frac{51414701739403105}{103754114414340313}.
\]

Both parameters have valuation one. For any such parameter the nth term
of the logarithm has valuation at least \(n-v_5(n)\). Since
\(v_5(n)\le n/2\), every term with \(n\ge2N\) vanishes modulo \(5^N\).
For \(N=31\), computing degrees 1 through 61 therefore suffices for 31
absolute digits, or 30 digits after division by 5.

Terms with \(5\mid n\) cannot be evaluated by inverting n modulo a power
of 5. Write \(n=5^a n_0\), with \(5\nmid n_0\). We compute the numerator
modulo \(5^{N+A}\), where \(A=\max_{n<2N}v_5(n)\), divide the known
multiple of \(5^a\) as an integer, then multiply by the inverse of
\(n_0\) modulo \(5^N\). The extra A digits guarantee that this division
retains all N required digits. Finally divide \(\log([9]P)\) and
\(\log([9]Q)\) by 9, a 5-adic unit.

Validation uses the alternative multiples \([18]P,[18]Q\), logarithmic
additivity for \(P+Q\) and \(Q-P\), and a fresh shorter truncation.
All agree. These checks specifically exercise the differential, signs,
nonunit divisions, and precision accounting. The saved result is
deterministic and reproduced by the package runner.

## Use in the research problem

With the completed pilot corollary, P and Q form a basis after tensoring
with \(\mathbf Q_5\), without a claim about integral saturation. A
constructed Selmer class z has unique coordinates a,b in this basis and

\[
\log_5(z)=a\log_5(P)+b\log_5(Q).
\]

The benchmark therefore distinguishes the strict generalized Kato line
from a transverse class with nonzero localization. It is suitable for
checking a future explicit reciprocity formula, but does not compute the
global coordinates of a diagonal-cycle class or its reflected derivative.

The coefficient ratio r is not an algebraic-number recognition target.
The curve is non-CM: its j-invariant \(112^3/389\) is not an algebraic
integer, whereas a CM j-invariant is. The p-adic analytic subgroup theorem
then implies that logarithms of the independent algebraic points P,Q
are linearly independent over \(\overline{\mathbf Q}\). In particular
r is transcendental over \(\mathbf Q\). See the proof and primary reference
in `../rationality/README.md`, Section 5. The meaningful geometric
comparison concerns the exterior class or enhanced regulator, not an
attempt to recognize r as an algebraic number.

The ordinary unit root of \(X^2+3X+5\) is also computed to 31 digits.
It satisfies \(\alpha_5\equiv7\pmod{25}\). The p-cleared local height factor

\[
5\frac{1-\alpha_5/5}{1-\alpha_5^{-1}}
=\frac{(5-\alpha_5)\alpha_5}{\alpha_5-1}
\equiv1\pmod5
\]

is a unit. This says nothing about the valuation of the unspecified global
period/congruence constant in the published reciprocity formula.

## Reproduce

From `research/bsd-localization/`:

```sh
python local_model/formal_log.py --check local_model/result.json
```

The program uses Python's standard library and the existing exact rational
group law. No floating-point approximation or GRH hypothesis is used.
An independent review checked the differential sign, both expressions for
the differential, nonunit divisions, and the infinite tail argument.
This addition is not a new Lean formalization.
