# Additional consequences of the completed p=5 pilot

This note builds on the separately supplied `bsd-rank-two` package, whose
archive SHA256 is
`f4d0332acbe087da2dda53a9a380f41c75d3ec63c5ad59441f2a5785ef21531a`.
It does not repeat that package's CM construction or full verification.
The exact source-file hashes and extracted small inputs are in `inputs.json`.

The additions are: an actual cyclic ordering of the seven values and its
period norm; a 5-adic unit certificate; a precise coefficient-descent argument;
two explicit local logarithms; and the resulting finite-5-primary-Sha
corollary when combined with the previous independent-point certificate.

## 1. The actual toric period has norm 49, not the norm of the saved j-order

The source stores the seven CM values in increasing vertex-index order:

    [-1,-1,0,1,1,0,0].

That is a multiset/list of j-invariants, not a class-group cyclic ordering.
Nonconstancy proves nonvanishing regardless of the ordering, but calculating
an actual character period or its norm requires the cyclic order.

Following the source's induced horizontal 2-isogeny seven-cycle gives local
indices

    [0,2,1,4,5,6,3]

and hence the cyclic value vector

    [-1,0,-1,1,0,0,1].

For this origin and orientation the period is

\[
u=-1-\zeta_7^2+\zeta_7^3+\zeta_7^6,
\qquad N_{\mathbf Q(\zeta_7)/\mathbf Q}(u)=49.
\]

The norm is computed by exact arithmetic in Z[X]/Phi_7. A change of cyclic
origin multiplies u by a root of unity; replacing the generator permutes its
conjugates. Thus the norm49 is invariant under the relevant choices for the
source's fixed primitive integral eigenfunction. In contrast, treating the
saved j-order as cyclic yields norm7, which is not its toric-period norm.

Every actual nontrivial period is a **5-adic unit**. Here is an explicit
small certificate in F5[X]/(Phi_7):

\[
(-1-X^2+X^3+X^6)
(3+2X+X^2+X^3+2X^4+3X^5)=1.
\]

The equality is modulo5 and Phi_7. The checker verifies it directly.
Alternatively, the norm49 is a 5-adic unit. There is also an argument that
does not need the cyclic ordering: Phi_7 is irreducible over F5, so a vector
whose seven coefficients are not all congruent modulo5 cannot have zero
period in F_(5^6). This applies to the given multiset in any ordering.

The CM/Gross identification of the input graph and function values remains
the supplied package's theorem-level input. This small script checks the
additional consequences, not that geometric identification again.

## 2. The coefficient field and the correct descent statement

The powers of5 modulo7 are

    1,5,4,6,2,3,1.

Thus Phi_7 is irreducible modulo5 and Q5(zeta_7) is the unramified extension
of degree6. It must not be replaced by Q5. Even the real cubic Hecke field
of the unramified weight-one theta series does not embed in Q5: its defining
polynomial X^3+X^2-2X-1 has no root modulo5. The chosen p-stabilization uses
the individual order-seven eigenvalues and therefore the degree6 extension.

Castella--Hsieh's introductory Qp-valued simplification is explicitly labeled
as such on published p.3. Section2.1, p.7, then works over the integers of an
arbitrary finite extension L/Qp, and Section2.4 constructs the CM families
over this coefficient ring. Take L large enough to contain Q5(zeta_7) and
the coefficients of any chosen test vectors. Further finite extensions, if
used for auxiliary algebraic constants, make no difference below.

Put S = Sel(Q,V5 E). The safe interpretation of the constructed class is

\[
\kappa_L\in S\otimes_{\mathbf Q_5}L.
\]

Finite extension of coefficient scalars commutes with the global/local
cohomology and the linear local conditions defining this Selmer space.
One can see this by choosing a Q5-basis of L: the representations and
cochain complexes become finite direct sums, and kernels commute with
this exact scalar extension. Therefore

\[
\dim_L(S\otimes L)=\dim_{\mathbf Q_5}S.
\]

Consequently a theorem giving dimension2 after extending coefficients
gives dimension2 over Q5. This is **dimension descent**, and it does not
assert that an arbitrarily normalized individual Kato class is Q5-valued.

For nonvanishing, write kappa_L = sum_i s_i tensor e_i in a Q5-basis of L.
At least one s_i is nonzero. If localization of kappa_L vanishes, linear
independence of the e_i implies localization of every s_i vanishes. Choosing
a corresponding coordinate functional L -> Q5 gives a nonzero Q5-valued
strict Selmer class. The choice is not canonical.

An unweighted field trace is not a substitute: zeta_7-zeta_7^2 is nonzero
but has trace0. Thus a nonzero vector s tensor (zeta_7-zeta_7^2) has zero
trace even when s is nonzero. The checker includes this failure case.

Once dim_Q5 S=2 and localization is nonzero, its kernel is a Q5-line D.
Any nonzero strict kappa_L spans D tensor L, so **the line descends**, and
kappa_L is a nonzero L-scalar multiple of a Q5-generator. No assertion
about a canonical scalar or its algebraicity over Q is required.

### Character conventions

The earlier local package uses a=(2,omega), while the supplied p5 package
uses c=[(29,omega-13)]=a^4 as its ordinary class-group generator. These are
compatible, but assigning zeta_7 to one generator changes the character.

| Character convention | Prime (5,omega-2), whose class is a^5=c^3 |
|---|---|
| psi(a)=zeta_7, chi=psi^2 | psi(p5)=zeta_7^5, chi(p5)=zeta_7^3 |
| psi(c)=zeta_7, chi=psi^2, as in supplied package | psi(p5)=zeta_7^3, chi(p5)=zeta_7^6 |

Both choices are eligible nontrivial order-seven characters; conjugating the
prime inverts the values. They must not be mixed in a coefficient-level
comparison. The nonvanishing and unit results hold for all six characters.

## 3. Nonexceptional factors and explicit localization

Exact enumeration gives #E(F5)=9 and a5=-3. The good ordinary unit root of
X^2+3X+5 is alpha5=7 modulo25, hence2 modulo5. The order-seven value chi(p5)
cannot equal the order-four element2 in the residue field. It follows that

\[
1-\alpha_5^{-1}\chi(\mathfrak p_5)
\]

is a unit. Likewise 1-alpha5^(-1) is a unit. These facts exclude a local
zero or denominator problem in the factors displayed in CH Corollary3.7.
They do not determine the valuation of every global period/congruence
constant in that reciprocity formula.

Let P=(0,0), Q=(1,0), and use omega_E=dx/(2y+1). Exact rational addition
gives

\[
z([9]P)=20\pmod{25},\qquad z([9]Q)=10\pmod{25},\qquad z=-x/y.
\]

Both points [9]P and [9]Q lie in the formal subgroup, and both parameters
have valuation1. The integral invariant differential yields
log(z)=z+sum_(n>=2) b_(n-1)z^n/n with b_i in Z5. Since n-v5(n)>=2 for
n>=2, the remainder is0 modulo25. Dividing by9 therefore gives

\[
\log_5(P)=5\pmod{25},\qquad \log_5(Q)=15\pmod{25}.
\]

In particular localization is nonzero. In the Q5-basis P,Q of their span,
the normalized strict regulator vector

\[
R=\frac{\log_5(Q)}5 P-\frac{\log_5(P)}5 Q
\]

has coordinates (3,-1) modulo5. This is a coordinate statement in that
rational-point basis; it does not assert that P,Q form a saturated integral
Mordell--Weil basis. The root task develops higher precision separately.

The supplied grouped theta coefficients (5,-1,-1,5,-8) have moments
(0,-20,-34). The norm-element correction has T-expansion T^4 modulo5.
Thus ordinary regularization multiplies the nonzero quadratic residue1
by alpha5^(-2)=4 modulo5. This small recomputation agrees with the supplied
certificate, without rerunning its140-root construction.

## 4. The pilot corollary now available

**Conditional only on the explicitly supplied classical/theta bridges, the
completed pilot implies rational rank2 and finite Sha(E/Q)[5^infinity].**

Precisely, use the following inputs:

1. The supplied package's identification of the finite CM/Brandt computation
   with the Chida--Hsieh theta element, including its exact lower zeros and
   its nonzero quadratic coefficient, so ord_T Theta=2.
2. The CH hypotheses established by its arithmetic audit: p=5>3 good
   ordinary, split K, eligible unramified psi, nonzero auxiliary central
   values, the root number and L(E,1)=0, residual irreducibility and
   ramification, and positive rational rank. The prior rational-interval
   twist certificate is an independent alternative for one L-value input.
3. The published CH Theorems A/B, interpreted with the finite coefficient
   extension explained above.
4. The previous `eligibility/arithmetic/README.md` certificate that P,Q are
   Z-independent, using reduction at3,7,11, rather than merely one
   nontorsion point.

Inputs1--3 give kappa_L nonzero and dim_L(S tensor L)=2, hence dim_Q5 S=2.
Input4 gives dim_Q5(E(Q) tensor Q5)>=2. The global Kummer injection bounds
this dimension by dim S, so it equals2. In the exact sequence

\[
0\longrightarrow E(\mathbf Q)\otimes\mathbf Q_5
\longrightarrow S\longrightarrow V_5\Sha(E/\mathbf Q)\longrightarrow0,
\]

the quotient is therefore0. The 5-primary Sha group is cofinitely generated
over Z5; zero divisible corank makes it finite. This proves the stated
corollary without assuming finite Sha in order to identify S with the
Kummer image.

It does not prove that the 5-primary group is trivial, finiteness of every
primary component, the full BSD leading-term formula, or a uniform theorem
for analytic-rank-two curves. In particular no inference about the order
of Sha follows merely from the unit theta coefficient.

For this pilot the nonzero strict Kato line now belongs to the Kummer image
because S equals that image. This is a conclusion obtained using the two
known independent rational points; it does not remove that arithmetic
input in a general construction.

## Sources, execution, and limits

Primary theorem: Castella--Hsieh, *On the nonvanishing of generalised Kato
classes for elliptic curves of rank2*, Forum of Mathematics, Sigma10(2022),
e12. Published pp.3--7, Theorems A/B; Corollary3.7 on p.18; Section5.
https://web.math.ucsb.edu/~castella/Kato-print.pdf

The supplied source package provides `research/theta-certificate.md` and
`research/arithmetic-audit.md`, and the exact CM/Brandt data extracted here.
The local preexisting package provides the independent rational-point and
twist-interval certificates.

Run from `research/bsd-localization/`:

```sh
python p5/check_refinements.py --check p5/result.json
```

All computations here use Python integers and fractions. The descent,
formal-group, and Selmer interpretations are mathematical arguments in
this note, not new Lean formalizations.
