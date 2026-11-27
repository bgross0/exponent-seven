# The remaining ambient global-control question

The reflected class is a specialization of ambient global Iwasawa
cohomology. The ordinary-Selmer universal-norm obstruction does not by
itself describe which of these ambient specializations happen to satisfy
the finite condition at the base. A stronger arithmetic obstruction could
still force the reflected specialization into the strict line. We have
not proved or excluded such a theorem.

For the actual global cohomology complex, the specialization sequence gives
the underlying vector-space exact sequence

\[
0\longrightarrow H^1_{\mathrm{Iw}}/tH^1_{\mathrm{Iw}}
\longrightarrow H^1(K,V)
\longrightarrow H^2_{\mathrm{Iw}}[t]\longrightarrow0.
\]

The connecting map is affected by the sign of the anti-invariant parameter
when recording conjugation actions. Thus the global H2 obstruction, not
only the ordinary Selmer module, matters for the reflected proposal.

The following two exact algebraic models show that a particular set of
theta-order and Selmer elementary-divisor data does not determine this
ambient obstruction. They are not asserted to be Galois representations,
arithmetic Selmer complexes, or to satisfy full Poitou--Tate duality.

## Two models with the same Selmer elementary divisors

Work over R=Q[[t]], with coefficient involution t -> -t. Use an ambient
complex R^3 -> R in degrees one and two, with differential D, and two
local quotient maps F+ and F-. The combined differential has rows
(D,F+,F-). Denote the coordinate basis by e1,e2,e3.

**Even-length ambient obstruction:**

\[
A_{\mathrm{even}}=
\begin{pmatrix}
0&0&t^2\\
t^2&1&0\\
t^2&-1&0
\end{pmatrix},\qquad
c(e_1)=e_1,\ c(e_2)=-e_2,\ c(e_3)=e_3.
\]

The ambient H1 is Re1+Re2 and H2 is R/(t^2). The base Selmer kernel is
Qe1+Qe3, all conjugation invariant. Its intersection with the ambient
specialization image is only Qe1.

Take kappa=(1,-t^2,0). Then D(kappa)=F+(kappa)=0, while
F+(c(kappa))=2t^2. Its reflected quotient has base value

\[
\left.(\kappa-c\kappa)/t\right|_0=0.
\]

**Odd-length ambient obstruction:**

\[
A_{\mathrm{odd}}=
\begin{pmatrix}
0&0&t\\
t^2&t&1\\
t^2&-t&-1
\end{pmatrix},\qquad
c(e_1)=e_1,\ c(e_2)=e_2,\ c(e_3)=-e_3.
\]

Here ambient H1 is again Re1+Re2, but H2 is R/(t). The base Selmer
kernel is Qe1+Qe2, all conjugation invariant, and both its directions
are ambient specializations. Take kappa=(1,-t,0). Again
D(kappa)=F+(kappa)=0 and F+(c(kappa))=2t^2, but now

\[
\left.(\kappa-c\kappa)/t\right|_0=-2e_2.
\]

In either model the original kappa specializes to e1. Give the base
Selmer space the functional ell(e1)=0, with ell(e3)=1 in the even model
and ell(e2)=1 in the odd model. The two reflected finite-logarithm
outputs are respectively zero and -2. These ell maps are part of the
abstract models, not claimed arithmetic logarithms.

In both models F- is the coefficient-conjugate of F+ composed with c,
and the ambient differential is equivariant if conjugation is +1 on
the target basis. The local reflection conventions are therefore
consistent with the displayed semilinear action.

## Exact elementary-divisor comparison

Both matrices have determinant -2t^4. Each contains a unit entry, so
its first Smith factor is a unit. Every 2x2 minor is divisible by t^2,
and each matrix has a 2x2 minor equal to a unit times t^2. The Smith
factors over R are consequently

\[
(1,t^2,t^2)
\]

in both cases. Thus both combined complexes have the same two-dimensional
base kernel, zero first lifting obstruction, and second-order elementary
divisors. They also have the same nonzero order-two reflected regulator
coefficient. Nevertheless, their ambient H2 modules and their reflected
base classes differ.

This calculation does not settle the arithmetic nonvanishing question.
It identifies what an argument using additional global control or
self-duality must actually add. Neither a deduction that the reflected
class always vanishes nor a deduction that it is always transverse follows
from these elementary-divisor data alone.

For the actual construction and its published Selmer inputs see
`DERIVED_CLASSES.md`, Section 6, and `../rationality/REFLECTED_REVIEW.md`.
