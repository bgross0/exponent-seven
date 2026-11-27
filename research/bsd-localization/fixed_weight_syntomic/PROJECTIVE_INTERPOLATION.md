# Conditional interpolation of the full projective line

Date: 2026-11-27.

This note proves a local analytic lemma that uses the fixed-weight
identity in `README.md`. It **does not construct the required arithmetic
family**. Its value is to specify exactly what comparison at classical
weights would suffice, and to remove the temptation to substitute k=1
into p^(k-1) or (k-2)!.

## 1. Precise premise

Let D be the fixed two-dimensional proper elliptic de Rham space over a
finite extension L of Q_p, with geometric Frobenius F. Let

\[
 N(F)=I-\chi_f(p)^{-1}F^2/p^2
\]

be invertible. Work on a small weight disk around s=k-1=0 with coordinate
W=(1+p)^s-1. Let a(W),c(W) be nonvanishing analytic functions giving the
ordinary Hecke roots of g,h, and hold their tame characters fixed.
Define

\[
 C(W)=\left(I-\frac{a(W)\chi_h(p)}{c(W)p}F\right)
       \left(I-\frac{\chi_g(p)c(W)}{a(W)p}F\right).
\]

Assume C(0) is invertible; shrink the disk so C(W) remains invertible.
For the weight-one CM pilot this follows directly from purity: a(0),c(0)
and the character values are roots of unity, whereas the eigenvalues of
F have complex absolute value sqrt(p).

Suppose two D-valued analytic functions A(W),Z(W), neither identically
zero, have been constructed. The analytic product construction supplies
the candidate A. The substantive **additional arithmetic premise** is:

> At every sufficiently large classical weight
> k_n=1+2(p-1)p^n, the actual full two-coordinate vector Z(W_n), in a
> specified common de Rham trivialization, is a nonzero scalar multiple
> of the proper syntomic vector Pi xi_(k_n) for the same cusp-normalized
> diagonal cycle and tame test vector as in the fixed-weight lemma.
> At those weights A(W_n) is the corresponding proper inverse-Bol product.

This sequence lies in the BSV classical congruence class modulo
`2(p-1)`. The same proof works for any fixed positive p-adic unit
multiple of `(p-1)p^n`; changing from one such sequence does not change
the analytic germ or its leading direction.

Here W_n=(1+p)^(2(p-1)p^n)-1. The scalar is allowed to depend arbitrarily
on n. No bound or analyticity of it is assumed. Any non-scalar comparison
matrix, Tate-trivialization change or test-vector map must already be
included in the definition of Z: it cannot be hidden in that scalar.

This premise is stronger than matching the ordinary scalar pairing. It
does not follow merely from the known analyticity of A or from the
existence of an Iwasawa class without a full de Rham comparison.

## 2. The lemma

Under these hypotheses put

\[
 M(W)=C(W)^{-1}F^{-1}N(F).
\]

Then

\[
 \boxed{\quad M(W)^{-1}Z(W)\wedge A(W)=0\quad}       \tag{1}
\]

as an analytic germ at W=0. Thus Z and M A define the same meromorphic
projective line near zero. This assertion permits either vector to vanish
at zero.

### Proof

At the integer k_n set q_n=p^(k_n-1). The exact fixed-weight factorization
is

\[
 S_n=\left(I-\frac{p q_n}{a(W_n)c(W_n)}F^{-1}\right)
      \left(I-\frac{\chi_f(p)^{-1}q_n}{p a(W_n)c(W_n)}F\right).
\]

Equation (10) of the fixed-weight note, together with the arithmetic
premise, gives

\[
 Z(W_n)\ \parallel\ S_n^{-1}M(W_n)A(W_n).            \tag{2}
\]

The factorial, power p^(k_n), inverse ac and global sign have disappeared
by taking a projective relation at this fixed n. No value for any of these
scalars at k=1 has been assigned. The matrices S_n and M(W_n) commute,
since each is a rational expression in the same fixed F with scalar
coefficients.

Put B(W)=M(W)^(-1)Z(W). Equation (2) implies

\[
 (S_n B(W_n))\wedge A(W_n)=0.
\]

Choose any lattice in D and restrict to a smaller closed disk. A,B and
the inverses of a,c are bounded there. The explicit expression for S_n
then gives a constant C_0, independent of n, such that

\[
 v_p\bigl((B\wedge A)(W_n)\bigr)
 =v_p\bigl(-((S_n-I)B(W_n))\wedge A(W_n)\bigr)
 \ \ge\ k_n-1-C_0.                                 \tag{3}
\]

Use any fixed basis of the one-dimensional space exterior-square D for
this valuation. Changing the lattice or basis only changes C_0.

For p>2,

\[
 v_p(W_n)=n+1,\qquad k_n-1=2(p-1)p^n.
\]

If the analytic function J(W)=B(W) wedge A(W) were not identically
zero, it would have a finite order m at zero: J(W)=W^m u(W), where u is
analytic and u(0) is nonzero. For all sufficiently large n,

\[
 v_p(J(W_n))=m(n+1)+v_p(u(0)).
\]

This grows linearly in n, contradicting the exponential lower bound
(3). Therefore J=0 as a germ, which proves (1). This is the entire
argument; it requires no analytic interpolation of q_n or of a factorial.

## 3. What happens to the first nonzero coefficients

Suppose

\[
 A(W)=W^u A_u+O(W^{u+1}),\qquad
 Z(W)=W^v Z_v+O(W^{v+1}),
 \quad A_u,Z_v\ne0.
\]

Taking the first possibly nonzero term of (1) gives

\[
 \boxed{\quad Z_v\ \parallel\ M(0)A_u.\quad}       \tag{4}
\]

It does **not** prove u=v, determine the scalar of proportionality, or
construct division of a global class. In particular the premise cannot
be used to infer an arithmetic nonzero localization merely from the
analytic product being nonzero. Its consequence is a full projective
coordinate comparison, conditional on the stated arithmetic family.

## 4. Explicit pilot matrix, still conditional on Section 1

For p=5 and the pilot elliptic curve,

\[
 F^2+3F+5I=0,\qquad \chi_f(5)=\chi_g(5)=\chi_h(5)=1.
\]

Set

\[
 t=a(0)/c(0),\qquad \tau=t+t^{-1}.
\]

This tau is defined by the **ratio of the two ordinary roots**. The
project's exact ideal convention checks its value as follows. With
omega^2-omega+18=0 and a_2=(2,omega), the two norm-five ideals have
representatives

    (-2+3 omega)/a_2^5,       (-2+omega)/a_2^2.

Their principal norms are 160=5*2^5 and 20=5*2^2, respectively. Their
numerators lie in a_2^5 and a_2^2: the chosen lifts of omega modulo 32
and 4 are 22 and 2. For omega=2 modulo5 the first numerator is a local
unit and the second is not; for omega=4 the roles reverse. Since the
coefficient convention is psi(a_2)=zeta7, psi((alpha)/a_2^j)=zeta7^(-j),
the ordinary roots of g are zeta7^2 and zeta7^5, respectively. The roots
of h are their inverses, because h uses the inverse class character and
the same CM type. This reproduces `reflected_pilot/cm_weight_jets.py`'s
normalized a_5 convention using exact small ideal witnesses.

Consequently both embeddings give

\[
 \tau=\zeta_7^3+\zeta_7^4
      =1-\xi-\xi^2,\qquad \xi=\zeta_7+\zeta_7^{-1}.
\]

Thus the trace agrees with the separate depletion calculation, after
checking the root ratio rather than identifying the symbols by name.

Then

\[
 C(0)=\frac{20I-(5\tau+3)F}{25},\qquad
 N(F)=\frac{30I+3F}{25},
\]

and exact reduction modulo F^2+3F+5I gives

\[
 \boxed{
 M(0)=-\frac{3}{5(5\tau^2+18\tau+25)}
             \bigl((5\tau+23)I+(5\tau+11)F\bigr).}  \tag{5}
\]

Its exact inverse in this normalization is particularly simple:

\[
 \boxed{\quad M(0)^{-1}
     =\frac{10(\tau+1)I+(5\tau+11)F}{9}.\quad}       \tag{5a}
\]

On any integral F-stable lattice this inverse is integral; M(0) has at
most a one-digit denominator. This is a matrix norm statement, not a
claim that the arithmetic comparison uses this lattice or normalization.

Hence the two directions of the conditional projective comparison are

\[
\begin{split}
 Z_v&\parallel\bigl((5\tau+23)I+(5\tau+11)F\bigr)A_u,\\
 A_u&\parallel\bigl(10(\tau+1)I+(5\tau+11)F\bigr)Z_v.
\end{split}                                                    \tag{6}
\]

The denominator is nonzero by the invertibility already proved. More
explicitly, det C(0)=(5 tau^2+18 tau+25)/25 and
det N(F)=27/25. If t is a nontrivial seventh root of unity, tau is a
5-adic unit and 5 tau^2+18 tau+25 is a unit. These are exact algebraic
observations, not a numerical assertion about the bad line.

Equations (5)--(6) only give the matrix that the stated arithmetic premise
would force. They neither identify the arithmetic line im(P_0) nor prove
that the proposed DL line is that line. The common de Rham trivialization
and cycle-to-Iwasawa comparison remain to be checked.
`check_identity.py` verifies (5), (5a) and the norm-five convention witnesses
by exact reduction in Q[tau,F]/(F^2+3F+5).
