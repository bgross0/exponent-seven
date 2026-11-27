# A curve-independent finite line-separation contract

## Exact mathematical content

Let p be an odd prime and let F(X) be a monic integer polynomial
irreducible modulo p. It defines an unramified integer coefficient
ring `O_L=Z_p[theta]/F(theta)`, with the integral basis
`1,theta,...,theta^(d-1)`.

The input supplies two primitive integral vectors `a,b in O_L^2`,
in the same named basis of a two-dimensional vector space. Each
coordinate is given modulo `p^N`. It **claims** that these are
representatives of the true analytic leading line and the true
exceptional line with coordinate errors in `p^N O_L^2`.

The checker validates the finite field, the residue format, the
matching basis identifiers, and primitivity, then computes

\[
                   d_N=a_1b_2-a_2b_1\pmod{p^N}.
\]

If d_N is nonzero, the true determinant cannot be zero: perturbing
either integral vector by an element of `p^N O_L^2` changes the
determinant by an element of `p^N O_L`. The exact valuation of
the determinant is the least valuation of its polynomial-basis
coefficients, and is strictly below N. Thus the true lines differ,
**provided the input's mathematical identification and precision
claims have been proved**.

A zero residue is inconclusive. It is compatible with equal
lines and with distinct lines separated only at higher precision.

## What is and is not checked

`certificate_checker.py` uses only standard Python and exact integer
arithmetic. Trial division checks primality within the stated
32-bit bound. Rabin's finite-field criterion checks irreducibility.
Polynomial multiplication and reduction are performed modulo p^N.

It does not verify that a finite CM fit equals an infinite analytic
coefficient, that a proposed exceptional line comes from the actual
normalized regulator, or that a global theorem's hypotheses hold.
The required `source_bindings` fields make those obligations visible;
they are copied into the result as unverified references. A source
reference string is not a proof certificate. The result always
lists the unverified mathematical obligations.

The result also hashes the exact input file. This binds the
arithmetic receipt to the reviewed finite data; it does not
authenticate the provenance of those data.

The schema supports odd p <= 2^31-1, precision 1 through 1024,
and unramified degree 1 through 64. These are implementation
limits, not restrictions of the mathematical criterion. Ramified
coefficient rings require a different valuation/basis contract.

## Coordinate and precision conventions

`modulus_polynomial` lists coefficients in increasing degree.
The last coefficient must be exactly one. Each field coordinate
has exactly d canonical integer residues between zero and p^N-1.
There are exactly two field coordinates per vector.

Primitive means at least one polynomial-basis coefficient is a
unit modulo p. Multiplying a true vector by a nonzero scalar does
not change its line, but a normalization involving p-powers or
nonintegral matrices changes its error bound. The producer must
recompute that bound before using this uniform p^N contract.

There are two equivalent input conventions:

1. `analytic=A_m`, `exceptional=K_lead^(-1)*zeta`; or
2. `analytic=K_lead*A_m`, `exceptional=zeta`.

Both vectors must use the same convention and basis. The checker
does not infer a matrix from their values. The source bindings
must state which convention was used.

## Generic example

`certificate-example.json` is a deliberately non-arithmetic toy:

\[
 p=7,\quad\theta^2=-1,\quad N=3,
 \qquad a=(1,\theta),\quad b=(1,\theta+7).
\]

The polynomial X^2+1 is irreducible modulo seven and the
determinant is exactly seven. The checker returns
`CERTIFIED_DISTINCT`, valuation one. Reducing the input to only
one digit returns `INCONCLUSIVE`, correctly: the two lines have
the same residue modulo seven.

## First-pilot finite adapter

`pilot-line-certificate.json` uses the first pilot's already
corrected vector and exceptional line in its common stabilization
basis. Its certified scaled ratios give primitive representatives

\[
                  a=(5,21),\qquad b=(5,86)\pmod{125}
\]

over the unramified cubic ring defined by
`X^3+X^2-2X-1`. Their determinant is

\[
                   5\cdot86-5\cdot21=325=75\pmod{125},
\]

with valuation two, hence nonzero. This independently checks
the finite last step of the pilot's direction test. It neither
reproves the projection error bounds nor fills a geometric
specialization gap. The repaired arithmetic comparison has its
own proof in `BSV_REPAIR.md`.

## Commands and exit codes

From the package root:

```sh
python general_criterion/certificate_checker.py general_criterion/certificate-example.json
python general_criterion/certificate_checker.py general_criterion/pilot-line-certificate.json
python general_criterion/test_certificate.py
```

Use `--output path.json` to save the JSON receipt. Exit codes are
zero for `CERTIFIED_DISTINCT`, two for `INCONCLUSIVE`, and one
for `INVALID`.

The tests check both examples, insufficient precision, coincident
residues, unit rescaling, common integral basis changes, the
degree-one field, exact irreducible-polynomial counts through
degree four, repeated factors, and fourteen malformed or
incompatible inputs. None of these tests claims to check the
arithmetic hypotheses in the main theorem.
