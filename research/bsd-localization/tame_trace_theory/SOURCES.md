# Primary-source ledger for the tame trace argument

Checked 2026-11-27. Printed page numbers are used where available.

| Source | Exact input | Use and scope |
|---|---|---|
| Robert F. Coleman, *Classical and overconvergent modular forms*, Invent. Math. 124 (1996), 215--241 | Proposition 4.3, p.222; Theorem 5.1, p.223; Theorem 5.4, p.225 | The overconvergent Bol operator, finite-dimensional cohomological quotient, and invertibility of Ver. Together these give existence of the depleted inverse-Bol primitive. The uniqueness in ker U_5 is the elementary q-expansion argument in this note. |
| Markus Schwagenscheidt and Brandon Williams, *Binary theta functions and Borcherds products*, author version 2022-11-23 | Introduction, p.2 | Confirms the usual weight-one binary-theta Fricke eigenvalue -i. The higher-weight harmonic extension is derived here by Poisson summation with the lattice and polynomial normalizations specified. |
| Nicolas Mascot, *Companion forms and explicit computation of PGL_2 number fields with very little ramification*, author version 2016-11-14 | Section 2.1; Theorem 2.2.1, p.5; Theorem 2.4.1, pp.8--9 | Independent formulas for newform pseudo-eigenvalues and oldform/Atkin--Lehner normalization. His selected odd-weight matrix convention differs from the usual Fricke by a sign; the present proof uses explicit matrices throughout. |
| Henri Darmon and Alan Lauder, *Stark points on elliptic curves via Perrin-Riou's philosophy* | Section 1, pp.4--5; Theorem 3.1 and Conjecture 3.2, p.10 | The analytic weight-two de Rham input family. The trace argument uses the analytic family, not the conjectural arithmetic derivative comparison. Its depletion convention is the one reflected by Theorem 3.1, namely depletion on the differentiated factor. |

## URLs

- Coleman: https://wstein.org/people/coleman/papers/classical_and_overconvergent_forms.pdf
- Schwagenscheidt--Williams: https://math.berkeley.edu/~btw/binarytheta_paper3.pdf
- Mascot: https://warwick.ac.uk/fac/sci/maths/people/staff/mascot/companion.pdf
- Darmon--Lauder: https://people.maths.ox.ac.uk/lauder/papers/DL.pdf

The 72-coset trace formula and the explicit matrices are proved directly
in `TAME_TRACE.md`. The finite ring computation of those traces belongs
to the separate executable trace workstream. Neither source citation nor
a finite q-jet is substituted for the still-missing arithmetic regulator
comparison.
