# Primary-source and implementation ledger

All URLs were inspected during this research turn. No author was contacted
and no Magma or Sage job was run remotely.

1. **Darmon--Lauder, _Stark points on elliptic curves via Perrin-Riou's
   philosophy_.**
   https://people.maths.ox.ac.uk/lauder/papers/DL.pdf
   Section1, equations(5)--(6), printedp4: the overconvergent quotient,
   residues, canonical proper Frobenius splitting, and elliptic pushforward.
   Section4, printedp11: numerical extraction of both stabilization
   coefficients; the authors explicitly cite the final sentence of LSZ
   Section6.3 for higher-slope projection. This is an actual computational
   precedent, not a proof of our still-missing arithmetic comparison.

2. **Loeffler--Skinner--Zerbes, _Syntomic regulators of Asai--Flach classes_.**
   https://discovery.ucl.ac.uk/id/eprint/10067174/1/asai_regulator.pdf
   Section6.3, printedpp40--42: computable matrix, condition number via
   elementary divisors, precision of a kernel direction, and extraction
   of a projection functional from the transposed kernel. Their example
   is a critical-slope Eisenstein series; our elliptic use needs its own
   packet isolation and tail conditions.

3. **Lauder, _Efficient computation of Rankin p-adic L-functions_.**
   https://people.maths.ox.ac.uk/lauder/papers/AgbLauderFINAL.pdf
   Algorithm2.1 and Section2.2.2, printedpp7--8: finite Katz matrix and
   first U application to the input. Note2.2(3), printedp9: matrix
   integrality caveat. Note2.3(1), printedp14: analytic radius versus
   the unproved integral-growth hypothesis used in the experiments.
   These distinctions are retained in our handoff.

4. **Lauder's author-provided code index.**
   https://people.maths.ox.ac.uk/lauder/
   The index advertises Algorithms1 and2 of the 2011 paper, with Sage,
   documented Python/Sage, and Magma sources:
   https://people.maths.ox.ac.uk/lauder/code/CCpMF-191011.sage
   https://people.maths.ox.ac.uk/lauder/code/CCpMF_131111.py
   https://people.maths.ox.ac.uk/lauder/code/CCpMF-030112.m
   The Sage source was retrieved and inspected. These are matrix/Hecke
   series routines, not a ready-made implementation of DL's full vector
   for our input. No separately advertised 2023 two-slope package was
   located on this page.

5. **Maintained Sage documentation and source.**
   https://doc.sagemath.org/html/en/reference/modfrm/sage/modular/overconvergent/hecke_series.html
   https://github.com/sagemath/sage/blob/develop/src/sage/modular/overconvergent/hecke_series.py
   `higher_level_UpGj(..., extra_data=True)` returns the matrix list, Katz
   q-basis, Sturm parameter, and working precision. The inspected source
   solves T=A E with row conventions. The runtime driver records the
   actual installed source hash and version, rather than trusting a
   moving web branch.

6. **Magma handbook.**
   https://docs.magma-maths.org/ModularArithmeticGeometry/ModularForms/overconvergent.html
   The public interface primarily exposes characteristic-series
   computations. A characteristic series by itself cannot apply the
   desired projection to an input. This is why the explicit Sage matrix
   interface is the recommended first handoff.

7. **Sage classical spaces and Atkin--Lehner conventions.**
   https://doc.sagemath.org/html/en/reference/modfrm/sage/modular/modform/space.html
   `integral_basis`, `q_integral_basis`, and `sturm_bound` supply the
   classical numerator-space operations in the finite core.
   https://doc.sagemath.org/html/en/reference/hecke/sage/modular/hecke/module.html
   The Atkin--Lehner documentation explicitly states the factor
   N^(k/2-1) relative to the determinant-normalized convention and
   W_N^2=N^(k-2) for trivial character. This is essential at weight10.

8. **Coleman, _Classical and overconvergent modular forms_.**
   https://wstein.org/people/coleman/papers/classical_and_overconvergent_forms.pdf
   Theorems5.1 and5.4 supply the cohomological quotient and U=Ver
   interpretation used throughout this project. They justify the
   cohomological meaning; they are not a numerical bound for the saved
   weight jets by themselves.

The finite pole presentation, its principal-part denominator bound, and
the trace expression for the targeted cup functional are derived in
`README.md`. They are not attributed as new named results in these papers
and carry no novelty assertion. Their mathematical proof is separate from
the unexecuted Sage backend and from the standard-library calibration
checks actually completed here.
