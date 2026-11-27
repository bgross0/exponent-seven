# BSD rank-two research: an exact theta certificate

Research checkpoint: **27 November 2026**.

For

\[
E:\ y^2+y=x^3+x^2-2x\quad(389.a1),\qquad
K=\mathbf Q(\sqrt{-71}),\qquad p=5,
\]

this package gives an exact computational certificate, with an explicit mathematical bridge to the anticyclotomic theta construction, for

\[
\boxed{\operatorname{ord}_T\Theta_{E/K,5}=2.}
\]

Its quadratic coefficient is a 5-adic unit in the primitive integral normalization. The calculation uses the full class group of the order of conductor 25 in K. That class group has **140 elements**. The coefficient certificate was reproduced independently in Python and PARI/GP; the Python verifier independently reconstructs the class polynomials with rigorous complex ball arithmetic.

The accompanying formal project proves **15 algebraic theorems in Lean**, including exact lower-order vanishing from inversion symmetry and the soundness of the finite-level coefficient certificate. The arithmetic CM/Jacquet–Langlands/theta correspondence uses the cited classical theorems and is documented in the research notes. It has not been formalized end to end.

## The exact finite witness

Let gamma be the image in the first anticyclotomic quotient of the norm-two ideal-class generator of Pic(O_25). Grouping the 140 CM values by their image in this cyclic quotient of order five gives

\[
G(\gamma)=5-\gamma-\gamma^2+5\gamma^3-8\gamma^4.
\]

Putting gamma = 1 + T yields

\[
G(1+T)=-20T-34T^2-27T^3-8T^4,
\qquad [T^2]G\equiv1\pmod5.
\]

The raw finite sum has linear coefficient **−20**, not zero. Exact vanishing of the first two coefficients belongs to the infinite theta element and is proved separately using its interpolation formula and functional equation. The verifier never promotes a modular zero into an exact zero.

Ordinary regularization changes the raw sum by an invertible scalar and a lower-level norm term. The latter has zero quadratic jet modulo five because

\[
\sum_{j=0}^4(1+T)^j\equiv T^4\pmod5.
\]

The ordinary unit root is alpha_5 = 2 modulo 5. In the Chida–Hsieh §4.2 convention and the recorded primitive eigenfunction, the regularized quadratic residue is **4 modulo 5**. Sign, unit, CM-basepoint, and generator changes can change this displayed residue; its nonvanishing is invariant. The separate conductor-five class sum is also checked to vanish exactly, although that stronger check is unnecessary for the quadratic residue.

## What the certificate implies

The arithmetic audit verifies the hypotheses of Castella–Hsieh Theorems A and B for this example, allowing the finite coefficient extension Q_5(zeta_7). In particular:

- The quadratic-twist modular-symbol sum is exactly **−4**, proving L(E^(-71),1) is nonzero.
- The seven conductor-one CM function values are **[−1, −1, 0, 1, 1, 0, 0]**. They are not constant. Irreducibility of the seventh cyclotomic polynomial gives nonzero toric periods for every nontrivial order-seven class character; the Gross period formula gives the required auxiliary L-value nonvanishing.
- The mod-five representation is absolutely irreducible and is ramified at 389. The prime five is good, ordinary, and split in K.
- The rational point (0,0) has infinite order: the good reduction group orders at 3 and 7 are 6 and 13, so rational torsion is trivial.

Applying the published criterion therefore gives nonzero diagonal generalized Kato classes for the selected auxiliary character and a two-dimensional Q_5 Selmer group. This is an explicit computational application of existing theorems. The package makes no claim that this individual example is new in the literature.

The general rank-two BSD problem, the leading-coefficient formula, and the proposed removal of the positive-Mordell–Weil-rank assumption remain separate research problems. A Selmer dimension statement must not be silently identified with a Mordell–Weil rank statement: the divisible part of Sha has to be accounted for.

## Why p = 5

The original arithmetic screen at p = 29 remains in the evidence. At that prime the first useful ring class group has 5,684 elements. At p = 5 it has 140, a factor of **40.6** fewer. The order-seven auxiliary character is allowed over Q_5(zeta_7), an unramified extension of degree six. This avoids imposing the unnecessary condition that its values already lie in Q_5.

K has class number seven and belongs to the completed exponent-seven classification. The BSD computation uses the whole class group. It does not substitute a class-number-one formula or multiply a principal-class computation by seven.

## Certificate construction and checking

1. Enumerate the 194 distinct roots of the Deuring polynomial over F_(389^2), obtaining all 33 supersingular j-invariants.
2. Factor the classical modular polynomial Phi_2 at every vertex, retaining multiplicities. The resulting outgoing Brandt function matrix has a unique rational eigenline with eigenvalue a_2(E) = −2. Normalize it to a primitive integer eigenfunction.
3. Compute the degree-140 Hilbert class polynomial H_(-44375). Independently reconstruct it from all reduced primitive quadratic forms using rigorous FLINT/Arb enclosures of j(tau), and isolate every integer coefficient uniquely.
4. Certify all 140 roots over the unramified quadratic extension of Q_389. Strong Hensel inequalities give at least 32 digits of precision; the comparison graph uses only four. The root balls are disjoint.
5. Use Phi_2 to exclude every incorrect horizontal neighbor. The CM theorem supplies exactly two true neighbors, and exactly two candidates survive at every root. The resulting graph is one cycle of length 140, which labels the norm-two class generator.
6. Reduce each CM root to a supersingular vertex and project the class-cycle index modulo five. Sum the exact eigenfunction values and compute the three integer moments (0, −20, −34).
7. Apply the ordinary-regularization, exact-vanishing, and finite-precision arguments in the proof note.

This is a finite certificate. No decimal estimate of an L-value is used as a proof of vanishing or nonvanishing.

## Reproduce the checks

The complete Python verifier requires Python and the pinned python-flint package:

```bash
python -m pip install -r requirements.txt
python verify_certificate.py
python -m unittest discover -s tests -v
```

With PARI/GP 2.19.1 available as `gp`, replay the independent arithmetic and CM audits as well:

```bash
python scripts/reproduce.py --gp gp
```

The formal project is pinned to Lean 4.36.0 and Mathlib commit `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`. Install that Lean toolchain, fetch the dependencies and cache in `formal/`, then run:

```bash
cd formal
lake update
lake exe cache get
python verify.py
```

Once dependencies are present and the pinned Lean tools are on PATH, run all checks from the project root:

```bash
python scripts/reproduce.py --gp gp --formal
```

The formal verification script runs the Lake build, a fresh declaration and axiom report, and `leanchecker` replay of the project module against compiled imports. All 15 axiom reports contain only `propext`, `Classical.choice`, and `Quot.sound`.

To regenerate the discovery data instead of checking the supplied witnesses:

```bash
python -m pip install -r requirements-discovery.txt
python tools/supersingular_probe.py
python scripts/generate_cm_data.py --gp gp
python tools/cm_jet_probe.py
python scripts/reproduce.py --gp gp
```

The independent checker imports neither discovery script. Eight adversarial checks cover altered class polynomials, inadequate Hensel precision, overlapping root balls, wrong isogeny multiplicities, malformed CM cycles, forged residues, and the exact-vanishing/prime-two pitfalls.

## Files

| Path | Purpose |
| --- | --- |
| `research/theta-certificate.md` | Complete mathematical assembly of the theta certificate |
| `research/arithmetic-audit.md` | Curve, characters, residual representations, exact L-value and normalization audit |
| `research/localization-obstruction.md` | Precise limit of the proposed general localization argument |
| `formal/BSDRankTwo.lean` | Fifteen proved algebraic theorems |
| `verify_certificate.py` | Independent rigorous CM and integer-arithmetic verifier |
| `scripts/arithmetic_audit.gp` | Independent modular-symbol and hypothesis verification |
| `scripts/cm_independent_audit.gp` | Independent PARI CM, Hensel, graph, and moment verification |
| `data/` | Exact witnesses, class-polynomial coefficients, roots, matrices, and moments |
| `evidence/`, `formal/verification/` | Completed replay logs and hash-bound receipts |

## The next mathematical obligation

The intended generalization is to replace the positive-rank input in Castella–Hsieh by an independent proof that localization is nonzero. The precise sufficient statement is the existence of a global Selmer class z with

\[
\log_{\omega_E}(\operatorname{Loc}_p z)\ne0.
\]

It must be proved without assuming positive Mordell–Weil rank, finiteness of the relevant Sha component, or nonvanishing of the generalized Kato class being targeted. The obstruction note gives an explicit linear-algebra model showing why the leading-term identity and duality alone do not force this conclusion. A finite-level class also needs a compatible inverse-limit lift that survives tensoring with Q_p.

The pilot now supplies a checked test case for developing such a construction. Extending the computation to further curves or exponent-seven fields would produce additional calibration data; it would not by itself prove the general localization statement.

## Primary mathematical sources

- Castella–Hsieh, [On the nonvanishing of generalised Kato classes for elliptic curves of rank 2](https://www.cambridge.org/core/journals/forum-of-mathematics-sigma/article/on-the-nonvanishing-of-generalised-kato-classes-for-elliptic-curves-of-rank-2/72ED842AB428A7ED619B1B84287A6864), Theorems A/B and §§5–6.
- Chida–Hsieh, [Special values of anticyclotomic L-functions for modular forms](https://www.math.ntu.edu.tw/~mlhsieh/research/central.pdf), interpolation, functional equation, and §4.2 regularization.
- Liu–Masri–Young, [Rankin–Selberg L-functions and the reduction of CM elliptic curves](https://sites.math.rutgers.edu/~mpy4/ReductionFinalVersion.pdf), CM reduction, supersingular pairing, and Gross period identity.
- PARI/GP, [modular-symbol reference](https://pari.math.u-bordeaux.fr/dochtml/ref/Modular_symbols.html) and [polynomial reference](https://pari.math.u-bordeaux.fr/dochtml/html/Polynomials_and_power_series.html).
- FLINT, [unique integer polynomial from complex balls](https://flintlib.org/doc/acb_poly/index.html), and [python-flint modular-j documentation](https://python-flint.readthedocs.io/en/latest/acb.html).

The source code and evidence in this package distinguish the compiled algebraic results, exact computational inputs, cited arithmetic theorems, and the remaining open research target.
