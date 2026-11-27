# Shared BSD handoff: reuse the completed work

Reconciled on 27 November 2026 for Ben's Number Theory Proofs project.

**The conductor-one CM computation requested by the localization branch is
complete. Reuse the certified data below. The theta calculation at 5 is also
complete; the theta calculation at 29 has not been performed by either package
at the commits reconciled here.**

This handoff is the current integration status. The two component directories
are preserved snapshots, including their original next-step sections. Statements
there that the seven CM values still need to be computed are superseded by this
handoff and its linked evidence.

## 1. Source anchors and responsibility

| Stream | Source anchor | Canonical directory in this branch | Completed contribution |
| --- | --- | --- | --- |
| Localization audit | `bgross0/exponent-seven`, branch `bsd-localization-audit`, commit `12c58ddf46ebd89141d4392b519ca7ae533e67ea` | `research/bsd-localization/` | Exact point independence and 29-adic logarithm; all-level cyclic ring-class tower at 29; rigorous twist L-value interval; strict-Kummer proposition |
| Theta certificate | Local research commit `cd494a3d8cef7fe5d2831c5fb5402ace5e4b6ac9`; archived manifest imported verbatim | `research/bsd-theta/` | Supersingular eigenline and actual CM evaluations; rigorous conductor-25 certificate; theta order two at 5; 15 Lean algebraic theorems |
| Integration | This companion branch, `bsd-coordinated-handoff` | `research/bsd-coordination/` | Actual CM values supplied to the existing cyclotomic checker; shared status, provenance, and combined theorem dependencies |

The source commit for the theta package is a provenance identifier from the
separate local research checkout; it is not asserted to be a commit already in
the remote exponent-seven history. All 43 imported files are byte-identical to
that checkout. Their existing [manifest](../bsd-theta/MANIFEST.json) binds the
source, data, and previous verification evidence. The archived package SHA-256
is `f4d0332acbe087da2dda53a9a380f41c75d3ec63c5ad59441f2a5785ef21531a`.

**Coordination acknowledgment:** the integration agent has read both packages.
The separate localization conversation has not yet acknowledged this handoff.
The proposed division of future work below must not be reported as a mutually
accepted assignment until that acknowledgment is recorded.

## 2. What is complete and what remains

| Obligation | Current status | Evidence / next action |
| --- | --- | --- |
| Quaternionic eigenline for 389.a1 | Complete | 33 supersingular vertices; the outgoing T2 matrix has a one-dimensional −2 eigenspace; primitive integral eigenfunction recorded in [canonical data](../bsd-theta/data/supersingular-389.json) |
| Seven conductor-one CM evaluations | Complete | Roots of the certified H_−71; correct cyclic ordering and exact periods in [cm-periods.json](cm-periods.json) |
| Nontrivial class-character auxiliary L-values | Complete, using the documented Gross formula | All six periods are nonzero; see Section 3 and the existing geometric and theorem notes |
| Quadratic-twist auxiliary L-value | Complete by two methods | The localization package's rigorous positive interval and the theta package's exact nonzero modular-symbol sum −4 are independent certificates of nonvanishing |
| Positive rational rank | Complete | The localization audit proves that P=(0,0) and Q=(1,0) are independent |
| Nonzero localization at 29 | Complete | The exact log(P)=29 modulo 841 certificate is in the localization audit |
| Theta order at 5 | Complete, using the documented arithmetic bridges | Theta=T²U with U(0) a 5-adic unit; first useful full ring-class group has 140 entries |
| 29-power class-group coordinates | Complete | Pic(Z+29^m O_K) is cyclic of order 196·29^(m−1), with compatible norm-two generator |
| Theta quadratic coefficient at 29 | Uncomputed | Optional separate extension: start modulo 29 at conductor 29², with 5,684 entries; reuse the eigenfunction and tower implementation |
| Numerical-appendix normalization dictionary | Open as recorded by the localization audit | The completed calculation at 5 uses the primary Chida–Hsieh definition directly; it does not settle that separate dictionary |
| General strict-class membership in the rational Kummer image | Open | Prove the geometricity statement under explicit hypotheses; another Selmer class alone is insufficient |
| General removal of positive-rank/localization assumptions | Open | Requires an independent global class with nonzero finite localization and all comparison/local-condition lemmas |
| Full rank-two BSD or the leading-coefficient formula | Open | Not a conclusion of either package or this integration |

The 15 Lean theorems concern the finite-level coefficient criterion and
power-series algebra. They do not formalize the CM, Jacquet–Langlands,
special-value, or Selmer-theoretic bridges end to end.

## 3. The exact handoff to the existing seven-value checker

The shared data source is
[`research/bsd-theta/data/supersingular-389.json`](../bsd-theta/data/supersingular-389.json).
Do not create a second supersingular matrix or another independently maintained
copy of the seven values in the localization package.

The previously displayed list `[-1,-1,0,1,1,0,0]` is in sorted supersingular
j-invariant order. It validly proves that the CM values are not constant, but
that ordering must not be used to attach individual character periods or their
cyclotomic norm.

The norm-two CM graph gives this cycle, with zero-based indices into the
canonical supersingular array and u²=2 in F_(389²):

| Cycle exponent | Supersingular index | j-invariant | Eigenfunction value |
| --- | --- | --- | --- |
| 0 | 9 | 78+112u | −1 |
| 1 | 13 | 121 | 0 |
| 2 | 10 | 78+277u | −1 |
| 3 | 22 | 181+321u | 1 |
| 4 | 28 | 347+53u | 0 |
| 5 | 29 | 347+336u | 0 |
| 6 | 21 | 181+68u | 1 |

Thus, for an arbitrary base CM point and one of the two orientations of
a=(2,omega), the cyclic vector is

\[
(v_0,\ldots,v_6)=(-1,0,-1,1,0,0,1).
\]

The adapter derives this cycle from the saved matrix. It starts at the smallest
global CM index and chooses its smaller-index neighbor as the next vertex.
It does not claim that the undirected graph distinguishes a from a^−1 or fixes
an absolute Gross-point origin. Translation multiplies a character period by
a root of unity; inversion permutes the conjugates. Both preserve the norm and
the all-six nonvanishing conclusion.

For a primitive seventh root zeta, the existing checker computes

\[
P_j=\sum_{i=0}^6v_i\zeta^{ji},\qquad
\prod_{j=1}^6P_j=49\ne0.
\]

In particular all six periods are nonzero. The product is **49** for the actual
cyclic ordering; the number 7 obtained from the sorted-j list is not the norm
of these cyclically indexed periods. Since these are algebraic integers and 49
is prime to both 5 and 29, every one of these periods is a unit at primes above
5 and 29 in this integral normalization. This is a statement about the periods;
it is not a claim about normalized central L-value units without their other
constants.

The unmodified existing checker can be run directly:

```sh
python research/bsd-localization/logic/c7_period.py \
  --values-json '[-1,0,-1,1,0,0,1]'
```

The adapter additionally checks the input provenance and cycle construction:

```sh
python research/bsd-coordination/check_alignment.py \
  --check research/bsd-coordination/cm-periods.json
```

The existing checker's `geometric_validation_performed` and
`L_value_nonvanishing_certified` fields remain false: that function performs
cyclotomic algebra only. The geometric evidence and theorem interpretation are
carried separately in the adapter report and these notes.

### Geometric bridge and weights

The exact verifier constructs the full supersingular module, checks the
eigenline, and identifies the seven distinct reductions of the rigorously
reconstructed H_−71. The CM reduction theorem identifies them with the relevant
class-group orbit. For the outgoing matrix A and stabilizer weights w_j, the
divisor eigenvector corresponding to a function eigenvector phi is

\[
g=\sum_j\frac{\phi_j}{w_j}e_j.
\]

With Gross's pairing \(\langle e_i,e_j\rangle=w_i\delta_{ij}\), one has
\(\langle e_i,g\rangle=\phi_i\). All seven CM vertices here have w_i=1. Therefore these are the
weighted pairings requested by the localization package, without inserting an
extra stabilizer factor.

The detailed identification is in the theta package's
[mathematical certificate, Sections 4–5](../bsd-theta/research/theta-certificate.md).
The applicable positive special-value formula is recorded in the localization
package's [Gross-period interface](../bsd-localization/logic/C7_AUXILIARY_PERIOD.md)
and [source ledger](../bsd-localization/literature/THEOREM_LEDGER.md).
Their combination supplies the formerly missing conductor-one class-character
factor. This conductor-one calculation is independent of the choice of
Iwasawa prime and therefore applies to the proposed calculation at 29 as well
as the completed calculation at 5.

### Keep the class-character conventions explicit

Retain the localization package's a=(2,omega) convention. It is represented by
the reduced form (2,−1,9), and [(29,omega−13)]=a^4. PARI's default
`qfbprimeform(-71,2)` instead gives the conjugate form (2,1,9).
Our theta audit labels its selected character using the class of
(29,omega−13); the localization audit labels its character using a. These
choices permute the six nontrivial characters. All-six nonvanishing supplies
either choice, but individual exponents and residues must retain their stated
convention.

## 4. The combined pilot conclusion

For E: y²+y=x³+x²−2x, the imported theta package applies the documented
Castella–Hsieh criteria at 5, over the allowed finite coefficient extension
Q_5(zeta_7), to obtain

\[
\dim_{\mathbf Q_5}\operatorname{Sel}(\mathbf Q,V_5E)=2.
\]

Here the finite extension is an extension of coefficients, not of the base
number field: finite scalar extension commutes with the cohomology and local
conditions defining this Selmer space. Thus
\(\dim_L(\operatorname{Sel}(\mathbf Q,V_5E)\otimes L)
=\dim_{\mathbf Q_5}\operatorname{Sel}(\mathbf Q,V_5E)\).
The globally nontorsion point P supplies the positive-rank input at 5 directly;
the numerical 29-adic logarithm is not transferred to a different prime.

The localization audit independently proves that P=(0,0) and Q=(1,0) are
independent rational points. The Kummer exact sequence

\[
0\longrightarrow E(\mathbf Q)\otimes\mathbf Q_5
\longrightarrow\operatorname{Sel}(\mathbf Q,V_5E)
\longrightarrow V_5\Sha(E/\mathbf Q)\longrightarrow0
\]

therefore gives rank E(Q)=2 and V_5 Sha=0. The standard cofinitely generated
structure of the 5-primary Selmer/Sha group then gives

\[
\operatorname{rank}E(\mathbf Q)=2,\qquad
\Sha(E/\mathbf Q)[5^\infty]\text{ is finite}.
\]

This is an application of existing theorems to the pilot, not a novelty claim
for this curve. It does not give finite 29-primary Sha: that version still
requires the missing theta/Selmer input at 29. It does not give finiteness of
the full Sha or its BSD-predicted order.

The exact rational-point independence proof is in
[the localization audit](../bsd-localization/logic/AUDIT.md). The hypotheses,
coefficient extension, and theorem application at 5 are in
[the theta arithmetic audit](../bsd-theta/research/arithmetic-audit.md).

## 5. Proposed next-work division

The following routing is proposed, with acknowledgment from the separate chat
still pending. Record a task's owner and starting commit before beginning a
new calculation; check the shared branch for a completed artifact first.

| Lane | Suggested owner | Next distinct deliverable | Reuse |
| --- | --- | --- | --- |
| Integration and verification | Theta/integration stream | Maintain this adapter, provenance, and shared status; review imported evidence | Both existing packages; no second C7 checker or CM producer |
| Optional 29-adic extension | Localization stream, if it elects to continue that computation | A normalized quadratic theta coefficient modulo 29 at conductor 29²; escalate only if inconclusive | Existing cyclic coordinates, complete 196-element tame fibers, shared 33-vertex eigenfunction, completed auxiliary periods |
| General geometricity theorem | One explicitly claimed owner; unassigned here | A precise theorem placing the relevant nonzero strict class in the rational Kummer image, with dependencies and attempted proof | The strict-Kummer sufficient proposition and both logical audits |
| Independent localization construction | One explicitly claimed owner; unassigned here | A global finite Selmer class with independently proved nonzero localization, including compatible lifting and local-condition proofs | The theta obstruction note; keep this distinct from the generalized Kato class in the strict kernel |

The first useful new theoretical target is **geometricity of a nonzero strict
Selmer class**, under a separately justified Selmer-dimension bound. The
localization audit proves that dimension at most two plus such a class in the
rational Kummer image forces rational rank two and finite p-primary Sha. Any
attempt must state how nonzero class and dimension bound were obtained; an
argument using the positive-rank theorem cannot be relabeled as removal of its
positive-rank hypothesis.

The general localization obstruction remains a separate problem. A generalized
Kato class known to lie in the localization kernel cannot simultaneously be
the class proving localization nonzero. Likewise a nonzero global Selmer class
does not by itself prove membership in the rational Kummer image. Keep these
two obligations separate in every proposed proof.

Further pilot computations are useful calibration, but they do not discharge
either missing general theorem. The calculation at 29 is an optional extension
of the completed pilot rather than a prerequisite for using the result at 5.

## 6. Verification and preservation

The integration verification receipts are under [evidence/](evidence/):

- The localization package's five original checks are replayed without changing
  its scripts or saved certificates.
- The relocated theta verifier is replayed, including rigorous class-polynomial
  reconstruction and the independent PARI arithmetic audit.
- The adapter is checked against its deterministic actual-data report.
- The original 43-file theta import and all 22 localization files are checked
  for exact preservation against their source commits. The preserved Lean
  sources and previous build/kernel receipts remain hash-bound by the original
  manifest; this integration does not claim a new Lean replay.

Reproduce the integration arithmetic from the repository root:

```sh
python research/bsd-localization/verify_all.py
python -m pip install -r research/bsd-theta/requirements.txt
python research/bsd-theta/verify_certificate.py --gp gp \
  --output ../bsd-coordination/evidence/p5-replay.json
python research/bsd-coordination/check_alignment.py \
  --check research/bsd-coordination/cm-periods.json
```

The PARI executable is optional for the Python verifier; omit `--gp gp` if it
is not installed. The previous independent CM replay, rejection tests, and
Lean build/kernel replay are preserved in the theta package. Their documented
commands remain available there for an independent reproduction.
