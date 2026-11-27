# Independent replay of the actual Katz certificate

The downloaded run `46059120633`, built from the `8726d59` branch state,
contains the actual level389 finite Katz calculation. The replay entry
point is `replay_actual_katz.py`; its receipt is
`actual-katz-replay.json`. The replay requires ordinary Python, NumPy, and
SymPy, with no local Sage installation.

```sh
python research/bsd-localization/projection_backend/replay_actual_katz.py \
  --artifact-root /workspace/scratch/50ed92e4bf2d/bsd-geometry-downloads/katz-success-8726d59 \
  --check research/bsd-localization/projection_backend/actual-katz-replay.json
```

## What the replay establishes

The short checkpoints cover all coefficients through q389. The independent
classical dimensions are33,99,163 in weights2,4,6. The script recomputes
every selected product, explicit Eisenstein row, and scaled Serre
derivative. It then replays each simultaneous division by5, checks every
coefficient's divisibility, and verifies a full-rank coefficient minor
modulo5 in each final basis. The independent Sturm bound is checked from
the level index390. No expensive rational row reduction is used.

The M2 modular-space construction is inherited from the recorded Sage
computation. As an independent arithmetic calibration, the replay derives
the pilot elliptic coefficients through q389 from finite-field point
counts and Hecke recurrences and verifies their exact membership in the
saved M2 span. This distinguishes the independent arithmetic check from
a claim to have rebuilt all33 modular forms without Sage.

For the matrix, the replay uses E from `katz/katz-capsule.json.gz` together
with the separate `katz/katz-matrix-fit.json.gz`. It checks their common
precision metadata and the canonical residue-matrix digest. It then
verifies the full finite coordinate equation

    E_short^T A_lift^T = U5(E)^T  (mod5^8),

and both scaled inverse identities for the1333-dimensional pivot minor.
The sharp inverse guard is1, so any compatible exact integral coordinate
solution is uniquely determined modulo5^7. The released A is reduced
modulo5^6; its equality with the operator in the gated capsule is checked
entry by entry. The full reduced equation U5(E)=A E is also checked.

The basis contains6830 coefficients per row; the finite equation uses1366
samples per row, hence1,820,878 coefficient equations. The script separately
checks the ordinary/critical root labels, their polynomial X^2+3X+5, both
fixture q1 normalizations, and all2732 fixture U5 identities modulo5^8.
It records hashes of the five actual source artifacts it consumes.

These are finite certificate checks. They do not establish a CM input
fit, a geometric infinite-operator comparison, an omitted-tail bound, a
nonzero localization, or a global BSD conclusion.

## The regression receipt mismatch and its exact cause

After the Sage coefficient-count correction, `check_projection.py --check`
reported one difference. It was solely the hash of
`de_rham_strategy/result.json` stored at
`actual_crystalline_two_slope_regression.source_sha256`:

    old 5654f8cf30854cbeedf03d5e2359bf9769bd79fd3ce580c39980759ea438aafc
    new f37d632ec5ca7c7193cc073e98284a45b7a90e069583fe3884dd1ee58738bad7

Every computed scalar, precision, coordinate, and rejection check was
unchanged. The prior hash was reconstructed exactly from the current
calibration JSON by removing the newly added `Sage_sturm_q_precision`
field from each job row and subtracting5 from each `q_precision_exclusive`.
No other field was altered in that reconstruction.

The receipt was therefore updated by changing that one hash only. This
documents the corrected source's coefficient-count convention; it does
not replace or relax a numerical expectation. The regression then passed.
