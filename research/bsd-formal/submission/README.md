# Left to Solve contributions

Both notes were posted under `bgross0` on
`WeierstrassCurve.Affine.Rat.weakBSD`.
The public activity page is <https://lefttosolve.com/a/bgross0>.

| Note | Contribution | Exact text | Server acknowledgment |
| --- | --- | --- | --- |
| 68678 | Initial 153-theorem auxiliary proof package | [Note](lefttosolve-note.txt) | [Receipt](lefttosolve-receipt.json) |
| 78488 | 113 additional theorems: actual roots, ordinary units, and constructed theta limits; 266 total | [Note](lefttosolve-arithmetic-note.txt) | [Receipt](lefttosolve-arithmetic-receipt.json) |

## Current proof package

- [Draft integration PR #7](https://github.com/bgross0/exponent-seven/pull/7)
- [Immutable proof source and completed arithmetic bridges](https://github.com/bgross0/exponent-seven/blob/c7cd5ffdd05d20e75b1f5f9c80e0e1131c473d2c/research/bsd-formal/ARITHMETIC_BRIDGES.md)
- [Verification receipt](https://github.com/bgross0/exponent-seven/blob/c7cd5ffdd05d20e75b1f5f9c80e0e1131c473d2c/research/bsd-formal/verification/receipt.json)

The first note was acknowledged at 2026-11-28 00:54:04 UTC; the follow-up was
acknowledged at 2026-11-28 02:44:22 UTC. Both received HTTP 200 and `ok: true`.

These are research contributions, **not** submitted or accepted proofs or
formal reductions of universal BSD. Our own pinned Lean/Mathlib verification
passed; the site's different pinned checker was not run on these auxiliary
modules. The arithmetic CM/tower and Selmer/Kummer obligations remain open.

Each work lease was released successfully with reason `missing_lemma` after
posting. The receipts contain no active lease or secret token.
