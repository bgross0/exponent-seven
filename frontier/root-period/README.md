# Compressing the square-root residue enumeration

**Status: compiled successfully in Lean 4.35.0 with Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`, exit status 0.** All four printed theorem dependencies are exactly `propext`, `Classical.choice`, and `Quot.sound`. The proof is intended for the exact integer arithmetic part of SearchHigh and requires no GRH hypothesis. See `verification.json` and the complete `build.log`.

The original condition is

`x^2 + 3*y^2 ≡ 4*p^7 (mod 8*y^2)`.

Every solution has `x ≡ y (mod 2)`. With this parity, translating `x` by `2*y^2*t` changes its square by

`4*y^2 * (x*t + y^2*t^2)`,

and the bracket is even. Thus the **root predicate** has period `2*y^2`. One can enumerate representatives in `[0, 2*y^2)`, retaining the original congruence test modulo `8*y^2`, and recover the four lifts in `[0, 8*y^2)`.

This does **not** justify replacing the modulus in the congruence test by `2*y^2`; that would accept extra residues. It justifies shortening the representative range while preserving the original test.

`RootPeriod.lean` contains checked proofs of:

- the parity forced by the original root condition;
- divisibility of the translated square difference by `8*y^2`;
- invariance of the root predicate, in both directions;
- invariance after reduction modulo the shorter period;
- existence of a compressed representative for positive `y`.

The congruence lemmas are formulated over integers and include `y = 0`; the bounded representative lemma assumes `0 < y` so its modulus is positive.

For `x = r + 2*y^2*t` and nonzero `y`, the quotient used in the sieve becomes

`q(t) = q0 - 4*r*t - 4*y^2*t^2`, where `q0 = (4*p^7-r^2)/y^2`.

The number of root representatives is reduced by four in a full residue interval. This is not a claim of fourfold runtime improvement: the resulting progressions are correspondingly longer.

Executed check in the isolated pinned Lean environment:

```bash
lake env lean /absolute/path/to/frontier/root-period/RootPeriod.lean
```

The file has not yet been compiled at the project's original Lean 4.37 pin or connected to the SearchHigh generator. The proof certifies the arithmetic reduction; it does not by itself prove search completeness or a measured speedup.

