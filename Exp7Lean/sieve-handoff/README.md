# Packed-bitset search formalization handoff

**Status:** draft, NOT a compiled Lean proof of SearchHigh or SearchLow. The pilot is executed Python code; the Lean primitives are uncompiled because the originating environment lacks Lean/Mathlib. No changes to main or the production imports.

The files are:
- ../Exp7Lean/SieveKernel.lean: draft packed-bitset soundness lemmas.
- pilot.py: exact integer pilot for p=701, y=1.
- pilot-result.json: original output.

## Immediate integration

From the project root, after fetching this branch, bring the new files into the active working tree (do not overwrite unrelated Claude work). Then:

    cd Exp7Lean
    lake env lean Exp7Lean/SieveKernel.lean
    python3 sieve-handoff/pilot.py

Audit the actual axioms of the soundness lemmas. Repair any compilation errors before relying on them. The toy example is deliberately tiny. In the latest main, the target is Exp7.SearchHigh from Final2.lean (also used by Final3.lean). No external computation or log should be asserted as a proof of this proposition.

## Pilot (executed)

The norm bound at p=701 makes y=1, and q=3 mod 8 forces x odd. Write x=2t+1, with 0<=t<2383564743. Wheel W=255255=3*5*7*11*13*17. All residues in [0,W) are explicitly checked; 3456 remain. For each r, t=r+W*k. For each further prime l, generate the allowed period-l bitmask B_l(k) from the quadratic nonresidue condition for x=2W*k+1. The appropriate phase is (r*W^-1) mod l; its correctness follows from x congruence modulo l. The finite progression has n=floor((T-1-r)/W)+1 positions. Intersect shifted periodic masks with the low n bits set. All masks become zero by l=137. Exact Python integers, independent of production logs.

## Next proof obligations

1. Compile and repair SieveKernel.lean. In particular check actual Mathlib bitwise APIs, and normalize phase addition orientation as needed.
2. Build a p=701 driver: prove norm and parity reductions, enumerate wheel residues with range/filter, generate masks via makeBits, prove phase invariance by modular congruence. Check all 3456 masks with kernel decide in shards. This step is NOT implemented yet.
3. Generalize to y>1. Generate or certify all roots modulo y^2 (Hensel/CRT), check q mod 8 via roots mod 8*y^2. When l does not divide y, the Jacobi symbol condition becomes a nonresidue condition on x^2-4p^7. When l divides y, omitting the mask is safe for exclusion; check exact q if a candidate survives. Use exact bounds for x,y and shard coverage. SearchHigh does not assume p does not divide y, so do not silently add that hypothesis. SearchLow does include it.
4. Prefer bounded-width or chunked kernel reductions; profile p=701 before scaling. The full search has trillions of positions after the wheel. Do not treat a hash or a zero log as proof of completeness. If native_decide is considered, explicitly document its larger trust base. For the lower range, prove inclusion in survivorQs rather than zero intersection.
5. Only after a successful build and axiom audit, instantiate SearchHigh and SearchLow in the final theorem. Keep GRH explicit.

References: Mathlib.Data.Nat.Bitwise, Init.Data.Nat.Bitwise.Lemmas, Batteries.Data.Nat.Lemmas, Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol.
