import Exp7Lean.Cond.RobustBounds

/-!
Conditional and threshold certificates: summary and axiom audit.

* `Cond/Reduce.lean`      : `primeT`, `condSum`, `condMargin`, `lt_of_condMargin`
                            (per-prime version: `p` is the least split prime);
* `Cond/Robust.lean`      : `robustSum`, `robustMargin`, `lt_of_robustMargin`
                            (threshold version: no prime below `T` splits);
* `Cond/Table.lean`       : `primeTable8400` (certified `log p`, `√p` for the primes below 8400);
* `Cond/Eval.lean`        : evaluators of `primeT f X l (±1)` and of `Jterm`, any `X`;
* `Cond/RobustCheck.lean` : `robustCheck`, `robustCheck_sound`, `RobustOK`, `lt_of_robustOK`;
* `Cond/Data/Robust*.lean`: the 26 rows of `sieve-reduction/robust26.txt` (`decide +kernel`);
* `Cond/RobustRows.lean`  : `robustRows`, `robustRows_ok`;
* `Cond/RobustBounds.lean`: `QloRobust`, `QloR`, `QloR_le`, `excludedPrimes`,
                            `mem_excludedPrimes`, `excluded_lt`, `excluded_no_solution`.
-/

#print axioms Exp7.lt_of_condMargin
#print axioms Exp7.lt_of_robustMargin
#print axioms Exp7.robustSum_eq_inertSum_sub
#print axioms Exp7.Num.primeTable8400_spec
#print axioms Exp7.Rows.robustCheck_sound
#print axioms Exp7.lt_of_robustOK
#print axioms Exp7.robustRows_ok
#print axioms Exp7.robustRow_lt
#print axioms Exp7.QloRobust_lt
#print axioms Exp7.QloR_le
#print axioms Exp7.QloR_le_of_jacobi
#print axioms Exp7.mem_excludedPrimes
#print axioms Exp7.mem_excludedPrimes_of_gt
#print axioms Exp7.excluded_lt
#print axioms Exp7.excluded_no_solution
#print axioms Exp7.excluded_search
