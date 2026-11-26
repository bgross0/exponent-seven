import Exp7Lean.Numerics.LogSeries
import Exp7Lean.Numerics.FixedLog
import Exp7Lean.Numerics.FixedSqrt
import Exp7Lean.Numerics.FixedExp
import Exp7Lean.Numerics.FixedArith
import Exp7Lean.Numerics.EulerGamma
import Exp7Lean.Numerics.Constants
import Exp7Lean.Numerics.Interval
import Exp7Lean.Numerics.PrimeSum
import Exp7Lean.Numerics.PrimeList
import Exp7Lean.Numerics.Checks
import Exp7Lean.Numerics.PrimeTable
import Exp7Lean.Numerics.Bench
import Exp7Lean.Numerics.BenchTable
import Exp7Lean.Numerics.RowPrototype

/-!
# Verified numerics toolkit: entry point and axiom audit

Importing this file brings in the whole toolkit.  The `#print axioms` commands below must each
report exactly `[propext, Classical.choice, Quot.sound]`.
-/

open Exp7.Num

#print axioms logLo_le
#print axioms le_logHi
#print axioms log_mem
#print axioms logRatioLo_le
#print axioms le_logRatioHi
#print axioms sqrt_mem
#print axioms expLo_le
#print axioms le_expHi
#print axioms expNegLo_le
#print axioms le_expNegHi
#print axioms P20_valid
#print axioms P20w_valid
#print axioms log_two_mem
#print axioms pi_mem
#print axioms log_pi_mem
#print axioms gamSeq_sub_le_gamma
#print axioms gamma_le_gamSeq_sub
#print axioms gamma_mem
#print axioms FI.has_mul
#print axioms FI.has_div
#print axioms FI.has_log
#print axioms FI.has_sqrt
#print axioms FI.has_exp
#print axioms RExpr.eval_sound
#print axioms RExpr.pos_of_isPos
#print axioms isPrimeB_iff
#print axioms mem_primeList6400
#print axioms log_sqrt_accuracy
#print axioms log_mem_6400
#print axioms sqrt_mem_6400
#print axioms exp_neg_mem
#print axioms rowConst_mem
#print axioms primeTable6400_spec
#print axioms primeTable6400_complete
#print axioms fmulLo_le
#print axioms le_fdivHi
#print axioms le_fpowHi
#print axioms bench_enclosure
#print axioms bench_enclosure_list
#print axioms bench_enclosure_table
#print axioms tableSumBelow_le
#print axioms listSumBelow_le
#print axioms sumPrimes_le
#print axioms fdivLo_le
#print axioms fpowLo_le
#print axioms le_fmulHi
#print axioms FI.has_inv
#print axioms FI.has_add
#print axioms RExpr.lt_of_isPos
#print axioms RExpr.mem_of_eval
#print axioms ctx20_valid
#print axioms P26_valid
#print axioms primeTable6400_check
#print axioms RowProto.row0_check
