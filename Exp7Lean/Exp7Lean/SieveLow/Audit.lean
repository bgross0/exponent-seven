import Exp7Lean.SieveLow.Assembly

/-!
# Axiom audit for `Exp7.SieveLow`

Every line below must report only `propext`, `Classical.choice`, `Quot.sound`.
-/

open Exp7.SieveLow

-- Core.lean: the generic sieve
#print axioms Fam.ofCond_sound
#print axioms groupOkF_sound
#print axioms leafLo_sound
#print axioms Task.ok_sound
#print axioms Task.sound
-- Stmt.lean
#print axioms LowStatement.glue
#print axioms witOk_sound
-- XSieve.lean: the sieve over x for one y, the ranges of y
#print axioms famX_sound
#print axioms tabPats_sound
#print axioms XC.ok_sound
#print axioms XC.sound
#print axioms XT.ok_sound
#print axioms YC.ok_sound
#print axioms UpTo.range
#print axioms low_of_upTo
-- QSieve.lean: the sieve over q, the exceptions
#print axioms famQ_sound
#print axioms qOk_sound
#print axioms q_sound
#print axioms famY_sound
#print axioms nosolOk_sound
#print axioms low_of_q
-- Assembly.lean
#print axioms mem_lowPrimes
#print axioms lowStatement_of_cert
#print axioms searchLow_of_primes
#print axioms searchLow_of_done
