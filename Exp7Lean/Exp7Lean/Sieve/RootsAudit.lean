import Mathlib
import Exp7Lean.Sieve.RootsCert

/-!
# Axiom audit for `Exp7.Roots`

Every line below must report only `propext`, `Classical.choice`, `Quot.sound`.
-/

open Exp7.Roots

-- Goal 1
#print axioms sq_modEq_odd_prime_pow
#print axioms complete_odd_prime_pow
-- Goal 2
#print axioms powMod_eq
#print axioms not_sq_of_eulerNonRes
#print axioms complete_of_eulerNonRes
#print axioms isOddPrimeB_sound
#print axioms isOddPrimeF_sound
-- Goal 4
#print axioms invMod_spec
#print axioms crt_modEq_left
#print axioms crt_modEq_right
#print axioms crt_lt
#print axioms mod_mul_eq_crt
#print axioms Complete.crt
#print axioms crt_glue
-- Goal 3
#print axioms sq_modEq_four_mul_two_pow
#print axioms not_sq_two_pow_of_mod_eight
#print axioms not_sq_two_pow_of_mod_four
#print axioms sq_modEq_two_pow
#print axioms complete_two_pow
#print axioms complete_twoRootsOdd
#print axioms Complete.liftTwo
-- Goal 5
#print axioms twoList_complete
#print axioms rootsOf_complete_core
#print axioms rootsOf_complete_with
#print axioms rootsOf_complete
#print axioms rootsOf_complete_int
#print axioms rootsOf_complete_dvd
#print axioms rootsOf_sound
#print axioms mem_rootsOf_iff
#print axioms noRoots_of_nonres
#print axioms noRoots_two
#print axioms yRoots_complete
#print axioms rootsOf8_complete
#print axioms rootsOf8_complete_quot

/-- A `decide +kernel` certificate check, to audit the axioms used by such proofs. -/
theorem audit_rootsOk_35 :
    rootsOk (4 * 211 ^ 7) 35 ⟨0, 0, [⟨5, 1, some 3, 1⟩, ⟨7, 1, some 2, 2⟩]⟩ = true := by
  decide +kernel

#print axioms audit_rootsOk_35
