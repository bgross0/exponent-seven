import Exp7Lean.Frontier.All

/-! Check the exact height-60 coefficient and the proof dependencies of every
exported frontier theorem. This file does not assume the missing smoothed formula. -/

namespace Exp7.Frontier

example : (((60 + 1 : ℝ) ^ 2 + 60 ^ 2) / 60 ^ 4) = 7321 / 12960000 := by
  norm_num

example : realZeroKernel 61 (1 / 2 + 60 * Complex.I) = 242 / 29041 := by
  norm_num [realZeroKernel]

example : 1 / (60 : ℝ) ^ 4 ≤ (7321 / 12960000) / (61 ^ 2 + 60 ^ 2) := by
  norm_num

#print axioms pointwise_identity_unconditional
#print axioms re_one_div_sub_eq_offLine
#print axioms summable_offLineZerosKernel
#print axioms offLineZerosKernel_eq_of_GRH
#print axioms offLine_poisson_bound
#print axioms integral_h_mul_offLineZerosKernel
#print axioms offLineZeroSideR_eq_arithSideR_of_half_lt
#print axioms re_one_div_real_sub
#print axioms summable_realZeroKernel
#print axioms realZeroKernel_tsum
#print axioms logDerivativeMass_eq
#print axioms realZeroKernel_nonneg
#print axioms standard_weight_le_kernel
#print axioms standard_mass_le
#print axioms shifted_weight_le_kernel
#print axioms summable_shifted_weight
#print axioms shifted_mass_le
#print axioms quartic_tail_weight
#print axioms high_zero_loss_le
#print axioms zero_sum_lower_bound
#print axioms mult_reflection
#print axioms exists_right_zero_of_not_lowStrip
#print axioms exists_right_zero_of_margin
#print axioms zero_obstruction_of_inert_certificate
#print axioms zeroRows_cutoff
#print axioms zeroRows_cover
#print axioms exists_inert_zeroRow

end Exp7.Frontier
