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

#print axioms expTwist_convolution
#print axioms complexTransform_convolution
#print axioms expTwist_intervalBox
#print axioms integrable_expTwist_intervalBox
#print axioms complexTransform_intervalBox
#print axioms complexTransform_intervalBox_zero
#print axioms expTwist_haarBase
#print axioms expTwist_averagingBox
#print axioms integrable_expTwist_haarBase
#print axioms integrable_expTwist_averagingBox
#print axioms integrable_expTwist_smoothedHaar
#print axioms complexTransform_smoothedHaar_factor
#print axioms complexTransform_haarBase
#print axioms complexTransform_averagingBox
#print axioms complexTransform_smoothedHaar
#print axioms complexTransform_smoothedHaar_zero
#print axioms complexSinc_zero
#print axioms complexSinc_of_ne_zero
#print axioms analyticAt_complexSinc
#print axioms complexSinc_neg
#print axioms complexSinc_ofReal
#print axioms smoothG_zero
#print axioms smoothH_zero
#print axioms analyticAt_smoothG
#print axioms analyticAt_smoothH
#print axioms smoothG_neg
#print axioms smoothH_product
#print axioms smoothG_closed
#print axioms complexTransform_smoothedHaar_eq_smoothG
#print axioms smoothH_closed
#print axioms smoothH_ofReal
#print axioms smoothH_real_nonneg
#print axioms smoothH_real_im
#print axioms expTwist_reflect
#print axioms complexTransform_reflect
#print axioms integrable_expTwist_smoothCorrelation
#print axioms complexTransform_smoothCorrelation
#print axioms norm_cos_le_cosh_im
#print axioms norm_sin_le_cosh_im
#print axioms smoothTailConstant_nonneg
#print axioms cosh_mul_im_le
#print axioms smoothH_strip_bound
#print axioms smoothH_quartic_bound
#print axioms zeroFrequency_parts
#print axioms smoothH_zero_quartic_bound
#print axioms smoothH_high_zero_loss_le
#print axioms smoothH_strip_weight_bound
#print axioms summable_smoothH_zero_norm
#print axioms summable_smoothH_zero
#print axioms summable_smoothH_zero_re
#print axioms smoothH_zero_sum_lower_bound
#print axioms smoothH_zero_obstruction_of_inert_certificate

end Exp7.Frontier
