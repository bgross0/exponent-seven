import Mathlib

#check Real.exp_nat_mul
#check AnalyticOnNhd.circleAverage_log_norm
#check CircleIntegrable.const_smul

example (w : ℝ) (n : ℕ) : Real.exp ((n : ℝ) * (-w)) = Real.exp (-w) ^ n := by
  rw [Real.exp_nat_mul]
