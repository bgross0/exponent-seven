import Exp7Lean.Tail.LogWeight

/-! # Positive primes in the upper half of the Haar row -/

namespace Exp7.ChebyshevTail

open Finset MeasureTheory

private theorem theta_lower {t : ℝ} (ht : 4 ≤ t) :
    Real.log 2 * t - 2 * Real.sqrt t * Real.log t - 2 * Real.log t ≤ Chebyshev.theta t := by
  have ht' : 0 < t := by linarith
  have h := Real.log_le_log (show 0 < 2 * (t + 2) by positivity)
    (show 2 * (t + 2) ≤ t * t by nlinarith [mul_nonneg (sub_nonneg.mpr ht) ht'.le])
  rw [Real.log_mul (by norm_num) (by positivity), Real.log_mul ht'.ne' ht'.ne'] at h
  linarith [Chebyshev.theta_ge' (show 1 ≤ t by linarith)]

private noncomputable def thetaIntegrand (L t : ℝ) :=
  logKernel L t * (Real.log 2 * t - 2 * Real.sqrt t * Real.log t) -
    (L / 2 + 2) / (t * Real.sqrt t)

private noncomputable def thetaPrimitive (L t : ℝ) :=
  weightPrimitive (Real.log 2) (-1) L t + (L + 4) / Real.sqrt t

private theorem thetaPrimitive_hasDerivAt {L t : ℝ} (hL : 0 < L) (ht : 0 < t) :
    HasDerivAt (thetaPrimitive L) (thetaIntegrand L t) t := by
  have hs := Real.sqrt_pos.mpr ht
  have hsq := Real.sq_sqrt ht.le
  have ha := weightPrimitive_hasDerivAt (Real.log 2) (-1) hL ht
  have hb := (hasDerivAt_const t (L + 4)).div (Real.hasDerivAt_sqrt ht.ne') hs.ne'
  convert ha.add hb using 1 <;> try rfl
  unfold thetaIntegrand
  field_simp [hs.ne', ht.ne']
  ring_nf
  simp only [hsq]
  ring

private theorem thetaIntegrand_le {L t : ℝ} (hL : 0 < L) (ht : 4 ≤ t)
    (hlo : L / 2 ≤ Real.log t) (hhi : Real.log t ≤ L) :
    thetaIntegrand L t ≤ logKernel L t * Chebyshev.theta t := by
  have ht' : 0 < t := by linarith
  have hk := logKernel_nonneg hL ht' hhi
  have hs := Real.sqrt_pos.mpr ht'
  have herr : logKernel L t * (2 * Real.log t) ≤ (L / 2 + 2) / (t * Real.sqrt t) := by
    calc
      _ ≤ logKernel L t * (2 * L) := mul_le_mul_of_nonneg_left (by linarith) hk
      _ ≤ _ := by
        unfold logKernel
        field_simp
        nlinarith [mul_le_mul_of_nonneg_right hlo hL.le]
  have htheta := mul_le_mul_of_nonneg_left (theta_lower ht) hk
  unfold thetaIntegrand
  linarith

private noncomputable def primeLog (n : ℕ) : ℝ := if n.Prime then Real.log n else 0

private theorem theta_sum (t : ℝ) :
    ∑ n ∈ Icc 0 ⌊t⌋₊, primeLog n = Chebyshev.theta t := by
  rw [Chebyshev.theta_eq_sum_Icc, sum_filter]
  rfl

/-- Lower bound for the positive-prime term, using all primes in (√X, X].
The prime at the upper endpoint has weight zero. -/
theorem positive_primes_ge {X : ℝ} (hX : 4 ≤ Real.sqrt X) :
    let L := Real.log X
    let A := Real.sqrt X
    let U := Real.sqrt A
    8 * Real.log 2 * A / L - Real.log 2 * (3 + 8 / L) * U -
      L ^ 2 / 6 - 3 * L / 2 - (2 * L + 8) / U ≤
    2 * ∑ p ∈ Ioc ⌊A⌋₊ ⌊X⌋₊ with p.Prime, logWeight L p * Real.log p := by
  dsimp only
  let L := Real.log X
  let A := Real.sqrt X
  let U := Real.sqrt A
  have hA : 4 ≤ A := hX
  have hApos : 0 < A := by linarith
  have hXpos := Real.sqrt_pos.mp hApos
  have hAsq : A ^ 2 = X := Real.sq_sqrt hXpos.le
  have hAX : A ≤ X := by nlinarith [mul_nonneg (show 0 ≤ A - 1 by linarith) hApos.le]
  have hXone : 1 < X := by linarith
  have hU : 0 < U := Real.sqrt_pos.mpr hApos
  have hUsq : U ^ 2 = A := Real.sq_sqrt hApos.le
  have hL : 0 < L := Real.log_pos hXone
  have hlogA : Real.log A = L / 2 := Real.log_sqrt hXpos.le
  have hpos {t : ℝ} (ht : t ∈ Set.Icc A X) : 0 < t := hApos.trans_le ht.1
  have hc : ContinuousOn (logKernel L) (Set.Icc A X) :=
    fun _ ht ↦ (logKernel_continuousAt L (hpos ht)).continuousWithinAt
  have hd (t : ℝ) (ht : t ∈ Set.Icc A X) := logWeight_hasDerivAt hL (hpos ht)
  have hder : ContinuousOn (deriv (logWeight L)) (Set.Icc A X) :=
    hc.neg.congr (fun t ht ↦ (hd t ht).deriv)
  have habel := sum_mul_eq_sub_sub_integral_mul primeLog (f := logWeight L)
    hApos.le hAX (fun t ht ↦ (hd t ht).differentiableAt) hder.integrableOn_Icc
  have hend : logWeight L X = 0 := by simp [logWeight, L, (Real.log_pos hXone).ne']
  rw [hend, zero_mul, zero_sub, theta_sum, ← intervalIntegral.integral_of_le hAX] at habel
  have hsum : (∑ p ∈ Ioc ⌊A⌋₊ ⌊X⌋₊ with p.Prime, logWeight L p * Real.log p) =
      -(logWeight L A * Chebyshev.theta A) + ∫ t in A..X, logKernel L t * Chebyshev.theta t := by
    have h : (∫ t in A..X, deriv (logWeight L) t * ∑ n ∈ Icc 0 ⌊t⌋₊, primeLog n) =
        -(∫ t in A..X, logKernel L t * Chebyshev.theta t) := by
      rw [← intervalIntegral.integral_neg]
      refine intervalIntegral.integral_congr fun t ht ↦ ?_
      rw [Set.uIcc_of_le hAX] at ht
      rw [(hd t ht).deriv, theta_sum, neg_mul]
    rw [h, sub_neg_eq_add] at habel
    rw [← habel, sum_filter]
    refine sum_congr rfl fun n _ ↦ ?_
    by_cases hp : n.Prime <;> simp [primeLog, hp]
  have hi : IntervalIntegrable (fun t ↦ logKernel L t * Chebyshev.theta t) volume A X := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le hAX).mpr
    simp_rw [← theta_sum]
    exact integrableOn_mul_sum_Icc _ hApos.le hc.integrableOn_Icc
  have hj : IntervalIntegrable (thetaIntegrand L) volume A X := by
    apply ContinuousOn.intervalIntegrable_of_Icc hAX
    intro t ht
    apply ContinuousAt.continuousWithinAt
    have ht' := hpos ht
    have hk := logKernel_continuousAt L ht'
    unfold thetaIntegrand
    fun_prop (disch := positivity)
  have hint : thetaPrimitive L X - thetaPrimitive L A ≤
      ∫ t in A..X, logKernel L t * Chebyshev.theta t := by
    have h := intervalIntegral.integral_mono_on hAX hj hi (fun t ht ↦
      thetaIntegrand_le hL (hA.trans ht.1) (hlogA ▸ Real.log_le_log hApos ht.1)
        (Real.log_le_log (hpos ht) ht.2))
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt _ hj] at h
    · exact h
    · intro t ht
      rw [Set.uIcc_of_le hAX] at ht
      exact thetaPrimitive_hasDerivAt hL (hpos ht)
  have hweight : logWeight L A = 1 / (2 * U) := by
    unfold logWeight
    rw [hlogA]
    change (1 - L / 2 / L) / U = _
    field_simp
    ring
  have hfour : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    ring
  have hb := mul_le_mul_of_nonneg_left (Chebyshev.theta_le_log4_mul_x hApos.le)
    (show 0 ≤ 1 / (2 * U) by positivity)
  rw [hfour] at hb
  change 8 * Real.log 2 * A / L - Real.log 2 * (3 + 8 / L) * U -
    L ^ 2 / 6 - 3 * L / 2 - (2 * L + 8) / U ≤ 2 * _
  rw [hsum, hweight]
  have heval : 2 * (-(1 / (2 * U) * (2 * Real.log 2 * A)) +
      (thetaPrimitive L X - thetaPrimitive L A)) =
      8 * Real.log 2 * A / L - Real.log 2 * (3 + 8 / L) * U - L ^ 2 / 6 -
        3 * L / 2 - (2 * L + 8) / U + (2 * L + 8) / A := by
    unfold thetaPrimitive weightPrimitive
    rw [hlogA]
    change 2 * (-(1 / (2 * U) * (2 * Real.log 2 * A)) +
      ((Real.log 2 * A * (1 + 4 / L - L / L) + -1 * ((1 + 2 / L) / 2 * L ^ 2 -
        L ^ 3 / (3 * L)) + (L + 4) / A) -
      (Real.log 2 * U * (1 + 4 / L - L / 2 / L) + -1 * ((1 + 2 / L) / 2 * (L/2) ^ 2 -
        (L/2) ^ 3 / (3 * L)) + (L + 4) / U))) = _
    field_simp
    rw [← hUsq]
    ring
  linarith [show 0 ≤ (2 * L + 8) / A by positivity]

end Exp7.ChebyshevTail
