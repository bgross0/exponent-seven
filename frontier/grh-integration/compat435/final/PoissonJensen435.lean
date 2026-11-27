/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
module

public import Mathlib.Analysis.Complex.CanonicalDecomposition
public import Mathlib.Analysis.Complex.JensenFormula
public import Mathlib.Analysis.Normed.Module.Connected

/-!
# Poisson–Jensen on a disc centred at zero

Centred Poisson–Jensen formula adapted from Mathlib's CanonicalDecomposition.lean
and JensenFormula.lean at 31ce06eaadf4a200c0e1407c5f10953cf606b8f8.
-/

public section

namespace Exp7.EF.PoissonJensen435

open Complex Filter Function MeromorphicOn Metric Real Set Topology
variable {R : ℝ} {w : ℂ} {f h : ℂ → ℂ}

private lemma log_norm_on_circle (D : ECanonicalDecomp f h R) :
    (Real.log ‖f ·‖) =ᶠ[codiscreteWithin (sphere 0 R)]
      ∑ᶠ u, (divisor f (sphere 0 R) u * Real.log ‖· - u‖) + (Real.log ‖h ·‖) := by
  let B := divisor f (sphere 0 R)
  let g := (∏ᶠ u, (· - u) ^ B u) • h
  have hg := extract_zeros_poles_log (D := B) (f := g) (g := h)
    (fun u ↦ D.ne_zero u (sphere_subset_closedBall u.property)) Filter.EventuallyEq.rfl
  apply Filter.EventuallyEq.trans _ hg
  filter_upwards [D.eventuallyEq.filter_mono (codiscreteWithin_mono sphere_subset_closedBall),
    self_mem_codiscreteWithin (sphere 0 R)] with z hz hzs
  have hp : ‖(∏ᶠ u, (canonicalFactor R u) ^ (-divisor f (ball 0 R) u)) z‖ = 1 := by
    refine finprod_induction (fun p : ℂ → ℂ ↦ ‖p z‖ = 1) (by simp)
      (fun _ _ ha hb ↦ by simp [ha, hb]) fun u ↦ ?_
    by_cases hu : divisor f (ball 0 R) u = 0
    · simp [hu]
    · simp [norm_canonicalFactor_eval_circle_eq_one
        ((divisor f (ball 0 R)).supportWithinDomain hu) hzs]
  simp only [hz, Pi.smul_apply', Pi.mul_apply, norm_smul, norm_mul, hp, one_mul, g, B]

private lemma poisson_boundary_sum (D : locallyFinsuppWithin (sphere (0 : ℂ) R) ℤ)
    (hw : w ∈ ball 0 R) (hK : ContinuousOn (poissonKernel 0 w) (sphere 0 |R|)) :
    circleAverage (poissonKernel 0 w • ∑ᶠ u, (D u * Real.log ‖· - u‖)) 0 R =
      ∑ᶠ u, D u * Real.log ‖w - u‖ := by
  have hD := D.finiteSupport (isCompact_sphere 0 R)
  rw [finsum_eq_sum_of_support_subset (s := hD.toFinset) _ (fun u ↦ by contrapose; aesop),
    finsum_eq_sum_of_support_subset (s := hD.toFinset) _ (fun u ↦ by aesop),
    Finset.smul_sum, circleAverage_sum]
  · refine Finset.sum_congr rfl fun u hu ↦ ?_
    have hsingle := circleAverage_re_herglotzRieszKernel_mul_log₀
      (D.supportWithinDomain (hD.mem_toFinset.1 hu)) hw
    rw [← poissonKernel_eq_re_herglotzRieszKernel] at hsingle
    rw [← hsingle, ← smul_eq_mul, ← circleAverage_smul]
    congr 1
    ext z
    simp only [Pi.smul_apply, Pi.smul_apply', Pi.mul_apply, smul_eq_mul]
    ring
  · intro u _
    apply CircleIntegrable.continuousOn_smul _ hK
    exact IntervalIntegrable.const_mul
      ((analyticOnNhd_id.sub analyticOnNhd_const).meromorphicOn.circleIntegrable_log_norm) _

/-- The centred Poisson–Jensen identity at a point of order zero. -/
theorem log_norm_meromorphicTrailingCoeffAt (hw : w ∈ ball 0 R)
    (hord : meromorphicOrderAt f w = 0) (hf : MeromorphicOn f (closedBall 0 R)) :
    Real.log ‖meromorphicTrailingCoeffAt f w‖ =
      circleAverage (poissonKernel 0 w • (Real.log ‖f ·‖)) 0 R -
        ∑ᶠ i, divisor f (ball 0 R) i * Real.log ‖canonicalFactor R i w‖ := by
  have hR := pos_of_mem_ball hw
  have hK : ContinuousOn (poissonKernel 0 w) (sphere 0 |R|) := by
    rw [poissonKernel_eq_re_herglotzRieszKernel]
    exact continuous_re.comp_continuousOn
      (continuousOn_herglotzRieszKernel_sphere (by grind [mem_sphere, mem_ball, le_abs_self R]))
  obtain ⟨h, D⟩ := hf.exists_ecanonicalDecomp <| by
    apply (hf.exists_meromorphicOrderAt_ne_top_iff_forall (isConnected_closedBall hR.le)).1
    exact ⟨⟨w, ball_subset_closedBall hw⟩, by simp [hord]⟩
  have hb : poissonKernel 0 w • (Real.log ‖f ·‖) =ᶠ[codiscreteWithin (sphere 0 |R|)]
      poissonKernel 0 w •
        ((∑ᶠ u, (divisor f (sphere 0 R) u * Real.log ‖· - u‖)) + (Real.log ‖h ·‖)) := by
    rw [abs_of_pos hR]
    filter_upwards [log_norm_on_circle D] with z hz
    exact congrArg (fun t : ℝ ↦ poissonKernel 0 w z * t) hz
  rw [circleAverage_congr_codiscreteWithin hb hR.ne',
    smul_add, circleAverage_add, poisson_boundary_sum _ hw hK,
    InnerProductSpace.HarmonicOnNhd.circleAverage_poissonKernel_smul
      (fun x hx ↦ (D.analyticOnNhd x hx).harmonicAt_log_norm (D.ne_zero x hx)) hw,
    D.log_norm_eq (ball_subset_closedBall hw) hord hR]
  · ring
  · apply CircleIntegrable.continuousOn_smul _ hK
    apply CircleIntegrable.finsum
    intro i
    exact IntervalIntegrable.const_mul
      ((analyticOnNhd_id.sub analyticOnNhd_const).meromorphicOn.circleIntegrable_log_norm) _
  · apply CircleIntegrable.continuousOn_smul _ hK
    apply circleIntegrable_log_norm (D.analyticOnNhd.meromorphicOn.mono_set _)
    simpa [abs_of_pos hR] using sphere_subset_closedBall

end Exp7.EF.PoissonJensen435
