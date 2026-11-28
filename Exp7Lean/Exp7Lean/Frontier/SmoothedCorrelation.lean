import Exp7Lean.Frontier.SmoothedKernel

/-!
# The transform of the actual smoothed correlation

This identifies `smoothH` with an integral of a concrete convolution, at every
complex frequency. The denominator is explicit; `SmoothedNorm` proves that
it is the squared L2 norm and that the correlation has value one at zero.
-/

namespace Exp7.Frontier

open Complex MeasureTheory
open scoped Convolution

theorem expTwist_reflect (f : ℝ → ℂ) (z : ℂ) :
    expTwist z (fun x ↦ f (-x)) = fun x ↦ expTwist (-z) f (-x) := by
  funext x
  simp [expTwist]

theorem complexTransform_reflect (f : ℝ → ℂ) (z : ℂ) :
    complexTransform (fun x ↦ f (-x)) z = complexTransform f (-z) := by
  simp only [complexTransform, expTwist_reflect]
  exact integral_neg_eq_self (expTwist (-z) f) volume

noncomputable def smoothCorrelation (a b : ℝ) (u : ℝ) : ℂ :=
  (smoothedHaar a b ⋆[ContinuousLinearMap.mul ℂ ℂ]
    (fun x ↦ smoothedHaar a b (-x))) u / (2 * a - 2 * b)

theorem integrable_expTwist_smoothCorrelation (a b : ℝ) (z : ℂ) :
    Integrable (expTwist z (smoothCorrelation a b)) := by
  have hreflection : Integrable (expTwist z (fun x ↦ smoothedHaar a b (-x))) := by
    rw [expTwist_reflect]
    exact (integrable_expTwist_smoothedHaar a b (-z)).comp_neg
  have hconv := (integrable_expTwist_smoothedHaar a b z).integrable_convolution
    (ContinuousLinearMap.mul ℂ ℂ) hreflection
  rw [← expTwist_convolution] at hconv
  convert hconv.div_const (2 * (a : ℂ) - 2 * b) using 1
  funext x
  simp only [expTwist, smoothCorrelation]
  ring

theorem complexTransform_smoothCorrelation {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (z : ℂ) : complexTransform (smoothCorrelation a b) z = smoothH a b z := by
  have hreflection : Integrable (expTwist z (fun x ↦ smoothedHaar a b (-x))) := by
    rw [expTwist_reflect]
    exact (integrable_expTwist_smoothedHaar a b (-z)).comp_neg
  have hscale : complexTransform (smoothCorrelation a b) z =
      complexTransform (smoothedHaar a b ⋆[ContinuousLinearMap.mul ℂ ℂ]
        (fun x ↦ smoothedHaar a b (-x))) z / (2 * a - 2 * b) := by
    unfold complexTransform expTwist smoothCorrelation
    rw [← integral_div]
    congr 1
    funext x
    ring
  rw [hscale, complexTransform_convolution z (integrable_expTwist_smoothedHaar a b z)
    hreflection, complexTransform_reflect, complexTransform_smoothedHaar_eq_smoothG ha hb,
    complexTransform_smoothedHaar_eq_smoothG ha hb, smoothH_product]

end Exp7.Frontier
