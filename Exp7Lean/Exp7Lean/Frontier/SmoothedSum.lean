import Exp7Lean.Frontier.SmoothedDecay
import Exp7Lean.Frontier.SmoothedCorrelation
import Exp7Lean.Frontier.Obstruction

/-!
# Absolute convergence of the actual smoothed zero sum

Compactness controls the removable singularity at zero. Quartic decay controls
the tails. The resulting sum uses actual completed-L-function multiplicities
and requires no assumption about zeros lying on the critical line.
-/

namespace Exp7.Frontier

open Complex Exp7.EF

theorem smoothH_strip_weight_bound {a b d : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hab : b < a) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ z : ℂ, |z.im| ≤ d → ‖smoothH a b z‖ ≤ K / (4 + z.re ^ 2) := by
  have hcont : Continuous (smoothH a b) :=
    continuous_iff_continuousAt.mpr (fun z ↦ (analyticAt_smoothH a b z).continuousAt)
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) (1 + d)).exists_bound_of_continuousOn
    hcont.continuousOn
  let C := smoothTailConstant a b d
  have hC : 0 ≤ C := smoothTailConstant_nonneg hab d
  refine ⟨5 * (max M 0 + C), by positivity, ?_⟩
  intro z hs
  have hden : 0 < 4 + z.re ^ 2 := by positivity
  by_cases ht : |z.re| ≤ 1
  · have hz : z ∈ Metric.closedBall (0 : ℂ) (1 + d) := by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact (norm_le_abs_re_add_abs_im z).trans (add_le_add ht hs)
    have hval : ‖smoothH a b z‖ ≤ max M 0 := (hM z hz).trans (le_max_left _ _)
    have ht2 : z.re ^ 2 ≤ 1 := by nlinarith [sq_abs z.re, abs_nonneg z.re]
    apply (le_div_iff₀ hden).mpr
    calc
      _ ≤ max M 0 * (4 + z.re ^ 2) := mul_le_mul_of_nonneg_right hval hden.le
      _ ≤ max M 0 * 5 := mul_le_mul_of_nonneg_left (by linarith) (le_max_right _ _)
      _ ≤ _ := by nlinarith
  · have hge : 1 ≤ |z.re| := (not_le.mp ht).le
    have hn : z.re ≠ 0 := by intro h; simp [h] at ht
    calc
      _ ≤ C / z.re ^ 4 := smoothH_quartic_bound ha hb hab hn hs
      _ ≤ (C * 5) / (4 + z.re ^ 2) := by
        have h := mul_le_mul_of_nonneg_left (quartic_tail_weight (by norm_num : (0:ℝ) < 1) hge) hC
        norm_num at h
        convert h using 1 <;> ring
      _ ≤ _ := div_le_div_of_nonneg_right (by nlinarith [le_max_right M 0]) hden.le

variable (q : ℕ) [Fact q.Prime]

theorem summable_smoothH_zero_norm (hq : q % 4 = 3) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hab : b < a) :
    Summable (fun ρ : ℂ ↦ (mult q ρ : ℝ) * ‖smoothH a b ((ρ - 1 / 2) / I)‖) := by
  obtain ⟨K, hK, hbound⟩ := smoothH_strip_weight_bound (d := 1 / 2) ha hb hab
  have hsum : Summable (fun ρ : ℂ ↦ K * ((mult q ρ : ℝ) / (4 + ρ.im ^ 2))) := by
    convert (summable_shifted_weight q hq (by norm_num : (0:ℝ) < 1)).mul_left K using 1
    norm_num
  apply Summable.of_nonneg_of_le (fun ρ ↦ by positivity) _ hsum
  intro ρ
  by_cases hm : mult q ρ = 0
  · simp [hm]
  obtain ⟨hlo, hhi, _⟩ := mult_ne_zero_imp q hq hm
  have hp := zeroFrequency_parts ρ
  have hs : |((ρ - 1 / 2) / I).im| ≤ (1 / 2 : ℝ) := by
    rw [hp.2, abs_le]
    constructor <;> linarith
  have h := mul_le_mul_of_nonneg_left (hbound _ hs)
    (Nat.cast_nonneg (mult q ρ) : (0:ℝ) ≤ _)
  rw [hp.1] at h
  convert h using 1
  ring

theorem summable_smoothH_zero (hq : q % 4 = 3) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hab : b < a) :
    Summable (fun ρ : ℂ ↦ (mult q ρ : ℂ) * smoothH a b ((ρ - 1 / 2) / I)) := by
  apply (summable_smoothH_zero_norm q hq ha hb hab).of_norm_bounded
  intro ρ
  simp only [norm_mul, Complex.norm_natCast, le_refl]

theorem summable_smoothH_zero_re (hq : q % 4 = 3) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hab : b < a) :
    Summable (fun ρ : ℂ ↦ (mult q ρ : ℝ) * (smoothH a b ((ρ - 1 / 2) / I)).re) := by
  apply (summable_smoothH_zero_norm q hq ha hb hab).of_norm_bounded
  intro ρ
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
  exact mul_le_mul_of_nonneg_left (abs_re_le_norm _) (Nat.cast_nonneg _)

/-- Only the low-zero estimate remains an input to this kernel's zero-side bound. -/
theorem smoothH_zero_sum_lower_bound (hq : q % 4 = 3) {a b T A : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hab : b < a) (hT : 0 < T) (hA : 0 ≤ A)
    (hlow : ∀ ρ : ℂ, mult q ρ ≠ 0 → |ρ.im| ≤ T →
      -A / (1 + ρ.im ^ 2) ≤ (smoothH a b ((ρ - 1 / 2) / I)).re) :
    -(A * (2 * logDerivativeMass q 2) +
      (smoothTailConstant a b (1 / 2) * (((T + 1) ^ 2 + T ^ 2) / T ^ 4)) *
        (logDerivativeMass q (T + 1) / T)) ≤
      ∑' ρ : ℂ, (mult q ρ : ℝ) * (smoothH a b ((ρ - 1 / 2) / I)).re := by
  apply zero_sum_lower_bound q hq hT hA (smoothTailConstant_nonneg hab _) _
    (summable_smoothH_zero_re q hq ha hb hab) hlow
  intro ρ hm ht
  exact smoothH_zero_quartic_bound q hq ha hb hab hm (by
    intro h; simp only [h, abs_zero] at ht; linarith)

/-- Concrete-kernel assembly: convergence and high-zero decay are now proved.
The undamped identity, low-zero estimate, archimedean estimate and numeric
margin remain explicit inputs. -/
theorem smoothH_zero_obstruction_of_inert_certificate {X : ℕ} (hE : IsExp7 q)
    (hcut : 4 * X ^ 7 < q) {a b d T A J : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hab : b < a) (hT : 0 < T) (hA : 0 ≤ A)
    (hEF : (∑' ρ : ℂ, (mult q ρ : ℝ) * (smoothH a b ((ρ - 1 / 2) / I)).re) =
      Real.log ((q : ℝ) / Real.pi) + psi34 +
        Jterm (fun u ↦ (smoothCorrelation a b u).re) -
        primeSum q (fun u ↦ (smoothCorrelation a b u).re) X)
    (hJ : Jterm (fun u ↦ (smoothCorrelation a b u).re) ≤ J)
    (hlow : ∀ ρ : ℂ, mult q ρ ≠ 0 → |ρ.im| ≤ T → |ρ.re - 1 / 2| ≤ d →
      -A / (1 + ρ.im ^ 2) ≤ (smoothH a b ((ρ - 1 / 2) / I)).re)
    (hmargin : Real.log ((q : ℝ) / Real.pi) + psi34 + J -
        inertSum (fun u ↦ (smoothCorrelation a b u).re) X <
      -(A * (2 * logDerivativeMass q 2) +
        (smoothTailConstant a b (1 / 2) * (((T + 1) ^ 2 + T ^ 2) / T ^ 4)) *
          (logDerivativeMass q (T + 1) / T))) :
    ∃ ρ : ℂ, 0 < ρ.re ∧ ρ.re < 1 ∧ (chi q).LFunction ρ = 0 ∧
      1 / 2 + d < ρ.re ∧ |ρ.im| ≤ T := by
  apply zero_obstruction_of_inert_certificate q hE hcut hT hA
    (smoothTailConstant_nonneg hab _) _ _
    (summable_smoothH_zero_re q hE.2.1 ha hb hab) hEF hJ hlow _ hmargin
  intro ρ hm ht
  exact smoothH_zero_quartic_bound q hE.2.1 ha hb hab hm (by
    intro h; simp only [h, abs_zero] at ht; linarith)

end Exp7.Frontier
