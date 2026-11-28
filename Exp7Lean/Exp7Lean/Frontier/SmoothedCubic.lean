import Exp7Lean.Frontier.SmoothedAdmissible

/-! # The piecewise cubic of the height-60 integer verifier

In units of log(X)/200 the smoothed Haar function is a sum of six shifted ramps.
Convolving two ramps gives a truncated cube, including at a coincident endpoint.
-/

namespace Exp7.Frontier

open MeasureTheory
open scoped BigOperators

private noncomputable def ramp (x : ℝ) : ℝ := max x 0

private lemma overlap_ramps {l r v w : ℝ} (hl : l ≤ r) (hv : v ≤ w) (x : ℝ) :
    intervalOverlap l r v w x =
      ramp (x - l - v) - ramp (x - r - v) - ramp (x - l - w) + ramp (x - r - w) := by
  unfold intervalOverlap ramp
  simp only [min_def, max_def]
  split_ifs <;> linarith

-- The unit of length here is h = log(X)/200. The numerator of the Haar function
-- changes slope by the six indicated integers at these knots.
private noncomputable def haarKnots : Fin 6 → ℝ := ![-100, -98, -1, 1, 98, 100]
private noncomputable def haarJumps : Fin 6 → ℝ := ![1, -1, -2, 2, 1, -1]

private lemma haar_ramps {h : ℝ} (hh : 0 < h) (x : ℝ) :
    smoothedHaarReal (99 * h) h x =
      (∑ i, haarJumps i * ramp (x - h * haarKnots i)) / (2 * h) := by
  unfold smoothedHaarReal
  rw [overlap_ramps (by linarith) (by linarith), overlap_ramps (by linarith) (by linarith)]
  simp [haarKnots, haarJumps, Fin.sum_univ_succ]
  ring_nf

private lemma ramp_support (s z : ℝ) :
    Function.support (fun x ↦ ramp (x - s) * ramp (z - x)) ⊆ Set.Ioc s z := by
  intro x hx
  change ramp (x - s) * ramp (z - x) ≠ 0 at hx
  constructor
  · by_contra! h
    simp [ramp, max_eq_right (sub_nonpos.mpr h)] at hx
  · by_contra! h
    simp [ramp, max_eq_right (sub_nonpos.mpr h.le)] at hx

private lemma ramp_pair_integrable (s z : ℝ) :
    Integrable (fun x ↦ ramp (x - s) * ramp (z - x)) := by
  have hc : Continuous (fun x ↦ ramp (x - s) * ramp (z - x)) := by unfold ramp; fun_prop
  exact hc.integrable_of_hasCompactSupport
    (HasCompactSupport.of_support_subset_isCompact isCompact_Icc
      ((ramp_support s z).trans Set.Ioc_subset_Icc_self))

private lemma integral_ramp_pair (s z : ℝ) :
    (∫ x : ℝ, ramp (x - s) * ramp (z - x)) = ramp (z - s) ^ 3 / 6 := by
  by_cases h : s ≤ z
  · rw [← intervalIntegral.integral_eq_integral_of_support_subset (ramp_support s z)]
    calc
      _ = ∫ x in s..z, (x - s) * (z - x) := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [Set.uIcc_of_le h] at hx
        simp [ramp, max_eq_left (sub_nonneg.mpr hx.1), max_eq_left (sub_nonneg.mpr hx.2)]
      _ = _ := by
        let F := fun x : ℝ ↦ (z - s) * (x - s) ^ 2 / 2 - (x - s) ^ 3 / 3
        have hd (x : ℝ) : HasDerivAt F ((x - s) * (z - x)) x := by
          dsimp [F]
          convert (((((hasDerivAt_id x).sub_const s).pow 2).const_mul (z - s)).div_const 2).sub
            ((((hasDerivAt_id x).sub_const s).pow 3).div_const 3) using 1 <;>
            first | rfl | (simp only [id_eq]; ring)
        rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := F) (fun x _ ↦ hd x)
          (by apply Continuous.intervalIntegrable; fun_prop)]
        simp only [F, ramp, max_eq_left (sub_nonneg.mpr h)]
        ring
  · have hz := ramp_support s z
    rw [Set.Ioc_eq_empty (not_lt_of_ge (le_of_not_ge h)), Set.subset_empty_iff,
      Function.support_eq_empty_iff] at hz
    rw [hz]
    simp [ramp, max_eq_right (sub_nonpos.mpr (le_of_not_ge h))]

private lemma integral_ramp_sums {ι : Type*} [Fintype ι] (c k : ι → ℝ) (u : ℝ) :
    (∫ x : ℝ, (∑ i, c i * ramp (x - k i)) * (∑ j, c j * ramp (u - x - k j))) =
      ∑ i, ∑ j, c i * c j * (ramp (u - k j - k i) ^ 3 / 6) := by
  let term := fun i j (x : ℝ) ↦ (c i * c j) * (ramp (x - k i) * ramp ((u - k j) - x))
  have ht (i j) : Integrable (term i j) :=
    (ramp_pair_integrable (k i) (u - k j)).const_mul _
  have he (x : ℝ) :
      (∑ i, c i * ramp (x - k i)) * (∑ j, c j * ramp (u - x - k j)) =
      ∑ i, ∑ j, term i j x := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    dsimp [term]
    rw [show u - x - k j = u - k j - x by ring]
    ring
  simp_rw [he]
  rw [integral_finsetSum _ (fun i _ ↦ integrable_finsetSum _ (fun j _ ↦ ht i j))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _ ↦ ht i j)]
  simp only [term, integral_const_mul, integral_ramp_pair]

/-- Second difference at a jump of the unsmoothed correlation. The input t is
u/log X; the integer k specifies a knot in units of 1/200. -/
noncomputable def rowCubeDifference (t k : ℝ) : ℝ :=
  max (t - (k - 2) / 200) 0 ^ 3 - 2 * max (t - k / 200) 0 ^ 3 +
    max (t - (k + 2) / 200) 0 ^ 3

/-- The exact truncated-power formula `f_fraction` in frontier/zero-integer/verify.py. -/
noncomputable def rowTruncatedCubic (t : ℝ) : ℝ :=
  (-rowCubeDifference t (-198) + 4 * rowCubeDifference t (-99) -
    6 * rowCubeDifference t 0 + 4 * rowCubeDifference t 99 - rowCubeDifference t 198) /
    (24 * (1 / 200) ^ 2 * (2 * (99 / 200) - 2 * (1 / 200)))

private lemma collect_jumps (t : ℝ) :
    -(∑ i, ∑ j, haarJumps i * haarJumps j *
        ramp (t - (haarKnots j + haarKnots i) / 200) ^ 3) /
        (24 * (1 / 200) ^ 2 * (2 * (99 / 200) - 2 * (1 / 200))) = rowTruncatedCubic t := by
  norm_num [Fin.sum_univ_succ, haarKnots, haarJumps, rowTruncatedCubic, rowCubeDifference, ramp]
  ring_nf

private lemma scaled_row_correlation {h : ℝ} (hh : 0 < h) (t : ℝ) :
    (smoothCorrelation (99 * h) h (200 * h * t)).re = rowTruncatedCubic t := by
  let k := fun i ↦ h * haarKnots i
  -- Reflection negates the odd Haar function, so the integral is minus its self-convolution.
  have integrand (x : ℝ) :
      smoothedHaarReal (99 * h) h x * smoothedHaarReal (99 * h) h (x - 200 * h * t) =
        -((∑ i, haarJumps i * ramp (x - k i)) *
          (∑ j, haarJumps j * ramp (200 * h * t - x - k j))) / (2 * h) ^ 2 := by
    rw [← neg_sub (200 * h * t) x, smoothedHaarReal_neg, haar_ramps hh, haar_ramps hh]
    dsimp [k]
    ring
  have scale (i j) :
      ramp (200 * h * t - k j - k i) =
        (200 * h) * ramp (t - (haarKnots j + haarKnots i) / 200) := by
    dsimp only [k, ramp]
    rw [show 200 * h * t - h * haarKnots j - h * haarKnots i =
        200 * h * (t - (haarKnots j + haarKnots i) / 200) by ring]
    rw [mul_max_of_nonneg _ _ (by positivity : 0 ≤ 200 * h), mul_zero]
  rw [smoothCorrelation_eq_ofReal, Complex.ofReal_re]
  simp_rw [integrand]
  rw [integral_div, integral_neg, integral_ramp_sums]
  simp_rw [scale]
  have extract (i j) :
      haarJumps i * haarJumps j *
          (((200 * h) * ramp (t - (haarKnots j + haarKnots i) / 200)) ^ 3 / 6) =
        (200 * h) ^ 3 / 6 * (haarJumps i * haarJumps j *
          ramp (t - (haarKnots j + haarKnots i) / 200) ^ 3) := by ring
  simp_rw [extract, ← Finset.mul_sum]
  rw [← collect_jumps]
  field_simp
  ring

/-- The actual smoothed correlation in every height-60 row equals the integer
verifier's exact cubic at its dimensionless argument, including all knots. -/
theorem smoothCorrelation_row_eq_truncatedCubic {X : ℕ} (hX : 1 < X) (u : ℝ) :
    (smoothCorrelation (99 * Real.log X / 200) (Real.log X / 200) u).re =
      rowTruncatedCubic (u / Real.log X) := by
  have hL : 0 < Real.log (X : ℝ) := Real.log_pos (by exact_mod_cast hX)
  convert scaled_row_correlation (h := Real.log X / 200) (by positivity)
    (u / Real.log X) using 2
  field_simp

/-- Closed cells and their Horner values in the order used by the integer evaluator.
Both touching cells can be used at an internal breakpoint. -/
noncomputable def rowCubicPieces (t : ℝ) : List (ℝ × ℝ × ℝ) :=
  [(0, 1 / 100, 1 + t ^ 2 * (-15000 / 49 + t * (500000 / 49))),
   (1 / 100, 97 / 200, 99 / 98 + t * (-150 / 49)),
   (97 / 200, 99 / 200,
      -911485 / 1176 + t * (235075 / 49 + t * (-485000 / 49 + t * (1000000 / 147)))),
   (99 / 200, 101 / 200,
      1029113 / 1176 + t * (-36425 / 7 + t * (505000 / 49 + t * (-1000000 / 147)))),
   (101 / 200, 49 / 50, -99 / 98 + t * (50 / 49)),
   (49 / 50, 99 / 100, 470299 / 294 + t * (-240050 / 49 + t * (5000 + t * (-250000 / 147)))),
   (99 / 100, 1, -250000 / 147 + t * (250000 / 49 + t * (-250000 / 49 + t * (250000 / 147))))]

/-- Every applicable polynomial, including either neighbor of a knot, has the
same exact value as the truncated-cube sum. -/
theorem rowTruncatedCubic_eq_piece {t l r v : ℝ} (hp : (l, r, v) ∈ rowCubicPieces t)
    (hl : l ≤ t) (hr : t ≤ r) : rowTruncatedCubic t = v := by
  simp only [rowCubicPieces, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hp
  rcases hp with h | h | h | h | h | h | h <;> obtain ⟨rfl, rfl, rfl⟩ := h <;>
    unfold rowTruncatedCubic rowCubeDifference <;>
    norm_num at hl hr ⊢ <;>
    (repeat' (conv in (max _ 0) =>
      equals _ =>
        first | apply max_eq_left; linarith only [hl, hr]
              | apply max_eq_right; linarith only [hl, hr])) <;> ring

/-- The closed cells cover the full interval of the integer evaluator. -/
theorem rowCubicPieces_cover {t : ℝ} (hl : 0 ≤ t) (hr : t ≤ 1) :
    ∃ p ∈ rowCubicPieces t, p.1 ≤ t ∧ t ≤ p.2.1 := by
  simp [rowCubicPieces, or_and_right, exists_or]
  grind

/-- The extra zero used by the interval evaluator on the right is exact even at t=1. -/
theorem rowTruncatedCubic_zero_of_one_le {t : ℝ} (ht : 1 ≤ t) :
    rowTruncatedCubic t = 0 := by
  unfold rowTruncatedCubic rowCubeDifference
  norm_num
  repeat' (conv in (max _ 0) => equals _ => apply max_eq_left; linarith only [ht])
  ring

/-- The values actually selected by the seven-cell evaluator equal the analytic kernel. -/
theorem smoothCorrelation_row_eq_piece {X : ℕ} (hX : 1 < X) {u l r v : ℝ}
    (hp : (l, r, v) ∈ rowCubicPieces (u / Real.log X))
    (hl : l ≤ u / Real.log X) (hr : u / Real.log X ≤ r) :
    (smoothCorrelation (99 * Real.log X / 200) (Real.log X / 200) u).re = v :=
  (smoothCorrelation_row_eq_truncatedCubic hX u).trans (rowTruncatedCubic_eq_piece hp hl hr)

end Exp7.Frontier
