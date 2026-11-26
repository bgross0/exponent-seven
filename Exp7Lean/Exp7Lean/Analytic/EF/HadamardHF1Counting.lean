import Mathlib

/-!
# HF1, part 1: counting zeros of an entire function of order ≤ 1

Nodes **Z1, J1a, J1, J2, J3** of `HADAMARD_BLUEPRINT.md`, all proved (no `sorry`).  Pure complex
analysis, no `L`-functions; this file must not import `HadamardFallback.lean` (which will
eventually import the HF1 files).

Throughout `F : ℂ → ℂ` is entire, `F 0 ≠ 0`, and the multiplicity of `ρ` is
`analyticOrderNatAt F ρ` (zero off the zero set).

* `analyticOrderNatAt_eq_zero_iff` (Z1): order zero ⇔ non-vanishing.
* `sum_analyticOrderNatAt_le_log_div` (J1a): Jensen's inequality in `Finset` form,
  `∑_{ρ ∈ S} m ρ ≤ log (M / ‖F 0‖) / log 2` if `S ⊆ closedBall 0 r` and `‖F‖ ≤ M` on `‖z‖ = 2r`.
* `sum_analyticOrderNatAt_le` (J1): `n(r) ≤ A r log (2 + r)` under the order-one growth bound.
* `summable_div_one_add_sq_of_count` (J2): hence `∑ m ρ / (1 + ‖ρ‖²) < ∞`.
* `summable_norm_mul_one_div_sub_add` (J3): hence `∑ ‖m ρ (1/(s-ρ) + 1/ρ)‖ < ∞` for every `s`.
-/

namespace Exp7.EF.HF1

open Complex Filter Topology Metric

/-! ## Z1: multiplicities of an entire function -/

/-- An entire function that is not identically zero has finite order everywhere. -/
theorem analyticOrderAt_ne_top_of_entire {F : ℂ → ℂ} (hF : Differentiable ℂ F) {z₀ : ℂ}
    (h0 : F z₀ ≠ 0) (z : ℂ) : analyticOrderAt F z ≠ ⊤ := by
  have han : AnalyticOnNhd ℂ F Set.univ := fun w _ ↦ hF.analyticAt w
  exact han.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ (Set.mem_univ z₀)
    (Set.mem_univ z) (by rw [(hF.analyticAt z₀).analyticOrderAt_eq_zero.mpr h0]; simp)

/-- **Z1** (proved). For an entire function that is not identically zero,
`analyticOrderNatAt F z = 0` iff `F z ≠ 0`. -/
theorem analyticOrderNatAt_eq_zero_iff {F : ℂ → ℂ} (hF : Differentiable ℂ F) {z₀ : ℂ}
    (h0 : F z₀ ≠ 0) (z : ℂ) : analyticOrderNatAt F z = 0 ↔ F z ≠ 0 := by
  have htop := analyticOrderAt_ne_top_of_entire hF h0 z
  rw [← (hF.analyticAt z).analyticOrderAt_eq_zero]
  unfold analyticOrderNatAt
  rw [ENat.toNat_eq_zero]
  simp [htop]

theorem analyticOrderNatAt_ne_zero_iff {F : ℂ → ℂ} (hF : Differentiable ℂ F) {z₀ : ℂ}
    (h0 : F z₀ ≠ 0) (z : ℂ) : analyticOrderNatAt F z ≠ 0 ↔ F z = 0 := by
  rw [Ne, analyticOrderNatAt_eq_zero_iff hF h0 z, not_not]

/-! ## J1: Jensen's bound for the number of zeros -/

/-- **J1a** (proved). Jensen's inequality (`AnalyticOnNhd.sum_divisor_le` with radii `r < 2r`)
restated for finite sets of points and `analyticOrderNatAt`: if `‖F‖ ≤ M` on the circle
`‖z‖ = 2r`, then the zeros of `F` in `‖z‖ ≤ r`, counted with multiplicity, number at most
`log (M / ‖F 0‖) / log 2`.

Proof sketch: `AnalyticOnNhd.sum_divisor_le (c := 0) (r := r) (R := 2 * r)` bounds
`∑ᶠ u, divisor F (closedBall 0 |r|) u`; `AnalyticOnNhd.divisor_apply` identifies the divisor on the
closed ball with `analyticOrderNatAt` (the order is finite by `analyticOrderAt_ne_top_of_entire`);
the divisor is nonnegative (`AnalyticOnNhd.divisor_nonneg`) with finite support
(`Function.locallyFinsuppWithin.finiteSupport` on the compact ball), so the sum over
`S ⊆ closedBall 0 r` is at most the `finsum`. -/
theorem sum_analyticOrderNatAt_le_log_div {F : ℂ → ℂ} (hF : Differentiable ℂ F) (h0 : F 0 ≠ 0)
    {r M : ℝ} (hr : 0 < r) (hM : 1 ≤ M) (hbound : ∀ z : ℂ, ‖z‖ = 2 * r → ‖F z‖ ≤ M)
    {S : Finset ℂ} (hS : ∀ ρ ∈ S, ‖ρ‖ ≤ r) :
    ∑ ρ ∈ S, (analyticOrderNatAt F ρ : ℝ) ≤ Real.log (M / ‖F 0‖) / Real.log 2 := by
  classical
  have han : AnalyticOnNhd ℂ F (closedBall 0 |2 * r|) := fun x _ ↦ hF.analyticAt x
  have hanr : AnalyticOnNhd ℂ F (closedBall 0 |r|) := fun x _ ↦ hF.analyticAt x
  have h2r : |2 * r| = 2 * r := abs_of_pos (by linarith)
  have hrr : |r| = r := abs_of_pos hr
  have hJ := AnalyticOnNhd.sum_divisor_le (c := 0) (r := r) (R := 2 * r) (M := M)
    (by rw [hrr]; exact hr) (by rw [hrr, h2r]; linarith) hM han h0
    (fun z hz ↦ hbound z (by rwa [mem_sphere_zero_iff_norm, h2r] at hz))
  have hdiv2 : 2 * r / r = 2 := by field_simp
  rw [hdiv2] at hJ
  refine le_trans ?_ hJ
  have hfin : (Function.support (MeromorphicOn.divisor F (closedBall 0 |r|))).Finite :=
    (MeromorphicOn.divisor F (closedBall 0 |r|)).finiteSupport (isCompact_closedBall 0 |r|)
  have hDnn : ∀ x, 0 ≤ MeromorphicOn.divisor F (closedBall 0 |r|) x := fun x ↦
    MeromorphicOn.AnalyticOnNhd.divisor_nonneg hanr x
  have hDS : ∀ ρ ∈ S, ((MeromorphicOn.divisor F (closedBall 0 |r|) ρ : ℤ) : ℝ)
      = (analyticOrderNatAt F ρ : ℝ) := by
    intro ρ hρ
    have htop := analyticOrderAt_ne_top_of_entire hF h0 ρ
    rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hanr
      (by rw [mem_closedBall_zero_iff, hrr]; exact hS ρ hρ), ← Nat.cast_analyticOrderNatAt htop]
    simp
  rw [finsum_eq_sum_of_support_subset (s := hfin.toFinset ∪ S) _
    (fun x hx ↦ by
      simp only [Finset.coe_union, Set.Finite.coe_toFinset]
      exact Or.inl hx)]
  push_cast
  calc ∑ ρ ∈ S, (analyticOrderNatAt F ρ : ℝ)
      = ∑ ρ ∈ S, ((MeromorphicOn.divisor F (closedBall 0 |r|) ρ : ℤ) : ℝ) :=
        Finset.sum_congr rfl fun ρ hρ ↦ (hDS ρ hρ).symm
    _ ≤ ∑ ρ ∈ hfin.toFinset ∪ S, ((MeromorphicOn.divisor F (closedBall 0 |r|) ρ : ℤ) : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_right
          (fun x _ _ ↦ by exact_mod_cast hDnn x)

/-- **J1** (proved from J1a). Zero counting for order ≤ 1: `n(r) ≤ A r log (2 + r)` for `r ≥ 1`. -/
theorem sum_analyticOrderNatAt_le {F : ℂ → ℂ} (hF : Differentiable ℂ F) (h0 : F 0 ≠ 0) {C : ℝ}
    (hgrowth : ∀ z : ℂ, ‖F z‖ ≤ Real.exp (C * (1 + ‖z‖) * Real.log (2 + ‖z‖))) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ r : ℝ, 1 ≤ r → ∀ S : Finset ℂ, (∀ ρ ∈ S, ‖ρ‖ ≤ r) →
      ∑ ρ ∈ S, (analyticOrderNatAt F ρ : ℝ) ≤ A * r * Real.log (2 + r) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  set C' := max C 0 with hC'
  have hC'0 : 0 ≤ C' := le_max_right _ _
  set L0 := |Real.log ‖F 0‖| with hL0
  have hL00 : 0 ≤ L0 := abs_nonneg _
  refine ⟨(6 * C' + L0 / Real.log 2) / Real.log 2, by positivity, fun r hr S hS ↦ ?_⟩
  have hr0 : 0 < r := by linarith
  have hlogr : Real.log 2 ≤ Real.log (2 + r) := Real.log_le_log (by norm_num) (by linarith)
  have hlogr0 : 0 < Real.log (2 + r) := lt_of_lt_of_le hlog2 hlogr
  have hlog2r : Real.log (2 + 2 * r) ≤ 2 * Real.log (2 + r) := by
    have h2 : Real.log ((2 + r) ^ 2) = 2 * Real.log (2 + r) := by
      rw [Real.log_pow]
      norm_num
    rw [← h2]
    exact Real.log_le_log (by linarith) (by nlinarith)
  have hlog2r0 : 0 ≤ Real.log (2 + 2 * r) := Real.log_nonneg (by linarith)
  set M := Real.exp (C' * (1 + 2 * r) * Real.log (2 + 2 * r)) with hM
  have hM1 : 1 ≤ M := Real.one_le_exp (by positivity)
  have hb : ∀ z : ℂ, ‖z‖ = 2 * r → ‖F z‖ ≤ M := by
    intro z hz
    refine (hgrowth z).trans (Real.exp_le_exp.mpr ?_)
    rw [hz]
    have : C ≤ C' := le_max_left _ _
    gcongr
  refine (sum_analyticOrderNatAt_le_log_div hF h0 hr0 hM1 hb hS).trans ?_
  rw [div_le_iff₀ hlog2, Real.log_div (by positivity) (norm_ne_zero_iff.mpr h0), hM, Real.log_exp]
  have h1 : -Real.log ‖F 0‖ ≤ L0 := neg_le_abs _
  have h2 : C' * (1 + 2 * r) * Real.log (2 + 2 * r) ≤ 6 * C' * (r * Real.log (2 + r)) := by
    calc C' * (1 + 2 * r) * Real.log (2 + 2 * r)
        ≤ C' * (3 * r) * (2 * Real.log (2 + r)) := by gcongr; linarith
      _ = 6 * C' * (r * Real.log (2 + r)) := by ring
  have h3 : L0 ≤ L0 / Real.log 2 * (r * Real.log (2 + r)) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hlog2]
    have : Real.log 2 ≤ r * Real.log (2 + r) := by nlinarith
    exact mul_le_mul_of_nonneg_left this hL00
  have h4 : (6 * C' + L0 / Real.log 2) / Real.log 2 * r * Real.log (2 + r) * Real.log 2 =
      6 * C' * (r * Real.log (2 + r)) + L0 / Real.log 2 * (r * Real.log (2 + r)) := by
    field_simp
  rw [h4]
  linarith

/-! ## J2: convergence exponent -/

/-- Dyadic majorant of `1 / (1 + x²)` used in J2. -/
theorem one_div_one_add_sq_le_sum (K : ℕ) : ∀ x : ℝ, 0 ≤ x → x ≤ 2 ^ K →
    1 / (1 + x ^ 2) ≤
      ∑ k ∈ Finset.range (K + 1), 4 * (1 / 4 : ℝ) ^ k * (if x ≤ 2 ^ k then 1 else 0) := by
  induction K with
  | zero =>
    intro x hx0 hx
    simp only [zero_add, Finset.range_one, Finset.sum_singleton, pow_zero] at hx ⊢
    rw [ite_eq_left hx]
    have h : 1 / (1 + x ^ 2) ≤ 1 := by
      rw [div_le_one (by positivity)]
      nlinarith
    linarith
  | succ K ih =>
    intro x hx0 hx
    rw [Finset.sum_range_succ]
    by_cases hxK : x ≤ 2 ^ K
    · have h := ih x hx0 hxK
      have hnn : 0 ≤ 4 * (1 / 4 : ℝ) ^ (K + 1) * (if x ≤ 2 ^ (K + 1) then 1 else 0) :=
        mul_nonneg (by positivity) (by rw [ite_eq_left hx]; norm_num)
      linarith
    · push Not at hxK
      have hsum : 0 ≤ ∑ k ∈ Finset.range (K + 1),
          4 * (1 / 4 : ℝ) ^ k * (if x ≤ 2 ^ k then (1 : ℝ) else 0) :=
        Finset.sum_nonneg fun k _ ↦ mul_nonneg (by positivity) (by split_ifs <;> norm_num)
      rw [ite_eq_left hx]
      have h4 : (4 : ℝ) ^ K < x ^ 2 := by
        have h : (4 : ℝ) ^ K = (2 ^ K) ^ 2 := by
          rw [← pow_mul, mul_comm, pow_mul]
          norm_num
        rw [h]
        exact pow_lt_pow_left₀ hxK (by positivity) (by norm_num)
      have e : 4 * (1 / 4 : ℝ) ^ (K + 1) * 1 = 1 / 4 ^ K := by
        rw [one_div_pow, pow_succ]
        field_simp
      have h1 : 1 / (1 + x ^ 2) ≤ 4 * (1 / 4 : ℝ) ^ (K + 1) * 1 := by
        rw [e]
        exact one_div_le_one_div_of_le (by positivity) (by linarith)
      linarith

/-- **J2** (proved). A counting bound `n(r) ≤ A r log (2 + r)` implies `∑ m ρ / (1 + ‖ρ‖²) < ∞`.

Proof sketch (dyadic, no integrals): by `summable_of_sum_le` it suffices to bound finite partial
sums.  For `x ≥ 0`, `1 / (1 + x²) ≤ 4 ∑_{k ≥ 0} 4^{-k} 1[x ≤ 2^k]` (take the least `k` with
`x ≤ 2^k`; then `2^k ≤ 2 max x 1`).  Exchanging the finite sum over `ρ ∈ S` with the sum over `k`
and using the hypothesis with `r = 2^k` on `S.filter (‖·‖ ≤ 2^k)` gives the bound
`4 ∑_k 4^{-k} A 2^k log (2 + 2^k) ≤ 4 A ∑_k (k + 2) 2^{-k} < ∞`
(`summable_pow_mul_geometric_of_norm_lt_one`). -/
theorem summable_div_one_add_sq_of_count {m : ℂ → ℕ} {A : ℝ}
    (hcount : ∀ r : ℝ, 1 ≤ r → ∀ S : Finset ℂ, (∀ ρ ∈ S, ‖ρ‖ ≤ r) →
      ∑ ρ ∈ S, (m ρ : ℝ) ≤ A * r * Real.log (2 + r)) :
    Summable fun ρ : ℂ ↦ (m ρ : ℝ) / (1 + ‖ρ‖ ^ 2) := by
  classical
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hA : 0 ≤ A := by
    have h := hcount 1 le_rfl ∅ (by simp)
    simp only [Finset.sum_empty, mul_one] at h
    have h3 : 0 < Real.log (2 + 1) := Real.log_pos (by norm_num)
    exact nonneg_of_mul_nonneg_left h h3
  set d : ℕ → ℝ := fun k ↦ ((k : ℝ) + 2) * (1 / 2 : ℝ) ^ k with hd
  have hdsum : Summable d := by
    have h1 : Summable fun k : ℕ ↦ (k : ℝ) ^ 1 * (1 / 2 : ℝ) ^ k :=
      summable_pow_mul_geometric_of_norm_lt_one 1 (by norm_num)
    have h2 : Summable fun k : ℕ ↦ 2 * (1 / 2 : ℝ) ^ k :=
      (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left 2
    refine (h1.add h2).congr fun k ↦ ?_
    simp only [hd, pow_one]
    ring
  have hd0 : ∀ k, 0 ≤ d k := fun k ↦ by positivity
  refine summable_of_sum_le (c := 4 * A * Real.log 2 * ∑' k, d k) (fun ρ ↦ by positivity)
    fun u ↦ ?_
  obtain ⟨K, hK⟩ : ∃ K : ℕ, ∀ ρ ∈ u, ‖ρ‖ ≤ 2 ^ K := by
    obtain ⟨K, hK⟩ := pow_unbounded_of_one_lt (1 + ∑ ρ ∈ u, ‖ρ‖) (one_lt_two : (1 : ℝ) < 2)
    refine ⟨K, fun ρ hρ ↦ ?_⟩
    have := Finset.single_le_sum (f := fun ρ : ℂ ↦ ‖ρ‖) (fun ρ _ ↦ norm_nonneg ρ) hρ
    linarith
  calc ∑ ρ ∈ u, (m ρ : ℝ) / (1 + ‖ρ‖ ^ 2)
      ≤ ∑ ρ ∈ u, ∑ k ∈ Finset.range (K + 1),
          4 * (1 / 4 : ℝ) ^ k * (if ‖ρ‖ ≤ 2 ^ k then (m ρ : ℝ) else 0) := by
        refine Finset.sum_le_sum fun ρ hρ ↦ ?_
        have h := one_div_one_add_sq_le_sum K ‖ρ‖ (norm_nonneg ρ) (hK ρ hρ)
        have hm : (0 : ℝ) ≤ m ρ := Nat.cast_nonneg _
        calc (m ρ : ℝ) / (1 + ‖ρ‖ ^ 2) = (m ρ : ℝ) * (1 / (1 + ‖ρ‖ ^ 2)) := by ring
          _ ≤ (m ρ : ℝ) * ∑ k ∈ Finset.range (K + 1),
                4 * (1 / 4 : ℝ) ^ k * (if ‖ρ‖ ≤ 2 ^ k then 1 else 0) := by gcongr
          _ = ∑ k ∈ Finset.range (K + 1),
                4 * (1 / 4 : ℝ) ^ k * (if ‖ρ‖ ≤ 2 ^ k then (m ρ : ℝ) else 0) := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun k _ ↦ ?_
              split_ifs <;> ring
    _ = ∑ k ∈ Finset.range (K + 1),
          4 * (1 / 4 : ℝ) ^ k * ∑ ρ ∈ u.filter (fun ρ ↦ ‖ρ‖ ≤ 2 ^ k), (m ρ : ℝ) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ ↦ ?_
        rw [← Finset.mul_sum, Finset.sum_filter]
    _ ≤ ∑ k ∈ Finset.range (K + 1), 4 * A * Real.log 2 * d k := by
        refine Finset.sum_le_sum fun k _ ↦ ?_
        have h2k : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
        have hc := hcount (2 ^ k) h2k (u.filter fun ρ ↦ ‖ρ‖ ≤ 2 ^ k)
          (fun ρ hρ ↦ (Finset.mem_filter.mp hρ).2)
        have hlog : Real.log (2 + 2 ^ k) ≤ ((k : ℝ) + 2) * Real.log 2 := by
          have h : Real.log ((2 : ℝ) ^ (k + 2)) = ((k : ℝ) + 2) * Real.log 2 := by
            rw [Real.log_pow]
            push_cast
            ring
          rw [← h]
          apply Real.log_le_log (by positivity)
          rw [pow_add]
          nlinarith
        have hc' : ∑ ρ ∈ u.filter (fun ρ ↦ ‖ρ‖ ≤ 2 ^ k), (m ρ : ℝ)
            ≤ A * 2 ^ k * (((k : ℝ) + 2) * Real.log 2) := hc.trans (by gcongr)
        calc 4 * (1 / 4 : ℝ) ^ k * ∑ ρ ∈ u.filter (fun ρ ↦ ‖ρ‖ ≤ 2 ^ k), (m ρ : ℝ)
            ≤ 4 * (1 / 4 : ℝ) ^ k * (A * 2 ^ k * (((k : ℝ) + 2) * Real.log 2)) := by gcongr
          _ = 4 * A * Real.log 2 * (((k : ℝ) + 2) * ((1 / 4 : ℝ) ^ k * 2 ^ k)) := by ring
          _ = 4 * A * Real.log 2 * d k := by
              have e : (1 / 4 : ℝ) ^ k * 2 ^ k = (1 / 2) ^ k := by
                rw [← mul_pow]
                norm_num
              rw [e]
    _ = 4 * A * Real.log 2 * ∑ k ∈ Finset.range (K + 1), d k := by rw [Finset.mul_sum]
    _ ≤ 4 * A * Real.log 2 * ∑' k, d k := by
        gcongr
        exact hdsum.sum_le_tsum _ (fun k _ ↦ hd0 k)

/-! ## J3: consequences of the convergence exponent -/

/-- If `∑ m ρ / (1 + ‖ρ‖²)` converges, only finitely many `ρ` with `m ρ ≠ 0` lie in a ball. -/
theorem finite_setOf_ne_zero_norm_le {m : ℂ → ℕ}
    (hsum : Summable fun ρ : ℂ ↦ (m ρ : ℝ) / (1 + ‖ρ‖ ^ 2)) (R : ℝ) :
    {ρ : ℂ | m ρ ≠ 0 ∧ ‖ρ‖ ≤ R}.Finite := by
  have hpos : (0 : ℝ) < 1 / (1 + R ^ 2) := by positivity
  have hev : ∀ᶠ ρ in cofinite, (m ρ : ℝ) / (1 + ‖ρ‖ ^ 2) < 1 / (1 + R ^ 2) :=
    hsum.tendsto_cofinite_zero.eventually (gt_mem_nhds hpos)
  refine (eventually_cofinite.mp hev).subset ?_
  rintro ρ ⟨hm, hR⟩
  simp only [Set.mem_ofPred_eq, not_lt]
  have h1 : (1 : ℝ) ≤ m ρ := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hm
  have h2 : ‖ρ‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hR 2
  calc 1 / (1 + R ^ 2) ≤ 1 / (1 + ‖ρ‖ ^ 2) := by gcongr
    _ ≤ (m ρ : ℝ) / (1 + ‖ρ‖ ^ 2) := by gcongr

/-- Pointwise bound for the Hadamard summand far from `s`. -/
theorem norm_one_div_sub_add_le {s ρ : ℂ} (hbig : 2 * ‖s‖ + 1 < ‖ρ‖) :
    ‖1 / (s - ρ) + 1 / ρ‖ ≤ 4 * ‖s‖ / (1 + ‖ρ‖ ^ 2) := by
  have hs0 : 0 ≤ ‖s‖ := norm_nonneg s
  have hρpos : 0 < ‖ρ‖ := by linarith
  have hρ0 : ρ ≠ 0 := norm_pos_iff.mp hρpos
  have hz : ‖ρ‖ / 2 ≤ ‖s - ρ‖ := by
    have := norm_sub_norm_le ρ s
    rw [norm_sub_rev] at this
    linarith
  have hzpos : 0 < ‖s - ρ‖ := by linarith
  have hsρ : s - ρ ≠ 0 := norm_pos_iff.mp hzpos
  have heq : 1 / (s - ρ) + 1 / ρ = s / ((s - ρ) * ρ) := by
    field_simp
    ring
  rw [heq, norm_div, norm_mul, div_le_div_iff₀ (by positivity) (by positivity)]
  have h1 : 1 + ‖ρ‖ ^ 2 ≤ 4 * (‖s - ρ‖ * ‖ρ‖) := by nlinarith
  calc ‖s‖ * (1 + ‖ρ‖ ^ 2) ≤ ‖s‖ * (4 * (‖s - ρ‖ * ‖ρ‖)) := by gcongr
    _ = 4 * ‖s‖ * (‖s - ρ‖ * ‖ρ‖) := by ring

/-- **J3** (proved). Absolute convergence of the Hadamard partial-fraction series. -/
theorem summable_norm_mul_one_div_sub_add {m : ℂ → ℕ}
    (hsum : Summable fun ρ : ℂ ↦ (m ρ : ℝ) / (1 + ‖ρ‖ ^ 2)) (s : ℂ) :
    Summable fun ρ : ℂ ↦ ‖(m ρ : ℂ) * (1 / (s - ρ) + 1 / ρ)‖ := by
  refine Summable.of_norm_bounded_eventually (hsum.mul_left (4 * ‖s‖)) ?_
  rw [eventually_cofinite]
  refine (finite_setOf_ne_zero_norm_le hsum (2 * ‖s‖ + 1)).subset ?_
  intro ρ hρ
  simp only [Set.mem_ofPred_eq, not_le] at hρ ⊢
  by_contra hcon
  refine absurd hρ (not_lt.mpr ?_)
  by_cases hm : m ρ = 0
  · simp [hm]
  have hbig : 2 * ‖s‖ + 1 < ‖ρ‖ := by
    by_contra h
    exact hcon ⟨hm, not_lt.mp h⟩
  have hb := norm_one_div_sub_add_le hbig
  rw [norm_norm, norm_mul, Complex.norm_natCast]
  calc (m ρ : ℝ) * ‖1 / (s - ρ) + 1 / ρ‖ ≤ (m ρ : ℝ) * (4 * ‖s‖ / (1 + ‖ρ‖ ^ 2)) := by gcongr
    _ = 4 * ‖s‖ * ((m ρ : ℝ) / (1 + ‖ρ‖ ^ 2)) := by ring

end Exp7.EF.HF1
