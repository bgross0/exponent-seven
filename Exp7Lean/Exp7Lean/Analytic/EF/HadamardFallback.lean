import Exp7Lean.Analytic.EF.HadamardInput

/-!
# Explicit formula blueprint: in-house decomposition of the Hadamard input (fallback)

**Not on the import path of `Main.lean`.**  This file only records the statements into which
H1/H2 of `HadamardInput.lean` decompose if the Tau Ceti library is *not* imported.  See
`BLUEPRINT.md`, section "The Hadamard input", for the proof plan and size estimates.

Route: differentiated Poisson–Jensen formula on discs `|z| < R`, `R → ∞`
(Mathlib: `MeromorphicOn.circleAverage_log_norm` and the Poisson–Jensen formula in
`Mathlib/Analysis/Complex/JensenFormula.lean`; the Schwarz/Herglotz kernel calculus
`hasDerivAt_circleAverage_herglotzRieszKernel_smul` in `Mathlib/Analysis/Complex/Poisson.lean`)
instead of canonical products.
-/

namespace Exp7.EF.Fallback

open Complex

variable {N : ℕ} [NeZero N]

/-- The entire completion `ξ_χ(s) = N^{s/2} Λ(s, χ)` (so that `ξ_χ(1-s) = W(χ) ξ_{χ⁻¹}(s)`). -/
noncomputable def xi (χ : DirichletCharacter ℂ N) (s : ℂ) : ℂ :=
  (N : ℂ) ^ (s / 2) * χ.completedLFunction s

/-- **HF1** (XL, pure complex analysis). Hadamard's partial fractions for an entire function with
`F 0 ≠ 0` and `log ‖F z‖ ≤ C (1+‖z‖) log (2+‖z‖)`: the zeros satisfy `∑ m_ρ/(1+|ρ|²) < ∞` and
`F'/F(s) = F'/F(0) + ∑_ρ m_ρ (1/(s-ρ) + 1/ρ)` (absolutely convergent) off the zeros.

Plan: (i) Jensen (`AnalyticOnNhd.circleAverage_log_norm`) gives `n(R) ≤ C' R log R`, hence the
summability; (ii) differentiate the Poisson–Jensen representation of `log ‖F‖` on `|z| < R` to get
`F'/F(s) - F'/F(0) = ∑_{|ρ|<R} m_ρ (1/(s-ρ) + 1/ρ) + E_R(s)` with
`|E_R(s)| ≤ C'' |s| (log R)/R` for `R ≥ 2|s|` (uses only the *upper* bound on `log ‖F‖` and Jensen
for `∫ |log ‖F‖|`); (iii) let `R → ∞`. -/
theorem logDeriv_eq_add_tsum_of_order_one {F : ℂ → ℂ} (hF : Differentiable ℂ F) (h0 : F 0 ≠ 0)
    (hgrowth : ∃ C : ℝ, ∀ z : ℂ, ‖F z‖ ≤ Real.exp (C * (1 + ‖z‖) * Real.log (2 + ‖z‖))) :
    Summable (fun ρ : ℂ ↦ (analyticOrderNatAt F ρ : ℝ) / (1 + ‖ρ‖ ^ 2)) ∧
    (∀ s : ℂ, Summable (fun ρ : ℂ ↦ ‖(analyticOrderNatAt F ρ : ℂ) * (1 / (s - ρ) + 1 / ρ)‖)) ∧
    ∀ s : ℂ, F s ≠ 0 →
      logDeriv F s = logDeriv F 0 +
        ∑' ρ : ℂ, (analyticOrderNatAt F ρ : ℂ) * (1 / (s - ρ) + 1 / ρ) := by
  sorry

/-! ### Helpers for HF2 (`xi_growth`)

Route actually used: no functional equation and no Phragmén–Lindelöf.  For `χ ≠ 1` the completed
`L`-function is `N^{-s} ∑_j χ(j) (Λ₀^{even}(j/N, s) + Λ^{odd}(j/N, s))`, where the two completed
Hurwitz zeta functions are Mellin transforms (at `s/2`, `(s+1)/2`) of theta kernels that decay like
`e^{-pt}` at `∞` and like `t^{-k} e^{-p/t}` at `0`.  Such a Mellin transform is bounded by
`A m! (2/p)^{m+1}`, `m ≈ |Re s|`, which is `exp (O(|s| log |s|))`. -/

/-- `1 ≤ 2 log (2 + x)` for `x ≥ 0`. -/
private lemma hf2_one_le_two_mul_log {x : ℝ} (hx : 0 ≤ x) : 1 ≤ 2 * Real.log (2 + x) := by
  have h1 : Real.log 2 ≤ Real.log (2 + x) := Real.log_le_log (by norm_num) (by linarith)
  have h2 := Real.log_two_gt_d9
  norm_num at h2
  linarith

/-- `K (1 + x) ≤ 2 K (1 + x) log (2 + x)` for `K, x ≥ 0`. -/
private lemma hf2_mul_one_add_le {K x : ℝ} (hK : 0 ≤ K) (hx : 0 ≤ x) :
    K * (1 + x) ≤ 2 * K * (1 + x) * Real.log (2 + x) := by
  have h := hf2_one_le_two_mul_log hx
  have h' : 0 ≤ K * (1 + x) := by positivity
  nlinarith

/-- `D · m! · b^(m+1) ≤ exp (C (1+x) log (2+x))` as soon as `m ≤ K (1 + x)`. -/
private lemma hf2_factorial_mul_pow_le (D b K : ℝ) (hD : 0 ≤ D) (hb : 1 ≤ b) (hK : 0 ≤ K) :
    ∃ C : ℝ, ∀ (m : ℕ) (x : ℝ), 0 ≤ x → (m : ℝ) ≤ K * (1 + x) →
      D * ((m.factorial : ℝ) * b ^ (m + 1)) ≤ Real.exp (C * (1 + x) * Real.log (2 + x)) := by
  set K' : ℝ := max 1 K with hK'
  have hK'1 : 1 ≤ K' := le_max_left _ _
  have hKK' : K ≤ K' := le_max_right _ _
  have hlK' : 0 ≤ Real.log K' := Real.log_nonneg hK'1
  have hlb : 0 ≤ Real.log b := Real.log_nonneg hb
  refine ⟨2 * D + K * (2 * Real.log K' + 1) + 2 * ((K + 1) * Real.log b), fun m x hx hm ↦ ?_⟩
  have hL := hf2_one_le_two_mul_log hx
  have hL0 : 0 ≤ Real.log (2 + x) := by linarith
  have h1 : D ≤ Real.exp (2 * D * (1 + x) * Real.log (2 + x)) := by
    calc D ≤ D * (1 + x) := by nlinarith
      _ ≤ 2 * D * (1 + x) * Real.log (2 + x) := hf2_mul_one_add_le hD hx
      _ ≤ _ := by linarith [Real.add_one_le_exp (2 * D * (1 + x) * Real.log (2 + x))]
  have h2 : (m.factorial : ℝ) ≤
      Real.exp (K * (2 * Real.log K' + 1) * (1 + x) * Real.log (2 + x)) := by
    have hm' : (m : ℝ) ≤ K' * (2 + x) := by nlinarith
    have hpos : 0 < K' * (2 + x) := by positivity
    calc (m.factorial : ℝ) ≤ (m : ℝ) ^ m := by exact_mod_cast Nat.factorial_le_pow m
      _ ≤ (K' * (2 + x)) ^ m := pow_le_pow_left₀ (Nat.cast_nonneg m) hm' m
      _ = Real.exp (m * Real.log (K' * (2 + x))) := by
          rw [Real.exp_natCast_mul, Real.exp_log hpos]
      _ ≤ _ := by
          apply Real.exp_le_exp.mpr
          rw [Real.log_mul (by positivity) (by positivity)]
          have h0 : 0 ≤ Real.log K' + Real.log (2 + x) := by positivity
          have h00 : 0 ≤ K * (1 + x) := by positivity
          calc (m : ℝ) * (Real.log K' + Real.log (2 + x))
              ≤ K * (1 + x) * (Real.log K' + Real.log (2 + x)) := by gcongr
            _ ≤ K * (1 + x) * ((2 * Real.log K' + 1) * Real.log (2 + x)) := by
                apply mul_le_mul_of_nonneg_left _ h00
                nlinarith
            _ = _ := by ring
  have h3 : b ^ (m + 1) ≤ Real.exp (2 * ((K + 1) * Real.log b) * (1 + x) * Real.log (2 + x)) := by
    calc b ^ (m + 1) = Real.exp (((m + 1 : ℕ) : ℝ) * Real.log b) := by
          rw [Real.exp_natCast_mul, Real.exp_log (by linarith)]
      _ ≤ _ := by
          apply Real.exp_le_exp.mpr
          push_cast
          calc ((m : ℝ) + 1) * Real.log b ≤ ((K + 1) * (1 + x)) * Real.log b := by
                gcongr; nlinarith
            _ = (K + 1) * Real.log b * (1 + x) := by ring
            _ ≤ 2 * ((K + 1) * Real.log b) * (1 + x) * Real.log (2 + x) :=
                hf2_mul_one_add_le (by positivity) hx
  calc D * ((m.factorial : ℝ) * b ^ (m + 1))
      ≤ Real.exp (2 * D * (1 + x) * Real.log (2 + x)) *
        (Real.exp (K * (2 * Real.log K' + 1) * (1 + x) * Real.log (2 + x)) *
          Real.exp (2 * ((K + 1) * Real.log b) * (1 + x) * Real.log (2 + x))) := by gcongr
    _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring

/-- `u^m e^{-pu} ≤ m! / p^m`. -/
private lemma hf2_pow_mul_exp_neg_le {p u : ℝ} (hp : 0 < p) (hu : 0 ≤ u) (m : ℕ) :
    u ^ m * Real.exp (-(p * u)) ≤ m.factorial / p ^ m := by
  have h := Real.pow_div_factorial_le_exp (x := p * u) (by positivity) m
  rw [div_le_iff₀ (by positivity)] at h
  rw [le_div_iff₀ (pow_pos hp m)]
  calc u ^ m * Real.exp (-(p * u)) * p ^ m = (p * u) ^ m * Real.exp (-(p * u)) := by
        rw [mul_pow]; ring
    _ ≤ Real.exp (p * u) * m.factorial * Real.exp (-(p * u)) := by gcongr
    _ = m.factorial := by rw [mul_right_comm, ← Real.exp_add]; simp

/-- Growth of the Mellin transform of a function with exponential decay at `∞` and at `0`. -/
private lemma hf2_norm_mellin_le_of_exp_decay {h : ℝ → ℂ} {A p k : ℝ} (hp : 0 < p)
    (hconv : ∀ s : ℂ, MellinConvergent h s)
    (htop : ∀ t : ℝ, 1 < t → ‖h t‖ ≤ A * Real.exp (-(p * t)))
    (hzero : ∀ t : ℝ, 0 < t → t ≤ 1 → ‖h t‖ ≤ A * t ^ (-k) * Real.exp (-(p / t))) :
    ∃ C : ℝ, ∀ s z : ℂ, ‖s‖ ≤ 1 + ‖z‖ →
      ‖mellin h s‖ ≤ Real.exp (C * (1 + ‖z‖) * Real.log (2 + ‖z‖)) := by
  have hA : 0 ≤ A := by
    have h2 := (norm_nonneg _).trans (htop 2 (by norm_num))
    exact nonneg_of_mul_nonneg_left h2 (Real.exp_pos _)
  set b : ℝ := max 1 (2 / p) with hb
  have hb1 : 1 ≤ b := le_max_left _ _
  have hb2 : 2 / p ≤ b := le_max_right _ _
  obtain ⟨C, hC⟩ :=
    hf2_factorial_mul_pow_le (2 * A) b (|k| + 3) (by positivity) hb1 (by positivity)
  refine ⟨C, fun s z hsz ↦ ?_⟩
  set m : ℕ := ⌈|k| + 1 + |s.re|⌉₊ with hm
  have hm1 : |k| + 1 + |s.re| ≤ m := Nat.le_ceil _
  have hm2 : (m : ℝ) ≤ (|k| + 3) * (1 + ‖z‖) := by
    have h1 := (Nat.ceil_lt_add_one (by positivity : 0 ≤ |k| + 1 + |s.re|)).le
    have h3 : |s.re| ≤ ‖s‖ := Complex.abs_re_le_norm s
    nlinarith [norm_nonneg z, abs_nonneg k]
  refine le_trans ?_ (hC m ‖z‖ (norm_nonneg z) hm2)
  have hI := hconv s
  rw [MellinConvergent] at hI
  have hsplit : mellin h s = (∫ t in Set.Ioc (0 : ℝ) 1, (t : ℂ) ^ (s - 1) • h t) +
      ∫ t in Set.Ioi (1 : ℝ), (t : ℂ) ^ (s - 1) • h t := by
    rw [mellin, ← Set.Ioc_union_Ioi_eq_Ioi (zero_le_one' ℝ)]
    exact MeasureTheory.setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      (hI.mono_set Set.Ioc_subset_Ioi_self) (hI.mono_set (Set.Ioi_subset_Ioi zero_le_one))
  have hnorm : ∀ t : ℝ, 0 < t → ‖(t : ℂ) ^ (s - 1) • h t‖ = t ^ (s.re - 1) * ‖h t‖ := by
    intro t ht
    rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht]
    simp
  have hsk : k + 1 - s.re ≤ m := by linarith [le_abs_self k, neg_abs_le s.re]
  have hs1 : s.re - 1 ≤ m := by linarith [abs_nonneg k, le_abs_self s.re]
  -- the piece over `(0, 1]`
  have h1 : ‖∫ t in Set.Ioc (0 : ℝ) 1, (t : ℂ) ^ (s - 1) • h t‖ ≤ A * (m.factorial / p ^ m) := by
    have key := MeasureTheory.norm_setIntegral_le_of_norm_le_const (μ := MeasureTheory.volume)
      (s := Set.Ioc (0 : ℝ) 1) (C := A * (m.factorial / p ^ m))
      (f := fun t : ℝ ↦ (t : ℂ) ^ (s - 1) • h t) (by simp) ?_
    · simpa [Real.volume_real_Ioc_of_le] using key
    rintro t ⟨ht0, ht1⟩
    rw [hnorm t ht0]
    have hu : 1 ≤ t⁻¹ := (one_le_inv₀ ht0).mpr ht1
    calc t ^ (s.re - 1) * ‖h t‖
        ≤ t ^ (s.re - 1) * (A * t ^ (-k) * Real.exp (-(p / t))) := by
          gcongr; exact hzero t ht0 ht1
      _ = A * (t⁻¹ ^ (k + 1 - s.re) * Real.exp (-(p * t⁻¹))) := by
          rw [Real.inv_rpow ht0.le, ← Real.rpow_neg ht0.le, div_eq_mul_inv]
          have e : t ^ (s.re - 1) * t ^ (-k) = t ^ (-(k + 1 - s.re)) := by
            rw [← Real.rpow_add ht0]; congr 1; ring
          rw [← e]; ring
      _ ≤ A * (t⁻¹ ^ m * Real.exp (-(p * t⁻¹))) := by
          gcongr
          rw [← Real.rpow_natCast]
          exact Real.rpow_le_rpow_of_exponent_le hu hsk
      _ ≤ A * (m.factorial / p ^ m) := by
          gcongr; exact hf2_pow_mul_exp_neg_le hp (by positivity) m
  -- the piece over `(1, ∞)`
  have hp2 : 0 < p / 2 := by positivity
  have h2 : ‖∫ t in Set.Ioi (1 : ℝ), (t : ℂ) ^ (s - 1) • h t‖ ≤
      A * (m.factorial / (p / 2) ^ m) * (2 / p) := by
    have hint : MeasureTheory.IntegrableOn
        (fun t : ℝ ↦ A * (m.factorial / (p / 2) ^ m) * Real.exp (-(p / 2) * t)) (Set.Ioi 1) :=
      (integrableOn_exp_mul_Ioi (by linarith) 1).const_mul _
    refine (MeasureTheory.norm_integral_le_of_norm_le hint ?_).trans ?_
    · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi fun t ht ↦ ?_
      have ht1 : (1 : ℝ) < t := ht
      have ht0 : 0 < t := by linarith
      rw [hnorm t ht0]
      calc t ^ (s.re - 1) * ‖h t‖ ≤ t ^ m * (A * Real.exp (-(p * t))) := by
            gcongr
            · rw [← Real.rpow_natCast]
              exact Real.rpow_le_rpow_of_exponent_le ht1.le hs1
            · exact htop t ht1
        _ = A * (t ^ m * Real.exp (-(p / 2 * t))) * Real.exp (-(p / 2) * t) := by
            rw [show -(p * t) = -(p / 2 * t) + -(p / 2) * t by ring, Real.exp_add]; ring
        _ ≤ A * (m.factorial / (p / 2) ^ m) * Real.exp (-(p / 2) * t) := by
            gcongr; exact hf2_pow_mul_exp_neg_le hp2 ht0.le m
    · rw [MeasureTheory.integral_const_mul, integral_exp_mul_Ioi (by linarith) 1]
      have hA' : 0 ≤ A * (m.factorial / (p / 2) ^ m) := by positivity
      apply mul_le_mul_of_nonneg_left _ hA'
      have he : Real.exp (-(p / 2) * 1) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
      rw [neg_div_neg_eq, div_le_div_iff₀ hp2 hp]
      nlinarith
  rw [hsplit]
  refine (norm_add_le _ _).trans ((add_le_add h1 h2).trans ?_)
  have hpinv : p⁻¹ ≤ b := by
    refine le_trans ?_ hb2
    rw [div_eq_mul_inv]
    nlinarith [inv_pos.mpr hp]
  have e1 : (m.factorial : ℝ) / p ^ m ≤ m.factorial * b ^ (m + 1) := by
    rw [div_eq_mul_inv, ← inv_pow]
    gcongr
    calc (p⁻¹) ^ m ≤ b ^ m := pow_le_pow_left₀ (by positivity) hpinv m
      _ ≤ b ^ (m + 1) := pow_le_pow_right₀ hb1 (Nat.le_succ m)
  have e2 : (m.factorial : ℝ) / (p / 2) ^ m * (2 / p) ≤ m.factorial * b ^ (m + 1) := by
    have e : (m.factorial : ℝ) / (p / 2) ^ m * (2 / p) = m.factorial * (2 / p) ^ (m + 1) := by
      rw [pow_succ, div_eq_mul_inv, ← inv_pow, inv_div]; ring
    rw [e]
    gcongr
  calc A * (m.factorial / p ^ m) + A * (m.factorial / (p / 2) ^ m) * (2 / p)
      = A * (m.factorial / p ^ m) + A * (m.factorial / (p / 2) ^ m * (2 / p)) := by ring
    _ ≤ A * (m.factorial * b ^ (m + 1)) + A * (m.factorial * b ^ (m + 1)) := by gcongr
    _ = 2 * A * (m.factorial * b ^ (m + 1)) := by ring

/-- A continuous function on `(0, ∞)` which is `O(e^{-pt})` at `∞` is `≤ A e^{-pt}` on `[1, ∞)`. -/
private lemma hf2_exists_forall_abs_le_mul_exp {φ : ℝ → ℝ} {p : ℝ}
    (hc : ContinuousOn φ (Set.Ioi 0))
    (hO : φ =O[Filter.atTop] fun x ↦ Real.exp (-p * x)) :
    ∃ A : ℝ, ∀ t : ℝ, 1 ≤ t → |φ t| ≤ A * Real.exp (-(p * t)) := by
  obtain ⟨c, hc'⟩ := hO.bound
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp hc'
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hc.mono (fun x hx ↦ lt_of_lt_of_le one_pos hx.1) : ContinuousOn φ (Set.Icc 1 (max T 1)))
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 1 ⟨le_rfl, le_max_right _ _⟩)
  refine ⟨|c| + B * Real.exp (|p| * max T 1), fun t ht ↦ ?_⟩
  have hE : 0 ≤ B * Real.exp (|p| * max T 1) := by positivity
  rcases le_total (max T 1) t with h | h
  · have h1 := hT t ((le_max_left _ _).trans h)
    rw [Real.norm_eq_abs, Real.norm_of_nonneg (Real.exp_pos _).le, neg_mul] at h1
    calc |φ t| ≤ c * Real.exp (-(p * t)) := h1
      _ ≤ (|c| + B * Real.exp (|p| * max T 1)) * Real.exp (-(p * t)) := by
          gcongr; linarith [le_abs_self c]
  · have h1 := hB t ⟨ht, h⟩
    rw [Real.norm_eq_abs] at h1
    have ht0 : 0 ≤ t := by linarith
    calc |φ t| ≤ B := h1
      _ = B * Real.exp (p * t) * Real.exp (-(p * t)) := by
          rw [mul_assoc, ← Real.exp_add]; simp
      _ ≤ (B * Real.exp (|p| * max T 1)) * Real.exp (-(p * t)) := by
          refine mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hB0) (Real.exp_pos _).le
          calc p * t ≤ |p| * t := by gcongr; exact le_abs_self p
            _ ≤ |p| * max T 1 := by gcongr
      _ ≤ _ := by gcongr; linarith [abs_nonneg c]

/-- Two exponentially decaying continuous functions share a decay rate and a constant. -/
private lemma hf2_exists_common_exp_decay {φ₁ φ₂ : ℝ → ℝ}
    (hc₁ : ContinuousOn φ₁ (Set.Ioi 0)) (hc₂ : ContinuousOn φ₂ (Set.Ioi 0))
    (h₁ : ∃ p : ℝ, 0 < p ∧ φ₁ =O[Filter.atTop] fun x ↦ Real.exp (-p * x))
    (h₂ : ∃ p : ℝ, 0 < p ∧ φ₂ =O[Filter.atTop] fun x ↦ Real.exp (-p * x)) :
    ∃ A p : ℝ, 0 ≤ A ∧ 0 < p ∧ ∀ t : ℝ, 1 ≤ t →
      |φ₁ t| ≤ A * Real.exp (-(p * t)) ∧ |φ₂ t| ≤ A * Real.exp (-(p * t)) := by
  obtain ⟨p₁, hp₁, hO₁⟩ := h₁
  obtain ⟨p₂, hp₂, hO₂⟩ := h₂
  obtain ⟨A₁, hA₁⟩ := hf2_exists_forall_abs_le_mul_exp hc₁ hO₁
  obtain ⟨A₂, hA₂⟩ := hf2_exists_forall_abs_le_mul_exp hc₂ hO₂
  have hA₁0 : 0 ≤ A₁ :=
    nonneg_of_mul_nonneg_left ((abs_nonneg _).trans (hA₁ 1 le_rfl)) (Real.exp_pos _)
  refine ⟨max A₁ A₂, min p₁ p₂, hA₁0.trans (le_max_left _ _), lt_min hp₁ hp₂, fun t ht ↦ ?_⟩
  have ht0 : 0 ≤ t := by linarith
  have hA0 : 0 ≤ max A₁ A₂ := hA₁0.trans (le_max_left _ _)
  constructor
  · calc |φ₁ t| ≤ A₁ * Real.exp (-(p₁ * t)) := hA₁ t ht
      _ ≤ max A₁ A₂ * Real.exp (-(p₁ * t)) := by gcongr; exact le_max_left _ _
      _ ≤ max A₁ A₂ * Real.exp (-(min p₁ p₂ * t)) := by gcongr; exact min_le_left _ _
  · calc |φ₂ t| ≤ A₂ * Real.exp (-(p₂ * t)) := hA₂ t ht
      _ ≤ max A₁ A₂ * Real.exp (-(p₂ * t)) := by gcongr; exact le_max_right _ _
      _ ≤ max A₁ A₂ * Real.exp (-(min p₁ p₂ * t)) := by gcongr; exact min_le_right _ _

open HurwitzZeta in
/-- Order-one growth of the entire even completed Hurwitz zeta function. -/
private lemma hf2_growth_completedHurwitzZetaEven₀ (a : UnitAddCircle) :
    ∃ C : ℝ, ∀ z : ℂ, ‖completedHurwitzZetaEven₀ a z‖ ≤
      Real.exp (C * (1 + ‖z‖) * Real.log (2 + ‖z‖)) := by
  obtain ⟨A, p, hA, hp, hdec⟩ := hf2_exists_common_exp_decay
    (φ₁ := fun x ↦ evenKernel a x - (if a = 0 then 1 else 0)) (φ₂ := fun x ↦ cosKernel a x - 1)
    ((continuousOn_evenKernel a).sub continuousOn_const)
    ((continuousOn_cosKernel a).sub continuousOn_const)
    (isBigO_atTop_evenKernel_sub a) (isBigO_atTop_cosKernel_sub a)
  set P := hurwitzEvenFEPair a with hP
  have htop : ∀ t : ℝ, 1 < t → ‖P.f_modif t‖ ≤ A * Real.exp (-(p * t)) := by
    intro t ht
    have e : P.f_modif t = ((evenKernel a t - (if a = 0 then 1 else 0) : ℝ) : ℂ) := by
      simp only [WeakFEPair.f_modif, Pi.add_apply, Set.indicator_of_mem (Set.mem_Ioi.mpr ht),
        Set.indicator_of_notMem (Set.notMem_Ioo_of_ge ht.le), add_zero]
      simp only [hP, hurwitzEvenFEPair, Function.comp_apply]
      split_ifs <;> simp
    rw [e, Complex.norm_real, Real.norm_eq_abs]
    exact (hdec t ht.le).1
  have hzero : ∀ t : ℝ, 0 < t → t ≤ 1 →
      ‖P.f_modif t‖ ≤ A * t ^ (-(1 / 2 : ℝ)) * Real.exp (-(p / t)) := by
    intro t ht0 ht1
    rcases ht1.lt_or_eq with ht1 | rfl
    · have e : P.f_modif t = ((t ^ (-(1 / 2 : ℝ)) * (cosKernel a (1 / t) - 1) : ℝ) : ℂ) := by
        simp only [WeakFEPair.f_modif, Pi.add_apply,
          Set.indicator_of_notMem (Set.notMem_Ioi.mpr ht1.le),
          Set.indicator_of_mem (Set.mem_Ioo.mpr ⟨ht0, ht1⟩), zero_add]
        simp only [hP, hurwitzEvenFEPair, Function.comp_apply]
        rw [evenKernel_functional_equation, Real.rpow_neg ht0.le]
        push_cast
        simp
        ring
      rw [e, Complex.norm_real, Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (Real.rpow_nonneg ht0.le _)]
      have h1 : (1 : ℝ) ≤ 1 / t := by rw [le_div_iff₀ ht0]; linarith
      calc t ^ (-(1 / 2 : ℝ)) * |cosKernel a (1 / t) - 1|
          ≤ t ^ (-(1 / 2 : ℝ)) * (A * Real.exp (-(p * (1 / t)))) := by
            gcongr; exact (hdec (1 / t) h1).2
        _ = A * t ^ (-(1 / 2 : ℝ)) * Real.exp (-(p / t)) := by
            rw [mul_one_div]; ring
    · have e : P.f_modif 1 = 0 := by simp [WeakFEPair.f_modif]
      rw [e, norm_zero]
      positivity
  obtain ⟨C, hC⟩ := hf2_norm_mellin_le_of_exp_decay hp
    (fun s ↦ (P.isStrongFEPair_toStrongFEPair.hasMellin s).1) htop hzero
  refine ⟨C, fun z ↦ ?_⟩
  have h1 : ‖completedHurwitzZetaEven₀ a z‖ ≤ ‖mellin P.f_modif (z / 2)‖ := by
    rw [completedHurwitzZetaEven₀, WeakFEPair.Λ₀, norm_div]
    simp only [Complex.norm_ofNat]
    linarith [norm_nonneg (mellin P.f_modif (z / 2))]
  refine h1.trans (hC _ z ?_)
  rw [norm_div]
  simp only [Complex.norm_ofNat]
  linarith [norm_nonneg z]

open HurwitzZeta in
/-- Order-one growth of the odd completed Hurwitz zeta function. -/
private lemma hf2_growth_completedHurwitzZetaOdd (a : UnitAddCircle) :
    ∃ C : ℝ, ∀ z : ℂ, ‖completedHurwitzZetaOdd a z‖ ≤
      Real.exp (C * (1 + ‖z‖) * Real.log (2 + ‖z‖)) := by
  obtain ⟨A, p, hA, hp, hdec⟩ := hf2_exists_common_exp_decay
    (continuousOn_oddKernel a) (continuousOn_sinKernel a)
    (isBigO_atTop_oddKernel a) (isBigO_atTop_sinKernel a)
  set P := hurwitzOddFEPair a with hP
  have htop : ∀ t : ℝ, 1 < t → ‖P.f t‖ ≤ A * Real.exp (-(p * t)) := by
    intro t ht
    simp only [hP, hurwitzOddFEPair_f, Function.comp_apply, Complex.norm_real, Real.norm_eq_abs]
    exact (hdec t ht.le).1
  have hzero : ∀ t : ℝ, 0 < t → t ≤ 1 →
      ‖P.f t‖ ≤ A * t ^ (-(3 / 2 : ℝ)) * Real.exp (-(p / t)) := by
    intro t ht0 ht1
    simp only [hP, hurwitzOddFEPair_f, Function.comp_apply, Complex.norm_real, Real.norm_eq_abs]
    rw [oddKernel_functional_equation, abs_mul, Real.rpow_neg ht0.le, one_div,
      abs_of_nonneg (inv_nonneg.mpr (Real.rpow_nonneg ht0.le _))]
    have h1 : (1 : ℝ) ≤ 1 / t := by rw [le_div_iff₀ ht0]; linarith
    calc (t ^ (3 / 2 : ℝ))⁻¹ * |sinKernel a (1 / t)|
        ≤ (t ^ (3 / 2 : ℝ))⁻¹ * (A * Real.exp (-(p * (1 / t)))) := by
          gcongr; exact (hdec (1 / t) h1).2
      _ = A * (t ^ (3 / 2 : ℝ))⁻¹ * Real.exp (-(p / t)) := by
          rw [mul_one_div]; ring
  obtain ⟨C, hC⟩ := hf2_norm_mellin_le_of_exp_decay hp
    (fun s ↦ ((isStrong_hurwitzOddFEPair a).hasMellin s).1) htop hzero
  refine ⟨C, fun z ↦ ?_⟩
  have h1 : ‖completedHurwitzZetaOdd a z‖ ≤ ‖mellin P.f ((z + 1) / 2)‖ := by
    rw [completedHurwitzZetaOdd, (isStrong_hurwitzOddFEPair a).Λ_eq, norm_div]
    simp only [Complex.norm_ofNat]
    linarith [norm_nonneg (mellin P.f ((z + 1) / 2))]
  refine h1.trans (hC _ z ?_)
  rw [norm_div]
  simp only [Complex.norm_ofNat]
  have := norm_add_le z 1
  simp only [norm_one] at this
  linarith [norm_nonneg z]

/-- **HF2** (L). `ξ_χ` has order at most one. For `Re s ≥ 1/2`: `‖L(s,χ)‖ ≤ C N ‖s‖` (partial
summation, cf. `LSeries_eq_mul_integral` in `Mathlib/NumberTheory/LSeries/SumCoeff.lean`),
`‖Γ(z)‖ ≤ Γ(Re z) ≤ exp (C |z| log |z|)`; for `Re s ≤ 1/2` use the functional equation
`IsPrimitive.completedLFunction_one_sub` and `norm_rootNumber`. -/
theorem xi_growth (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) (hne : χ ≠ 1) :
    ∃ C : ℝ, ∀ z : ℂ, ‖xi χ z‖ ≤ Real.exp (C * (1 + ‖z‖) * Real.log (2 + ‖z‖)) := by
  have _ := hχ
  choose CE hCE using hf2_growth_completedHurwitzZetaEven₀
  choose CO hCO using hf2_growth_completedHurwitzZetaOdd
  have hN1 : N ≠ 1 := fun h ↦ hne (χ.level_one' h)
  have hNpos : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hNpos
  have hlN : 0 ≤ Real.log N := Real.log_nonneg hN1'
  set M : ℝ := ∑ j : ZMod N, (|CE (ZMod.toAddCircle j)| + |CO (ZMod.toAddCircle j)|) with hM
  refine ⟨4 * Real.log N + 4 * N + M, fun z ↦ ?_⟩
  have hx := norm_nonneg z
  have hL := hf2_one_le_two_mul_log hx
  have hG : 0 ≤ (1 + ‖z‖) * Real.log (2 + ‖z‖) := mul_nonneg (by linarith) (by linarith)
  have hxi : xi χ z = (N : ℂ) ^ (z / 2) * ((N : ℂ) ^ (-z) * ∑ j : ZMod N, χ j *
      (HurwitzZeta.completedHurwitzZetaEven₀ (ZMod.toAddCircle j) z +
        HurwitzZeta.completedHurwitzZetaOdd (ZMod.toAddCircle j) z)) := by
    rw [xi, DirichletCharacter.completedLFunction, ZMod.completedLFunction_eq, χ.map_zero' hN1,
      χ.sum_eq_zero_of_ne_one hne, ZMod.completedLFunction₀]
    simp [mul_add, Finset.sum_add_distrib]
  have hpow : ∀ w : ℂ, ‖w‖ ≤ 1 + ‖z‖ → ‖(N : ℂ) ^ w‖ ≤
      Real.exp (2 * Real.log N * (1 + ‖z‖) * Real.log (2 + ‖z‖)) := by
    intro w hw
    rw [Complex.norm_natCast_cpow_of_pos hNpos, Real.rpow_def_of_pos (by exact_mod_cast hNpos)]
    apply Real.exp_le_exp.mpr
    calc Real.log N * w.re ≤ Real.log N * (1 + ‖z‖) := by
          gcongr; exact ((le_abs_self _).trans (Complex.abs_re_le_norm w)).trans hw
      _ ≤ _ := hf2_mul_one_add_le hlN hx
  have hterm : ∀ j : ZMod N, ‖χ j * (HurwitzZeta.completedHurwitzZetaEven₀ (ZMod.toAddCircle j) z +
        HurwitzZeta.completedHurwitzZetaOdd (ZMod.toAddCircle j) z)‖ ≤
      2 * Real.exp (M * (1 + ‖z‖) * Real.log (2 + ‖z‖)) := by
    intro j
    have hjE : |CE (ZMod.toAddCircle j)| ≤ M := by
      refine le_trans ?_ (Finset.single_le_sum (f := fun j : ZMod N ↦
        |CE (ZMod.toAddCircle j)| + |CO (ZMod.toAddCircle j)|)
        (fun i _ ↦ by positivity) (Finset.mem_univ j))
      linarith [abs_nonneg (CO (ZMod.toAddCircle j))]
    have hjO : |CO (ZMod.toAddCircle j)| ≤ M := by
      refine le_trans ?_ (Finset.single_le_sum (f := fun j : ZMod N ↦
        |CE (ZMod.toAddCircle j)| + |CO (ZMod.toAddCircle j)|)
        (fun i _ ↦ by positivity) (Finset.mem_univ j))
      linarith [abs_nonneg (CE (ZMod.toAddCircle j))]
    have hmono : ∀ c : ℝ, |c| ≤ M → Real.exp (c * (1 + ‖z‖) * Real.log (2 + ‖z‖)) ≤
        Real.exp (M * (1 + ‖z‖) * Real.log (2 + ‖z‖)) := by
      intro c hc
      apply Real.exp_le_exp.mpr
      rw [mul_assoc, mul_assoc]
      exact mul_le_mul_of_nonneg_right ((le_abs_self c).trans hc) hG
    calc ‖χ j * (HurwitzZeta.completedHurwitzZetaEven₀ (ZMod.toAddCircle j) z +
          HurwitzZeta.completedHurwitzZetaOdd (ZMod.toAddCircle j) z)‖
        ≤ 1 * (Real.exp (M * (1 + ‖z‖) * Real.log (2 + ‖z‖)) +
            Real.exp (M * (1 + ‖z‖) * Real.log (2 + ‖z‖))) := by
          rw [norm_mul]
          refine mul_le_mul (χ.norm_le_one j) ((norm_add_le _ _).trans (add_le_add ?_ ?_))
            (norm_nonneg _) zero_le_one
          · exact (hCE _ z).trans (hmono _ hjE)
          · exact (hCO _ z).trans (hmono _ hjO)
      _ = _ := by ring
  have hsum : ‖∑ j : ZMod N, χ j * (HurwitzZeta.completedHurwitzZetaEven₀ (ZMod.toAddCircle j) z +
        HurwitzZeta.completedHurwitzZetaOdd (ZMod.toAddCircle j) z)‖ ≤
      Real.exp (4 * N * (1 + ‖z‖) * Real.log (2 + ‖z‖)) *
        Real.exp (M * (1 + ‖z‖) * Real.log (2 + ‖z‖)) := by
    calc _ ≤ ∑ _j : ZMod N, 2 * Real.exp (M * (1 + ‖z‖) * Real.log (2 + ‖z‖)) :=
          norm_sum_le_of_le _ fun j _ ↦ hterm j
      _ = (2 * N) * Real.exp (M * (1 + ‖z‖) * Real.log (2 + ‖z‖)) := by
          simp [Finset.sum_const, ZMod.card]; ring
      _ ≤ _ := by
          gcongr
          have h0 : (0 : ℝ) ≤ 2 * N := by positivity
          calc (2 * N : ℝ) ≤ 2 * N * (1 + ‖z‖) := by nlinarith
            _ ≤ 2 * (2 * N) * (1 + ‖z‖) * Real.log (2 + ‖z‖) := hf2_mul_one_add_le h0 hx
            _ = 4 * N * (1 + ‖z‖) * Real.log (2 + ‖z‖) := by ring
            _ ≤ _ := by linarith [Real.add_one_le_exp (4 * N * (1 + ‖z‖) * Real.log (2 + ‖z‖))]
  have hw1 : ‖z / 2‖ ≤ 1 + ‖z‖ := by
    rw [norm_div]; simp only [Complex.norm_ofNat]; linarith
  have hw2 : ‖-z‖ ≤ 1 + ‖z‖ := by rw [norm_neg]; linarith
  rw [hxi, norm_mul, norm_mul]
  calc ‖(N : ℂ) ^ (z / 2)‖ * (‖(N : ℂ) ^ (-z)‖ * ‖∑ j : ZMod N, χ j *
        (HurwitzZeta.completedHurwitzZetaEven₀ (ZMod.toAddCircle j) z +
          HurwitzZeta.completedHurwitzZetaOdd (ZMod.toAddCircle j) z)‖)
      ≤ Real.exp (2 * Real.log N * (1 + ‖z‖) * Real.log (2 + ‖z‖)) *
        (Real.exp (2 * Real.log N * (1 + ‖z‖) * Real.log (2 + ‖z‖)) *
          (Real.exp (4 * N * (1 + ‖z‖) * Real.log (2 + ‖z‖)) *
            Real.exp (M * (1 + ‖z‖) * Real.log (2 + ‖z‖)))) := by
        gcongr
        · exact hpow _ hw1
        · exact hpow _ hw2
    _ = _ := by
        rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; congr 1; ring

/-- Helper for HF3–HF5: `ξ_χ` is entire for `χ ≠ 1`. -/
private lemma xi_differentiable {χ : DirichletCharacter ℂ N} (hne : χ ≠ 1) :
    Differentiable ℂ (xi χ) := by
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  exact ((differentiable_id.div_const 2).const_cpow (Or.inl hN)).mul
    (DirichletCharacter.differentiable_completedLFunction hne)

/-- Helper for HF3–HF5: the functional equation `ξ_χ(1 - s) = W(χ) ξ_{χ⁻¹}(s)`. -/
private lemma xi_one_sub {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (s : ℂ) :
    xi χ (1 - s) = χ.rootNumber * xi χ⁻¹ s := by
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have h : (N : ℂ) ^ ((1 - s) / 2) * (N : ℂ) ^ (s - 1 / 2) = (N : ℂ) ^ (s / 2) := by
    rw [← cpow_add _ _ hN]
    congr 1
    ring
  rw [xi, xi, hχ.completedLFunction_one_sub]
  linear_combination (χ.rootNumber * χ⁻¹.completedLFunction s) * h

/-- **HF3** (S). `ξ_χ` is entire and does not vanish at `0`
(`differentiable_completedLFunction`; `Λ(0,χ) = W Λ(1,χ⁻¹) ≠ 0`). -/
theorem xi_differentiable_and_ne_zero (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive)
    (hne : χ ≠ 1) : Differentiable ℂ (xi χ) ∧ xi χ 0 ≠ 0 := by
  refine ⟨xi_differentiable hne, ?_⟩
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hne' : χ⁻¹ ≠ 1 := by simpa using hne
  have h := xi_one_sub hχ 1
  rw [sub_self] at h
  rw [h]
  refine mul_ne_zero (DirichletCharacter.rootNumber_ne_zero hχ) (mul_ne_zero ?_ ?_)
  · exact (cpow_ne_zero_iff_of_exponent_ne_zero (by norm_num)).mpr hN
  · exact DirichletCharacter.completedLFunction_ne_zero_of_one_le_re χ⁻¹ (Or.inl hne') (by simp)

/-- **HF4** (M). Functional equation for the logarithmic derivative, valid at every `s`. -/
theorem logDeriv_xi_one_sub (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) (hne : χ ≠ 1)
    (s : ℂ) :
    logDeriv (xi χ) (1 - s) = -logDeriv (xi χ⁻¹) s := by
  have hfun : xi χ ∘ (fun z : ℂ ↦ 1 - z) = fun z ↦ χ.rootNumber * xi χ⁻¹ z :=
    funext fun z ↦ xi_one_sub hχ z
  have h1 := logDeriv_comp (f := xi χ) (g := fun z : ℂ ↦ 1 - z) (x := s)
    (xi_differentiable hne _) (by fun_prop)
  rw [hfun, logDeriv_const_mul _ _ (DirichletCharacter.rootNumber_ne_zero hχ)] at h1
  have hd : deriv (fun z : ℂ ↦ 1 - z) s = -1 := by simp
  rw [hd] at h1
  linear_combination h1

omit [NeZero N] in
/-- Helper for HF5: parity is invariant under `χ ↦ χ⁻¹`. -/
private lemma even_inv_iff (χ : DirichletCharacter ℂ N) : χ⁻¹.Even ↔ χ.Even := by
  rw [DirichletCharacter.Even, DirichletCharacter.Even, ← MulChar.star_apply']
  exact (starRingEnd ℂ).injective.eq_iff' (map_one _)

omit [NeZero N] in
/-- Helper for HF5: the Gamma factors of `χ` and `χ⁻¹` agree. -/
private lemma gammaFactor_inv (χ : DirichletCharacter ℂ N) (s : ℂ) :
    χ⁻¹.gammaFactor s = χ.gammaFactor s := by
  by_cases h : χ.Even
  · rw [h.gammaFactor_def, ((even_inv_iff χ).mpr h).gammaFactor_def]
  · have h' : ¬ χ⁻¹.Even := fun h' ↦ h ((even_inv_iff χ).mp h')
    simp [DirichletCharacter.gammaFactor, h, h']

omit [NeZero N] in
/-- Helper for HF5: the Gamma factor commutes with complex conjugation. -/
private lemma gammaFactor_conj (χ : DirichletCharacter ℂ N) (s : ℂ) :
    χ.gammaFactor ((starRingEnd ℂ) s) = (starRingEnd ℂ) (χ.gammaFactor s) := by
  rcases χ.even_or_odd with h | h
  · rw [h.gammaFactor_def, h.gammaFactor_def, Gammaℝ_conj]
  · rw [h.gammaFactor_def, h.gammaFactor_def, ← Gammaℝ_conj, map_add, map_one]

/-- Helper for HF5: `Λ(s, χ) = L(s, χ) γ(s, χ)` with the naive Dirichlet series on `Re s > 1`. -/
private lemma completedLFunction_eq_LSeries_mul (χ : DirichletCharacter ℂ N) {s : ℂ}
    (hs : 1 < s.re) : χ.completedLFunction s = LSeries (χ ·) s * χ.gammaFactor s := by
  have h0 : s ≠ 0 := by
    rintro rfl
    norm_num at hs
  have hg : χ.gammaFactor s ≠ 0 := by
    rcases χ.even_or_odd with h | h
    · rw [h.gammaFactor_def]
      exact Gammaℝ_ne_zero_of_re_pos (by linarith)
    · rw [h.gammaFactor_def]
      exact Gammaℝ_ne_zero_of_re_pos (by rw [add_re, one_re]; linarith)
  rw [← χ.LFunction_eq_LSeries hs, χ.LFunction_eq_completed_div_gammaFactor s (Or.inl h0),
    div_mul_cancel₀ _ hg]

omit [NeZero N] in
/-- Helper for HF5: conjugation symmetry of the naive Dirichlet series (termwise, no convergence
hypothesis needed). -/
private lemma LSeries_inv_conj (χ : DirichletCharacter ℂ N) (s : ℂ) :
    LSeries (χ⁻¹ ·) ((starRingEnd ℂ) s) = (starRingEnd ℂ) (LSeries (χ ·) s) := by
  rw [LSeries, LSeries, conj_tsum]
  refine tsum_congr fun n ↦ ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn, map_div₀,
      cpow_conj _ _ (by rw [natCast_arg]; exact Real.pi_pos.ne), conj_natCast,
      ← MulChar.star_apply']
    rfl

/-- Helper for HF5: conjugation symmetry `Λ(conj s, χ⁻¹) = conj Λ(s, χ)` of the completed
`L`-function of a nontrivial character (identity theorem from `Re s > 1`). -/
private lemma completedLFunction_inv_conj {χ : DirichletCharacter ℂ N} (hne : χ ≠ 1) (s : ℂ) :
    χ⁻¹.completedLFunction ((starRingEnd ℂ) s) = (starRingEnd ℂ) (χ.completedLFunction s) := by
  have hne' : χ⁻¹ ≠ 1 := by simpa using hne
  have hd1 : Differentiable ℂ ((starRingEnd ℂ) ∘ χ.completedLFunction ∘ (starRingEnd ℂ)) :=
    fun z ↦ differentiableAt_conj_conj_iff.mpr
      (DirichletCharacter.differentiable_completedLFunction hne _)
  have hd2 : Differentiable ℂ χ⁻¹.completedLFunction :=
    DirichletCharacter.differentiable_completedLFunction hne'
  have hEq : ∀ z : ℂ, 1 < z.re →
      ((starRingEnd ℂ) ∘ χ.completedLFunction ∘ (starRingEnd ℂ)) z = χ⁻¹.completedLFunction z := by
    intro z hz
    have hz' : 1 < ((starRingEnd ℂ) z).re := by rwa [conj_re]
    have h := LSeries_inv_conj χ ((starRingEnd ℂ) z)
    rw [Complex.conj_conj] at h
    simp only [Function.comp_apply]
    rw [completedLFunction_eq_LSeries_mul χ hz', completedLFunction_eq_LSeries_mul χ⁻¹ hz,
      map_mul, ← h, gammaFactor_inv, gammaFactor_conj, Complex.conj_conj]
  have hmem : {z : ℂ | 1 < z.re} ∈ nhds (2 : ℂ) :=
    (isOpen_lt continuous_const continuous_re).mem_nhds (by simp)
  have heq : Set.EqOn ((starRingEnd ℂ) ∘ χ.completedLFunction ∘ (starRingEnd ℂ))
      χ⁻¹.completedLFunction Set.univ :=
    AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq (fun z _ ↦ hd1.analyticAt z)
      (fun z _ ↦ hd2.analyticAt z) isPreconnected_univ (Set.mem_univ (2 : ℂ))
      (Filter.eventuallyEq_of_mem hmem fun z hz ↦ hEq z hz)
  have h := heq (Set.mem_univ ((starRingEnd ℂ) s))
  simp only [Function.comp_apply, Complex.conj_conj] at h
  exact h.symm

/-- Helper for HF5: conjugation symmetry `ξ_{χ⁻¹}(conj s) = conj ξ_χ(s)`. -/
private lemma xi_inv_conj {χ : DirichletCharacter ℂ N} (hne : χ ≠ 1) (s : ℂ) :
    xi χ⁻¹ ((starRingEnd ℂ) s) = (starRingEnd ℂ) (xi χ s) := by
  have h2 : (starRingEnd ℂ) s / 2 = (starRingEnd ℂ) (s / 2) := by
    rw [map_div₀, map_ofNat]
  rw [xi, xi, map_mul, completedLFunction_inv_conj hne, h2,
    cpow_conj _ _ (by rw [natCast_arg]; exact Real.pi_pos.ne), conj_natCast]

/-- Helper for HF5: iterated derivatives commute with `f ↦ conj ∘ f ∘ conj`. -/
private lemma iteratedDeriv_conj_conj (f : ℂ → ℂ) (n : ℕ) :
    iteratedDeriv n ((starRingEnd ℂ) ∘ f ∘ (starRingEnd ℂ)) =
      (starRingEnd ℂ) ∘ iteratedDeriv n f ∘ (starRingEnd ℂ) := by
  induction n with
  | zero => simp
  | succ n ih => rw [iteratedDeriv_succ, ih, deriv_conj_conj, iteratedDeriv_succ]

/-- Helper for HF5: the vanishing order of `conj ∘ f ∘ conj` at `conj z` is that of `f` at `z`. -/
private lemma analyticOrderAt_conj_conj {f : ℂ → ℂ} (hf : Differentiable ℂ f) (z : ℂ) :
    analyticOrderAt ((starRingEnd ℂ) ∘ f ∘ (starRingEnd ℂ)) ((starRingEnd ℂ) z) =
      analyticOrderAt f z := by
  have hf' : Differentiable ℂ ((starRingEnd ℂ) ∘ f ∘ (starRingEnd ℂ)) :=
    fun w ↦ differentiableAt_conj_conj_iff.mpr (hf _)
  refine ENat.eq_of_forall_natCast_le_iff fun n ↦ ?_
  rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (hf'.analyticAt _),
    natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (hf.analyticAt _)]
  simp [iteratedDeriv_conj_conj]

/-- **HF5** (M). Symmetry of the zeros with multiplicity under `ρ ↦ 1 - conj ρ`
(functional equation composed with complex conjugation `Λ(conj s, χ⁻¹) = conj Λ(s, χ)`). -/
theorem analyticOrderNatAt_xi_one_sub_conj (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive)
    (hne : χ ≠ 1) (ρ : ℂ) :
    analyticOrderNatAt (xi χ) (1 - (starRingEnd ℂ) ρ) = analyticOrderNatAt (xi χ) ρ := by
  have hne' : χ⁻¹ ≠ 1 := by simpa using hne
  have hW : χ.rootNumber ≠ 0 := DirichletCharacter.rootNumber_ne_zero hχ
  have hd : Differentiable ℂ (xi χ) := xi_differentiable hne
  have hd' : Differentiable ℂ (xi χ⁻¹) := xi_differentiable hne'
  have h1 : xi χ = (fun _ : ℂ ↦ χ.rootNumber) * (xi χ⁻¹ ∘ fun w : ℂ ↦ 1 - w) := by
    funext w
    have h := xi_one_sub hχ (1 - w)
    rw [sub_sub_cancel] at h
    simpa using h
  have h2 : xi χ⁻¹ = (starRingEnd ℂ) ∘ xi χ ∘ (starRingEnd ℂ) := by
    funext w
    simpa using xi_inv_conj hne ((starRingEnd ℂ) w)
  have hcomp : Differentiable ℂ (xi χ⁻¹ ∘ fun w : ℂ ↦ 1 - w) :=
    hd'.comp (by fun_prop)
  have hderiv : deriv (fun w : ℂ ↦ 1 - w) (1 - (starRingEnd ℂ) ρ) ≠ 0 := by simp
  have key : analyticOrderAt (xi χ⁻¹ ∘ fun w : ℂ ↦ 1 - w) (1 - (starRingEnd ℂ) ρ) =
      analyticOrderAt (xi χ) ρ := by
    rw [analyticOrderAt_comp_of_deriv_ne_zero (by fun_prop) hderiv, sub_sub_cancel, h2,
      analyticOrderAt_conj_conj hd]
  conv_lhs => rw [h1]
  rw [analyticOrderNatAt_const_mul (hcomp.analyticAt _) hW, analyticOrderNatAt, key,
    analyticOrderNatAt]

/- **HF6** (L): H1 and H2 of `HadamardInput.lean` from HF1–HF5.
`Re B(χ) = -∑ m_ρ Re (1/ρ)` by pairing `ρ ↔ 1 - conj ρ` (HF4 at `s = 0, 1`, HF5), then take real
parts in HF1; `logDeriv (xi χ) = ½ log N + logDeriv gammaFactor + logDeriv LFunction` on `Re s > 0`
off the zeros; the multiplicities of `xi χ` and of `completedLFunction χ` agree. -/

end Exp7.EF.Fallback
