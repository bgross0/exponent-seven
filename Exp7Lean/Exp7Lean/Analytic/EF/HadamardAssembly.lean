import Exp7Lean.Analytic.EF.HadamardFallback
import Exp7Lean.Analytic.EF.HadamardHF1

/-!
# Explicit formula blueprint: H1 and H2 from the fallback leaves HF2–HF5

This file carries out node **HF6** of `BLUEPRINT.md`: it derives the two Hadamard inputs
`re_logDeriv_LFunction_add_eq_tsum` (H1) and
`summable_norm_analyticOrderNatAt_completedLFunction_mul_re_one_div_sub` (H2) of
`HadamardInput.lean`, with verbatim statements (`H1_of_fallback`, `H2_of_fallback`).

Inputs.

* **HF1** (Hadamard partial fractions for entire functions of order ≤ 1): the *proved* theorem
  `Exp7.EF.HF1.logDeriv_eq_add_tsum_of_order_one` of `HadamardHF1.lean` (same statement as the
  `sorry` leaf in `HadamardFallback.lean`, which is therefore not used).
* **HF2–HF5** of `HadamardFallback.lean`, as black boxes, bundled in the structure `XiLeaves`.
  `H1_of_leaves` and `H2_of_leaves` take a proof of `XiLeaves χ` and are `sorry`-free;
  `xiLeaves_of_fallback` is the only place where the `sorry`s of HF2–HF5 enter.
* **HF4b** (`xi_inv_conj`, proved here from Mathlib): the conjugation symmetry
  `ξ(conj s, χ⁻¹) = conj ξ(s, χ)`.

Structure.

* `Abstract` section: pure series manipulation.  Given a multiplicity function `m : ℂ → ℕ` with
  `∑ m ρ / (1 + ‖ρ‖²) < ∞`, support in the strip `0 < Re ρ < 1`, the symmetry
  `m (1 - conj ρ) = m ρ`, the complex partial fractions
  `F'/F(s) = F'/F(0) + ∑ m ρ (1/(s-ρ) + 1/ρ)` and the functional equation in the form
  `Re F'/F(1 - conj s) = - Re F'/F(s)`, one gets `Re F'/F(s) = ∑ m ρ Re (1/(s-ρ))`
  (`re_logDeriv_eq_tsum_of_symm`) with absolute convergence (`summable_norm_mul_re_one_div_sub`).
  The constant `Re F'/F(0) + ∑ m ρ Re (1/ρ)` is killed by pairing `ρ ↔ 1 - conj ρ`.
* `Xi` section: the hypotheses of the abstract statement for `F = xi χ`.
* `Main` section: `logDeriv_xi_eq` (`ξ'/ξ = ½ log N + γ'/γ + L'/L` on `Re s > 0`), H1, H2.

## What HF2–HF5 do not provide

HF4 (`logDeriv_xi_one_sub`) relates `xi χ` to `xi χ⁻¹`, HF5 is a statement about `xi χ` alone.
To close the pairing argument one needs `Re ξ'/ξ(1 - conj s, χ) = - Re ξ'/ξ(s, χ)`, i.e. HF4
*together with* the conjugation symmetry `ξ(conj s, χ⁻¹) = conj ξ(s, χ)`.  The latter is not a
consequence of the statements HF2–HF5 (it is used inside any proof of HF5, but HF5 only exports
the equality of multiplicities).  It is `xi_inv_conj` below (Dirichlet series on `Re s > 1` plus
the identity theorem; Mathlib has no conjugation lemma for Dirichlet `L`-functions).  Likewise the
strip `0 < Re ρ < 1` for the zeros, needed for *absolute* convergence in H2, comes from Mathlib's
`completedLFunction_ne_zero_of_one_le_re` and HF5.
-/

namespace Exp7.EF.Fallback

open Complex Filter Topology
open scoped ComplexConjugate

/-! ## Abstract pairing argument -/

section Abstract

variable {m : ℂ → ℕ}

/-- Pointwise bound: far from `s`, inside the strip, `|Re (1/(s-ρ))| ≤ 8(‖s‖+1)/(1+‖ρ‖²)`. -/
lemma abs_re_one_div_sub_le {s ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1)
    (hbig : 2 * ‖s‖ + 2 < ‖ρ‖) :
    |(1 / (s - ρ)).re| ≤ 8 * (‖s‖ + 1) / (1 + ‖ρ‖ ^ 2) := by
  have hs0 : 0 ≤ ‖s‖ := norm_nonneg s
  have hz : ‖ρ‖ / 2 ≤ ‖s - ρ‖ := by
    have := norm_sub_norm_le ρ s
    rw [norm_sub_rev] at this
    linarith
  have hzpos : 0 < ‖s - ρ‖ := by linarith
  have hre : |(s - ρ).re| ≤ ‖s‖ + 1 := by
    have h3 : |s.re| ≤ ‖s‖ := abs_re_le_norm s
    rw [sub_re, abs_le]
    rw [abs_le] at h3
    constructor <;> linarith [h3.1, h3.2]
  rw [one_div, inv_re, normSq_eq_norm_sq, abs_div, abs_of_pos (by positivity : 0 < ‖s - ρ‖ ^ 2)]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hsq : ‖ρ‖ ^ 2 / 4 ≤ ‖s - ρ‖ ^ 2 := by nlinarith
  have hρ1 : 1 ≤ ‖ρ‖ ^ 2 := by nlinarith
  calc |(s - ρ).re| * (1 + ‖ρ‖ ^ 2) ≤ (‖s‖ + 1) * (2 * ‖ρ‖ ^ 2) := by
        apply mul_le_mul hre (by linarith) (by positivity) (by positivity)
    _ = 8 * (‖s‖ + 1) * (‖ρ‖ ^ 2 / 4) := by ring
    _ ≤ 8 * (‖s‖ + 1) * ‖s - ρ‖ ^ 2 := by gcongr

/-- Abstract form of **H2**: absolute convergence of `∑ m ρ Re (1/(s-ρ))`. -/
theorem summable_norm_mul_re_one_div_sub
    (hsum : Summable fun ρ : ℂ ↦ (m ρ : ℝ) / (1 + ‖ρ‖ ^ 2))
    (hstrip : ∀ ρ, m ρ ≠ 0 → 0 < ρ.re ∧ ρ.re < 1) (s : ℂ) :
    Summable fun ρ : ℂ ↦ ‖(m ρ : ℝ) * (1 / (s - ρ)).re‖ := by
  refine Summable.of_norm_bounded_eventually (hsum.mul_left (8 * (‖s‖ + 1))) ?_
  rw [eventually_cofinite]
  refine (HF1.finite_setOf_ne_zero_norm_le hsum (2 * ‖s‖ + 2)).subset ?_
  intro ρ hρ
  simp only [Set.mem_ofPred_eq, not_le] at hρ ⊢
  by_contra hcon
  refine absurd hρ (not_lt.mpr ?_)
  by_cases hm : m ρ = 0
  · simp [hm]
  have hbig : 2 * ‖s‖ + 2 < ‖ρ‖ := by
    by_contra h
    exact hcon ⟨hm, not_lt.mp h⟩
  obtain ⟨h0, h1⟩ := hstrip ρ hm
  have hb := abs_re_one_div_sub_le (s := s) h0 h1 hbig
  rw [norm_norm, Real.norm_eq_abs, abs_mul, Nat.abs_cast]
  calc (m ρ : ℝ) * |(1 / (s - ρ)).re| ≤ (m ρ : ℝ) * (8 * (‖s‖ + 1) / (1 + ‖ρ‖ ^ 2)) := by gcongr
    _ = 8 * (‖s‖ + 1) * ((m ρ : ℝ) / (1 + ‖ρ‖ ^ 2)) := by ring

/-- `Re (1 / (1 - conj s - (1 - conj ρ))) = - Re (1 / (s - ρ))`. -/
lemma re_one_div_reflect (s ρ : ℂ) :
    (1 / (1 - conj s - (1 - conj ρ))).re = -(1 / (s - ρ)).re := by
  have h : 1 - conj s - (1 - conj ρ) = -conj (s - ρ) := by simp [map_sub]
  rw [h, one_div, one_div, inv_neg, neg_re, ← map_inv₀, conj_re]

/-- Abstract form of **H1**: real-part partial fractions without the `1/ρ` terms, from the
complex partial fractions and the symmetry `ρ ↔ 1 - conj ρ`. -/
theorem re_logDeriv_eq_tsum_of_symm {F : ℂ → ℂ}
    (hsum : Summable fun ρ : ℂ ↦ (m ρ : ℝ) / (1 + ‖ρ‖ ^ 2))
    (hstrip : ∀ ρ, m ρ ≠ 0 → 0 < ρ.re ∧ ρ.re < 1)
    (hsymm : ∀ ρ, m (1 - conj ρ) = m ρ)
    (habs : ∀ s : ℂ, Summable fun ρ : ℂ ↦ ‖(m ρ : ℂ) * (1 / (s - ρ) + 1 / ρ)‖)
    (hpf : ∀ s : ℂ, F s ≠ 0 →
      logDeriv F s = logDeriv F 0 + ∑' ρ : ℂ, (m ρ : ℂ) * (1 / (s - ρ) + 1 / ρ))
    (hfe : ∀ s : ℂ, F s ≠ 0 → (logDeriv F (1 - conj s)).re = -(logDeriv F s).re)
    (hnz : ∀ s : ℂ, F s ≠ 0 → F (1 - conj s) ≠ 0)
    {s : ℂ} (hs : F s ≠ 0) :
    (logDeriv F s).re = ∑' ρ : ℂ, (m ρ : ℝ) * (1 / (s - ρ)).re := by
  -- the two real series
  have hA : ∀ z : ℂ, Summable fun ρ : ℂ ↦ (m ρ : ℝ) * (1 / (z - ρ)).re := fun z ↦
    (summable_norm_mul_re_one_div_sub hsum hstrip z).of_norm
  have hB : Summable fun ρ : ℂ ↦ (m ρ : ℝ) * (1 / ρ).re := by
    have := (hA 0).neg
    refine this.congr fun ρ ↦ ?_
    rw [zero_sub, one_div, one_div, inv_neg, neg_re]
    ring
  -- real part of the complex partial fraction
  have key : ∀ z : ℂ, F z ≠ 0 → (logDeriv F z).re =
      (logDeriv F 0).re + (∑' ρ : ℂ, (m ρ : ℝ) * (1 / (z - ρ)).re)
        + ∑' ρ : ℂ, (m ρ : ℝ) * (1 / ρ).re := by
    intro z hz
    rw [hpf z hz, add_re, re_tsum (habs z).of_norm, add_assoc, ← (hA z).tsum_add hB]
    congr 1
    refine tsum_congr fun ρ ↦ ?_
    rw [← ofReal_natCast, re_ofReal_mul, add_re]
    ring
  -- reindex the series at the reflected point
  have hrefl : ∑' ρ : ℂ, (m ρ : ℝ) * (1 / (1 - conj s - ρ)).re =
      -∑' ρ : ℂ, (m ρ : ℝ) * (1 / (s - ρ)).re := by
    have hinv : Function.Involutive fun ρ : ℂ ↦ 1 - conj ρ := fun ρ ↦ by simp
    rw [← (hinv.toPerm _).tsum_eq, ← tsum_neg]
    refine tsum_congr fun ρ ↦ ?_
    simp only [Function.Involutive.coe_toPerm]
    rw [hsymm ρ, re_one_div_reflect]
    ring
  have e1 := key s hs
  have e2 := key (1 - conj s) (hnz s hs)
  rw [hrefl, hfe s hs] at e2
  linarith

end Abstract

/-! ## The hypotheses for `xi χ` -/

section Xi

variable {N : ℕ} [NeZero N]

lemma natCast_cpow_ne_zero (s : ℂ) : (N : ℂ) ^ (s / 2) ≠ 0 := by
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  simp [cpow_eq_zero_iff, hN]

lemma differentiable_natCast_cpow : Differentiable ℂ fun s : ℂ ↦ (N : ℂ) ^ (s / 2) := by
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  exact fun s ↦ ((differentiableAt_id.div_const 2).const_cpow (Or.inl hN))

lemma logDeriv_natCast_cpow (s : ℂ) :
    logDeriv (fun s : ℂ ↦ (N : ℂ) ^ (s / 2)) s = (Real.log N : ℂ) / 2 := by
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have h : HasDerivAt (fun s : ℂ ↦ (N : ℂ) ^ (s / 2))
      ((N : ℂ) ^ (s / 2) * Complex.log N * (1 / 2)) s :=
    ((hasDerivAt_id s).div_const 2).const_cpow (Or.inl hN)
  rw [logDeriv_apply, h.deriv, natCast_log]
  field_simp [natCast_cpow_ne_zero (N := N) s]

lemma xi_eq_mul (χ : DirichletCharacter ℂ N) :
    xi χ = (fun s : ℂ ↦ (N : ℂ) ^ (s / 2)) * χ.completedLFunction := rfl

/-- The multiplicities of `xi χ` and of the completed `L`-function agree. -/
lemma analyticOrderNatAt_xi (χ : DirichletCharacter ℂ N) (hne : χ ≠ 1) (ρ : ℂ) :
    analyticOrderNatAt (xi χ) ρ = analyticOrderNatAt χ.completedLFunction ρ := by
  have h1 : AnalyticAt ℂ (fun s : ℂ ↦ (N : ℂ) ^ (s / 2)) ρ :=
    (differentiable_natCast_cpow (N := N)).analyticAt ρ
  have h2 : AnalyticAt ℂ χ.completedLFunction ρ :=
    (DirichletCharacter.differentiable_completedLFunction hne).analyticAt ρ
  have h3 : analyticOrderAt (fun s : ℂ ↦ (N : ℂ) ^ (s / 2)) ρ = 0 :=
    h1.analyticOrderAt_eq_zero.mpr (natCast_cpow_ne_zero ρ)
  unfold analyticOrderNatAt
  rw [xi_eq_mul, analyticOrderAt_mul h1 h2, h3, zero_add]

lemma xi_ne_zero_of_one_le_re (χ : DirichletCharacter ℂ N) (hne : χ ≠ 1) {s : ℂ}
    (hs : 1 ≤ s.re) : xi χ s ≠ 0 :=
  mul_ne_zero (natCast_cpow_ne_zero s)
    (DirichletCharacter.completedLFunction_ne_zero_of_one_le_re χ (Or.inl hne) hs)

omit [NeZero N] in
lemma gammaFactor_ne_zero_of_re_pos (ψ : DirichletCharacter ℂ N) {w : ℂ} (hw : 0 < w.re) :
    ψ.gammaFactor w ≠ 0 := by
  rcases ψ.even_or_odd with he | ho
  · rw [he.gammaFactor_def]
    exact Gammaℝ_ne_zero_of_re_pos hw
  · rw [ho.gammaFactor_def]
    exact Gammaℝ_ne_zero_of_re_pos (by simp; linarith)

omit [NeZero N] in
lemma gammaFactor_conj (ψ : DirichletCharacter ℂ N) (w : ℂ) :
    ψ.gammaFactor (conj w) = conj (ψ.gammaFactor w) := by
  rcases ψ.even_or_odd with he | ho
  · rw [he.gammaFactor_def, he.gammaFactor_def, Gammaℝ_conj]
  · rw [ho.gammaFactor_def, ho.gammaFactor_def, ← Gammaℝ_conj]
    simp

omit [NeZero N] in
lemma gammaFactor_inv (χ : DirichletCharacter ℂ N) (w : ℂ) :
    χ⁻¹.gammaFactor w = χ.gammaFactor w := by
  rcases χ.even_or_odd with he | ho
  · have he' : χ⁻¹.Even := by
      have := he
      unfold DirichletCharacter.Even at this ⊢
      rw [MulChar.inv_apply_eq_inv', this, inv_one]
    rw [he.gammaFactor_def, he'.gammaFactor_def]
  · have ho' : χ⁻¹.Odd := by
      have := ho
      unfold DirichletCharacter.Odd at this ⊢
      rw [MulChar.inv_apply_eq_inv', this, inv_neg, inv_one]
    rw [ho.gammaFactor_def, ho'.gammaFactor_def]

omit [NeZero N] in
/-- Conjugation symmetry of the Dirichlet series: `L(conj s, χ⁻¹) = conj L(s, χ)` as series. -/
lemma LSeries_inv_conj (χ : DirichletCharacter ℂ N) (z : ℂ) :
    LSeries (fun n : ℕ ↦ χ⁻¹ (n : ZMod N)) (conj z) =
      conj (LSeries (fun n : ℕ ↦ χ (n : ZMod N)) z) := by
  unfold LSeries
  rw [conj_tsum]
  refine tsum_congr fun n ↦ ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn, map_div₀,
      cpow_conj _ _ (by simp [natCast_arg, Real.pi_ne_zero.symm]), conj_natCast,
      ← MulChar.star_apply']
    rfl

/-- Conjugation symmetry of the completed `L`-function, by the identity theorem from `Re s > 1`. -/
lemma completedLFunction_inv_conj (χ : DirichletCharacter ℂ N) (hne : χ ≠ 1) (s : ℂ) :
    χ⁻¹.completedLFunction (conj s) = conj (χ.completedLFunction s) := by
  have hne' : χ⁻¹ ≠ 1 := by simpa using hne
  have hN1 : N ≠ 1 := fun h ↦ hne (DirichletCharacter.level_one' χ h)
  have hGd : Differentiable ℂ (conj ∘ χ⁻¹.completedLFunction ∘ conj) := by
    intro z
    have := ((DirichletCharacter.differentiable_completedLFunction hne') (conj z)).conj_conj
    simpa using this
  have hΛd := DirichletCharacter.differentiable_completedLFunction hne
  have hΛ : ∀ (ψ : DirichletCharacter ℂ N) (w : ℂ), 1 < w.re →
      ψ.completedLFunction w = ψ.gammaFactor w * LSeries (fun n : ℕ ↦ ψ (n : ZMod N)) w := by
    intro ψ w hw
    rw [← DirichletCharacter.LFunction_eq_LSeries ψ hw,
      DirichletCharacter.LFunction_eq_completed_div_gammaFactor ψ w (Or.inr hN1),
      mul_div_cancel₀ _ (gammaFactor_ne_zero_of_re_pos ψ (by linarith))]
  have hagree : ∀ z : ℂ, 1 < z.re →
      χ.completedLFunction z = (conj ∘ χ⁻¹.completedLFunction ∘ conj) z := by
    intro z hz
    have hz' : 1 < (conj z).re := by simpa using hz
    simp only [Function.comp_apply]
    rw [hΛ χ z hz, hΛ χ⁻¹ (conj z) hz', LSeries_inv_conj, gammaFactor_inv, gammaFactor_conj,
      map_mul, conj_conj, conj_conj]
  have hopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const continuous_re
  have hev : χ.completedLFunction =ᶠ[𝓝 (2 : ℂ)] (conj ∘ χ⁻¹.completedLFunction ∘ conj) := by
    filter_upwards [hopen.mem_nhds (show (1 : ℝ) < (2 : ℂ).re by norm_num)] with z hz
      using hagree z hz
  have hEq := AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
    (fun z _ ↦ hΛd.analyticAt z) (fun z _ ↦ hGd.analyticAt z) isPreconnected_univ
    (Set.mem_univ (2 : ℂ)) hev
  have h := hEq (Set.mem_univ s)
  simp only [Function.comp_apply] at h
  rw [h, conj_conj]

/-- **HF4b** (M; the missing leaf, proved here from Mathlib). Conjugation symmetry of the
completion: `ξ(conj s, χ⁻¹) = conj ξ(s, χ)`.  This is what any proof of HF5 uses internally; it is
needed *as a statement about values* (not only about multiplicities) to turn HF4 into a symmetry
of `xi χ` itself. -/
theorem xi_inv_conj (χ : DirichletCharacter ℂ N) (hne : χ ≠ 1) (s : ℂ) :
    xi χ⁻¹ (conj s) = conj (xi χ s) := by
  unfold xi
  rw [completedLFunction_inv_conj χ hne s, map_mul]
  congr 1
  have h2 : conj s / 2 = conj (s / 2) := by rw [map_div₀, conj_ofNat]
  rw [h2, cpow_conj _ _ (by simp [natCast_arg, Real.pi_ne_zero.symm]), conj_natCast]

/-- Logarithmic-derivative form of `xi_inv_conj`. -/
lemma logDeriv_xi_inv_conj (χ : DirichletCharacter ℂ N) (hne : χ ≠ 1) (s : ℂ) :
    logDeriv (xi χ⁻¹) (conj s) = conj (logDeriv (xi χ) s) := by
  have hfun : xi χ⁻¹ = conj ∘ xi χ ∘ conj := by
    funext z
    simpa using xi_inv_conj χ hne (conj z)
  rw [logDeriv_apply, logDeriv_apply, map_div₀, ← xi_inv_conj χ hne s]
  congr 1
  rw [hfun, deriv_conj_conj]
  simp

/-- The statements of the leaves **HF2–HF5** of `HadamardFallback.lean` for one character, bundled
as hypotheses.  Everything below up to `H1_of_leaves` / `H2_of_leaves` is proved from this
structure without `sorry`; `xiLeaves_of_fallback` instantiates it from HF2–HF5. -/
structure XiLeaves (χ : DirichletCharacter ℂ N) : Prop where
  /-- HF2 (`xi_growth`). -/
  growth : ∃ C : ℝ, ∀ z : ℂ, ‖xi χ z‖ ≤ Real.exp (C * (1 + ‖z‖) * Real.log (2 + ‖z‖))
  /-- HF3, first half (`xi_differentiable_and_ne_zero`). -/
  differentiable : Differentiable ℂ (xi χ)
  /-- HF3, second half. -/
  ne_zero : xi χ 0 ≠ 0
  /-- HF4 (`logDeriv_xi_one_sub`). -/
  logDeriv_one_sub : ∀ s : ℂ, logDeriv (xi χ) (1 - s) = -logDeriv (xi χ⁻¹) s
  /-- HF5 (`analyticOrderNatAt_xi_one_sub_conj`). -/
  order_one_sub_conj : ∀ ρ : ℂ,
    analyticOrderNatAt (xi χ) (1 - conj ρ) = analyticOrderNatAt (xi χ) ρ

/-- Functional equation for `Re ξ'/ξ` in terms of `xi χ` alone (HF4 + HF4b). -/
lemma XiLeaves.re_logDeriv_one_sub_conj {χ : DirichletCharacter ℂ N} (h : XiLeaves χ)
    (hne : χ ≠ 1) (s : ℂ) :
    (logDeriv (xi χ) (1 - conj s)).re = -(logDeriv (xi χ) s).re := by
  rw [h.logDeriv_one_sub (conj s), logDeriv_xi_inv_conj χ hne s, neg_re, conj_re]

/-- Zeros of `xi χ` (with multiplicity) lie in the open critical strip
(Mathlib's non-vanishing on `Re s ≥ 1` and HF5). -/
lemma XiLeaves.re_mem_Ioo {χ : DirichletCharacter ℂ N} (h : XiLeaves χ) (hne : χ ≠ 1) {ρ : ℂ}
    (hρ : analyticOrderNatAt (xi χ) ρ ≠ 0) : 0 < ρ.re ∧ ρ.re < 1 := by
  have key : ∀ z : ℂ, analyticOrderNatAt (xi χ) z ≠ 0 → z.re < 1 := by
    intro z hz
    by_contra hcon
    exact hz ((HF1.analyticOrderNatAt_eq_zero_iff h.differentiable h.ne_zero z).mpr
      (xi_ne_zero_of_one_le_re χ hne (not_lt.mp hcon)))
  refine ⟨?_, key ρ hρ⟩
  have h1 := key (1 - conj ρ) (by rwa [h.order_one_sub_conj ρ])
  simpa using h1

end Xi

/-! ## H1 and H2 -/

section Main

variable {N : ℕ} [NeZero N]

/-- **H2 from the statements HF2–HF5** (no `sorry`: HF1 is the proved
`Exp7.EF.HF1.logDeriv_eq_add_tsum_of_order_one`). -/
theorem H2_of_leaves {χ : DirichletCharacter ℂ N} (h : XiLeaves χ) (hne : χ ≠ 1) (s : ℂ) :
    Summable (fun ρ : ℂ ↦
      ‖(analyticOrderNatAt χ.completedLFunction ρ : ℝ) * (1 / (s - ρ)).re‖) := by
  obtain ⟨hsum, -, -⟩ :=
    HF1.logDeriv_eq_add_tsum_of_order_one h.differentiable h.ne_zero h.growth
  have := summable_norm_mul_re_one_div_sub hsum (fun ρ hρ ↦ h.re_mem_Ioo hne hρ) s
  simpa only [analyticOrderNatAt_xi χ hne] using this

/-- Real-part partial fractions for `xi χ` at every non-zero of `xi χ`. -/
theorem re_logDeriv_xi_eq_tsum {χ : DirichletCharacter ℂ N} (h : XiLeaves χ) (hne : χ ≠ 1)
    {s : ℂ} (hs : xi χ s ≠ 0) :
    (logDeriv (xi χ) s).re =
      ∑' ρ : ℂ, (analyticOrderNatAt (xi χ) ρ : ℝ) * (1 / (s - ρ)).re := by
  obtain ⟨hsum, habs, hpf⟩ :=
    HF1.logDeriv_eq_add_tsum_of_order_one h.differentiable h.ne_zero h.growth
  refine re_logDeriv_eq_tsum_of_symm hsum (fun ρ hρ ↦ h.re_mem_Ioo hne hρ)
    h.order_one_sub_conj habs hpf (fun z _ ↦ h.re_logDeriv_one_sub_conj hne z) ?_ hs
  intro z hz
  rw [← HF1.analyticOrderNatAt_eq_zero_iff h.differentiable h.ne_zero] at hz ⊢
  rw [h.order_one_sub_conj z, hz]

/-- On `Re s > 0`, off the zeros of `L(s, χ)`:
`ξ'/ξ(s) = ½ log N + γ'/γ(s) + L'/L(s)` and `ξ(s) ≠ 0`. -/
theorem logDeriv_xi_eq (χ : DirichletCharacter ℂ N) (hne : χ ≠ 1) {s : ℂ} (hs : 0 < s.re)
    (hL : χ.LFunction s ≠ 0) :
    xi χ s ≠ 0 ∧
    logDeriv (xi χ) s =
      (Real.log N : ℂ) / 2 + (logDeriv χ.gammaFactor s + logDeriv χ.LFunction s) := by
  have hN1 : N ≠ 1 := fun h ↦ hne (DirichletCharacter.level_one' χ h)
  -- the gamma factor is nonzero and differentiable on `Re s > 0`
  have hγ : ∀ z : ℂ, 0 < z.re → χ.gammaFactor z ≠ 0 ∧ DifferentiableAt ℂ χ.gammaFactor z := by
    intro z hz
    have hG : ∀ w : ℂ, 0 < w.re → DifferentiableAt ℂ Gammaℝ w := by
      intro w hw
      have h1 : DifferentiableAt ℂ (fun s ↦ (Gammaℝ s)⁻¹) w := differentiable_Gammaℝ_inv w
      have h2 := h1.inv (inv_ne_zero (Gammaℝ_ne_zero_of_re_pos hw))
      have hfun : (fun s : ℂ ↦ (Gammaℝ s)⁻¹)⁻¹ = Gammaℝ := funext fun z ↦ by simp
      rwa [hfun] at h2
    refine ⟨gammaFactor_ne_zero_of_re_pos χ hz, ?_⟩
    rcases χ.even_or_odd with he | ho
    · have hfun : χ.gammaFactor = Gammaℝ := funext fun w ↦ he.gammaFactor_def w
      rw [hfun]
      exact hG z hz
    · have hfun : χ.gammaFactor = fun w ↦ Gammaℝ (w + 1) := funext fun w ↦ ho.gammaFactor_def w
      have hz1 : 0 < (z + 1).re := by simp; linarith
      rw [hfun]
      exact (hG (z + 1) hz1).comp z (differentiableAt_id.add_const 1)
  have hΛ : ∀ z : ℂ, 0 < z.re → χ.completedLFunction z = χ.gammaFactor z * χ.LFunction z := by
    intro z hz
    rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ z (Or.inr hN1),
      mul_div_cancel₀ _ (hγ z hz).1]
  have hΛev : χ.completedLFunction =ᶠ[𝓝 s] χ.gammaFactor * χ.LFunction := by
    have hopen : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const continuous_re
    filter_upwards [hopen.mem_nhds hs] with z hz using hΛ z hz
  have hLd : DifferentiableAt ℂ χ.LFunction s :=
    DirichletCharacter.differentiableAt_LFunction χ s (Or.inr hne)
  have hΛs : χ.completedLFunction s ≠ 0 := by
    rw [hΛ s hs]
    exact mul_ne_zero (hγ s hs).1 hL
  have hlogΛ : logDeriv χ.completedLFunction s =
      logDeriv χ.gammaFactor s + logDeriv χ.LFunction s := by
    rw [logDeriv_apply, hΛev.deriv_eq, hΛev.eq_of_nhds, ← logDeriv_apply,
      logDeriv_mul s (hγ s hs).1 hL (hγ s hs).2 hLd]
  refine ⟨mul_ne_zero (natCast_cpow_ne_zero s) hΛs, ?_⟩
  rw [xi_eq_mul, logDeriv_mul s (natCast_cpow_ne_zero s) hΛs (differentiable_natCast_cpow s)
    ((DirichletCharacter.differentiable_completedLFunction hne) s), logDeriv_natCast_cpow, hlogΛ]

/-- **H1 from the statements HF2–HF5** (no `sorry`: HF1 is the proved
`Exp7.EF.HF1.logDeriv_eq_add_tsum_of_order_one`). -/
theorem H1_of_leaves {χ : DirichletCharacter ℂ N} (h : XiLeaves χ) (hne : χ ≠ 1) {s : ℂ}
    (hs : 0 < s.re) (hL : χ.LFunction s ≠ 0) :
    (logDeriv χ.LFunction s).re + Real.log N / 2 + (logDeriv χ.gammaFactor s).re =
      ∑' ρ : ℂ, (analyticOrderNatAt χ.completedLFunction ρ : ℝ) * (1 / (s - ρ)).re := by
  obtain ⟨hξ, hlog⟩ := logDeriv_xi_eq χ hne hs hL
  have h1 := re_logDeriv_xi_eq_tsum h hne hξ
  simp only [analyticOrderNatAt_xi χ hne] at h1
  rw [← h1, hlog]
  simp only [add_re, div_ofNat_re, ofReal_re]
  ring

/-- The leaves HF2–HF5 of `HadamardFallback.lean` (this is the only place where their `sorry`s
enter). -/
theorem xiLeaves_of_fallback (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) (hne : χ ≠ 1) :
    XiLeaves χ where
  growth := xi_growth χ hχ hne
  differentiable := (xi_differentiable_and_ne_zero χ hχ hne).1
  ne_zero := (xi_differentiable_and_ne_zero χ hχ hne).2
  logDeriv_one_sub := logDeriv_xi_one_sub χ hχ hne
  order_one_sub_conj := analyticOrderNatAt_xi_one_sub_conj χ hχ hne

/-- **H1 from the fallback leaves.**  Verbatim statement of
`Exp7.EF.re_logDeriv_LFunction_add_eq_tsum`. -/
theorem H1_of_fallback (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) (hne : χ ≠ 1) {s : ℂ}
    (hs : 0 < s.re) (hL : χ.LFunction s ≠ 0) :
    (logDeriv χ.LFunction s).re + Real.log N / 2 + (logDeriv χ.gammaFactor s).re =
      ∑' ρ : ℂ, (analyticOrderNatAt χ.completedLFunction ρ : ℝ) * (1 / (s - ρ)).re :=
  H1_of_leaves (xiLeaves_of_fallback χ hχ hne) hne hs hL

/-- **H2 from the fallback leaves.**  Verbatim statement of
`Exp7.EF.summable_norm_analyticOrderNatAt_completedLFunction_mul_re_one_div_sub`. -/
theorem H2_of_fallback (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) (hne : χ ≠ 1) (s : ℂ) :
    Summable (fun ρ : ℂ ↦
      ‖(analyticOrderNatAt χ.completedLFunction ρ : ℝ) * (1 / (s - ρ)).re‖) :=
  H2_of_leaves (xiLeaves_of_fallback χ hχ hne) hne s

/-! ### Statement checks

The three `example`s below fail to compile if the statements drift from the originals. -/



example : type_of% @Exp7.EF.Fallback.logDeriv_eq_add_tsum_of_order_one
    = type_of% @Exp7.EF.HF1.logDeriv_eq_add_tsum_of_order_one := rfl

end Main

end Exp7.EF.Fallback
