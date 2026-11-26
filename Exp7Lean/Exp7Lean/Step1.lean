import Exp7Lean.Low

/-!
Exponent 7: Step 1, proved from Mathlib's class group.
-/

namespace Exp7

open QuadraticAlgebra

open scoped nonZeroDivisors

/-- The coefficient `a = -(q+1)/4`, so that `ω^2 = a + ω` has discriminant `1 + 4a = -q`. -/
def aOf (q : ℕ) : ℤ := -(((q : ℤ) + 1) / 4)

/-- The ring of integers of `ℚ(√-q)` for `q ≡ 3 (mod 4)`: `ℤ[ω]`, `ω^2 = ω + a`. -/
abbrev OK (q : ℕ) : Type := QuadraticAlgebra ℤ (aOf q) 1

lemma four_aOf {q : ℕ} (h4 : q % 4 = 3) : 4 * aOf q = -((q : ℤ) + 1) := by
  unfold aOf
  omega

lemma discr_aOf {q : ℕ} (h4 : q % 4 = 3) : discr (aOf q) 1 = -(q : ℤ) := by
  unfold discr
  have := four_aOf h4
  linarith

section

variable {q : ℕ} [hq : Fact q.Prime] [h4 : Fact (q % 4 = 3)]

instance : Fact (¬ IsSquare (discr (aOf q) 1)) := ⟨by
  rw [discr_aOf h4.out]
  rintro ⟨r, hr⟩
  have : (0 : ℤ) < q := by exact_mod_cast hq.out.pos
  nlinarith [mul_self_nonneg r]⟩

instance : Fact (Int.IsFundamentalDiscr (discr (aOf q) 1)) := ⟨by
  rw [discr_aOf h4.out, Int.isFundamentalDiscr_iff_squarefree]
  left
  refine ⟨by have := h4.out; omega, ?_⟩
  rw [← Int.squarefree_natAbs]
  simpa using hq.out.squarefree⟩

instance : Fact (¬ IsSquare (discr ((aOf q : ℤ) : ℚ) ((1 : ℤ) : ℚ))) := ⟨by
  have h : discr ((aOf q : ℤ) : ℚ) ((1 : ℤ) : ℚ) = ((discr (aOf q) 1 : ℤ) : ℚ) := by
    simp [discr]
  rw [h, discr_aOf h4.out]
  rintro ⟨r, hr⟩
  have : (0 : ℚ) < q := by exact_mod_cast hq.out.pos
  push_cast at hr
  nlinarith [mul_self_nonneg r]⟩

instance : IsDedekindDomain (OK q) := by
  have : IsIntegralClosure (OK q) ℤ (QuadraticAlgebra ℚ ((aOf q : ℤ) : ℚ) ((1 : ℤ) : ℚ)) :=
    QuadraticAlgebra.Int.isIntegralClosure_iff.mpr Fact.out
  exact IsIntegralClosure.isDedekindDomain ℤ ℚ
    (QuadraticAlgebra ℚ ((aOf q : ℤ) : ℚ) ((1 : ℤ) : ℚ)) (OK q)

/-- The class group of `ℚ(√-q)` has exponent 7. -/
def ClassExp7 (q : ℕ) [Fact q.Prime] [Fact (q % 4 = 3)] : Prop :=
  Monoid.exponent (ClassGroup (OK q)) = 7

omit hq h4 in
lemma star_omega_sub (t : ℤ) : star (ω - (t : OK q)) = 1 - ω - (t : OK q) := by
  ext <;> simp

omit hq h4 in
lemma norm_omega_sub (t : ℤ) :
    QuadraticAlgebra.norm (ω - (t : OK q)) = t ^ 2 - t - aOf q := by
  simp [QuadraticAlgebra.norm_def]
  ring

/-- The ideal `(p, ω - t)`. -/
noncomputable def idealI (q p : ℕ) (t : ℤ) : Ideal (OK q) :=
  Ideal.span {(p : OK q), ω - (t : OK q)}

omit h4 in
lemma coprime_p {p : ℕ} (hp : p.Prime) (hpq : p ≠ q) (h4' : q % 4 = 3) {t : ℤ}
    (ht : (p : ℤ) ∣ t ^ 2 - t - aOf q) : IsCoprime (p : ℤ) (1 - 2 * t) := by
  rw [(Nat.prime_iff_prime_int.mp hp).coprime_iff_not_dvd]
  intro hd
  have h4a := four_aOf h4'
  have h1 : (p : ℤ) ∣ (1 - 2 * t) ^ 2 := dvd_pow hd (by norm_num)
  have h2 : (p : ℤ) ∣ 4 * (t ^ 2 - t - aOf q) := Dvd.dvd.mul_left ht 4
  have h3 : (q : ℤ) = 4 * (t ^ 2 - t - aOf q) - (1 - 2 * t) ^ 2 := by linear_combination h4a
  have h5 : (p : ℤ) ∣ (q : ℤ) := by rw [h3]; exact dvd_sub h2 h1
  exact hpq ((Nat.prime_dvd_prime_iff_eq hp hq.out).mp (Int.natCast_dvd_natCast.mp h5))

lemma idealI_mul_map {p : ℕ} (hp : p.Prime) (hpq : p ≠ q) {t : ℤ}
    (ht : (p : ℤ) ∣ t ^ 2 - t - aOf q) :
    idealI q p t * (idealI q p t).map (starRingEnd (OK q)) = Ideal.span {(p : OK q)} := by
  obtain ⟨u, v, huv⟩ := coprime_p hp hpq h4.out ht
  have huv' : ((u * p + v * (1 - 2 * t) : ℤ) : OK q) = 1 := by rw [huv]; simp
  push_cast at huv'
  unfold idealI
  rw [Ideal.map_span, Set.image_pair, Ideal.span_pair_mul_span_pair]
  simp only [starRingEnd_apply, star_natCast, star_omega_sub]
  apply le_antisymm
  · rw [Ideal.span_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rw [SetLike.mem_coe, Ideal.mem_span_singleton]
    rcases hx with rfl | rfl | rfl | rfl
    · exact dvd_mul_right _ _
    · exact dvd_mul_right _ _
    · exact dvd_mul_left _ _
    · obtain ⟨m, hm⟩ := ht
      have h := algebraMap_norm_eq_mul_star (ω - (t : OK q))
      rw [star_omega_sub, norm_omega_sub, hm] at h
      rw [← h]
      refine ⟨(m : OK q), ?_⟩
      simp
  · rw [Ideal.span_singleton_le_iff_mem]
    have key : (p : OK q) = (u : OK q) * ((p : OK q) * (p : OK q)) +
        (v : OK q) * ((p : OK q) * (1 - ω - (t : OK q)) + (ω - (t : OK q)) * (p : OK q)) := by
      linear_combination (-(p : OK q)) * huv'
    have hmem : (u : OK q) * ((p : OK q) * (p : OK q)) +
        (v : OK q) * ((p : OK q) * (1 - ω - (t : OK q)) + (ω - (t : OK q)) * (p : OK q)) ∈
        Ideal.span {(p : OK q) * (p : OK q), (p : OK q) * (1 - ω - (t : OK q)),
          (ω - (t : OK q)) * (p : OK q), (ω - (t : OK q)) * (1 - ω - (t : OK q))} := by
      refine Ideal.add_mem _ (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))) ?_
      refine Ideal.mul_mem_left _ _ (Ideal.add_mem _ (Ideal.subset_span (by simp))
        (Ideal.subset_span (by simp)))
    rwa [← key] at hmem

/-- If the class group has exponent 7 and `X^2 - X - a` has a root modulo `p`, then `P^7` is
principal for `P = (p, ω - t)`, and its generator `x + yω` has norm `p^7`. -/
theorem norm_equation (h : ClassExp7 q) {p : ℕ} (hp : p.Prime) (hpq : p ≠ q) {t : ℤ}
    (ht : (p : ℤ) ∣ t ^ 2 - t - aOf q) :
    ∃ x y : ℤ, y ≠ 0 ∧ 4 * (p : ℤ) ^ 7 = (2 * x + y) ^ 2 + q * y ^ 2 ∧
      (p ≠ 2 → ¬ (p : ℤ) ∣ y) := by
  have h4a := four_aOf h4.out
  have hprod := idealI_mul_map hp hpq ht
  have hpR : (p : OK q) ≠ 0 := by
    intro h0
    have := congrArg QuadraticAlgebra.re h0
    simp at this
    exact hp.ne_zero this
  have hpI : (p : OK q) ∈ idealI q p t := Ideal.subset_span (by simp)
  have hwI : ω - (t : OK q) ∈ idealI q p t := Ideal.subset_span (by simp)
  have hI0 : idealI q p t ≠ ⊥ := by
    intro hbot
    rw [hbot] at hpI
    exact hpR (by simpa using hpI)
  have hImem : idealI q p t ∈ (Ideal (OK q))⁰ := mem_nonZeroDivisors_of_ne_zero hI0
  have h7 : (idealI q p t ^ 7).IsPrincipal := by
    have hpow : idealI q p t ^ 7 ∈ (Ideal (OK q))⁰ := pow_mem hImem 7
    rw [← ClassGroup.mk0_eq_one_iff hpow]
    have e : (⟨idealI q p t ^ 7, hpow⟩ : (Ideal (OK q))⁰) = ⟨idealI q p t, hImem⟩ ^ 7 :=
      Subtype.ext (by simp)
    rw [e, map_pow]
    have h' : Monoid.exponent (ClassGroup (OK q)) = 7 := h
    rw [← h']
    exact Monoid.pow_exponent_eq_one _
  obtain ⟨α, hα⟩ := h7
  have hα' : idealI q p t ^ 7 = Ideal.span {α} := hα
  have hσ : (idealI q p t).map (starRingEnd (OK q)) ^ 7 = Ideal.span {star α} := by
    rw [← Ideal.map_pow, hα', Ideal.map_span, Set.image_singleton, starRingEnd_apply]
  have hassoc : Ideal.span {α * star α} = Ideal.span {(p : OK q) ^ 7} := by
    rw [← Ideal.span_singleton_mul_span_singleton, ← hα', ← hσ, ← mul_pow, hprod,
      Ideal.span_singleton_pow]
  rw [Ideal.span_singleton_eq_span_singleton] at hassoc
  obtain ⟨u, hu⟩ := hassoc
  set n : ℤ := QuadraticAlgebra.norm α with hn
  have hns : algebraMap ℤ (OK q) n = α * star α := algebraMap_norm_eq_mul_star α
  have hnorm := congrArg QuadraticAlgebra.norm hu
  rw [← hns, map_mul, map_pow, QuadraticAlgebra.norm_algebraMap, QuadraticAlgebra.norm_natCast]
    at hnorm
  have hunit : IsUnit (QuadraticAlgebra.norm (u : OK q)) :=
    QuadraticAlgebra.isUnit_iff_norm_isUnit.mp u.isUnit
  have hndef : n = α.re * α.re + 1 * α.re * α.im - aOf q * α.im * α.im :=
    QuadraticAlgebra.norm_def α
  have hn4 : 4 * n = (2 * α.re + α.im) ^ 2 + q * α.im ^ 2 := by
    linear_combination 4 * hndef - α.im ^ 2 * h4a
  have hppos : (0 : ℤ) < (p : ℤ) ^ 7 := pow_pos (by exact_mod_cast hp.pos) 7
  have hnn : 0 ≤ n := by nlinarith [sq_nonneg (2 * α.re + α.im), sq_nonneg α.im,
    (Nat.cast_nonneg q : (0 : ℤ) ≤ q)]
  have hnp : n = (p : ℤ) ^ 7 := by
    rcases Int.isUnit_iff.mp hunit with he | he
    · rw [he, mul_one] at hnorm
      have h0 : (n - (p : ℤ) ^ 7) * (n + (p : ℤ) ^ 7) = 0 := by
        linear_combination hnorm
      rcases mul_eq_zero.mp h0 with h1 | h1
      · linarith
      · linarith
    · rw [he] at hnorm
      nlinarith [sq_nonneg n, pow_pos hppos 2]
  refine ⟨α.re, α.im, ?_, by rw [← hn4, hnp], ?_⟩
  · -- `y ≠ 0`: otherwise `p^7` would be a square
    intro hy0
    rw [hy0] at hn4
    have hsq : (α.re.natAbs : ℤ) ^ 2 = (p : ℤ) ^ 7 := by
      rw [Int.natAbs_sq]; linarith
    have hsqN : α.re.natAbs ^ 2 = p ^ 7 := by exact_mod_cast hsq
    have := Fact.mk hp
    have hval := congrArg (multiplicity p) hsqN
    rw [Nat.multiplicity_pow, Nat.multiplicity_prime_pow] at hval
    omega
  · -- `p ∤ y` for odd `p`: otherwise `p ∣ α` and `P^7 ⊆ (p) ⊆ P'`
    intro hp2 hdvd
    have hpZ := Nat.prime_iff_prime_int.mp hp
    have heq : 4 * (p : ℤ) ^ 7 = (2 * α.re + α.im) ^ 2 + q * α.im ^ 2 := by rw [← hn4, hnp]
    have hd1 : (p : ℤ) ∣ (2 * α.re + α.im) ^ 2 := by
      have e1 : (2 * α.re + α.im) ^ 2 = 4 * (p : ℤ) ^ 7 - q * α.im ^ 2 := by linarith
      rw [e1]
      exact dvd_sub (Dvd.dvd.mul_left (dvd_pow_self _ (by norm_num)) 4)
        (Dvd.dvd.mul_left (dvd_pow hdvd (by norm_num)) _)
    have hd2 : (p : ℤ) ∣ 2 * α.re + α.im := hpZ.dvd_of_dvd_pow hd1
    have hd3 : (p : ℤ) ∣ 2 * α.re := by
      have := dvd_sub hd2 hdvd
      simpa using this
    have hd4 : (p : ℤ) ∣ α.re := by
      rcases hpZ.dvd_or_dvd hd3 with h2 | h2
      · exfalso
        have : p ∣ 2 := by exact_mod_cast h2
        exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this)
      · exact h2
    obtain ⟨x', hx'⟩ := hd4
    obtain ⟨y', hy'⟩ := hdvd
    have hαeq : α = (p : OK q) * ⟨x', y'⟩ := by
      ext <;> simp [hx', hy']
    have hαp : α ∈ Ideal.span {(p : OK q)} := Ideal.mem_span_singleton.mpr ⟨_, hαeq⟩
    have hle : idealI q p t ^ 7 ≤ (idealI q p t).map (starRingEnd (OK q)) := by
      rw [hα', Ideal.span_singleton_le_iff_mem]
      have : Ideal.span {(p : OK q)} ≤ (idealI q p t).map (starRingEnd (OK q)) := by
        rw [← hprod]; exact Ideal.mul_le_right
      exact this hαp
    obtain ⟨a', b', hab⟩ := coprime_p hp hpq h4.out ht
    have hab' : ((a' * p + b' * (1 - 2 * t) : ℤ) : OK q) = 1 := by rw [hab]; simp
    push_cast at hab'
    have hsup : idealI q p t ⊔ (idealI q p t).map (starRingEnd (OK q)) = ⊤ := by
      rw [Ideal.eq_top_iff_one]
      have hs' : star (ω - (t : OK q)) ∈ (idealI q p t).map (starRingEnd (OK q)) := by
        have := Ideal.mem_map_of_mem (starRingEnd (OK q)) hwI
        rwa [starRingEnd_apply] at this
      rw [star_omega_sub] at hs'
      have h1 : (1 : OK q) = (a' : OK q) * (p : OK q) +
          (b' : OK q) * ((ω - (t : OK q)) + (1 - ω - (t : OK q))) := by
        linear_combination -hab'
      rw [h1]
      refine Ideal.add_mem _ (Ideal.mul_mem_left _ _ (Ideal.mem_sup_left hpI)) ?_
      exact Ideal.mul_mem_left _ _ (Ideal.add_mem _ (Ideal.mem_sup_left hwI)
        (Ideal.mem_sup_right hs'))
    have hcop : IsCoprime (idealI q p t ^ 7) ((idealI q p t).map (starRingEnd (OK q))) :=
      (Ideal.isCoprime_iff_sup_eq.mpr hsup).pow_left
    have htop : (idealI q p t).map (starRingEnd (OK q)) = ⊤ := by
      rw [← sup_eq_right.mpr hle]; exact Ideal.isCoprime_iff_sup_eq.mp hcop
    rw [htop, Ideal.mul_top] at hprod
    rw [hprod] at hwI
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hwI
    have him := congrArg QuadraticAlgebra.im hc
    simp at him
    have : (p : ℤ) ∣ 1 := ⟨c.im, him⟩
    have hp1 : p ∣ 1 := by exact_mod_cast this
    exact hp.one_lt.ne' (Nat.dvd_one.mp hp1)

end

/-- A root of `X^2 - X - a` modulo a prime `p` that splits in `ℚ(√-q)`. -/
lemma exists_root {q : ℕ} (hq : q.Prime) (h4 : q % 4 = 3) {p : ℕ} (hp : p.Prime) (hpq : p ≠ q)
    (hs : Splits q p) : ∃ t : ℤ, (p : ℤ) ∣ t ^ 2 - t - aOf q := by
  have h4a := four_aOf h4
  by_cases h2 : p = 2
  · subst h2
    rw [splits_two_iff] at hs
    refine ⟨0, ?_⟩
    have : (2 : ℤ) ∣ aOf q := by unfold aOf; omega
    simpa using this
  · rw [splits_odd_iff q h2] at hs
    have := Fact.mk hp
    have hodd : p % 2 = 1 := by
      rcases hp.eq_two_or_odd with h | h
      · exact absurd h h2
      · exact h
    have hne : ((-(q : ℤ) : ℤ) : ZMod p) ≠ 0 := by
      intro h0
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd, dvd_neg] at h0
      exact hpq ((Nat.prime_dvd_prime_iff_eq hp hq).mp (Int.natCast_dvd_natCast.mp h0))
    have hleg : legendreSym p (-(q : ℤ)) = 1 := by rw [jacobiSym.legendreSym.to_jacobiSym]; exact hs
    obtain ⟨r, hr⟩ := (legendreSym.eq_one_iff p hne).mp hleg
    -- an integer `s0` with `p ∣ s0^2 + q`
    have hs0 : (p : ℤ) ∣ (r.val : ℤ) ^ 2 + q := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      rw [ZMod.natCast_zmod_val]
      have : ((-(q : ℤ) : ℤ) : ZMod p) = -(q : ZMod p) := by push_cast; rfl
      rw [this] at hr
      rw [pow_two, ← hr]; ring
    -- make it odd, `s = 2t - 1`
    obtain ⟨s, hsodd, hsd⟩ : ∃ s : ℤ, s % 2 = 1 ∧ (p : ℤ) ∣ s ^ 2 + q := by
      rcases Int.emod_two_eq_zero_or_one (r.val : ℤ) with he | he
      · refine ⟨(r.val : ℤ) + p, by omega, ?_⟩
        have e : ((r.val : ℤ) + p) ^ 2 + q = ((r.val : ℤ) ^ 2 + q) + p * (2 * r.val + p) := by ring
        rw [e]
        exact dvd_add hs0 (dvd_mul_right _ _)
      · exact ⟨_, he, hs0⟩
    refine ⟨(s + 1) / 2, ?_⟩
    have hst : s = 2 * ((s + 1) / 2) - 1 := by omega
    have e4 : 4 * (((s + 1) / 2) ^ 2 - (s + 1) / 2 - aOf q) = s ^ 2 + q := by
      set t := (s + 1) / 2 with ht
      rw [hst]
      linear_combination -h4a
    have hd : (p : ℤ) ∣ 4 * (((s + 1) / 2) ^ 2 - (s + 1) / 2 - aOf q) := by rw [e4]; exact hsd
    rcases (Nat.prime_iff_prime_int.mp hp).dvd_or_dvd hd with h | h
    · exfalso
      have h' : p ∣ 4 := by exact_mod_cast h
      have : p ∣ 2 := hp.dvd_of_dvd_pow (show p ∣ 2 ^ 2 by simpa using h')
      exact h2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this)
    · exact h

/-- `ℚ(√-q)`, for a prime `q ≡ 3 (mod 4)`, has class group of exponent 7. This is Mathlib's
`ClassGroup` of the ring of integers `ℤ[ω]`, `ω^2 = ω - (q+1)/4`. -/
def IsExp7 (q : ℕ) : Prop :=
  ∃ (hq : q.Prime) (h4 : q % 4 = 3), @ClassExp7 q ⟨hq⟩ ⟨h4⟩

/-- **Step 1**, proved: if the class group of `ℚ(√-q)` has exponent 7 and `p ≠ q` splits, then
`4p^7 = x^2 + qy^2` with `y ≥ 1`, and `p ∤ y` when `p` is odd. -/
theorem normEq_classGroup (q : ℕ) (hq : q.Prime) (h4 : q % 4 = 3) (hE : IsExp7 q) (p : ℕ)
    (hp : p.Prime) (hpq : p ≠ q) (hs : Splits q p) :
    ∃ x y : ℕ, 1 ≤ y ∧ (p ≠ 2 → ¬ p ∣ y) ∧ 4 * p ^ 7 = x ^ 2 + q * y ^ 2 := by
  obtain ⟨hq', h4', hC⟩ := hE
  have := Fact.mk hq'
  have := Fact.mk h4'
  obtain ⟨t, ht⟩ := exists_root hq h4 hp hpq hs
  obtain ⟨x, y, hy, heq, hprim⟩ := norm_equation hC hp hpq ht
  refine ⟨(2 * x + y).natAbs, y.natAbs, Int.natAbs_pos.mpr hy, ?_, ?_⟩
  · intro hp2 hd
    exact hprim hp2 (Int.natCast_dvd.mpr hd)
  · have : ((4 * p ^ 7 : ℕ) : ℤ) = (((2 * x + y).natAbs ^ 2 + q * y.natAbs ^ 2 : ℕ) : ℤ) := by
      push_cast
      rw [sq_abs, sq_abs]
      exact heq
    exact_mod_cast this

end Exp7
