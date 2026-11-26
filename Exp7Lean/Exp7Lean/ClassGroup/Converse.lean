import Exp7Lean.ClassGroup.Defs

/-!
Exponent 7: the converse of Step 1.

For a prime `l ≠ q` and a root `t` of `X^2 - X - a` modulo `l`, a solution of
`4 l^n = x^2 + q y^2` with `l ∤ y` makes `(l, ω - t)^n` principal. The proof is elementary: with
`α = (x - y)/2 + y ω` (or its conjugate) one has `(α)(ᾱ) = (l)^n = P^n P̄^n`, and `(α)` is coprime
to `P̄`, whence `(α) = P^n`. No unique factorisation of ideals is needed.

Also: the ramified prime `(q, ω - t) = (2ω - 1)`, and the non-principality witness (if
`4 l = x^2 + q y^2` has no solution then `(l, ω - t)` is not principal).
-/

namespace Exp7

open QuadraticAlgebra

open scoped nonZeroDivisors

section

variable {q : ℕ} [hq : Fact q.Prime] [h4 : Fact (q % 4 = 3)]

omit hq h4 in
/-- The conjugate of `(l, ω - t)` is `(l, 1 - ω - t)`. -/
lemma map_star_idealI (l : ℕ) (t : ℤ) :
    (idealI q l t).map (starRingEnd (OK q)) =
      Ideal.span {(l : OK q), 1 - ω - (t : OK q)} := by
  unfold idealI
  rw [Ideal.map_span, Set.image_pair]
  simp only [starRingEnd_apply, star_natCast, star_omega_sub]

omit hq h4 in
lemma mk_mul_star (u y : ℤ) :
    (⟨u, y⟩ : OK q) * star (⟨u, y⟩ : OK q) = ((u ^ 2 + u * y - aOf q * y ^ 2 : ℤ) : OK q) := by
  rw [← algebraMap_norm_eq_mul_star, QuadraticAlgebra.norm_def]
  simp only [eq_intCast]
  congr 1
  ring

/-- **Core of the converse.** If `α = u + y ω` has norm `l^n` and `l ∤ u + y (1 - t)` (that is,
`α ∉ P̄`), then `P^n = (α)` for `P = (l, ω - t)`. -/
theorem idealI_pow_eq_span {l : ℕ} (hl : l.Prime) (hlq : l ≠ q) {t : ℤ}
    (ht : (l : ℤ) ∣ t ^ 2 - t - aOf q) (n : ℕ) {u y : ℤ}
    (hN : u ^ 2 + u * y - aOf q * y ^ 2 = (l : ℤ) ^ n)
    (hc : ¬ (l : ℤ) ∣ u + y * (1 - t)) :
    idealI q l t ^ n = Ideal.span {(⟨u, y⟩ : OK q)} := by
  have hprod := idealI_mul_map hl hlq ht
  have hlI : (l : OK q) ∈ idealI q l t := Ideal.subset_span (by simp)
  have hwI : ω - (t : OK q) ∈ idealI q l t := Ideal.subset_span (by simp)
  have hlI' : (l : OK q) ∈ (idealI q l t).map (starRingEnd (OK q)) := by
    rw [map_star_idealI]; exact Ideal.subset_span (by simp)
  have hwI' : 1 - ω - (t : OK q) ∈ (idealI q l t).map (starRingEnd (OK q)) := by
    rw [map_star_idealI]; exact Ideal.subset_span (by simp)
  set P := idealI q l t with hP
  set P' := P.map (starRingEnd (OK q)) with hP'
  set α : OK q := ⟨u, y⟩ with hα
  have hαα : Ideal.span {α} * Ideal.span {star α} = P ^ n * P' ^ n := by
    rw [Ideal.span_singleton_mul_span_singleton, ← mul_pow, hprod, Ideal.span_singleton_pow,
      hα, mk_mul_star, hN]
    push_cast
    rfl
  obtain ⟨a', b', hab⟩ : IsCoprime (l : ℤ) (u + y * (1 - t)) :=
    (Nat.prime_iff_prime_int.mp hl).coprime_iff_not_dvd.mpr hc
  have hab' : ((a' * l + b' * (u + y * (1 - t)) : ℤ) : OK q) = 1 := by rw [hab]; simp
  push_cast at hab'
  have hα1 : α = (u : OK q) + (y : OK q) * ω := by
    rw [hα]; ext <;> simp
  have hsα : star α = (u : OK q) + (y : OK q) * (1 - ω) := by
    rw [hα]; ext <;> simp
  -- `(α) + P̄ = ⊤`
  have hcop : IsCoprime (Ideal.span {α}) P' := by
    rw [Ideal.isCoprime_iff_sup_eq, Ideal.eq_top_iff_one]
    have h1 : (1 : OK q) = (a' : OK q) * (l : OK q) +
        (b' : OK q) * (α + (y : OK q) * (1 - ω - (t : OK q))) := by
      rw [hα1]; linear_combination -hab'
    rw [h1]
    refine Ideal.add_mem _ (Ideal.mul_mem_left _ _ (Ideal.mem_sup_right hlI')) ?_
    exact Ideal.mul_mem_left _ _ (Ideal.add_mem _
      (Ideal.mem_sup_left (Ideal.mem_span_singleton_self α))
      (Ideal.mul_mem_left _ _ (Ideal.mem_sup_right hwI')))
  -- `(ᾱ) + P = ⊤`
  have hcop' : IsCoprime (Ideal.span {star α}) P := by
    rw [Ideal.isCoprime_iff_sup_eq, Ideal.eq_top_iff_one]
    have h1 : (1 : OK q) = (a' : OK q) * (l : OK q) +
        (b' : OK q) * (star α + (y : OK q) * (ω - (t : OK q))) := by
      rw [hsα]; linear_combination -hab'
    rw [h1]
    refine Ideal.add_mem _ (Ideal.mul_mem_left _ _ (Ideal.mem_sup_right hlI)) ?_
    exact Ideal.mul_mem_left _ _ (Ideal.add_mem _
      (Ideal.mem_sup_left (Ideal.mem_span_singleton_self (star α)))
      (Ideal.mul_mem_left _ _ (Ideal.mem_sup_right hwI)))
  have h1 : Ideal.span {α} ⊔ P' ^ n = ⊤ := Ideal.isCoprime_iff_sup_eq.mp hcop.pow_right
  have h2 : Ideal.span {star α} ⊔ P ^ n = ⊤ := Ideal.isCoprime_iff_sup_eq.mp hcop'.pow_right
  apply le_antisymm
  · calc P ^ n = P ^ n * (Ideal.span {α} ⊔ P' ^ n) := by rw [h1, Ideal.mul_top]
      _ = P ^ n * Ideal.span {α} ⊔ P ^ n * P' ^ n := Ideal.mul_sup _ _ _
      _ ≤ Ideal.span {α} := sup_le Ideal.mul_le_right (by rw [← hαα]; exact Ideal.mul_le_left)
  · calc Ideal.span {α} = Ideal.span {α} * (Ideal.span {star α} ⊔ P ^ n) := by
          rw [h2, Ideal.mul_top]
      _ = Ideal.span {α} * Ideal.span {star α} ⊔ Ideal.span {α} * P ^ n := Ideal.mul_sup _ _ _
      _ ≤ P ^ n := sup_le (by rw [hαα]; exact Ideal.mul_le_left) Ideal.mul_le_right

omit hq in
/-- In `4 m = x^2 + q y^2` with `q ≡ 3 (mod 4)`, `x` and `y` have the same parity. -/
lemma two_dvd_sub_of_eq {x y m : ℤ} (h : 4 * m = x ^ 2 + q * y ^ 2) : (2 : ℤ) ∣ x - y := by
  have h4' := h4.out
  have hq4 : (q : ℤ) = 4 * ((q / 4 : ℕ) : ℤ) + 3 := by omega
  have h2 : (x - y) * (x + y) = 4 * (m - y ^ 2 - ((q / 4 : ℕ) : ℤ) * y ^ 2) := by
    linear_combination -h - y ^ 2 * hq4
  by_contra hodd
  have h1 : (x - y) % 2 = 1 := by omega
  have h3 : (x + y) % 2 = 1 := by omega
  have h5 : ((x - y) * (x + y)) % 2 = 1 := by rw [Int.mul_emod, h1, h3]; rfl
  omega

/-- **Converse of Step 1** (any exponent `n`). For a prime `l ≠ q` and a root `t` of
`X^2 - X - a` modulo `l`, a solution of `4 l^n = x^2 + q y^2` with `l ∤ y` gives a generator of
`(l, ω - t)^n`. This covers `l = 2` (where `l ∤ y` says that `y`, hence `x`, is odd). -/
theorem idealI_pow_isPrincipal {l : ℕ} (hl : l.Prime) (hlq : l ≠ q) {t : ℤ}
    (ht : (l : ℤ) ∣ t ^ 2 - t - aOf q) (n : ℕ) {x y : ℤ}
    (hxy : 4 * (l : ℤ) ^ n = x ^ 2 + q * y ^ 2) (hy : ¬ (l : ℤ) ∣ y) :
    (idealI q l t ^ n).IsPrincipal := by
  have h4a := four_aOf h4.out
  obtain ⟨u, hu⟩ := two_dvd_sub_of_eq hxy
  have hx : x = 2 * u + y := by linarith
  have hN : u ^ 2 + u * y - aOf q * y ^ 2 = (l : ℤ) ^ n := by
    have : 4 * (u ^ 2 + u * y - aOf q * y ^ 2) = 4 * (l : ℤ) ^ n := by
      rw [hxy, hx]; linear_combination -y ^ 2 * h4a
    linarith
  have hlZ := Nat.prime_iff_prime_int.mp hl
  by_cases hc : (l : ℤ) ∣ u + y * (1 - t)
  · -- then `l ∤ u + y t`, and the conjugate `(u + y) - y ω` generates
    have hc' : ¬ (l : ℤ) ∣ (u + y) + (-y) * (1 - t) := by
      intro hd
      have hd2 : (l : ℤ) ∣ y * (1 - 2 * t) := by
        have := dvd_sub hc hd
        have e : u + y * (1 - t) - (u + y + -y * (1 - t)) = y * (1 - 2 * t) := by ring
        rwa [e] at this
      exact hy ((coprime_p hl hlq h4.out ht).dvd_of_dvd_mul_right hd2)
    have hN' : (u + y) ^ 2 + (u + y) * (-y) - aOf q * (-y) ^ 2 = (l : ℤ) ^ n := by
      rw [← hN]; ring
    exact ⟨⟨_, idealI_pow_eq_span hl hlq ht n hN' hc'⟩⟩
  · exact ⟨⟨_, idealI_pow_eq_span hl hlq ht n hN hc⟩⟩

/-- Converse of Step 1: a solution of `4 l^7 = x^2 + q y^2` with `l ∤ y` makes `(l, ω - t)^7`
principal. -/
theorem idealI_pow_seven_isPrincipal {l : ℕ} (hl : l.Prime) (hlq : l ≠ q) {t : ℤ}
    (ht : (l : ℤ) ∣ t ^ 2 - t - aOf q) {x y : ℤ}
    (hxy : 4 * (l : ℤ) ^ 7 = x ^ 2 + q * y ^ 2) (hy : ¬ (l : ℤ) ∣ y) :
    (idealI q l t ^ 7).IsPrincipal :=
  idealI_pow_isPrincipal hl hlq ht 7 hxy hy

omit hq in
/-- In a solution of `4 l = x^2 + q y^2` with `l ≠ q` prime, automatically `l ∤ y`. -/
lemma not_dvd_of_four_mul_eq {l : ℕ} (hl : l.Prime) (hlq : l ≠ q) {x y : ℤ}
    (hxy : 4 * (l : ℤ) = x ^ 2 + q * y ^ 2) : ¬ (l : ℤ) ∣ y := by
  intro hd
  have hlZ := Nat.prime_iff_prime_int.mp hl
  have hl0 : (0 : ℤ) < l := by exact_mod_cast hl.pos
  have hq3 : (3 : ℤ) ≤ q := by
    have := h4.out
    have : 3 ≤ q := by omega
    exact_mod_cast this
  obtain ⟨y', rfl⟩ := hd
  have hdx : (l : ℤ) ∣ x ^ 2 := ⟨4 - q * l * y' ^ 2, by linear_combination -hxy⟩
  obtain ⟨x', rfl⟩ := hlZ.dvd_of_dvd_pow hdx
  -- `4 = l (x'^2 + q y'^2)`
  have h1 : (4 : ℤ) = l * (x' ^ 2 + q * y' ^ 2) := by
    have : (l : ℤ) * 4 = l * (l * (x' ^ 2 + q * y' ^ 2)) := by linear_combination hxy
    exact mul_left_cancel₀ hl0.ne' this
  have hy0 : y' = 0 := by
    by_contra hne
    have : 1 ≤ y' ^ 2 := by
      have := sq_nonneg y'
      have h0 : y' ^ 2 ≠ 0 := pow_ne_zero 2 hne
      omega
    have hl2 : (2 : ℤ) ≤ l := by exact_mod_cast hl.two_le
    nlinarith [sq_nonneg x', mul_le_mul hq3 this (by norm_num) (by linarith : (0 : ℤ) ≤ q)]
  rw [hy0] at h1
  -- `4 = l x'^2` with `l` prime: `l = 2`, `x'^2 = 2`, impossible
  have hl4 : l ∣ 4 := by
    have : (l : ℤ) ∣ 4 := ⟨_, h1⟩
    exact_mod_cast this
  have hl2 : l = 2 := (Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).mp
    (hl.dvd_of_dvd_pow (show l ∣ 2 ^ 2 by simpa using hl4))
  subst hl2
  have h2 : x' ^ 2 = 2 := by push_cast at h1; linarith
  have hx1 : x' < 2 := by nlinarith
  have hx2 : -2 < x' := by nlinarith
  have : x' = -1 ∨ x' = 0 ∨ x' = 1 := by omega
  rcases this with rfl | rfl | rfl <;> norm_num at h2

/-- Exponent-one converse: if `4 l = x^2 + q y^2` has a solution, then `(l, ω - t)` is
principal. -/
theorem idealI_isPrincipal {l : ℕ} (hl : l.Prime) (hlq : l ≠ q) {t : ℤ}
    (ht : (l : ℤ) ∣ t ^ 2 - t - aOf q) {x y : ℤ}
    (hxy : 4 * (l : ℤ) = x ^ 2 + q * y ^ 2) : (idealI q l t).IsPrincipal := by
  have h := idealI_pow_isPrincipal hl hlq ht 1 (x := x) (y := y) (by rw [pow_one]; exact hxy)
    (not_dvd_of_four_mul_eq hl hlq hxy)
  rwa [pow_one] at h

/-- The ramified prime: `(q, ω - t) = (2ω - 1) = (√-q)`. -/
theorem idealI_ramified_eq {t : ℤ} (ht : (q : ℤ) ∣ t ^ 2 - t - aOf q) :
    idealI q q t = Ideal.span {(2 * ω - 1 : OK q)} := by
  have h4a := four_aOf h4.out
  have hqZ := Nat.prime_iff_prime_int.mp hq.out
  -- `q ∣ 2t - 1`
  have hd : (q : ℤ) ∣ (2 * t - 1) ^ 2 := by
    obtain ⟨m, hm⟩ := ht
    exact ⟨4 * m - 1, by linear_combination 4 * hm + h4a⟩
  obtain ⟨m, hm⟩ := hqZ.dvd_of_dvd_pow hd
  have hm' : ((2 * t - 1 : ℤ) : OK q) = ((q * m : ℤ) : OK q) := by rw [hm]
  push_cast at hm'
  -- `q = 2k + 1`
  obtain ⟨k, hk⟩ : ∃ k : ℤ, (q : ℤ) = 2 * k + 1 := ⟨(q : ℤ) / 2, by have := h4.out; omega⟩
  have hk' : ((q : ℤ) : OK q) = ((2 * k + 1 : ℤ) : OK q) := by rw [hk]
  push_cast at hk'
  -- `(2ω - 1)^2 = -q`
  have hsq : (2 * ω - 1 : OK q) * (2 * ω - 1) = -(q : OK q) := by
    have h4a' : ((4 * aOf q : ℤ) : OK q) = ((-((q : ℤ) + 1) : ℤ) : OK q) := by rw [h4a]
    push_cast at h4a'
    have hω : (ω : OK q) * ω = (aOf q : OK q) + ω := by
      rw [omega_mul_omega_eq_mk]; ext <;> simp
    linear_combination 4 * hω + h4a'
  unfold idealI
  apply le_antisymm
  · rw [Ideal.span_le]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rw [SetLike.mem_coe, Ideal.mem_span_singleton]
    have hqd : (2 * ω - 1 : OK q) ∣ (q : OK q) := ⟨-(2 * ω - 1), by linear_combination hsq⟩
    rcases hz with rfl | rfl
    · exact hqd
    · -- `ω - t = q (ω - t) - k ((2ω - 1) - (2t - 1))`
      have e : (ω : OK q) - (t : OK q) = (q : OK q) * (ω - (t : OK q) + (k : OK q) * (m : OK q))
          + (2 * ω - 1) * (-(k : OK q)) := by
        linear_combination (-(ω : OK q) + (t : OK q)) * hk' + (k : OK q) * hm'
      rw [e]
      exact dvd_add (Dvd.dvd.mul_right hqd _) (dvd_mul_right _ _)
  · rw [Ideal.span_singleton_le_iff_mem]
    have e : (2 * ω - 1 : OK q) = (m : OK q) * (q : OK q) + 2 * (ω - (t : OK q)) := by
      linear_combination hm'
    rw [e]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
      (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))

/-- The ramified prime `(q, ω - t)` is principal. -/
theorem idealI_ramified_isPrincipal {t : ℤ} (ht : (q : ℤ) ∣ t ^ 2 - t - aOf q) :
    (idealI q q t).IsPrincipal :=
  ⟨⟨_, idealI_ramified_eq ht⟩⟩

/-- **Non-principality witness.** If `l ≠ q` is a prime with a root `t` and `4 l = x^2 + q y^2`
has no integer solution, then `(l, ω - t)` is not principal: a generator would have norm `l`. -/
theorem not_isPrincipal_idealI {l : ℕ} (hl : l.Prime) (hlq : l ≠ q) {t : ℤ}
    (ht : (l : ℤ) ∣ t ^ 2 - t - aOf q)
    (hno : ∀ x y : ℤ, 4 * (l : ℤ) ≠ x ^ 2 + q * y ^ 2) : ¬ (idealI q l t).IsPrincipal := by
  rintro ⟨α, hα⟩
  have h4a := four_aOf h4.out
  have hprod := idealI_mul_map hl hlq ht
  have hα' : idealI q l t = Ideal.span {α} := hα
  have hσ : (idealI q l t).map (starRingEnd (OK q)) = Ideal.span {star α} := by
    rw [hα', Ideal.map_span, Set.image_singleton, starRingEnd_apply]
  have hassoc : Ideal.span {α * star α} = Ideal.span {(l : OK q)} := by
    rw [← Ideal.span_singleton_mul_span_singleton, ← hα', ← hσ, hprod]
  rw [Ideal.span_singleton_eq_span_singleton] at hassoc
  obtain ⟨u, hu⟩ := hassoc
  set n : ℤ := QuadraticAlgebra.norm α with hn
  have hns : algebraMap ℤ (OK q) n = α * star α := algebraMap_norm_eq_mul_star α
  have hnorm := congrArg QuadraticAlgebra.norm hu
  rw [← hns, map_mul, QuadraticAlgebra.norm_algebraMap, QuadraticAlgebra.norm_natCast] at hnorm
  have hunit : IsUnit (QuadraticAlgebra.norm (u : OK q)) :=
    QuadraticAlgebra.isUnit_iff_norm_isUnit.mp u.isUnit
  have hndef : n = α.re * α.re + 1 * α.re * α.im - aOf q * α.im * α.im :=
    QuadraticAlgebra.norm_def α
  have hn4 : 4 * n = (2 * α.re + α.im) ^ 2 + q * α.im ^ 2 := by
    linear_combination 4 * hndef - α.im ^ 2 * h4a
  have hlpos : (0 : ℤ) < (l : ℤ) := by exact_mod_cast hl.pos
  have hnn : 0 ≤ n := by nlinarith [sq_nonneg (2 * α.re + α.im), sq_nonneg α.im,
    (Nat.cast_nonneg q : (0 : ℤ) ≤ q)]
  have hnl : n = (l : ℤ) := by
    rcases Int.isUnit_iff.mp hunit with he | he
    · rw [he, mul_one] at hnorm
      have h0 : (n - (l : ℤ)) * (n + (l : ℤ)) = 0 := by linear_combination hnorm
      rcases mul_eq_zero.mp h0 with h1 | h1
      · linarith
      · linarith
    · rw [he] at hnorm
      nlinarith [sq_nonneg n, pow_pos hlpos 2]
  exact hno (2 * α.re + α.im) α.im (by rw [← hn4, hnl])

/-- For a prime `l` with `4 l < q`, the equation `4 l = x^2 + q y^2` has no solution. -/
lemma no_solution_of_lt {q l : ℕ} (hl : l.Prime) (hlt : 4 * l < q) (x y : ℤ) :
    4 * (l : ℤ) ≠ x ^ 2 + q * y ^ 2 := by
  intro h
  have hlt' : 4 * (l : ℤ) < q := by exact_mod_cast hlt
  have hy0 : y = 0 := by
    by_contra hne
    have h0 : y ^ 2 ≠ 0 := pow_ne_zero 2 hne
    have : 1 ≤ y ^ 2 := by
      have := sq_nonneg y
      omega
    nlinarith [sq_nonneg x, mul_le_mul (le_refl (q : ℤ)) this (by norm_num)
      (by linarith [(Nat.cast_nonneg l : (0 : ℤ) ≤ l)] : (0 : ℤ) ≤ q)]
  rw [hy0] at h
  have h2 : (2 : ℤ) ∣ x := by
    have : (2 : ℤ) ∣ x ^ 2 := ⟨2 * l, by linear_combination -h⟩
    exact Int.prime_two.dvd_of_dvd_pow this
  obtain ⟨x', rfl⟩ := h2
  have h3 : (l : ℤ) = x' * x' := by linarith
  exact (Nat.prime_iff_prime_int.mp hl).not_isSquare ⟨x', h3⟩

end

end Exp7
