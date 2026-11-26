import Mathlib

/-!
Exponent 7: Step 0 ("genus theory"), proved from Mathlib's class group.

Let `D = discr a b = b ^ 2 + 4 * a < 0` be a fundamental discriminant, so that
`QuadraticAlgebra ℤ a b = ℤ[ω]`, `ω ^ 2 = a + b ω`, is the ring of integers of `ℚ(√D)`.

If a prime `l` divides `D` and `4 * l < |D|`, then the ramified prime `P = (l, ω - t)` above `l`
(`t` the double root of `X ^ 2 - b X - a` modulo `l`) satisfies `P ^ 2 = (l)` and is not principal,
so its class has order exactly 2 and `2` divides the exponent of the class group.

Such a prime exists unless `D = -q` with `q ≡ 3 (mod 4)` prime, `D = -4` or `D = -8`. In the last
two cases the ring is norm-Euclidean, so the class group is trivial. Hence a class group of odd
exponent `> 1`, in particular of exponent 7, forces `D = -q` with `q ≡ 3 (mod 4)` prime.
-/

namespace Exp7

open QuadraticAlgebra

open scoped nonZeroDivisors

/-! ### The ring `ℤ[ω]` -/

section Ring

variable {a b : ℤ}

lemma not_isSquare_of_neg {D : ℤ} (h : D < 0) : ¬ IsSquare D := by
  rintro ⟨r, hr⟩
  nlinarith [mul_self_nonneg r]

/-- `ℤ[ω]` is a domain when the discriminant is negative. -/
theorem isDomain_of_discr_neg (hneg : discr a b < 0) : IsDomain (QuadraticAlgebra ℤ a b) :=
  QuadraticAlgebra.Int.isDomain_iff.mpr (not_isSquare_of_neg hneg)

/-- `ℤ[ω]` is a Dedekind domain when the discriminant is fundamental and negative. -/
theorem isDedekindDomain_of_fundamental (hfund : Int.IsFundamentalDiscr (discr a b))
    (hneg : discr a b < 0) : IsDedekindDomain (QuadraticAlgebra ℤ a b) := by
  have : Fact (¬ IsSquare (discr (a : ℚ) (b : ℚ))) := ⟨by
    rw [discr_intCast]
    rintro ⟨r, hr⟩
    have : ((discr a b : ℤ) : ℚ) < 0 := by exact_mod_cast hneg
    nlinarith [mul_self_nonneg r]⟩
  have : IsIntegralClosure (QuadraticAlgebra ℤ a b) ℤ (QuadraticAlgebra ℚ (a : ℚ) (b : ℚ)) :=
    QuadraticAlgebra.Int.isIntegralClosure_iff.mpr hfund
  have := isDomain_of_discr_neg hneg
  exact IsIntegralClosure.isDedekindDomain ℤ ℚ (QuadraticAlgebra ℚ (a : ℚ) (b : ℚ))
    (QuadraticAlgebra ℤ a b)

lemma omega_sub_mul_self (t : ℤ) :
    (ω - (t : QuadraticAlgebra ℤ a b)) * (ω - (t : QuadraticAlgebra ℤ a b)) =
      ((b - 2 * t : ℤ) : QuadraticAlgebra ℤ a b) * (ω - (t : QuadraticAlgebra ℤ a b)) -
        ((t ^ 2 - b * t - a : ℤ) : QuadraticAlgebra ℤ a b) := by
  ext <;> simp [sq] <;> ring

/-- The ideal `(l, ω - t)`. -/
noncomputable def ramIdeal (a b : ℤ) (l : ℕ) (t : ℤ) : Ideal (QuadraticAlgebra ℤ a b) :=
  Ideal.span {(l : QuadraticAlgebra ℤ a b), ω - (t : QuadraticAlgebra ℤ a b)}

lemma natCast_ne_zero' {l : ℕ} (hl : l ≠ 0) : (l : QuadraticAlgebra ℤ a b) ≠ 0 := by
  intro h0
  have h := congrArg QuadraticAlgebra.re h0
  exact hl (by simpa using h)

lemma ramIdeal_ne_bot {l : ℕ} (hl : l ≠ 0) (t : ℤ) : ramIdeal a b l t ≠ ⊥ := by
  intro hbot
  have hmem : (l : QuadraticAlgebra ℤ a b) ∈ ramIdeal a b l t := Ideal.subset_span (by simp)
  rw [hbot] at hmem
  exact natCast_ne_zero' (a := a) (b := b) hl (by simpa using hmem)

/-- If `t` is a double root of `X ^ 2 - b X - a` modulo the prime `l`, but not modulo `l ^ 2`,
then `(l, ω - t) ^ 2 = (l)`. -/
lemma ramIdeal_mul_self {l : ℕ} (hl : l.Prime) {t : ℤ} (h1 : (l : ℤ) ∣ t ^ 2 - b * t - a)
    (h2 : (l : ℤ) ∣ b - 2 * t) (h3 : ¬ (l : ℤ) ^ 2 ∣ t ^ 2 - b * t - a) :
    ramIdeal a b l t * ramIdeal a b l t = Ideal.span {(l : QuadraticAlgebra ℤ a b)} := by
  obtain ⟨m, hm⟩ := h1
  obtain ⟨c, hc⟩ := h2
  have hsq := omega_sub_mul_self (a := a) (b := b) t
  rw [hm, hc] at hsq
  push_cast at hsq
  have hcop : IsCoprime (l : ℤ) m := by
    rw [(Nat.prime_iff_prime_int.mp hl).coprime_iff_not_dvd]
    rintro ⟨m', rfl⟩
    exact h3 ⟨m', by rw [hm]; ring⟩
  obtain ⟨u, v, huv⟩ := hcop
  have huv' : ((u * l + v * m : ℤ) : QuadraticAlgebra ℤ a b) = 1 := by rw [huv]; simp
  push_cast at huv'
  unfold ramIdeal
  rw [Ideal.span_pair_mul_span_pair]
  apply le_antisymm
  · rw [Ideal.span_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rw [SetLike.mem_coe, Ideal.mem_span_singleton]
    rcases hx with rfl | rfl | rfl | rfl
    · exact dvd_mul_right _ _
    · exact dvd_mul_right _ _
    · exact dvd_mul_left _ _
    · rw [hsq]
      exact ⟨(c : QuadraticAlgebra ℤ a b) * (ω - (t : QuadraticAlgebra ℤ a b)) -
        (m : QuadraticAlgebra ℤ a b), by ring⟩
  · rw [Ideal.span_singleton_le_iff_mem]
    have key : (l : QuadraticAlgebra ℤ a b) =
        (u : QuadraticAlgebra ℤ a b) *
          ((l : QuadraticAlgebra ℤ a b) * (l : QuadraticAlgebra ℤ a b)) +
        ((v : QuadraticAlgebra ℤ a b) * (c : QuadraticAlgebra ℤ a b)) *
          ((l : QuadraticAlgebra ℤ a b) * (ω - (t : QuadraticAlgebra ℤ a b))) +
        (-(v : QuadraticAlgebra ℤ a b)) *
          ((ω - (t : QuadraticAlgebra ℤ a b)) * (ω - (t : QuadraticAlgebra ℤ a b))) := by
      linear_combination (-(l : QuadraticAlgebra ℤ a b)) * huv' +
        (v : QuadraticAlgebra ℤ a b) * hsq
    have aux : ∀ I : Ideal (QuadraticAlgebra ℤ a b),
        (l : QuadraticAlgebra ℤ a b) * (l : QuadraticAlgebra ℤ a b) ∈ I →
        (l : QuadraticAlgebra ℤ a b) * (ω - (t : QuadraticAlgebra ℤ a b)) ∈ I →
        (ω - (t : QuadraticAlgebra ℤ a b)) * (ω - (t : QuadraticAlgebra ℤ a b)) ∈ I →
        (l : QuadraticAlgebra ℤ a b) ∈ I := by
      intro I h1 h2 h3
      rw [key]
      exact Ideal.add_mem _ (Ideal.add_mem _ (Ideal.mul_mem_left _ _ h1)
        (Ideal.mul_mem_left _ _ h2)) (Ideal.mul_mem_left _ _ h3)
    exact aux _ (Ideal.subset_span (by simp)) (Ideal.subset_span (by simp))
      (Ideal.subset_span (by simp))

/-- If `4 * l < |D|` then an ideal of square `(l)` is not principal: a generator would have norm
`l`, and `x ^ 2 + b x y - a y ^ 2 = l` has no solution. -/
lemma ramIdeal_not_isPrincipal [IsDomain (QuadraticAlgebra ℤ a b)] (hneg : discr a b < 0)
    {l : ℕ} (hl : l.Prime) (hlt : 4 * (l : ℤ) < -discr a b) {t : ℤ}
    (hmul : ramIdeal a b l t * ramIdeal a b l t = Ideal.span {(l : QuadraticAlgebra ℤ a b)}) :
    ¬ (ramIdeal a b l t).IsPrincipal := by
  rintro ⟨β, hβ⟩
  have hβ' : ramIdeal a b l t = Ideal.span {β} := hβ
  rw [hβ', Ideal.span_singleton_mul_span_singleton, Ideal.span_singleton_eq_span_singleton] at hmul
  obtain ⟨u, hu⟩ := hmul
  have hnorm := congrArg QuadraticAlgebra.norm hu
  rw [map_mul, map_mul, QuadraticAlgebra.norm_natCast] at hnorm
  have hunit : IsUnit (QuadraticAlgebra.norm (u : QuadraticAlgebra ℤ a b)) :=
    QuadraticAlgebra.isUnit_iff_norm_isUnit.mp u.isUnit
  have h4 := four_mul_norm_eq β
  rw [trace_def] at h4
  set n : ℤ := QuadraticAlgebra.norm β with hn
  have hlpos : (0 : ℤ) < l := by exact_mod_cast hl.pos
  have hnn : 0 ≤ n := by nlinarith [sq_nonneg (2 * β.re + b * β.im), sq_nonneg β.im]
  have hnl : n = l := by
    rcases Int.isUnit_iff.mp hunit with he | he
    · rw [he, mul_one] at hnorm
      have h0 : (n - (l : ℤ)) * (n + (l : ℤ)) = 0 := by linear_combination hnorm
      rcases mul_eq_zero.mp h0 with h1 | h1
      · linarith
      · linarith
    · rw [he] at hnorm
      nlinarith [mul_self_nonneg n, mul_pos hlpos hlpos]
  rw [hnl] at h4
  by_cases hy : β.im = 0
  · rw [hy] at h4
    have hsq : (l : ℤ) = β.re * β.re := by nlinarith [h4]
    exact (Nat.prime_iff_prime_int.mp hl).not_isSquare ⟨_, hsq⟩
  · have h1 : 1 ≤ β.im ^ 2 := by
      rcases lt_or_gt_of_ne hy with h | h <;> nlinarith
    nlinarith [sq_nonneg (2 * β.re + b * β.im)]

/-! ### Small discriminants: `ℤ[ω]` is norm-Euclidean for `-12 < D < 0` -/

lemma norm_nonneg_of_discr_neg (hneg : discr a b < 0) (z : QuadraticAlgebra ℤ a b) :
    0 ≤ QuadraticAlgebra.norm z := by
  have h4 := four_mul_norm_eq z
  nlinarith [sq_nonneg (trace z), sq_nonneg z.im]

lemma eq_zero_of_norm_eq_zero (hneg : discr a b < 0) {z : QuadraticAlgebra ℤ a b}
    (h : QuadraticAlgebra.norm z = 0) : z = 0 := by
  have h4 := four_mul_norm_eq z
  rw [h, trace_def] at h4
  have him : z.im = 0 := by
    by_contra hne
    have : 0 < z.im ^ 2 := by positivity
    nlinarith [sq_nonneg (2 * z.re + b * z.im)]
  have hre : z.re = 0 := by
    rw [him] at h4
    have : z.re ^ 2 = 0 := by nlinarith
    exact pow_eq_zero_iff (by norm_num) |>.mp this
  ext <;> simp [hre, him]

/-- Division with remainder: for `-12 < D < 0` the norm is a Euclidean function on `ℤ[ω]`. -/
lemma exists_norm_sub_mul_lt (hneg : discr a b < 0) (hsmall : -12 < discr a b)
    (x y : QuadraticAlgebra ℤ a b) (hy : y ≠ 0) :
    ∃ q : QuadraticAlgebra ℤ a b, QuadraticAlgebra.norm (x - q * y) < QuadraticAlgebra.norm y := by
  set n : ℤ := QuadraticAlgebra.norm y with hn
  have hnpos : 0 < n :=
    lt_of_le_of_ne (norm_nonneg_of_discr_neg hneg y) fun h ↦
      hy (eq_zero_of_norm_eq_zero hneg h.symm)
  have h2n : (0 : ℤ) < 2 * n := by linarith
  set c : ℤ := (x * star y).re with hc
  set d : ℤ := (x * star y).im with hd
  -- `f` is `d / n` rounded, `e` is `(2 c + b (d - n f)) / (2 n)` rounded
  set f : ℤ := (2 * d + n) / (2 * n) with hf
  have hf1 := Int.emod_add_mul_ediv (2 * d + n) (2 * n)
  have hf2 := Int.emod_nonneg (2 * d + n) h2n.ne'
  have hf3 := Int.emod_lt_of_pos (2 * d + n) h2n
  rw [← hf] at hf1
  set e : ℤ := (2 * c + b * (d - n * f) + n) / (2 * n) with he
  have he1 := Int.emod_add_mul_ediv (2 * c + b * (d - n * f) + n) (2 * n)
  have he2 := Int.emod_nonneg (2 * c + b * (d - n * f) + n) h2n.ne'
  have he3 := Int.emod_lt_of_pos (2 * c + b * (d - n * f) + n) h2n
  rw [← he] at he1
  refine ⟨⟨e, f⟩, ?_⟩
  set r : QuadraticAlgebra ℤ a b := x - ⟨e, f⟩ * y with hr
  have hns : algebraMap ℤ (QuadraticAlgebra ℤ a b) n = y * star y := algebraMap_norm_eq_mul_star y
  have hw : r * star y = x * star y - ⟨e, f⟩ * algebraMap ℤ (QuadraticAlgebra ℤ a b) n := by
    rw [hns, hr]; ring
  have hre : (r * star y).re = c - n * e := by
    rw [hw]; simp [hc]; ring
  have him : (r * star y).im = d - n * f := by
    rw [hw]; simp [hd]; ring
  have h4 := four_mul_norm_eq (r * star y)
  rw [trace_def, hre, him, map_mul, QuadraticAlgebra.norm_star, ← hn] at h4
  -- `T = 2 (c - n e) + b (d - n f)` and `S = 2 (d - n f)` both lie in `[-n, n]`
  have hT : (2 * (c - n * e) + b * (d - n * f)) ^ 2 ≤ n ^ 2 := sq_le_sq' (by linarith) (by linarith)
  have hS : (2 * (d - n * f)) ^ 2 ≤ n ^ 2 := sq_le_sq' (by linarith) (by linarith)
  have h1 : -discr a b * (2 * (d - n * f)) ^ 2 ≤ -discr a b * n ^ 2 :=
    mul_le_mul_of_nonneg_left hS (by linarith)
  have h2 : -discr a b * n ^ 2 ≤ 11 * n ^ 2 :=
    mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg n)
  have hlt : QuadraticAlgebra.norm r * n < n * n := by nlinarith [pow_pos hnpos 2]
  exact lt_of_mul_lt_mul_right hlt hnpos.le

/-- For `-12 < D < 0`, i.e. `D ∈ {-3, -4, -7, -8, -11}`, the ring `ℤ[ω]` is a principal ideal
ring. -/
theorem isPrincipalIdealRing_of_discr_gt (hneg : discr a b < 0) (hsmall : -12 < discr a b) :
    IsPrincipalIdealRing (QuadraticAlgebra ℤ a b) := by
  classical
  refine ⟨fun I ↦ ?_⟩
  by_cases hI : I = ⊥
  · rw [hI]; exact bot_isPrincipal
  obtain ⟨x0, hx0, hx0ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  have hP : ∃ k : ℕ, ∃ β ∈ I, β ≠ 0 ∧ (QuadraticAlgebra.norm β).natAbs = k :=
    ⟨_, x0, hx0, hx0ne, rfl⟩
  obtain ⟨β, hβI, hβ0, hβn⟩ := Nat.find_spec hP
  refine ⟨⟨β, le_antisymm ?_ ?_⟩⟩
  · intro x hx
    obtain ⟨q, hq⟩ := exists_norm_sub_mul_lt hneg hsmall x β hβ0
    by_cases hr : x - q * β = 0
    · exact Ideal.mem_span_singleton.mpr ⟨q, by linear_combination hr⟩
    · exfalso
      have hrI : x - q * β ∈ I := I.sub_mem hx (I.mul_mem_left q hβI)
      have h0 := norm_nonneg_of_discr_neg hneg (x - q * β)
      refine Nat.find_min hP (m := (QuadraticAlgebra.norm (x - q * β)).natAbs) ?_
        ⟨_, hrI, hr, rfl⟩
      rw [← hβn]
      omega
  · exact (Ideal.span_singleton_le_iff_mem I).mpr hβI

end Ring

/-! ### Arithmetic of fundamental discriminants -/

section Arithmetic

/-- A prime `l` dividing a fundamental discriminant `b ^ 2 + 4 * a` gives a root `t` of
`X ^ 2 - b X - a` modulo `l` that is a double root, but not a root modulo `l ^ 2`. -/
lemma exists_double_root {a b : ℤ} (hfund : Int.IsFundamentalDiscr (discr a b)) {l : ℕ}
    (hl : l.Prime) (hd : (l : ℤ) ∣ discr a b) :
    ∃ t : ℤ, (l : ℤ) ∣ t ^ 2 - b * t - a ∧ (l : ℤ) ∣ b - 2 * t ∧
      ¬ (l : ℤ) ^ 2 ∣ t ^ 2 - b * t - a := by
  have hD : discr a b = b ^ 2 + 4 * a := rfl
  rcases hl.eq_two_or_odd' with rfl | hodd
  · -- `l = 2`: `b = 2k`, `D = 4 (k ^ 2 + a)` with `k ^ 2 + a ≡ 2, 3 (mod 4)`; take `t = a`
    have hb : (2 : ℤ) ∣ b := by
      rw [hD] at hd
      have h2 : (2 : ℤ) ∣ b ^ 2 :=
        (Int.dvd_add_left (show (2 : ℤ) ∣ 4 * a from ⟨2 * a, by ring⟩)).mp (by exact_mod_cast hd)
      exact Int.prime_two.dvd_of_dvd_pow h2
    obtain ⟨k, rfl⟩ := hb
    have hx := hfund.2.1 (k ^ 2 + a) (by rw [hD]; ring)
    refine ⟨a, ?_, ?_, ?_⟩
    · obtain ⟨c, hc⟩ := Int.even_mul_pred_self a
      exact ⟨c - k * a, by push_cast; linear_combination hc⟩
    · exact ⟨k - a, by push_cast; ring⟩
    · rintro ⟨e, he⟩
      push_cast at he
      rcases Int.emod_two_eq_zero_or_one (a - k) with h | h
      · obtain ⟨j, hj⟩ : ∃ j, a - k = 2 * j := ⟨(a - k) / 2, by omega⟩
        exact hx.1 ⟨j ^ 2 - e, by linear_combination (a - k + 2 * j) * hj - he⟩
      · obtain ⟨j, hj⟩ : ∃ j, a - k = 2 * j + 1 := ⟨(a - k) / 2, by omega⟩
        have h1 : k ^ 2 + a = 4 * (j ^ 2 + j - e) + 1 := by
          linear_combination (a - k + 2 * j + 1) * hj - he
        apply hx.2
        rw [h1]
        omega
  · -- `l` odd: `t = b (l + 1) / 2`, and `4 (t ^ 2 - b t - a) = (2 t - b) ^ 2 - D`
    have hl2 : (l : ℤ) % 2 = 1 := by exact_mod_cast Nat.odd_iff.mp hodd
    have hlp := Nat.prime_iff_prime_int.mp hl
    obtain ⟨s, hs⟩ : ∃ s : ℤ, 2 * s = l + 1 := ⟨((l : ℤ) + 1) / 2, by omega⟩
    have ht : 2 * (b * s) - b = b * l := by linear_combination b * hs
    have h4 : 4 * ((b * s) ^ 2 - b * (b * s) - a) = (2 * (b * s) - b) ^ 2 - discr a b := by
      rw [hD]; ring
    refine ⟨b * s, ?_, ?_, ?_⟩
    · have h : (l : ℤ) ∣ 4 * ((b * s) ^ 2 - b * (b * s) - a) := by
        rw [h4, ht]
        exact dvd_sub ⟨b ^ 2 * l, by ring⟩ hd
      rcases hlp.dvd_or_dvd h with h' | h'
      · exfalso
        have h2 : (l : ℤ) ∣ 2 := hlp.dvd_of_dvd_pow (show (l : ℤ) ∣ 2 ^ 2 by simpa using h')
        have hle := Int.le_of_dvd (by norm_num) h2
        have := hl.two_le
        omega
      · exact h'
    · exact ⟨-b, by linear_combination -ht⟩
    · intro h
      apply hfund.2.2 l hl hodd
      have h' : (l : ℤ) ^ 2 ∣ (2 * (b * s) - b) ^ 2 - 4 * ((b * s) ^ 2 - b * (b * s) - a) :=
        dvd_sub (by rw [ht]; exact ⟨b ^ 2, by ring⟩) (Dvd.dvd.mul_left h 4)
      rwa [h4, sub_sub_cancel] at h'

/-- A negative fundamental discriminant is `-q` with `q ≡ 3 (mod 4)` prime, or `-4`, or `-8`, or
it has a prime divisor `l` with `4 * l < |D|`. -/
lemma fundamentalDiscr_neg_cases {D : ℤ} (hfund : Int.IsFundamentalDiscr D) (hneg : D < 0) :
    (∃ q : ℕ, q.Prime ∧ q % 4 = 3 ∧ D = -(q : ℤ)) ∨ D = -4 ∨ D = -8 ∨
      ∃ l : ℕ, l.Prime ∧ (l : ℤ) ∣ D ∧ 4 * (l : ℤ) < -D := by
  rcases Int.isFundamentalDiscr_iff_squarefree.mp hfund with ⟨h1, hsq⟩ | ⟨h0, -, h23⟩
  · -- `D ≡ 1 (mod 4)` squarefree
    obtain ⟨n, hn⟩ : ∃ n : ℕ, (n : ℤ) = -D := ⟨D.natAbs, by omega⟩
    have hn4 : n % 4 = 3 := by omega
    have hnsq : Squarefree n := by
      have : n = D.natAbs := by omega
      rw [this]
      exact Int.squarefree_natAbs.mpr hsq
    by_cases hp : n.Prime
    · exact Or.inl ⟨n, hp, hn4, by omega⟩
    · right; right; right
      have hn1 : n ≠ 1 := by omega
      have hl : n.minFac.Prime := Nat.minFac_prime hn1
      obtain ⟨m, hm⟩ := Nat.minFac_dvd n
      set l := n.minFac with hldef
      have hm1 : m ≠ 1 := by
        rintro rfl
        rw [mul_one] at hm
        exact hp (hm ▸ hl)
      have hm0 : m ≠ 0 := by
        rintro rfl
        omega
      have hlm : l ≤ m := Nat.minFac_le_of_dvd (by omega) ⟨l, by rw [hm]; ring⟩
      have hne : l ≠ m := by
        intro h
        have hu : IsUnit l := hnsq l (Dvd.intro 1 (by rw [mul_one, hm, ← h]))
        exact hl.one_lt.ne' (Nat.isUnit_iff.mp hu)
      have hodd : Odd (l * m) := by
        rw [← hm, Nat.odd_iff]
        omega
      obtain ⟨hlo, hmo⟩ := Nat.odd_mul.mp hodd
      rw [Nat.odd_iff] at hlo hmo
      have hl2 := hl.two_le
      have hm5 : l + 2 ≤ m := by omega
      refine ⟨l, hl, ⟨-(m : ℤ), ?_⟩, ?_⟩
      · have : (n : ℤ) = (l : ℤ) * m := by exact_mod_cast hm
        linear_combination hn - this
      · rw [← hn]
        have h5 : 5 ≤ m := by omega
        have : 4 * l < n := by
          rw [hm]
          nlinarith [Nat.mul_le_mul_left l h5]
        exact_mod_cast this
  · -- `D = 4 d`, `d ≡ 2, 3 (mod 4)`
    by_cases h8 : 8 < -D
    · right; right; right
      exact ⟨2, Nat.prime_two, by norm_num; omega, by norm_num; omega⟩
    · right
      omega

end Arithmetic

/-! ### The class group -/

section ClassGroup

variable {a b : ℤ}

/-- **Genus theory, the part needed.** If a prime `l` divides the negative fundamental
discriminant `D` and `4 * l < |D|`, the class of the ramified prime above `l` has order 2, so the
exponent of the class group is even. -/
theorem two_dvd_exponent_of_ramified [IsDomain (QuadraticAlgebra ℤ a b)]
    (hfund : Int.IsFundamentalDiscr (discr a b)) (hneg : discr a b < 0) {l : ℕ} (hl : l.Prime)
    (hd : (l : ℤ) ∣ discr a b) (hlt : 4 * (l : ℤ) < -discr a b) :
    2 ∣ Monoid.exponent (ClassGroup (QuadraticAlgebra ℤ a b)) := by
  have := isDedekindDomain_of_fundamental hfund hneg
  obtain ⟨t, h1, h2, h3⟩ := exists_double_root hfund hl hd
  have hmul := ramIdeal_mul_self hl h1 h2 h3
  have hnp := ramIdeal_not_isPrincipal hneg hl hlt hmul
  have hImem : ramIdeal a b l t ∈ (Ideal (QuadraticAlgebra ℤ a b))⁰ :=
    mem_nonZeroDivisors_of_ne_zero (ramIdeal_ne_bot hl.ne_zero t)
  have hc1 : ClassGroup.mk0 ⟨ramIdeal a b l t, hImem⟩ ≠ 1 := fun h ↦
    hnp ((ClassGroup.mk0_eq_one_iff hImem).mp h)
  have hc2 : ClassGroup.mk0 ⟨ramIdeal a b l t, hImem⟩ ^ 2 = 1 := by
    have hsq : ramIdeal a b l t ^ 2 ∈ (Ideal (QuadraticAlgebra ℤ a b))⁰ := pow_mem hImem 2
    have e : (⟨ramIdeal a b l t, hImem⟩ : (Ideal (QuadraticAlgebra ℤ a b))⁰) ^ 2 =
        ⟨ramIdeal a b l t ^ 2, hsq⟩ := Subtype.ext (by simp)
    rw [← map_pow, e, ClassGroup.mk0_eq_one_iff hsq, pow_two, hmul]
    exact ⟨⟨_, rfl⟩⟩
  have := Fact.mk Nat.prime_two
  rw [← orderOf_eq_prime hc2 hc1]
  exact Monoid.order_dvd_exponent _

/-- For `-12 < D < 0` the class group is trivial, so its exponent is 1. -/
theorem exponent_classGroup_eq_one_of_discr_gt [IsDomain (QuadraticAlgebra ℤ a b)]
    (hneg : discr a b < 0) (hsmall : -12 < discr a b) :
    Monoid.exponent (ClassGroup (QuadraticAlgebra ℤ a b)) = 1 := by
  have := isPrincipalIdealRing_of_discr_gt hneg hsmall
  have hcard := card_classGroup_eq_one (R := QuadraticAlgebra ℤ a b)
  have : Subsingleton (ClassGroup (QuadraticAlgebra ℤ a b)) :=
    Fintype.card_le_one_iff_subsingleton.mp hcard.le
  exact Monoid.exp_eq_one_iff.mpr this

/-- **Step 0, general form.** If the class group of the imaginary quadratic order of fundamental
discriminant `D < 0` has odd exponent different from 1, then `D = -q` with `q ≡ 3 (mod 4)`
prime. -/
theorem prime_discr_of_odd_exponent (a b : ℤ)
    (hfund : Int.IsFundamentalDiscr (discr a b)) (hneg : discr a b < 0)
    [IsDomain (QuadraticAlgebra ℤ a b)]
    (hodd : ¬ 2 ∣ Monoid.exponent (ClassGroup (QuadraticAlgebra ℤ a b)))
    (hne : Monoid.exponent (ClassGroup (QuadraticAlgebra ℤ a b)) ≠ 1) :
    ∃ q : ℕ, q.Prime ∧ q % 4 = 3 ∧ discr a b = -(q : ℤ) := by
  rcases fundamentalDiscr_neg_cases hfund hneg with h | h | h | ⟨l, hl, hd, hlt⟩
  · exact h
  · exact absurd (exponent_classGroup_eq_one_of_discr_gt hneg (by omega)) hne
  · exact absurd (exponent_classGroup_eq_one_of_discr_gt hneg (by omega)) hne
  · exact absurd (two_dvd_exponent_of_ramified hfund hneg hl hd hlt) hodd

/-- **Step 0, strong form.** If the class group of the imaginary quadratic order of fundamental
discriminant `D < 0` has exponent 7, then `D = -q` with `q ≡ 3 (mod 4)` prime. -/
theorem prime_discr_of_exponent_seven' (a b : ℤ)
    (hfund : Int.IsFundamentalDiscr (discr a b)) (hneg : discr a b < 0)
    [IsDomain (QuadraticAlgebra ℤ a b)]
    (h : Monoid.exponent (ClassGroup (QuadraticAlgebra ℤ a b)) = 7) :
    ∃ q : ℕ, q.Prime ∧ q % 4 = 3 ∧ discr a b = -(q : ℤ) :=
  prime_discr_of_odd_exponent a b hfund hneg (by rw [h]; norm_num) (by rw [h]; norm_num)

/-- **Step 0.** If the class group of the imaginary quadratic order of fundamental discriminant
`D < 0` has exponent 7, then `D = -q` with `q ≡ 3 (mod 4)` prime, or `D = -4`, or `D = -8`.
(The last two cases do not occur: see `prime_discr_of_exponent_seven'`.) -/
theorem prime_discr_of_exponent_seven (a b : ℤ)
    (hfund : Int.IsFundamentalDiscr (QuadraticAlgebra.discr a b))
    (hneg : QuadraticAlgebra.discr a b < 0)
    [IsDomain (QuadraticAlgebra ℤ a b)]
    (h : Monoid.exponent (ClassGroup (QuadraticAlgebra ℤ a b)) = 7) :
    (∃ q : ℕ, q.Prime ∧ q % 4 = 3 ∧ QuadraticAlgebra.discr a b = -(q : ℤ)) ∨
      QuadraticAlgebra.discr a b = -4 ∨ QuadraticAlgebra.discr a b = -8 :=
  Or.inl (prime_discr_of_exponent_seven' a b hfund hneg h)

end ClassGroup

end Exp7
