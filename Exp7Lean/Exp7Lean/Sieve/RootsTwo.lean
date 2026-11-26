import Mathlib
import Exp7Lean.Sieve.RootsBasic

/-!
# Square roots of `4 * u` (`u` odd) modulo powers of two

* `sq_modEq_four_mul_two_pow` : `x ^ 2 ≡ 4 * u (mod 2 ^ (m + 2))` iff `x = 2 * s` with
  `s ^ 2 ≡ u (mod 2 ^ m)`.
* `not_sq_two_pow_of_mod_eight`, `not_sq_two_pow_of_mod_four` : no roots of an odd `u`
  unless `u ≡ 1 (mod 8)` (`m ≥ 3`), resp. `u ≡ 1 (mod 4)` (`m ≥ 2`).
* `sq_modEq_two_pow` : any two roots of an odd `u` modulo `2 ^ m` agree up to sign
  modulo `2 ^ (m - 1)`.
* `complete_two_pow` : the explicit list `±s₀, ±s₀ + 2 ^ (m - 1)` is complete.
* `twoRootsOdd`, `twoRootsOddOk`, `complete_twoRootsOdd` : kernel-checkable certificate form.
* `liftTwo`, `Complete.liftTwo` : passage from `s` modulo `2 ^ m` to `x = 2 * s` modulo
  `2 ^ (m + 2)`.
-/

namespace Exp7.Roots

theorem odd_of_sq_modEq_odd {m u s : ℕ} (hm : 1 ≤ m) (hu : u % 2 = 1)
    (hs : s ^ 2 ≡ u [MOD 2 ^ m]) : s % 2 = 1 := by
  have h2 : s ^ 2 ≡ u [MOD 2] := hs.of_dvd (dvd_pow_self 2 (by omega))
  have h3 : s ^ 2 % 2 = 1 := by rw [← hu]; exact h2
  rcases Nat.mod_two_eq_zero_or_one s with h | h
  · rw [Nat.pow_mod, h] at h3; simp at h3
  · exact h

/-- **Reduction to an odd number.** `x² ≡ 4u (mod 2^(m+2))` iff `x = 2s` with
`s² ≡ u (mod 2^m)`. -/
theorem sq_modEq_four_mul_two_pow (u m x : ℕ) :
    x ^ 2 ≡ 4 * u [MOD 2 ^ (m + 2)] ↔ ∃ s, x = 2 * s ∧ s ^ 2 ≡ u [MOD 2 ^ m] := by
  have e4 : 2 ^ (m + 2) = 4 * 2 ^ m := by rw [pow_add]; ring
  constructor
  · intro h
    have h2 : x ^ 2 ≡ 4 * u [MOD 2] := h.of_dvd (dvd_pow_self 2 (by omega))
    have h3 : x ^ 2 % 2 = 0 := by
      have : 4 * u % 2 = 0 := by omega
      rw [← this]; exact h2
    have hx : x % 2 = 0 := by
      rcases Nat.mod_two_eq_zero_or_one x with h | h
      · exact h
      · rw [Nat.pow_mod, h] at h3; simp at h3
    refine ⟨x / 2, by omega, ?_⟩
    have hx2 : x = 2 * (x / 2) := by omega
    rw [hx2, e4] at h
    have e : (2 * (x / 2)) ^ 2 = 4 * (x / 2) ^ 2 := by ring
    rw [e] at h
    exact Nat.ModEq.mul_left_cancel' (by norm_num) h
  · rintro ⟨s, rfl, hs⟩
    have e : (2 * s) ^ 2 = 4 * s ^ 2 := by ring
    rw [e, e4]
    exact hs.mul_left' 4

private theorem sq_mod_eight_of_odd {s : ℕ} (hs : s % 2 = 1) : s ^ 2 % 8 = 1 := by
  have h8 : s % 8 = 1 ∨ s % 8 = 3 ∨ s % 8 = 5 ∨ s % 8 = 7 := by omega
  rw [Nat.pow_mod]
  rcases h8 with h | h | h | h <;> rw [h]

/-- No square roots of an odd `u` modulo `2 ^ m`, `m ≥ 3`, unless `u ≡ 1 (mod 8)`. -/
theorem not_sq_two_pow_of_mod_eight {u m : ℕ} (hu : u % 2 = 1) (hm : 3 ≤ m) (h8 : u % 8 ≠ 1)
    (s : ℕ) : ¬ s ^ 2 ≡ u [MOD 2 ^ m] := by
  intro hs
  have hodd := odd_of_sq_modEq_odd (by omega) hu hs
  have h : s ^ 2 ≡ u [MOD 2 ^ 3] := hs.of_dvd (pow_dvd_pow 2 hm)
  have h' : s ^ 2 % 8 = u % 8 := h
  rw [sq_mod_eight_of_odd hodd] at h'
  exact h8 h'.symm

/-- No square roots of an odd `u` modulo `2 ^ m`, `m ≥ 2`, unless `u ≡ 1 (mod 4)`. -/
theorem not_sq_two_pow_of_mod_four {u m : ℕ} (hu : u % 2 = 1) (hm : 2 ≤ m) (h4 : u % 4 ≠ 1)
    (s : ℕ) : ¬ s ^ 2 ≡ u [MOD 2 ^ m] := by
  intro hs
  have hodd := odd_of_sq_modEq_odd (by omega) hu hs
  have h : s ^ 2 ≡ u [MOD 2 ^ 2] := hs.of_dvd (pow_dvd_pow 2 hm)
  have h' : s ^ 2 % 4 = u % 4 := h
  have h8 := sq_mod_eight_of_odd hodd
  omega

/-- **Powers of two (integers).** If `u` is odd, `m ≥ 1`, and `s₀`, `s` are both square roots
of `u` modulo `2 ^ m`, then `s ≡ ±s₀ (mod 2 ^ (m - 1))`; hence
`s ≡ ±s₀` or `±s₀ + 2 ^ (m - 1) (mod 2 ^ m)`. -/
theorem sq_modEq_two_pow {m : ℕ} (hm : 1 ≤ m) {u s₀ s : ℤ} (hu : ¬ (2 : ℤ) ∣ u)
    (h₀ : s₀ ^ 2 ≡ u [ZMOD 2 ^ m]) (hs : s ^ 2 ≡ u [ZMOD 2 ^ m]) :
    s ≡ s₀ [ZMOD 2 ^ (m - 1)] ∨ s ≡ -s₀ [ZMOD 2 ^ (m - 1)] := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have h2m : (2 : ℤ) ∣ 2 ^ (n + 1) := dvd_pow_self _ (by omega)
  have odd_of : ∀ t : ℤ, t ^ 2 ≡ u [ZMOD 2 ^ (n + 1)] → ¬ (2 : ℤ) ∣ t := by
    intro t ht h2
    have h3 : (2 : ℤ) ∣ u - t ^ 2 := h2m.trans ht.dvd
    have h4 := dvd_add h3 (dvd_pow h2 two_ne_zero)
    have e : u - t ^ 2 + t ^ 2 = u := by ring
    rw [e] at h4
    exact hu h4
  have hs1 := odd_of s hs
  have hs0 := odd_of s₀ h₀
  have h1 : (2 : ℤ) ^ (n + 1) ∣ (s - s₀) * (s + s₀) := by
    have h := (h₀.trans hs.symm).dvd
    have e : (s - s₀) * (s + s₀) = s ^ 2 - s₀ ^ 2 := by ring
    rw [e]; exact h
  obtain ⟨A, hA⟩ : ∃ A, s - s₀ = 2 * A := ⟨(s - s₀) / 2, by omega⟩
  obtain ⟨B, hB⟩ : ∃ B, s + s₀ = 2 * B := ⟨(s + s₀) / 2, by omega⟩
  have hAB : ¬ (2 : ℤ) ∣ A ∨ ¬ (2 : ℤ) ∣ B := by omega
  have h3 : (2 : ℤ) ^ n ∣ 2 * A * B := by
    have e1 : (s - s₀) * (s + s₀) = 2 * (2 * A * B) := by rw [hA, hB]; ring
    have e2 : (2 : ℤ) ^ (n + 1) = 2 * 2 ^ n := by rw [pow_succ]; ring
    rw [e1, e2] at h1
    exact (mul_dvd_mul_iff_left (two_ne_zero)).mp h1
  rcases hAB with hA2 | hB2
  · right
    have e : 2 * A * B = 2 * B * A := by ring
    rw [e] at h3
    have h4 := Int.prime_two.pow_dvd_of_dvd_mul_right n hA2 h3
    rw [← hB] at h4
    have e' : s + s₀ = s - (-s₀) := by ring
    rw [e'] at h4
    exact (Int.modEq_iff_dvd.mpr h4).symm
  · left
    have h4 := Int.prime_two.pow_dvd_of_dvd_mul_right n hB2 h3
    rw [← hA] at h4
    exact (Int.modEq_iff_dvd.mpr h4).symm

/-- A congruence modulo `H` leaves two possibilities modulo `2 * H`. -/
theorem mod_two_mul_cases {H x c : ℕ} (hH : 0 < H) (h : x ≡ c [MOD H]) :
    x % (2 * H) = c % (2 * H) ∨ x % (2 * H) = (c + H) % (2 * H) := by
  have h' : x % H = c % H := h
  rw [mul_comm 2 H, Nat.mod_mul, Nat.mod_mul (x := c), Nat.mod_mul (x := c + H),
    Nat.add_mod_right, Nat.add_div_right _ hH, h']
  have e : (c / H + 1) % 2 = 1 - c / H % 2 := by omega
  rw [e]
  rcases Nat.mod_two_eq_zero_or_one (x / H) with hx | hx <;>
    rcases Nat.mod_two_eq_zero_or_one (c / H) with hc | hc <;> rw [hx, hc] <;> simp

/-- The four candidates `s₀, -s₀, s₀ + 2^(m-1), -s₀ + 2^(m-1)` reduced modulo `2 ^ m`. -/
def twoPowRoots (m s₀ : ℕ) : List ℕ :=
  [s₀ % 2 ^ m, 2 ^ m - s₀ % 2 ^ m, (s₀ % 2 ^ m + 2 ^ (m - 1)) % 2 ^ m,
    (2 ^ m - s₀ % 2 ^ m + 2 ^ (m - 1)) % 2 ^ m]

/-- **Powers of two (naturals, list form).** For odd `u`, `m ≥ 1` and one root `s₀`, the list
`twoPowRoots m s₀` contains every root of `u` modulo `2 ^ m`. -/
theorem complete_two_pow {m u s₀ : ℕ} (hm : 1 ≤ m) (hu : u % 2 = 1)
    (h₀ : s₀ ^ 2 ≡ u [MOD 2 ^ m]) : Complete (2 ^ m) u (twoPowRoots m s₀) := by
  intro s hs
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  have hH : 0 < 2 ^ n := Nat.pow_pos (by norm_num)
  have eM : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [pow_succ]; ring
  have hHM : 2 ^ n ∣ 2 ^ (n + 1) := ⟨2, by rw [eM]; ring⟩
  have huZ : ¬ (2 : ℤ) ∣ (u : ℤ) := by omega
  have h₀Z : (s₀ : ℤ) ^ 2 ≡ (u : ℤ) [ZMOD 2 ^ (n + 1)] := by
    have := (Int.natCast_modEq_iff).mpr h₀
    simpa using this
  have hsZ : (s : ℤ) ^ 2 ≡ (u : ℤ) [ZMOD 2 ^ (n + 1)] := by
    have := (Int.natCast_modEq_iff).mpr hs
    simpa using this
  have hs₀odd := odd_of_sq_modEq_odd hm hu h₀
  have ha2 : s₀ % 2 ^ (n + 1) % 2 = 1 := by
    rw [Nat.mod_mod_of_dvd _ (dvd_pow_self 2 (by omega))]; exact hs₀odd
  have halt : s₀ % 2 ^ (n + 1) < 2 ^ (n + 1) := Nat.mod_lt _ (Nat.pow_pos (by norm_num))
  have haH : s₀ % 2 ^ (n + 1) ≡ s₀ [MOD 2 ^ n] := (Nat.mod_modEq _ _).of_dvd hHM
  simp only [twoPowRoots, Nat.add_sub_cancel]
  generalize ha : s₀ % 2 ^ (n + 1) = a at *
  rcases sq_modEq_two_pow hm huZ h₀Z hsZ with h | h
  · have h' : s ≡ s₀ [MOD 2 ^ n] := by
      apply (Int.natCast_modEq_iff).mp
      simpa using h
    have h'' : s ≡ a [MOD 2 ^ n] := h'.trans haH.symm
    rcases mod_two_mul_cases hH h'' with hc | hc
    · rw [← eM, Nat.mod_eq_of_lt halt] at hc
      simp [hc]
    · rw [← eM] at hc
      simp [hc]
  · have hdvd : 2 ^ n ∣ s + s₀ := by
      have h1 := h.symm.dvd
      have h2 : ((2 ^ n : ℕ) : ℤ) ∣ ((s + s₀ : ℕ) : ℤ) := by
        simpa using h1
      exact Int.natCast_dvd_natCast.mp h2
    have hb : s ≡ 2 ^ (n + 1) - a [MOD 2 ^ n] := by
      apply Nat.ModEq.add_right_cancel' s₀
      have e1 : s + s₀ ≡ 0 [MOD 2 ^ n] := (Nat.modEq_zero_iff_dvd).mpr hdvd
      have e2 : 2 ^ (n + 1) - a + s₀ ≡ 2 ^ (n + 1) - a + a [MOD 2 ^ n] :=
        (Nat.ModEq.refl _).add haH.symm
      have e3 : 2 ^ (n + 1) - a + a = 2 ^ (n + 1) := Nat.sub_add_cancel halt.le
      rw [e3] at e2
      exact e1.trans ((e2.trans ((Nat.modEq_zero_iff_dvd).mpr hHM)).symm)
    have hblt : 2 ^ (n + 1) - a < 2 ^ (n + 1) := Nat.sub_lt (Nat.pow_pos (by norm_num)) (by omega)
    rcases mod_two_mul_cases hH hb with hc | hc
    · rw [← eM, Nat.mod_eq_of_lt hblt] at hc
      simp [hc]
    · rw [← eM] at hc
      simp [hc]

/-! ## Certificate form -/

/-- All square roots of an odd `u` modulo `2 ^ m`, given one root `s₀` when `m ≥ 3` and
`u ≡ 1 (mod 8)` (otherwise `s₀` is ignored). -/
def twoRootsOdd (u : ℕ) : ℕ → ℕ → List ℕ
  | 0, _ => [0]
  | 1, _ => [1]
  | 2, _ => bif (u % 4).beq 1 then [1, 3] else []
  | m + 3, s₀ => bif (u % 8).beq 1 then twoPowRoots (m + 3) s₀ else []

/-- Check of the certificate `s₀`: required only when `m ≥ 3` and `u ≡ 1 (mod 8)`. -/
def twoRootsOddOk (u m s₀ : ℕ) : Bool :=
  Nat.blt m 3 || !(u % 8).beq 1 || (s₀ * s₀ % 2 ^ m).beq (u % 2 ^ m)

/-- **Powers of two (certificate form).** -/
theorem complete_twoRootsOdd {u m s₀ : ℕ} (hu : u % 2 = 1) (h : twoRootsOddOk u m s₀ = true) :
    Complete (2 ^ m) u (twoRootsOdd u m s₀) := by
  match m, h with
  | 0, _ =>
    intro x _
    simp [twoRootsOdd, Nat.mod_one]
  | 1, _ =>
    intro x hx
    have := odd_of_sq_modEq_odd (le_refl 1) hu hx
    simpa [twoRootsOdd] using this
  | 2, _ =>
    intro x hx
    have hodd := odd_of_sq_modEq_odd (by norm_num) hu hx
    by_cases h4 : u % 4 = 1
    · have hb : (u % 4).beq 1 = true := by rw [h4]; rfl
      have : x % 4 = 1 ∨ x % 4 = 3 := by omega
      simpa [twoRootsOdd, hb] using this
    · exact absurd hx (not_sq_two_pow_of_mod_four hu (le_refl 2) h4 x)
  | m + 3, h =>
    intro x hx
    by_cases h8 : u % 8 = 1
    · have hb : (u % 8).beq 1 = true := by rw [h8]; rfl
      have hlt : Nat.blt (m + 3) 3 = false := by
        rw [Bool.eq_false_iff]; intro hh
        simp at hh
      unfold twoRootsOddOk at h
      rw [hlt, hb] at h
      have h₀ : s₀ ^ 2 ≡ u [MOD 2 ^ (m + 3)] := by
        have := Nat.eq_of_beq_eq_true (by simpa using h)
        rw [pow_two]; exact this
      simp only [twoRootsOdd, hb, Bool.cond_true]
      exact complete_two_pow (by omega) hu h₀ x hx
    · exact absurd hx (not_sq_two_pow_of_mod_eight hu (by omega) h8 x)

/-- From roots `s` of `u` modulo `2 ^ m` to roots `x = 2 * s` of `4 * u` modulo `2 ^ (m + 2)`. -/
def liftTwo (m : ℕ) (L : List ℕ) : List ℕ :=
  List.rec (motive := fun _ => List ℕ) []
    (fun s _ ih => (2 * s) :: (2 * s + 2 ^ (m + 1)) :: ih) L

theorem liftTwo_eq (m : ℕ) (L : List ℕ) :
    liftTwo m L = L.flatMap fun s => [2 * s, 2 * s + 2 ^ (m + 1)] := by
  induction L with
  | nil => rfl
  | cons s tl ih =>
    change (2 * s) :: (2 * s + 2 ^ (m + 1)) :: liftTwo m tl = _
    rw [ih]
    simp

theorem Complete.liftTwo {u m : ℕ} {L : List ℕ} (h : Complete (2 ^ m) u L) :
    Complete (2 ^ (m + 2)) (4 * u) (liftTwo m L) := by
  intro x hx
  obtain ⟨s, rfl, hs⟩ := (sq_modEq_four_mul_two_pow u m x).mp hx
  have hmem := h s hs
  have e1 : 2 ^ (m + 2) = 2 * (2 ^ m * 2) := by rw [pow_add]; ring
  have e2 : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [pow_succ]; ring
  rw [e1, Nat.mul_mod_mul_left, Nat.mod_mul]
  rw [liftTwo_eq]
  refine List.mem_flatMap.mpr ⟨s % 2 ^ m, hmem, ?_⟩
  rcases Nat.mod_two_eq_zero_or_one (s / 2 ^ m) with hc | hc
  · rw [hc]; simp
  · rw [hc, e2]
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    right; ring

end Exp7.Roots
