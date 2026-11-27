import Exp7Lean.Tail.WeightedComparison
import Exp7Lean.Analytic.Autocorr
import Exp7Lean.Analytic.Reduce

/-! # From the weighted prime balance to the actual two-cell Haar row -/

namespace Exp7.ChebyshevTail

open Finset Real
open scoped ArithmeticFunction.vonMangoldt

private theorem row_ne : ∃ t ∈ ([1, -1] : List ℝ), t ≠ 0 := ⟨1, by simp, one_ne_zero⟩

private theorem corr_one : corr ([1, -1] : List ℝ) 1 = -(1 / 2 : ℝ) := by
  norm_num [corr, sum_range_succ, List.getD]

theorem haar_first {L u : ℝ} (hL : 0 < L) (hu : 0 ≤ u) (hh : u ≤ L / 2) :
    autocorr (stepFn L [1, -1]) u = 1 - 3 * u / L := by
  have h := autocorr_stepFn_of_mem_cell hL row_ne 0 (u := u) (by simpa using hu)
    (by simpa using hh)
  rw [corr_zero row_ne] at h
  norm_num [corr_one] at h
  rw [h]
  ring

theorem haar_second {L u : ℝ} (hL : 0 < L) (hh : L / 2 ≤ u) (hu : u ≤ L) :
    autocorr (stepFn L [1, -1]) u = u / L - 1 := by
  have h := autocorr_stepFn_of_mem_cell hL row_ne 1 (u := u) (by simpa using hh)
    (by norm_num; linarith)
  have h2 : corr ([1, -1] : List ℝ) 2 = 0 := corr_of_length_le (by decide)
  norm_num [corr_one, h2] at h
  rw [h]
  ring

private theorem haar_lower {L u : ℝ} (hL : 0 < L) (hu : 0 ≤ u) (hl : u ≤ L) :
    -(1 / 2 : ℝ) ≤ autocorr (stepFn L [1, -1]) u := by
  rcases le_total u (L / 2) with hh | hh
  · rw [haar_first hL hu hh]
    apply (le_sub_iff_add_le').mpr
    field_simp
    linarith
  · rw [haar_second hL hh hl]
    apply (le_sub_iff_add_le).mpr
    apply (le_div_iff₀ hL).mpr
    linarith

private noncomputable def actual (X n : ℕ) : ℝ :=
  Λ n * (-1 : ℝ) ^ (n.factorization n.minFac) *
    autocorr (stepFn (log X) [1, -1]) (log n) / sqrt n

private noncomputable def positive (X n : ℕ) : ℝ :=
  if n.Prime ∧ sqrt X < n then logWeight (log X) n * log n else 0

private noncomputable def oddLoss (X n : ℕ) : ℝ :=
  let Y := (X : ℝ) ^ (1 / 3 : ℝ)
  if n ≤ Y then logWeight (log Y) n * Λ n else 0

private noncomputable def squareLoss (n : ℕ) : ℝ :=
  if n.sqrt ^ 2 = n then Λ n.sqrt / n.sqrt else 0

private theorem squareLoss_nonneg (n : ℕ) : 0 ≤ squareLoss n := by
  unfold squareLoss
  split <;> positivity

private theorem oddLoss_nonneg {X n : ℕ} (hX : 1 < X) (hn : 0 < n) : 0 ≤ oddLoss X n := by
  let Y := (X : ℝ) ^ (1 / 3 : ℝ)
  have hY : 1 < Y := Real.one_lt_rpow (by exact_mod_cast hX) (by norm_num)
  change 0 ≤ if (n : ℝ) ≤ Y then _ else _
  split_ifs with h
  · apply mul_nonneg _ ArithmeticFunction.vonMangoldt_nonneg
    apply div_nonneg _ (sqrt_nonneg _)
    exact sub_nonneg.mpr ((div_le_one (log_pos hY)).mpr (log_le_log (by exact_mod_cast hn) h))
  · exact le_rfl

private theorem actual_odd {X n : ℕ} (hX : 1 < X) (hn : 0 < n) (hnX : n ≤ X)
    (hsign : (-1 : ℝ) ^ (n.factorization n.minFac) = -1) :
    -oddLoss X n ≤ actual X n := by
  let L := log (X : ℝ)
  let u := log (n : ℝ)
  let Y := (X : ℝ) ^ (1 / 3 : ℝ)
  have hXr : (1 : ℝ) < X := by exact_mod_cast hX
  have hY : 1 < Y := Real.one_lt_rpow hXr (by norm_num)
  have hL : 0 < L := log_pos hXr
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hu : 0 ≤ u := log_nonneg (by exact_mod_cast hn)
  have huL : u ≤ L := log_le_log hn' (by exact_mod_cast hnX)
  have hlogY : log Y = L / 3 := by rw [Real.log_rpow (by linarith : 0 < (X : ℝ))]; ring
  unfold actual
  rw [hsign]
  change -(if (n : ℝ) ≤ Y then logWeight (log Y) n * Λ n else 0) ≤
    Λ n * (-1) * autocorr (stepFn L [1, -1]) u / sqrt n
  split_ifs with h
  · have huY : u ≤ L / 3 := (log_le_log hn' h).trans_eq hlogY
    rw [haar_first hL hu (by linarith), logWeight, hlogY]
    change -((1 - u / (L / 3)) / sqrt n * Λ n) ≤ _
    apply le_of_eq
    ring
  · have huY : L / 3 ≤ u := hlogY ▸ log_le_log (by linarith : 0 < Y) (le_of_not_ge h)
    have hf : autocorr (stepFn L [1, -1]) u ≤ 0 := by
      rcases le_total u (L / 2) with hh | hh
      · rw [haar_first hL hu hh]
        have := (le_div_iff₀ hL).mpr (show 1 * L ≤ 3 * u by linarith)
        linarith
      · rw [haar_second hL hh huL]
        exact sub_nonpos.mpr ((div_le_one hL).mpr huL)
    rw [neg_zero, mul_neg_one, neg_mul, ← mul_neg]
    exact div_nonneg (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (neg_nonneg.mpr hf))
      (sqrt_nonneg _)

private theorem term_bound {X n : ℕ} (hX : 1 < X) (hn : 0 < n) (hnX : n ≤ X) :
    2 * positive X n - 2 * oddLoss X n - squareLoss n ≤ 2 * actual X n := by
  have hodd := oddLoss_nonneg hX hn
  have hsq := squareLoss_nonneg n
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hXr : (1 : ℝ) < X := by exact_mod_cast hX
  have hL := log_pos hXr
  have huL := log_le_log hn' (show (n : ℝ) ≤ X by exact_mod_cast hnX)
  by_cases hp : n.Prime ∧ sqrt X < n
  · have hexp : n.factorization n.minFac = 1 := by simp [hp.1.minFac_eq, hp.1.factorization_self]
    have hh := log_le_log (sqrt_pos.mpr (lt_trans zero_lt_one hXr)) hp.2.le
    rw [log_sqrt (by positivity)] at hh
    have he : actual X n = positive X n := by
      rw [positive, ite_eq_left hp, actual, hexp, pow_one, haar_second hL hh huL,
        ArithmeticFunction.vonMangoldt_apply_prime hp.1, logWeight]
      ring
    linarith
  rw [positive, ite_eq_right hp, mul_zero]
  by_cases hpp : IsPrimePow n
  · obtain ⟨p, k, hprime, hk, heq⟩ := (isPrimePow_nat_iff n).mp hpp
    subst n
    have hexp : (p^k).factorization (p^k).minFac = k := by
      rw [hprime.pow_minFac hk.ne', Nat.factorization_pow_self hprime]
    rcases Nat.even_or_odd k with hev | hod
    · obtain ⟨j, rfl⟩ := hev
      let m := p ^ j
      have hpow : p ^ (j + j) = m ^ 2 := by dsimp [m]; rw [pow_add, sq]
      have hm : 0 < m := pow_pos hprime.pos _
      have hs : Nat.sqrt (p ^ (j+j)) = m := by rw [hpow, Nat.sqrt_eq']
      have hsLoss : squareLoss (p ^ (j+j)) = Λ m / m := by simp [squareLoss, hs, hpow.symm]
      have hf := haar_lower hL (log_nonneg (by exact_mod_cast hn)) huL
      have hsign : (-1 : ℝ) ^ (j+j) = 1 := by rw [← two_mul, pow_mul]; norm_num
      have hcmp := mul_le_mul_of_nonneg_left hf (ArithmeticFunction.vonMangoldt_nonneg (n := m))
      have hact : 2 * actual X (p^(j+j)) ≥ -(Λ m / m) := by
        unfold actual
        rw [hexp, hsign, mul_one]
        rw [hpow, ArithmeticFunction.vonMangoldt_apply_pow (by decide : 2 ≠ 0)]
        push_cast
        rw [Real.sqrt_sq (by positivity)]
        rw [hpow, Nat.cast_pow] at hcmp
        have hm' : (0 : ℝ) < m := by exact_mod_cast hm
        calc
          -(Λ m / m) = -(Λ m) / m := by ring
          _ ≤ (2 * (Λ m * autocorr (stepFn (log X) [1, -1]) (log ((m : ℝ)^2)))) / m :=
            div_le_div_of_nonneg_right (by linarith) hm'.le
          _ = _ := by ring
      rw [hsLoss]
      linarith
    · have ha := actual_odd hX hn hnX (by rw [hexp]; exact hod.neg_one_pow)
      linarith
  · have hz := ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hpp
    simp only [actual, hz, zero_mul, zero_div]
    linarith

private theorem sum_positive (X : ℕ) :
    ∑ n ∈ Ioc 0 X, positive X n =
      ∑ p ∈ Ioc ⌊sqrt X⌋₊ X with p.Prime, logWeight (log X) p * log p := by
  unfold positive
  rw [← sum_filter]
  congr 1
  ext n
  simp only [mem_filter, mem_Ioc, Nat.floor_lt (sqrt_nonneg _)]
  constructor
  · rintro ⟨⟨_, h⟩, hp, hs⟩
    exact ⟨⟨hs, h⟩, hp⟩
  · rintro ⟨⟨hs, h⟩, hp⟩
    exact ⟨⟨hp.pos, h⟩, hp, hs⟩

private theorem sum_oddLoss {X : ℕ} (hX : 1 < X) :
    ∑ n ∈ Ioc 0 X, oddLoss X n =
      ∑ n ∈ Ioc 0 ⌊(X : ℝ) ^ (1 / 3 : ℝ)⌋₊,
        logWeight (log ((X : ℝ) ^ (1 / 3 : ℝ))) n * Λ n := by
  let Y := (X : ℝ) ^ (1 / 3 : ℝ)
  have hXr : (1 : ℝ) ≤ X := by exact_mod_cast hX.le
  have hYX : Y ≤ X := by
    calc
      _ ≤ (X : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hXr (by norm_num)
      _ = _ := Real.rpow_one _
  have hfloor : ⌊Y⌋₊ ≤ X := Nat.floor_le_of_le hYX
  unfold oddLoss
  dsimp only
  rw [← sum_filter]
  congr 1
  ext n
  simp only [mem_filter, mem_Ioc]
  change ((0 < n ∧ n ≤ X) ∧ (n : ℝ) ≤ Y) ↔ (0 < n ∧ n ≤ ⌊Y⌋₊)
  rw [← Nat.le_floor_iff (show 0 ≤ Y by positivity)]
  omega

private theorem sum_squareLoss (X : ℕ) :
    ∑ n ∈ Ioc 0 X, squareLoss n = ∑ d ∈ Ioc 0 ⌊sqrt X⌋₊, Λ d / d := by
  classical
  let S := Ioc 0 ⌊sqrt X⌋₊
  have hset : ((Ioc 0 X).filter fun n ↦ n.sqrt ^ 2 = n) = S.image (fun d ↦ d ^ 2) := by
    ext n
    simp only [mem_filter, mem_Ioc, mem_image]
    constructor
    · rintro ⟨⟨hn, hnX⟩, hs⟩
      refine ⟨n.sqrt, mem_Ioc.mpr ⟨?_, ?_⟩, hs⟩
      · by_contra! hz
        have : n.sqrt = 0 := by omega
        simp [this] at hs
        omega
      · apply Nat.le_floor
        apply Real.le_sqrt_of_sq_le
        exact_mod_cast hs.le.trans hnX
    · rintro ⟨d, hd, rfl⟩
      obtain ⟨hd0, hdX⟩ := mem_Ioc.mp hd
      have hle := (Nat.le_floor_iff (sqrt_nonneg (X : ℝ))).mp hdX
      have hs := (Real.le_sqrt (Nat.cast_nonneg d) (Nat.cast_nonneg X)).mp hle
      exact ⟨⟨pow_pos hd0 _, by exact_mod_cast hs⟩, by rw [Nat.sqrt_eq']⟩
  unfold squareLoss
  rw [← sum_filter, hset, sum_image]
  · apply sum_congr rfl
    intro d _
    rw [Nat.sqrt_eq']
  · intro a _ b _ hab
    simpa only [Nat.sqrt_eq'] using congrArg Nat.sqrt hab

private theorem sum_actual {X : ℕ} (hX : 1 < X) :
    2 * ∑ n ∈ Ioc 0 X, actual X n = inertSum (autocorr (stepFn (log X) [1, -1])) X := by
  have hL := log_pos (show (1 : ℝ) < X by exact_mod_cast hX)
  have hx : actual X X = 0 := by
    unfold actual
    rw [haar_second hL (by linarith) le_rfl, div_self hL.ne']
    ring
  have hz : actual X 0 = 0 := by simp [actual]
  change 2 * _ = 2 * ∑ n ∈ range X, actual X n
  congr 1
  calc
    _ = ∑ n ∈ Icc 0 X, actual X n := by
      rw [← add_sum_Ioc_eq_sum_Icc (Nat.zero_le X), hz, zero_add]
    _ = ∑ n ∈ range (X + 1), actual X n := by rw [Nat.range_succ_eq_Icc_zero]
    _ = _ := by rw [sum_range_succ, hx, add_zero]

/-- The project's actual inert prime-power sum dominates the three weighted
prime sums at every integer cutoff greater than one. -/
theorem weightedPrimeBalance_le_inertSum {X : ℕ} (hX : 1 < X) :
    weightedPrimeBalance X ≤ inertSum (autocorr (stepFn (log X) [1, -1])) X := by
  have h := sum_le_sum (s := Ioc 0 X) (fun n hn ↦
    term_bound hX (mem_Ioc.mp hn).1 (mem_Ioc.mp hn).2)
  simp only [sum_sub_distrib, ← mul_sum] at h
  rw [sum_positive, sum_oddLoss hX, sum_squareLoss, sum_actual hX] at h
  simpa only [weightedPrimeBalance, Nat.floor_natCast] using h

end Exp7.ChebyshevTail
