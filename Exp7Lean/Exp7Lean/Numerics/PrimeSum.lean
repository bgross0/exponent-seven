import Exp7Lean.Numerics.FixedLog

/-!
# Kernel-friendly sums over primes

* `isPrimeB n` : trial division written with `Nat.rec` and raw `Nat` operations, with
  `isPrimeB n = true ↔ n.Prime`.
* `sumPrimes g a len = ∑_{n ∈ [a, a+len), n prime} g n` computed by one `Nat.rec` loop, and the
  transfer lemmas `sumPrimes_le`, `le_sumPrimes` that turn term-wise fixed-point bounds
  `g p ≤ c * F p` into a bound for `∑ p ∈ (Finset.Ico a (a+len)).filter Nat.Prime, F p`.
-/

namespace Exp7.Num

/-- `noDivisor n fuel d = true` iff no `k ≥ d` with `k * k ≤ n` divides `n`
(provided `n < (d + fuel)^2`; otherwise it may return `false`). -/
def noDivisor (n fuel : ℕ) : ℕ → Bool :=
  Nat.rec (motive := fun _ => ℕ → Bool) (fun d => Nat.ble (Nat.succ n) (Nat.mul d d))
    (fun _ ih d => cond (Nat.ble (Nat.succ n) (Nat.mul d d)) true
      (cond (Nat.beq (Nat.mod n d) 0) false (ih (Nat.succ d)))) fuel

theorem ble_eq_decide (a b : ℕ) : Nat.ble a b = decide (a ≤ b) := by
  by_cases h : a ≤ b
  · rw [decide_eq_true h]; exact Nat.ble_eq_true_of_le h
  · rw [decide_eq_false h]
    cases hb : Nat.ble a b with
    | false => rfl
    | true => exact absurd (Nat.le_of_ble_eq_true hb) h

theorem beq_eq_decide (a b : ℕ) : Nat.beq a b = decide (a = b) := by
  by_cases h : a = b
  · subst h; rw [decide_eq_true rfl]; exact Nat.beq_refl a
  · rw [decide_eq_false h]
    cases hb : Nat.beq a b with
    | false => rfl
    | true => exact absurd (Nat.eq_of_beq_eq_true hb) h

theorem noDivisor_zero (n d : ℕ) : noDivisor n 0 d = decide (n < d * d) :=
  ble_eq_decide (n + 1) (d * d)

theorem noDivisor_succ (n fuel d : ℕ) : noDivisor n (fuel + 1) d =
    if n < d * d then true else if n % d = 0 then false else noDivisor n fuel (d + 1) := by
  change cond (Nat.ble (n + 1) (d * d)) true
    (cond (Nat.beq (n % d) 0) false (noDivisor n fuel (d + 1))) = _
  rw [ble_eq_decide, beq_eq_decide]
  by_cases h : n < d * d
  · have h' : n + 1 ≤ d * d := h
    simp [h, h']
  · have h' : ¬ (n + 1 ≤ d * d) := h
    by_cases h2 : n % d = 0 <;> simp [h, h', h2]

theorem noDivisor_iff (n : ℕ) : ∀ (fuel d : ℕ), n < (d + fuel) * (d + fuel) →
    (noDivisor n fuel d = true ↔ ∀ k, d ≤ k → k * k ≤ n → ¬ k ∣ n) := by
  intro fuel
  induction fuel with
  | zero =>
    intro d hd
    rw [noDivisor_zero]
    simp only [Nat.add_zero] at hd
    simp only [hd, decide_true, true_iff]
    intro k hk hkn
    exact absurd (lt_of_lt_of_le hd (Nat.mul_le_mul hk hk)) (not_lt.mpr hkn)
  | succ fuel ih =>
    intro d hd
    rw [noDivisor_succ]
    split_ifs with h1 h2
    · simp only [true_iff]
      intro k hk hkn
      exact absurd (lt_of_lt_of_le h1 (Nat.mul_le_mul hk hk)) (not_lt.mpr hkn)
    · simp only [false_iff, not_forall]
      exact ⟨d, le_rfl, not_lt.mp h1, fun h => h (Nat.dvd_of_mod_eq_zero h2)⟩
    · rw [ih (d + 1) (by rw [show d + 1 + fuel = d + (fuel + 1) by omega]; exact hd)]
      constructor
      · intro h k hk hkn
        rcases Nat.eq_or_lt_of_le hk with rfl | hlt
        · exact fun hdvd => h2 (Nat.mod_eq_zero_of_dvd hdvd)
        · exact h k hlt hkn
      · intro h k hk hkn
        exact h k (by omega) hkn

/-- Boolean primality by trial division. -/
def isPrimeB (n : ℕ) : Bool := Nat.ble 2 n && noDivisor n n 2

theorem isPrimeB_iff (n : ℕ) : isPrimeB n = true ↔ n.Prime := by
  unfold isPrimeB
  rw [Bool.and_eq_true, Nat.ble_eq, Nat.prime_def_le_sqrt,
    noDivisor_iff n n 2 (by nlinarith)]
  simp only [Nat.le_sqrt]

/-- `∑ g n` over the primes `n` with `a ≤ n < a + len`. -/
def sumPrimes (g : ℕ → ℕ) (a len : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0
    (fun i ih => cond (isPrimeB (Nat.add a i)) (Nat.add ih (g (Nat.add a i))) ih) len

theorem sumPrimes_zero (g : ℕ → ℕ) (a : ℕ) : sumPrimes g a 0 = 0 := rfl

theorem sumPrimes_succ (g : ℕ → ℕ) (a len : ℕ) : sumPrimes g a (len + 1) =
    if (a + len).Prime then sumPrimes g a len + g (a + len) else sumPrimes g a len := by
  change cond (isPrimeB (a + len)) (sumPrimes g a len + g (a + len)) (sumPrimes g a len) = _
  by_cases h : (a + len).Prime
  · simp [h, (isPrimeB_iff _).mpr h]
  · have : isPrimeB (a + len) = false := by
      rw [← Bool.not_eq_true, isPrimeB_iff]; exact h
    simp [h, this]

theorem filter_prime_Ico_succ (a len : ℕ) :
    (Finset.Ico a (a + (len + 1))).filter Nat.Prime =
      if (a + len).Prime then insert (a + len) ((Finset.Ico a (a + len)).filter Nat.Prime)
      else (Finset.Ico a (a + len)).filter Nat.Prime := by
  rw [← Nat.add_assoc, Nat.Ico_succ_right_eq_insert_Ico (Nat.le_add_right a len),
    Finset.filter_insert]

/-- Term-wise lower bounds give a lower bound for the sum over primes. -/
theorem sumPrimes_le (g : ℕ → ℕ) (F : ℕ → ℝ) (c : ℝ) (a len : ℕ)
    (h : ∀ p, p.Prime → a ≤ p → p < a + len → (g p : ℝ) ≤ c * F p) :
    (sumPrimes g a len : ℝ) ≤ c * ∑ p ∈ (Finset.Ico a (a + len)).filter Nat.Prime, F p := by
  induction len with
  | zero => simp [sumPrimes_zero]
  | succ len ih =>
    have ih' := ih (fun p hp h1 h2 => h p hp h1 (by omega))
    rw [sumPrimes_succ, filter_prime_Ico_succ]
    split_ifs with hp
    · rw [Finset.sum_insert (by simp)]
      have := h (a + len) hp (by omega) (by omega)
      push_cast
      linarith
    · exact ih'

/-- Term-wise upper bounds give an upper bound for the sum over primes. -/
theorem le_sumPrimes (g : ℕ → ℕ) (F : ℕ → ℝ) (c : ℝ) (a len : ℕ)
    (h : ∀ p, p.Prime → a ≤ p → p < a + len → c * F p ≤ (g p : ℝ)) :
    c * ∑ p ∈ (Finset.Ico a (a + len)).filter Nat.Prime, F p ≤ (sumPrimes g a len : ℝ) := by
  induction len with
  | zero => simp [sumPrimes_zero]
  | succ len ih =>
    have ih' := ih (fun p hp h1 h2 => h p hp h1 (by omega))
    rw [sumPrimes_succ, filter_prime_Ico_succ]
    split_ifs with hp
    · rw [Finset.sum_insert (by simp)]
      have := h (a + len) hp (by omega) (by omega)
      push_cast
      linarith
    · exact ih'

/-- The primes below `X`, as a filter of `Finset.range`. -/
theorem range_filter_prime_eq (X : ℕ) :
    (Finset.range X).filter Nat.Prime = (Finset.Ico 0 (0 + X)).filter Nat.Prime := by
  rw [Nat.zero_add, Finset.range_eq_Ico]

/-- `sumPrimes_le` for the primes below `X`. -/
theorem sumPrimes_range_le (g : ℕ → ℕ) (F : ℕ → ℝ) (c : ℝ) (X : ℕ)
    (h : ∀ p, p.Prime → p < X → (g p : ℝ) ≤ c * F p) :
    (sumPrimes g 0 X : ℝ) ≤ c * ∑ p ∈ (Finset.range X).filter Nat.Prime, F p := by
  rw [range_filter_prime_eq]
  exact sumPrimes_le g F c 0 X (fun p hp _ h2 => h p hp (by omega))

/-- `le_sumPrimes` for the primes below `X`. -/
theorem le_sumPrimes_range (g : ℕ → ℕ) (F : ℕ → ℝ) (c : ℝ) (X : ℕ)
    (h : ∀ p, p.Prime → p < X → c * F p ≤ (g p : ℝ)) :
    c * ∑ p ∈ (Finset.range X).filter Nat.Prime, F p ≤ (sumPrimes g 0 X : ℝ) := by
  rw [range_filter_prime_eq]
  exact le_sumPrimes g F c 0 X (fun p hp _ h2 => h p hp (by omega))

/-! ### The list of primes below a bound, and sums over a list -/

/-- The primes below `B`, in decreasing order (computed by trial division). -/
def primesBelow (B : ℕ) : List ℕ :=
  Nat.rec (motive := fun _ => List ℕ) [] (fun n ih => cond (isPrimeB n) (n :: ih) ih) B

theorem primesBelow_succ (B : ℕ) :
    primesBelow (B + 1) = if B.Prime then B :: primesBelow B else primesBelow B := by
  change cond (isPrimeB B) (B :: primesBelow B) (primesBelow B) = _
  by_cases h : B.Prime
  · simp [h, (isPrimeB_iff _).mpr h]
  · have : isPrimeB B = false := by rw [← Bool.not_eq_true, isPrimeB_iff]; exact h
    simp [h, this]

theorem mem_primesBelow {B p : ℕ} : p ∈ primesBelow B ↔ p.Prime ∧ p < B := by
  induction B with
  | zero => simp [primesBelow]
  | succ B ih =>
    rw [primesBelow_succ]
    split_ifs with h
    · rw [List.mem_cons, ih]
      constructor
      · rintro (rfl | ⟨h1, h2⟩)
        · exact ⟨h, Nat.lt_succ_self _⟩
        · exact ⟨h1, by omega⟩
      · rintro ⟨h1, h2⟩
        rcases Nat.eq_or_lt_of_le (Nat.lt_succ_iff.mp h2) with rfl | h3
        · exact Or.inl rfl
        · exact Or.inr ⟨h1, h3⟩
    · rw [ih]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨h1, by omega⟩
      · rintro ⟨h1, h2⟩
        rcases Nat.eq_or_lt_of_le (Nat.lt_succ_iff.mp h2) with rfl | h3
        · exact absurd h1 h
        · exact ⟨h1, h3⟩

theorem primesBelow_nodup (B : ℕ) : (primesBelow B).Nodup := by
  induction B with
  | zero => simp [primesBelow]
  | succ B ih =>
    rw [primesBelow_succ]
    split_ifs with h
    · rw [List.nodup_cons]
      refine ⟨fun hm => ?_, ih⟩
      exact absurd (mem_primesBelow.mp hm).2 (lt_irrefl _)
    · exact ih

/-- `∑ g p` over the entries `p < X` of the list `L` (raw `List.rec`, kernel-friendly). -/
def listSumBelow (g : ℕ → ℕ) (X : ℕ) (L : List ℕ) : ℕ :=
  List.rec (motive := fun _ => ℕ) 0
    (fun p _ ih => cond (Nat.ble (Nat.succ p) X) (Nat.add (g p) ih) ih) L

theorem listSumBelow_nil (g : ℕ → ℕ) (X : ℕ) : listSumBelow g X [] = 0 := rfl

theorem listSumBelow_cons (g : ℕ → ℕ) (X p : ℕ) (L : List ℕ) : listSumBelow g X (p :: L) =
    if p < X then g p + listSumBelow g X L else listSumBelow g X L := by
  change cond (Nat.ble (p + 1) X) (g p + listSumBelow g X L) (listSumBelow g X L) = _
  rw [cond_ble]; rfl

theorem listSumBelow_eq (g : ℕ → ℕ) (X : ℕ) {L : List ℕ} (hL : L.Nodup) :
    listSumBelow g X L = ∑ p ∈ L.toFinset.filter (· < X), g p := by
  induction L with
  | nil => simp [listSumBelow_nil]
  | cons p L ih =>
    rw [List.nodup_cons] at hL
    rw [listSumBelow_cons, ih hL.2, List.toFinset_cons, Finset.filter_insert]
    split_ifs with h
    · rw [Finset.sum_insert]
      simp [hL.1]
    · rfl

/-- If `L` lists exactly the primes below `B` and `X ≤ B`, the entries of `L` below `X` are the
primes below `X`. -/
theorem toFinset_filter_lt {L : List ℕ} {B X : ℕ} (hL : ∀ p, p ∈ L ↔ p.Prime ∧ p < B)
    (hX : X ≤ B) : L.toFinset.filter (· < X) = (Finset.range X).filter Nat.Prime := by
  ext p
  simp only [Finset.mem_filter, List.mem_toFinset, hL, Finset.mem_range]
  constructor
  · rintro ⟨⟨h1, _⟩, h2⟩; exact ⟨h2, h1⟩
  · rintro ⟨h1, h2⟩; exact ⟨⟨h2, by omega⟩, h1⟩

/-- Term-wise lower bounds give a lower bound for the sum over the primes below `X`, computed
from a certified list of primes. -/
theorem listSumBelow_le (g : ℕ → ℕ) (F : ℕ → ℝ) (c : ℝ) {L : List ℕ} {B X : ℕ}
    (hN : L.Nodup) (hL : ∀ p, p ∈ L ↔ p.Prime ∧ p < B) (hX : X ≤ B)
    (h : ∀ p, p.Prime → p < X → (g p : ℝ) ≤ c * F p) :
    (listSumBelow g X L : ℝ) ≤ c * ∑ p ∈ (Finset.range X).filter Nat.Prime, F p := by
  rw [listSumBelow_eq g X hN, toFinset_filter_lt hL hX, Finset.mul_sum]
  push_cast
  apply Finset.sum_le_sum
  intro p hp
  rw [Finset.mem_filter, Finset.mem_range] at hp
  exact h p hp.2 hp.1

/-- Term-wise upper bounds give an upper bound for the sum over the primes below `X`. -/
theorem le_listSumBelow (g : ℕ → ℕ) (F : ℕ → ℝ) (c : ℝ) {L : List ℕ} {B X : ℕ}
    (hN : L.Nodup) (hL : ∀ p, p ∈ L ↔ p.Prime ∧ p < B) (hX : X ≤ B)
    (h : ∀ p, p.Prime → p < X → c * F p ≤ (g p : ℝ)) :
    c * ∑ p ∈ (Finset.range X).filter Nat.Prime, F p ≤ (listSumBelow g X L : ℝ) := by
  rw [listSumBelow_eq g X hN, toFinset_filter_lt hL hX, Finset.mul_sum]
  push_cast
  apply Finset.sum_le_sum
  intro p hp
  rw [Finset.mem_filter, Finset.mem_range] at hp
  exact h p hp.2 hp.1

/-- Kernel-friendly universal check below a bound. -/
def allBelow (f : ℕ → Bool) (n : ℕ) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun k ih => Bool.rec false ih (f k)) n

theorem allBelow_iff (f : ℕ → Bool) (n : ℕ) : allBelow f n = true ↔ ∀ k < n, f k = true := by
  induction n with
  | zero => simp [allBelow]
  | succ n ih =>
    have e : allBelow f (n + 1) = Bool.rec false (allBelow f n) (f n) := rfl
    rw [e]
    constructor
    · intro h k hk
      cases hf : f n with
      | false => rw [hf] at h; exact absurd h (by simp)
      | true =>
        rw [hf] at h
        rcases Nat.eq_or_lt_of_le (Nat.lt_succ_iff.mp hk) with rfl | h3
        · exact hf
        · exact ih.mp h k h3
    · intro h
      rw [h n (Nat.lt_succ_self n)]
      exact ih.mpr (fun k hk => h k (by omega))

/-- Two-level universal check for `k < a * b` (keeps the kernel's recursion depth at `a + b`
instead of `a * b`). -/
def allBelow2 (f : ℕ → Bool) (a b : ℕ) : Bool :=
  allBelow (fun i => allBelow (fun j => f (Nat.add (Nat.mul i b) j)) b) a

theorem allBelow2_imp (f : ℕ → Bool) (a b : ℕ) (h : allBelow2 f a b = true) :
    ∀ k < a * b, f k = true := by
  intro k hk
  have hb : 0 < b := by
    rcases Nat.eq_zero_or_pos b with rfl | hb
    · simp at hk
    · exact hb
  have h1 := (allBelow_iff _ _).mp h (k / b) (by
    rw [Nat.div_lt_iff_lt_mul hb]; exact hk)
  have h2 := (allBelow_iff _ _).mp h1 (k % b) (Nat.mod_lt _ hb)
  have e : Nat.add (Nat.mul (k / b) b) (k % b) = k := by
    change k / b * b + k % b = k
    rw [Nat.mul_comm]; exact Nat.div_add_mod k b
  rw [e] at h2
  exact h2

end Exp7.Num
