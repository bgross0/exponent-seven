import Exp7Lean.SieveLow.Core

/-!
# The statement proved for one prime of the low-range search

`LowStatement p Qa Qb listed`: every solution of `4 p ^ 7 = x ^ 2 + q y ^ 2` (`y ≥ 1`, `p ∤ y`) with
`Qa ≤ q < Qb`, `q ≡ 3 (mod 8)` and `(-q / l) = -1` for all primes `3 ≤ l < p` has `q ∈ listed`.
`Exp7.SearchLow` is `LowStatement p (QloFull p) QLOW survivorQs` for the primes `3 ≤ p < 2760`
(with the additional hypothesis `q.Prime`, which is not used).

The statement can be cut at any `Qm` (`LowStatement.glue`): this is how the two certificates of
`DESIGN.md` are combined (the sieve over `q` below `Qm`, the sieve over `x` for each `y` above).
-/

namespace Exp7.SieveLow

open Exp7.Sieve

/-- The Jacobi-symbol hypothesis on `q`: every prime `3 ≤ l < L` is inert in `ℚ(√-q)`. -/
def Inert (L q : ℕ) : Prop :=
  ∀ l : ℕ, l.Prime → 3 ≤ l → l < L → jacobiSym (-(q : ℤ)) l = -1

/-- The statement for one prime `p` and the range `Qa ≤ q < Qb`. -/
def LowStatement (p Qa Qb : ℕ) (listed : List ℕ) : Prop :=
  ∀ x y q : ℕ, 1 ≤ y → ¬ p ∣ y → 4 * p ^ 7 = x ^ 2 + q * y ^ 2 → Qa ≤ q → q < Qb → q % 8 = 3 →
    (∀ l : ℕ, l.Prime → 3 ≤ l → l < p → jacobiSym (-(q : ℤ)) l = -1) → q ∈ listed

theorem LowStatement.mono {p Qa Qb Qa' Qb' : ℕ} {listed listed' : List ℕ}
    (h : LowStatement p Qa Qb listed) (ha : Qa ≤ Qa') (hb : Qb' ≤ Qb)
    (hl : ∀ q ∈ listed, q ∈ listed') : LowStatement p Qa' Qb' listed' :=
  fun x y q hy hpy hS hq hqb h8 hj =>
    hl q (h x y q hy hpy hS (ha.trans hq) (lt_of_lt_of_le hqb hb) h8 hj)

/-- Two ranges of `q` put together. -/
theorem LowStatement.glue {p Qa Qm Qb : ℕ} {listed : List ℕ} (h1 : LowStatement p Qa Qm listed)
    (h2 : LowStatement p Qm Qb listed) : LowStatement p Qa Qb listed := by
  intro x y q hy hpy hS hq hqb h8 hj
  rcases Nat.lt_or_ge q Qm with h | h
  · exact h1 x y q hy hpy hS hq h h8 hj
  · exact h2 x y q hy hpy hS h hqb h8 hj

/-- An empty range. -/
theorem lowStatement_empty (p Q : ℕ) (listed : List ℕ) : LowStatement p Q Q listed :=
  fun _ _ _ _ _ _ hq hqb _ _ => absurd hqb (Nat.not_lt.2 hq)

/-- Euler's criterion for the hypothesis `(-q / l) = -1`, in the form evaluated by the kernel. -/
theorem euler_neg {q l : ℕ} (hl : l.Prime) (hj : jacobiSym (-(q : ℤ)) l = -1) :
    ((l - q % l) % l) ^ (l / 2) % l = l - 1 := by
  have := Fact.mk hl
  have hleg : legendreSym l (-(q : ℤ)) = -1 := by
    rw [jacobiSym.legendreSym.to_jacobiSym]; exact hj
  have he := legendreSym.eq_pow l (-(q : ℤ))
  rw [hleg] at he
  push_cast at he
  have hc : (((l - q % l) % l : ℕ) : ZMod l) = -(q : ZMod l) := by
    rw [ZMod.natCast_mod, Nat.cast_sub (Nat.mod_lt q hl.pos).le, ZMod.natCast_mod,
      ZMod.natCast_self]
    ring
  have hfin : ((((l - q % l) % l) ^ (l / 2) : ℕ) : ZMod l) = ((l - 1 : ℕ) : ZMod l) := by
    rw [Nat.cast_pow, hc, ← he, Nat.cast_sub hl.pos, ZMod.natCast_self]
    simp
  have := (ZMod.natCast_eq_natCast_iff' _ _ _).1 hfin
  rwa [Nat.mod_eq_of_lt (Nat.sub_lt hl.pos Nat.one_pos)] at this

/-- A prime `l < L` (`3 ≤ l < 400`) that is not inert in `ℚ(√-q)`: `q` violates the hypothesis. -/
noncomputable def witOk (L q l : ℕ) : Bool :=
  Bool.and (primeB l) (Bool.and (Nat.ble 3 l) (Bool.and (Nat.ble (Nat.succ l) L)
    (Bool.not (Nat.beq
      (Nat.mod (Nat.pow (Nat.mod (Nat.sub l (Nat.mod q l)) l) (Nat.div l 2)) l) (Nat.sub l 1)))))

theorem witOk_sound {L q l : ℕ} (h : witOk L q l = true) : ¬ Inert L q := by
  intro hj
  unfold witOk at h
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Nat.ble_eq, Nat.ble_eq,
    Bool.not_eq_true'] at h
  obtain ⟨hp, h3, hL, hne⟩ := h
  have hpr := primeB_sound hp
  have he := euler_neg hpr (hj l hpr h3 hL)
  have hb : Nat.beq (Nat.mod (Nat.pow (Nat.mod (Nat.sub l (Nat.mod q l)) l) (Nat.div l 2)) l)
      (Nat.sub l 1) = true := by
    rw [Nat.beq_eq]; exact he
  rw [hb] at hne
  exact Bool.noConfusion hne

end Exp7.SieveLow
