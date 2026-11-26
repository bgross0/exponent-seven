import Exp7Lean.SieveLow.Stmt

/-!
# The sieve over `q` (small `q`), and the exceptions

For small `q` the unknown `y` is large, and enumerating the pairs `(y, x)` is hopeless in the
kernel (tens of millions of `y`).  Instead the hypothesis on `q` is sieved directly:

* `QStmt L Qa Qb E`: every `Qa ≤ q < Qb` with `q ≡ 3 (mod 8)` and `(-q / l) = -1` for all primes
  `3 ≤ l < L` is in the list `E`.  This does not involve `x`, `y` or `p` at all: it is a `Task`
  (`Core.lean`) for the class `3 (mod 8)`, the window `[Qa, Qb)` and the family `famQ`
  (Euler's criterion for `-q` modulo `l`).
* each `e ∈ E` is either in the list `listed` of survivors, or has no solution at all:
  `NoSol p e` says that `4 p ^ 7 - e y ^ 2` is not a square for any `y` prime to `p`, which is again
  a `Task`, over `y`, for the family `famY` (`4 p ^ 7 - e y ^ 2` must be a square modulo auxiliary
  primes `m`; and `p ∤ y`).

Together (`low_of_q`) they give `LowStatement p Qa Qb listed`.
-/

namespace Exp7.SieveLow

open Exp7.SieveKernel Exp7.Sieve

/-! ## The sieve over `q` -/

/-- Every `q` of the range with the residue conditions is in `E`. -/
def QStmt (L Qa Qb : ℕ) (E : List ℕ) : Prop :=
  ∀ q : ℕ, Qa ≤ q → q < Qb → q % 8 = 3 → Inert L q → q ∈ E

theorem QStmt.glue {L Qa Qm Qb : ℕ} {E1 E2 : List ℕ} (h1 : QStmt L Qa Qm E1)
    (h2 : QStmt L Qm Qb E2) : QStmt L Qa Qb (E1 ++ E2) := by
  intro q hq hqb h8 hj
  rcases Nat.lt_or_ge q Qm with h | h
  · exact List.mem_append_left _ (h1 q hq h h8 hj)
  · exact List.mem_append_right _ (h2 q h hqb h8 hj)

theorem qStmt_empty (L Q : ℕ) : QStmt L Q Q [] :=
  fun _ hq hqb _ _ => absurd hqb (Nat.not_lt.2 hq)

/-- Euler's criterion for `-q`, on the residue `r` of `q` modulo `l`: primes `3 ≤ l < L`,
`l < 400`. -/
noncomputable def famQ (L : ℕ) : Fam :=
  Fam.ofCond (fun l => Bool.and (primeB l) (Bool.and (Nat.ble 3 l) (Nat.ble (Nat.succ l) L)))
    (fun l r => Nat.beq (Nat.mod (Nat.pow (Nat.mod (Nat.sub l r) l) (Nat.div l 2)) l)
      (Nat.sub l 1))

theorem famQ_sound (L : ℕ) : (famQ L).Sound (Inert L) := by
  refine Fam.ofCond_sound fun l hl => ?_
  change Bool.and (primeB l) (Bool.and (Nat.ble 3 l) (Nat.ble (Nat.succ l) L)) = true at hl
  rw [Bool.and_eq_true, Bool.and_eq_true, Nat.ble_eq, Nat.ble_eq] at hl
  obtain ⟨hp, h3, hL⟩ := hl
  have hpr := primeB_sound hp
  refine ⟨hpr.pos, fun q hq => ?_⟩
  rw [Nat.beq_eq]
  exact euler_neg hpr (hq l hpr h3 hL)

/-- The window and the class of a task over `q`. -/
noncomputable def qPre (Qa Qb : ℕ) (t : Task) : Bool :=
  Bool.and (Nat.beq t.step0 8) (Bool.and (Nat.ble t.Xa Qa) (Nat.ble Qb t.Xb))

/-- The sieve over `q` in one computation. -/
noncomputable def qOk (L Qa Qb : ℕ) (t : Task) : Bool :=
  Bool.and (qPre Qa Qb t) (t.ok (famQ L) [] [3])

/-- The cheap part of a sieve over `q` cut into shards. -/
noncomputable def qHeader (L Qa Qb : ℕ) (t : Task) (chunk m : ℕ) : Bool :=
  Bool.and (qPre Qa Qb t) (t.header (famQ L) [3] chunk m)

theorem q_sound_of {L Qa Qb : ℕ} {t : Task} (hpre : qPre Qa Qb t = true)
    (hin : ∀ q, Inert L q → (∃ b ∈ [3], ∃ k, q = b + t.step0 * k) → t.Xa ≤ q → q < t.Xb →
      q ∈ t.exc) : QStmt L Qa Qb t.exc := by
  intro q hq hqb h8 hj
  unfold qPre at hpre
  rw [Bool.and_eq_true, Bool.and_eq_true, Nat.beq_eq, Nat.ble_eq, Nat.ble_eq] at hpre
  obtain ⟨hstep, hXa, hXb⟩ := hpre
  refine hin q hj ⟨3, List.mem_singleton_self 3, q / 8, ?_⟩ (hXa.trans hq)
    (lt_of_lt_of_le hqb hXb)
  rw [hstep]
  omega

/-- **Soundness of the sieve over `q`, in one computation.** -/
theorem qOk_sound {L Qa Qb : ℕ} {t : Task} (h : qOk L Qa Qb t = true) : QStmt L Qa Qb t.exc := by
  unfold qOk at h
  rw [Bool.and_eq_true] at h
  exact q_sound_of h.1 fun q hq hb ha hxb =>
    Task.ok_sound (famQ_sound L) (fun _ h => absurd h List.not_mem_nil) h.2 hq hb ha hxb

/-- **Soundness of the sieve over `q`, cut into shards.** -/
theorem q_sound {L Qa Qb : ℕ} {t : Task} {chunk m : ℕ} (hh : qHeader L Qa Qb t chunk m = true)
    (hs : t.ShardsUpTo (famQ L) [] [3] chunk m) : QStmt L Qa Qb t.exc := by
  unfold qHeader at hh
  rw [Bool.and_eq_true] at hh
  exact q_sound_of hh.1 fun q hq hb ha hxb =>
    Task.sound (famQ_sound L) (fun _ h => absurd h List.not_mem_nil) hh.2 hs hq hb ha hxb

/-! ## Exceptions without solutions -/

/-- `4 p ^ 7 = x ^ 2 + q y ^ 2` has no solution with `p ∤ y`. -/
def NoSol (p q : ℕ) : Prop :=
  ∀ x y : ℕ, ¬ p ∣ y → 4 * p ^ 7 = x ^ 2 + q * y ^ 2 → False

/-- `y` is prime to `p` and `S - q y ^ 2` is a square. -/
def YSol (p S q y : ℕ) : Prop := ¬ p ∣ y ∧ ∃ x : ℕ, S = x ^ 2 + q * y ^ 2

/-- Conditions on `y`: `y ≢ 0 (mod p)`; and for an odd prime `m < 400`, `m ≠ p`:
`S - q y ^ 2` is not a quadratic non-residue modulo `m` (Euler's criterion). -/
noncomputable def famY (p S q : ℕ) : Fam :=
  Fam.ofCond
    (fun m => Bool.and (Nat.ble 1 m) (Bool.or (Nat.beq m p) (Bool.and (primeB m) (Nat.ble 3 m))))
    (fun m r => bif Nat.beq m p then Bool.not (Nat.beq r 0)
      else Bool.not (Nat.beq
        (Nat.mod (Nat.pow (Nat.mod (Nat.add (Nat.mod S m)
          (Nat.mul (Nat.sub m (Nat.mod q m)) (Nat.mul r r))) m) (Nat.div m 2)) m)
        (Nat.sub m 1)))

/-- A square is not a quadratic non-residue: Euler's criterion in the form evaluated by the
kernel. -/
theorem euler_sq {S q x y m : ℕ} (hm : m.Prime) (h3 : 3 ≤ m) (hS : S = x ^ 2 + q * y ^ 2) :
    ((S % m + (m - q % m) * (y % m * (y % m))) % m) ^ (m / 2) % m ≠ m - 1 := by
  have := Fact.mk hm
  intro h
  have hodd : 2 * (m / 2) = m - 1 := by
    obtain ⟨k, rfl⟩ := hm.odd_of_ne_two (by omega)
    omega
  have hc : (((S % m + (m - q % m) * (y % m * (y % m))) % m : ℕ) : ZMod m) = (x : ZMod m) ^ 2 := by
    rw [ZMod.natCast_mod, Nat.cast_add, ZMod.natCast_mod, Nat.cast_mul,
      Nat.cast_sub (Nat.mod_lt q hm.pos).le, ZMod.natCast_mod, ZMod.natCast_self, Nat.cast_mul,
      ZMod.natCast_mod, hS]
    push_cast
    ring
  have hfin : (x : ZMod m) ^ (m - 1) = -1 := by
    have h1 : ((((S % m + (m - q % m) * (y % m * (y % m))) % m) ^ (m / 2) % m : ℕ) : ZMod m)
        = ((m - 1 : ℕ) : ZMod m) := by rw [h]
    rw [ZMod.natCast_mod, Nat.cast_pow, hc, ← pow_mul, hodd, Nat.cast_sub hm.pos,
      ZMod.natCast_self] at h1
    simpa using h1
  by_cases hx : (x : ZMod m) = 0
  · rw [hx, zero_pow (by omega)] at hfin
    have : (1 : ZMod m) = 0 := by
      have := congrArg (fun t => -t) hfin
      simpa using this.symm
    exact one_ne_zero this
  · rw [ZMod.pow_card_sub_one_eq_one hx] at hfin
    have h2 : ((2 : ℕ) : ZMod m) = 0 := by
      have : (1 : ZMod m) + 1 = 0 := by
        nth_rewrite 2 [hfin]
        ring
      push_cast
      rw [← this]
      ring
    have := (ZMod.natCast_eq_zero_iff 2 m).1 h2
    have := Nat.le_of_dvd (by norm_num) this
    omega

theorem famY_sound (p S q : ℕ) : (famY p S q).Sound (YSol p S q) := by
  refine Fam.ofCond_sound fun m hm => ?_
  change Bool.and (Nat.ble 1 m) (Bool.or (Nat.beq m p) (Bool.and (primeB m) (Nat.ble 3 m)))
    = true at hm
  rw [Bool.and_eq_true, Nat.ble_eq] at hm
  obtain ⟨hpos, hm⟩ := hm
  refine ⟨hpos, ?_⟩
  rintro y ⟨hpy, x, hS⟩
  cases hmp : Nat.beq m p
  · rw [hmp] at hm
    have hm' : (primeB m && Nat.ble 3 m) = true := by simpa using hm
    rw [Bool.and_eq_true, Nat.ble_eq] at hm'
    have hne := euler_sq (q := q) (y := y) (primeB_sound hm'.1) hm'.2 hS
    rw [Bool.cond_false, Bool.not_eq_true']
    cases hb : Nat.beq
        (Nat.mod (Nat.pow (Nat.mod (Nat.add (Nat.mod S m)
          (Nat.mul (Nat.sub m (Nat.mod q m)) (Nat.mul (y % m) (y % m)))) m) (Nat.div m 2)) m)
        (Nat.sub m 1)
    · rfl
    · rw [Nat.beq_eq] at hb
      exact absurd hb hne
  · rw [Nat.beq_eq] at hmp
    subst hmp
    rw [Bool.cond_true, Bool.not_eq_true']
    cases hb : Nat.beq (y % m) 0
    · rfl
    · rw [Nat.beq_eq] at hb
      exact absurd (Nat.dvd_of_mod_eq_zero hb) hpy

/-- The check that `q` has no solution: a task over `y` without exceptions, for the class
`0 (mod 1)` and the window `0 ≤ y < Xb`, where `S < q Xb ^ 2`. -/
noncomputable def nosolOk (p S q : ℕ) (t : Task) : Bool :=
  Bool.and (Nat.beq t.step0 1) (Bool.and (Nat.beq t.Xa 0)
    (Bool.and (Nat.ble (Nat.succ S) (Nat.mul (Nat.mul q t.Xb) t.Xb))
      (Bool.and (Nat.beq (lenR t.exc) 0) (t.ok (famY p S q) [] [0]))))

/-- **Soundness of the check that `q` has no solution.** -/
theorem nosolOk_sound {p q : ℕ} {t : Task} (h : nosolOk p (4 * p ^ 7) q t = true) :
    NoSol p q := by
  intro x y hpy hS
  unfold nosolOk at h
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Nat.beq_eq,
    Nat.beq_eq, Nat.ble_eq, Nat.beq_eq, lenR_eq] at h
  obtain ⟨hstep, hXa, hXb, hexc, hok⟩ := h
  have hXb' : 4 * p ^ 7 < q * t.Xb * t.Xb := hXb
  have hlt : y < t.Xb := by
    by_contra hc
    have h1 : q * t.Xb * t.Xb ≤ q * y * y := by
      rw [mul_assoc, mul_assoc]
      exact Nat.mul_le_mul_left _ (Nat.mul_le_mul (by omega) (by omega))
    have h2 : q * y * y = q * y ^ 2 := by ring
    omega
  have hmem := Task.ok_sound (famY_sound p (4 * p ^ 7) q)
    (fun _ h => absurd h List.not_mem_nil) hok (x := y) ⟨hpy, x, hS⟩
    ⟨0, List.mem_singleton_self 0, y, by rw [hstep]; omega⟩ (by omega) hlt
  rw [List.length_eq_zero_iff.1 hexc] at hmem
  exact absurd hmem List.not_mem_nil

/-! ## From the sieve over `q` to the statement -/

/-- Every exception is listed or has no solution. -/
def ExcDone (p : ℕ) (listed E : List ℕ) : Prop :=
  ∀ e ∈ E, e ∈ listed ∨ NoSol p e

theorem excDone_nil (p : ℕ) (listed : List ℕ) : ExcDone p listed [] :=
  fun _ h => absurd h List.not_mem_nil

theorem ExcDone.listed {p : ℕ} {listed E : List ℕ} (h : ExcDone p listed E) (e : ℕ)
    (he : elemL e listed = true) : ExcDone p listed (e :: E) := by
  intro e' he'
  rcases List.mem_cons.1 he' with rfl | h'
  · exact Or.inl (elemL_iff.1 he)
  · exact h e' h'

theorem ExcDone.nosol {p : ℕ} {listed E : List ℕ} (h : ExcDone p listed E) (e : ℕ)
    (he : NoSol p e) : ExcDone p listed (e :: E) := by
  intro e' he'
  rcases List.mem_cons.1 he' with rfl | h'
  · exact Or.inr he
  · exact h e' h'

theorem ExcDone.append {p : ℕ} {listed E1 E2 : List ℕ} (h1 : ExcDone p listed E1)
    (h2 : ExcDone p listed E2) : ExcDone p listed (E1 ++ E2) := by
  intro e he
  rcases List.mem_append.1 he with h | h
  · exact h1 e h
  · exact h2 e h

/-- **The range of small `q`.** -/
theorem low_of_q {p Qa Qb : ℕ} {listed E : List ℕ} (hq : QStmt p Qa Qb E)
    (hE : ExcDone p listed E) : LowStatement p Qa Qb listed := by
  intro x y q _ hpy hS hqa hqb h8 hj
  rcases hE q (hq q hqa hqb h8 hj) with h | h
  · exact h
  · exact absurd hS (fun hS => h x y hpy hS)

end Exp7.SieveLow
