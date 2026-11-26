import Exp7Lean.SieveLow.Stmt
import Exp7Lean.Sieve.RootsCert

/-!
# The sieve over `x` for one `y` (large `q`)

For a fixed `y`, the solutions `x` of `S = x ^ 2 + q y ^ 2` with `Qa ≤ q < Qb` lie

* in the classes modulo `8 y ^ 2` listed by `Roots.rootsOf8` (certified square roots of `S` modulo
  `y ^ 2`, refined by `q ≡ 3 (mod 8)`), and
* in the window `Xa ≤ x < Xb`, where `S - Qa y ^ 2 < Xb ^ 2` and `(Xa - 1) ^ 2 + Qb y ^ 2 ≤ S`;

and they satisfy the conditions `Bridge.condB` modulo the primes `l < L`, `l ∤ y`.  This is a `Task`
(`Core.lean`) for the family `famX`.  The `x` that survive the sieve are listed in the task; for
each of them the checker computes `q = (S - x ^ 2) / y ^ 2` and verifies that `q` is in the list
`listed`, or exhibits a prime `l < L` with `(-q / l) ≠ -1` (`excOk`).

`YC` is the certificate for one `y` (`skip`: `p ∣ y`; `nonres`, `two`: no square root modulo
`y ^ 2`; `full`: the sieve; `tab`: the sieve in table mode), `rangeOk` checks a list of them for
consecutive `y`, and `UpTo` chains the ranges.

**Table mode.**  The patterns of a task depend on `y` through the step `8 y ^ 2`: the pattern of
the prime `l` is `j ↦ condB S l (step * j % l)`, a *dilation* of the table of `l` by `step % l`.
Computing it costs `l` kernel steps for every `y` and `l`, which dominates when the blocks are
short.  In table mode all the dilations of the table of `l` are computed once per declaration
(`dilTab S l d`, one field of `l * 2 ^ d` bits for each `u < l`; the kernel caches the value of
this closed term), and the pattern for `y` is extracted with one shift (`tabPats`).  The inverse
of the step modulo `l` is computed by the kernel (`step ^ (l - 2)`) and *tested*; a prime that
divides `y`, or fails a test, is left out (which is always sound).
-/

namespace Exp7.SieveLow

open Exp7.SieveKernel Exp7.Sieve Exp7.Roots

/-- `x` is a solution for the fixed `y`, with `Qa ≤ q < Qb`. -/
def SolLo (S Qa Qb L y x : ℕ) : Prop :=
  ∃ q : ℕ, S = x ^ 2 + q * y ^ 2 ∧ Qa ≤ q ∧ q < Qb ∧ q % 8 = 3 ∧ Inert L q

theorem SolLo.sol {S Qa Qb L y x : ℕ} (h : SolLo S Qa Qb L y x) : Sol S Qa L y x := by
  obtain ⟨q, hS, hq, -, h8, hj⟩ := h
  exact ⟨q, hS, hq, h8, hj⟩

/-- The upper end of the window. -/
theorem SolLo.lt {S Qa Qb L y x Xb : ℕ} (h : SolLo S Qa Qb L y x)
    (hX : S - Qa * y * y < Xb * Xb) : x < Xb := h.sol.lt hX

/-- The lower end of the window. -/
theorem SolLo.ge {S Qa Qb L y x Xa : ℕ} (h : SolLo S Qa Qb L y x) (hy : 1 ≤ y)
    (hX : Xa = 0 ∨ (Xa - 1) * (Xa - 1) + Qb * y * y ≤ S) : Xa ≤ x := by
  rcases hX with hX | hX
  · omega
  obtain ⟨q, hS, -, hqb, -, -⟩ := h
  by_contra hx
  have h1 : x * x ≤ (Xa - 1) * (Xa - 1) := Nat.mul_le_mul (by omega) (by omega)
  have h2 : (q + 1) * y * y ≤ Qb * y * y :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hqb)
  have h3 : (q + 1) * y * y = q * y ^ 2 + y * y := by ring
  have h4 : 1 ≤ y * y := Nat.mul_pos hy hy
  have h5 : x ^ 2 = x * x := pow_two x
  omega

/-- The conditions modulo the primes `3 ≤ l < L`, `l < 400`, `l ∤ y`. -/
noncomputable def famX (S L y : ℕ) : Fam :=
  Fam.ofCond (fun l => Bool.and (primeB l) (Bool.and (Nat.ble 3 l)
    (Bool.and (Nat.ble (Nat.succ l) L) (Bool.not (Nat.beq (Nat.mod y l) 0))))) (condB S)

theorem famX_sound (S Qa Qb L y : ℕ) : (famX S L y).Sound (SolLo S Qa Qb L y) := by
  refine Fam.ofCond_sound fun l hl => ?_
  change Bool.and (primeB l) (Bool.and (Nat.ble 3 l) (Bool.and (Nat.ble (Nat.succ l) L)
    (Bool.not (Nat.beq (Nat.mod y l) 0)))) = true at hl
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Nat.ble_eq, Nat.ble_eq,
    Bool.not_eq_true'] at hl
  obtain ⟨hp, h3, hL, hy⟩ := hl
  have hpr := primeB_sound hp
  refine ⟨hpr.pos, ?_⟩
  rintro x ⟨q, hS, -, -, -, hj⟩
  refine condB_sound hS hpr h3 (fun hd => ?_) (hj l hpr h3 hL)
  have : Nat.beq (Nat.mod y l) 0 = true := by
    rw [Nat.beq_eq]; exact Nat.mod_eq_zero_of_dvd hd
  rw [this] at hy
  exact Bool.noConfusion hy

/-- An `x` that survives the sieve is harmless: its `q` is listed, or one of the primes `wits`
is not inert in `ℚ(√-q)`. -/
noncomputable def excOk (S L y : ℕ) (listed wits : List ℕ) (x : ℕ) : Bool :=
  (fun q : ℕ => Bool.or (anyL (witOk L q) wits) (elemL q listed))
    (Nat.div (Nat.sub S (Nat.mul x x)) (Nat.mul y y))

theorem excOk_sound {S L y x q : ℕ} {listed wits : List ℕ} (h : excOk S L y listed wits x = true)
    (hS : S = x ^ 2 + q * y ^ 2) (hy : 1 ≤ y) (hj : Inert L q) : q ∈ listed := by
  have hq : (S - x * x) / (y * y) = q := by
    have : S - x * x = q * (y * y) := by rw [hS]; ring_nf; omega
    rw [this]
    exact Nat.mul_div_cancel _ (Nat.mul_pos hy hy)
  have h' : (anyL (witOk L ((S - x * x) / (y * y))) wits ||
      elemL ((S - x * x) / (y * y)) listed) = true := h
  rw [hq, Bool.or_eq_true, elemL_iff, anyL_iff] at h'
  rcases h' with ⟨l, -, hl⟩ | h'
  · exact absurd hj (witOk_sound hl)
  · exact h'

/-- The same when the sieve did not use `q ≡ 3 (mod 8)`: the survivors with `q ≢ 3 (mod 8)` are
harmless too. -/
noncomputable def excOk8 (S L y : ℕ) (listed wits : List ℕ) (x : ℕ) : Bool :=
  (fun q : ℕ => Bool.or (Bool.not (Nat.beq (Nat.mod q 8) 3))
      (Bool.or (anyL (witOk L q) wits) (elemL q listed)))
    (Nat.div (Nat.sub S (Nat.mul x x)) (Nat.mul y y))

theorem excOk8_sound {S L y x q : ℕ} {listed wits : List ℕ}
    (h : excOk8 S L y listed wits x = true) (hS : S = x ^ 2 + q * y ^ 2) (hy : 1 ≤ y)
    (h8 : q % 8 = 3) (hj : Inert L q) : q ∈ listed := by
  have hq : (S - x * x) / (y * y) = q := by
    have : S - x * x = q * (y * y) := by rw [hS]; ring_nf; omega
    rw [this]
    exact Nat.mul_div_cancel _ (Nat.mul_pos hy hy)
  have h' : (!Nat.beq ((S - x * x) / (y * y) % 8) 3 ||
      excOk S L y listed wits x) = true := h
  rw [hq, Bool.or_eq_true, Bool.not_eq_true'] at h'
  rcases h' with h' | h'
  · have : Nat.beq (q % 8) 3 = true := by rw [Nat.beq_eq]; exact h8
    rw [this] at h'
    exact Bool.noConfusion h'
  · exact excOk_sound h' hS hy hj

/-- The statement for one `y` (`S = 4 p ^ 7`, `L = p`). -/
def YStmt (p S Qa Qb L : ℕ) (listed : List ℕ) (y : ℕ) : Prop :=
  ∀ x q : ℕ, ¬ p ∣ y → S = x ^ 2 + q * y ^ 2 → Qa ≤ q → q < Qb → q % 8 = 3 → Inert L q →
    q ∈ listed

/-- The sieve certificate for one `y`: a certificate for the square roots of `S` modulo `y ^ 2`,
the task, and the primes used as witnesses for the survivors that are not listed. -/
structure XC where
  c : Cert
  t : Task
  wits : List ℕ

namespace XC

/-- The cheap checks: roots, step, window, survivors. -/
noncomputable def pre (S Qa Qb L : ℕ) (listed : List ℕ) (y : ℕ) (c : XC) : Bool :=
  Bool.and (rootsOk S y c.c)
    (Bool.and (Nat.beq c.t.step0 (Nat.mul (Nat.mul 8 y) y))
      (Bool.and (Nat.ble (Nat.succ (Nat.sub S (Nat.mul (Nat.mul Qa y) y))) (Nat.mul c.t.Xb c.t.Xb))
        (Bool.and
          (Bool.or (Nat.beq c.t.Xa 0)
            (Nat.ble (Nat.add (Nat.mul (Nat.sub c.t.Xa 1) (Nat.sub c.t.Xa 1))
              (Nat.mul (Nat.mul Qb y) y)) S))
          (allL (excOk S L y listed c.wits) c.t.exc))))

/-- The certificate for one `y` in one computation, with additional patterns. -/
noncomputable def okE (S Qa Qb L : ℕ) (listed : List ℕ) (y : ℕ) (c : XC) (extra : List Pat) :
    Bool :=
  Bool.and (c.pre S Qa Qb L listed y) (c.t.ok (famX S L y) extra (rootsOf8 S y c.c))

/-- The certificate for one `y` in one computation. -/
noncomputable def ok (S Qa Qb L : ℕ) (listed : List ℕ) (y : ℕ) (c : XC) : Bool :=
  c.okE S Qa Qb L listed y []

/-- The cheap part of a certificate cut into shards. -/
noncomputable def header (S Qa Qb L : ℕ) (listed : List ℕ) (y : ℕ) (c : XC) (chunk m : ℕ) : Bool :=
  Bool.and (c.pre S Qa Qb L listed y) (c.t.header (famX S L y) (rootsOf8 S y c.c) chunk m)

/-- Shard `i` of a certificate cut into shards. -/
noncomputable def shardOk (S L y : ℕ) (c : XC) (chunk i : ℕ) : Bool :=
  c.t.shardOk (famX S L y) [] (rootsOf8 S y c.c) chunk i

/-- The shards `0, …, k - 1` have been checked. -/
def ShardsUpTo (S L y : ℕ) (c : XC) (chunk k : ℕ) : Prop :=
  ∀ i < k, c.shardOk S L y chunk i = true

theorem shardsUpTo_zero (S L y : ℕ) (c : XC) (chunk : ℕ) : c.ShardsUpTo S L y chunk 0 :=
  fun _ h => absurd h (Nat.not_lt_zero _)

theorem ShardsUpTo.succ {S L y : ℕ} {c : XC} {chunk k : ℕ} (h : c.ShardsUpTo S L y chunk k)
    (hk : c.shardOk S L y chunk k = true) : c.ShardsUpTo S L y chunk (k + 1) := by
  intro i hi
  rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h' | rfl
  · exact h i h'
  · exact hk

theorem sound_of {p S Qa Qb L y : ℕ} {listed : List ℕ} {c : XC} (hy : 1 ≤ y)
    (hpre : c.pre S Qa Qb L listed y = true)
    (hin : ∀ x, SolLo S Qa Qb L y x → (∃ b ∈ rootsOf8 S y c.c, ∃ k, x = b + c.t.step0 * k) →
      c.t.Xa ≤ x → x < c.t.Xb → x ∈ c.t.exc) : YStmt p S Qa Qb L listed y := by
  intro x q _ hS hq hqb h8 hj
  unfold pre at hpre
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Nat.beq_eq,
    Nat.ble_eq, Bool.or_eq_true, Nat.beq_eq, Nat.ble_eq, allL_iff] at hpre
  obtain ⟨hroots, hstep, hXb, hXa, hexc⟩ := hpre
  have hstep' : c.t.step0 = 8 * y * y := hstep
  have hXb' : S - Qa * y * y < c.t.Xb * c.t.Xb := hXb
  have hXa' : c.t.Xa = 0 ∨ (c.t.Xa - 1) * (c.t.Xa - 1) + Qb * y * y ≤ S := hXa
  have hsol : SolLo S Qa Qb L y x := ⟨q, hS, hq, hqb, h8, hj⟩
  have hmem := rootsOf8_complete_quot hroots x q hS h8
  have e8 : 8 * y ^ 2 = 8 * y * y := by ring
  rw [e8] at hmem
  have hx := hin x hsol
    ⟨_, hmem, x / (8 * y * y), by rw [hstep']; exact (Nat.mod_add_div x (8 * y * y)).symm⟩
    (hsol.ge hy hXa') (hsol.lt hXb')
  exact excOk_sound (hexc x hx) hS hy hj

/-- **Soundness of the certificate for one `y`, in one computation.** -/
theorem okE_sound {p S Qa Qb L y : ℕ} {listed : List ℕ} {c : XC} {extra : List Pat} (hy : 1 ≤ y)
    (he : ∀ pt ∈ extra, PatSound (SolLo S Qa Qb L y) c.t.stepF c.t.nmax pt)
    (h : c.okE S Qa Qb L listed y extra = true) : YStmt p S Qa Qb L listed y := by
  unfold okE at h
  rw [Bool.and_eq_true] at h
  exact sound_of hy h.1 fun x hx hb ha hxb =>
    Task.ok_sound (famX_sound S Qa Qb L y) he h.2 hx hb ha hxb

theorem ok_sound {p S Qa Qb L y : ℕ} {listed : List ℕ} {c : XC} (hy : 1 ≤ y)
    (h : c.ok S Qa Qb L listed y = true) : YStmt p S Qa Qb L listed y :=
  okE_sound hy (fun _ h => absurd h List.not_mem_nil) h

/-- **Soundness of the certificate for one `y`, cut into shards.** -/
theorem sound {p S Qa Qb L y : ℕ} {listed : List ℕ} {c : XC} {chunk m : ℕ} (hy : 1 ≤ y)
    (hh : c.header S Qa Qb L listed y chunk m = true) (hs : c.ShardsUpTo S L y chunk m) :
    YStmt p S Qa Qb L listed y := by
  unfold header at hh
  rw [Bool.and_eq_true] at hh
  exact sound_of hy hh.1 fun x hx hb ha hxb =>
    Task.sound (famX_sound S Qa Qb L y) (fun _ h => absurd h List.not_mem_nil) hh.2 hs hx hb ha hxb

end XC

/-! ## Table mode -/

theorem modEq_of_eq {S x q y : ℕ} (hS : S = x ^ 2 + q * y ^ 2) : x ^ 2 ≡ S [MOD y ^ 2] := by
  rw [hS]
  change x ^ 2 % y ^ 2 = (x ^ 2 + q * y ^ 2) % y ^ 2
  rw [Nat.add_mul_mod_self_right]

/-- Bit `r` is set iff `condB S l r`. -/
noncomputable def baseTab (S l : ℕ) : ℕ := mkBits l (condB S l)

/-- The fields `u < n` of `dilTab`. -/
noncomputable def dilAux (S l d n : ℕ) : ℕ :=
  Nat.rec 0 (fun u acc => Nat.lor acc (Nat.shiftLeft
    (tile l (mkBits l (fun j => tb (baseTab S l) (Nat.mod (Nat.mul u j) l))) d)
    (Nat.mul u (Nat.mul l (Nat.pow 2 d))))) n

/-- All the dilations of the table of `l`, tiled: the field number `u < l`, of `l * 2 ^ d` bits,
is the pattern `j ↦ condB S l (u * j % l)`. -/
noncomputable def dilTab (S l d : ℕ) : ℕ := dilAux S l d l

theorem dilAux_testBit {S l d n u i : ℕ} (hl : 0 < l) (hu : u < n) (hi : i < l * 2 ^ d)
    (hc : condB S l (u * (i % l) % l) = true) :
    (dilAux S l d n).testBit (u * (l * 2 ^ d) + i) = true := by
  induction n with
  | zero => omega
  | succ n ih =>
    have e : dilAux S l d (n + 1) = dilAux S l d n |||
        (tile l (mkBits l (fun j => tb (baseTab S l) (n * j % l))) d) <<< (n * (l * 2 ^ d)) := rfl
    rw [e, Nat.testBit_or]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hu with h | rfl
    · rw [ih h]
      rfl
    · rw [Nat.testBit_shiftLeft, Nat.add_sub_cancel_left]
      have h1 : (tile l (mkBits l (fun j => tb (baseTab S l) (u * j % l))) d).testBit i = true := by
        refine tile_keeps _ _ _ _ hl hi ?_
        refine mkBits_testBit (Nat.mod_lt _ hl) ?_
        rw [tb_eq]
        exact mkBits_testBit (Nat.mod_lt _ hl) hc
      rw [h1]
      simp

/-- The sieving primes of a range in table mode are primes `3 ≤ l < L`, `l < 400`. -/
noncomputable def tpOk (L : ℕ) (tp : List ℕ) : Bool :=
  allL (fun l => Bool.and (primeB l) (Bool.and (Nat.ble 3 l) (Nat.ble (Nat.succ l) L))) tp

/-- The patterns for `y` in table mode: for each prime `l` of `tp` that does not divide `y`, whose
tiling covers `l + nmax` bits, and for which the computed inverse of the step is one. -/
noncomputable def tabPats (S y d step nmax : ℕ) (tp : List ℕ) : List Pat :=
  List.rec []
    (fun l _ ih =>
      (fun inv : ℕ =>
        bif Bool.and (Bool.not (Nat.beq (Nat.mod y l) 0))
          (Bool.and (Nat.beq (Nat.mod (Nat.mul step inv) l) 1)
            (Nat.ble (Nat.add l nmax) (Nat.mul l (Nat.pow 2 d))))
        then (⟨l, inv, Nat.shiftRight (dilTab S l d)
          (Nat.mul (Nat.mod step l) (Nat.mul l (Nat.pow 2 d)))⟩ : Pat) :: ih
        else ih)
      (Nat.mod (Nat.pow (Nat.mod step l) (Nat.sub l 2)) l)) tp

theorem tabPats_cons (S y d step nmax l : ℕ) (tp : List ℕ) :
    tabPats S y d step nmax (l :: tp) =
      bif Bool.and (Bool.not (Nat.beq (y % l) 0))
          (Bool.and (Nat.beq (step * ((step % l) ^ (l - 2) % l) % l) 1)
            (Nat.ble (l + nmax) (l * 2 ^ d)))
      then (⟨l, (step % l) ^ (l - 2) % l,
        dilTab S l d >>> (step % l * (l * 2 ^ d))⟩ : Pat) :: tabPats S y d step nmax tp
      else tabPats S y d step nmax tp := rfl

theorem tabPats_sound {S Qa Qb L y d step nmax : ℕ} {tp : List ℕ} (htp : tpOk L tp = true) :
    ∀ pt ∈ tabPats S y d step nmax tp, PatSound (SolLo S Qa Qb L y) step nmax pt := by
  induction tp with
  | nil => intro pt h; exact absurd h List.not_mem_nil
  | cons l tp ih =>
    unfold tpOk at htp
    rw [allL_iff] at htp
    have ih' := ih (allL_iff.2 fun a ha => htp a (List.mem_cons_of_mem _ ha))
    intro pt hpt
    rw [tabPats_cons] at hpt
    cases hC : Bool.and (Bool.not (Nat.beq (y % l) 0))
        (Bool.and (Nat.beq (step * ((step % l) ^ (l - 2) % l) % l) 1)
          (Nat.ble (l + nmax) (l * 2 ^ d)))
    · rw [hC] at hpt
      exact ih' pt hpt
    · rw [hC] at hpt
      rcases List.mem_cons.1 hpt with rfl | hpt
      · have hC' : (!Nat.beq (y % l) 0 && (Nat.beq (step * ((step % l) ^ (l - 2) % l) % l) 1 &&
            Nat.ble (l + nmax) (l * 2 ^ d))) = true := hC
        rw [Bool.and_eq_true, Bool.and_eq_true, Bool.not_eq_true', Nat.beq_eq, Nat.ble_eq] at hC'
        obtain ⟨hy, hinv, hlen⟩ := hC'
        have hl := htp l List.mem_cons_self
        rw [Bool.and_eq_true, Bool.and_eq_true, Nat.ble_eq, Nat.ble_eq] at hl
        obtain ⟨hp, h3, hL⟩ := hl
        have hpr := primeB_sound hp
        rintro x base k ⟨q, hS, -, -, -, hj⟩ hxk hk
        change (dilTab S l d >>> (step % l * (l * 2 ^ d))).testBit
          (base * ((step % l) ^ (l - 2) % l) % l + k) = true
        rw [Nat.testBit_shiftRight]
        have hph : base * ((step % l) ^ (l - 2) % l) % l < l := Nat.mod_lt _ hpr.pos
        refine dilAux_testBit hpr.pos (Nat.mod_lt _ hpr.pos) (by omega) ?_
        have hx' : step % l * ((base * ((step % l) ^ (l - 2) % l) % l + k) % l) % l = x % l := by
          rw [Nat.mod_mul_mod, hxk]
          exact phase_mod hpr.pos hinv (Nat.mod_self l)
        rw [hx']
        refine condB_sound hS hpr h3 (fun hd => ?_) (hj l hpr h3 hL)
        have : Nat.beq (y % l) 0 = true := by
          rw [Nat.beq_eq]; exact Nat.mod_eq_zero_of_dvd hd
        rw [this] at hy
        exact Bool.noConfusion hy
      · exact ih' pt hpt

/-- The certificate for one `y` in table mode: the classes are those of the square roots of `S`
modulo `y ^ 2` (the condition `q ≡ 3 (mod 8)` is not used by the sieve, only for the survivors),
there is no wheel, and the patterns are the `tabPats` of the sieving primes of the range.
The fields `e2`, `s0`, `odd` are the certificate for the square roots (`XT.c`). -/
structure XT where
  e2 : ℕ
  s0 : ℕ
  odd : List ℕ
  Xa : ℕ
  Xb : ℕ
  exc : List ℕ
  wits : List ℕ

/-- The certificate for the square roots: `odd` is the flat list of the entries `l, e, r, inv`
of `Roots.OddEntry`, each preceded by a `0` (see `splitZ`). -/
noncomputable def XT.c (c : XT) : Cert :=
  ⟨c.e2, c.s0, mapR (fun g => (⟨gP g, gInv g, some (gD g), gP (gLs g)⟩ : OddEntry)) (splitZ c.odd)⟩

/-- The task of a certificate in table mode. -/
def XT.task (y : ℕ) (c : XT) : Task := ⟨Nat.mul y y, c.Xa, c.Xb, [], [], [], c.exc⟩

/-- Check of the certificate for one `y` in table mode. -/
noncomputable def XT.ok (S Qa Qb L : ℕ) (listed tp : List ℕ) (d y : ℕ) (c : XT) : Bool :=
  Bool.and (rootsOk S y c.c)
    (Bool.and (Nat.ble (Nat.succ (Nat.sub S (Nat.mul (Nat.mul Qa y) y))) (Nat.mul c.Xb c.Xb))
      (Bool.and
        (Bool.or (Nat.beq c.Xa 0)
          (Nat.ble (Nat.add (Nat.mul (Nat.sub c.Xa 1) (Nat.sub c.Xa 1))
            (Nat.mul (Nat.mul Qb y) y)) S))
        (Bool.and (allL (excOk8 S L y listed c.wits) c.exc)
          ((c.task y).ok (famX S L y)
            (tabPats S y d (c.task y).stepF (c.task y).nmax tp) (rootsOf S c.c)))))

theorem XT.ok_sound {p S Qa Qb L d y : ℕ} {listed tp : List ℕ} {c : XT} (hy : 1 ≤ y)
    (htp : tpOk L tp = true) (h : c.ok S Qa Qb L listed tp d y = true) :
    YStmt p S Qa Qb L listed y := by
  intro x q _ hS hq hqb h8 hj
  unfold XT.ok at h
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
    Nat.ble_eq, Bool.or_eq_true, Nat.beq_eq, Nat.ble_eq, allL_iff] at h
  obtain ⟨hroots, hXb, hXa, hexc, hok⟩ := h
  have hXb' : S - Qa * y * y < c.Xb * c.Xb := hXb
  have hXa' : c.Xa = 0 ∨ (c.Xa - 1) * (c.Xa - 1) + Qb * y * y ≤ S := hXa
  have hsol : SolLo S Qa Qb L y x := ⟨q, hS, hq, hqb, h8, hj⟩
  have hmem := rootsOf_complete hroots x (modEq_of_eq hS)
  have e2 : y ^ 2 = y * y := pow_two y
  rw [e2] at hmem
  have hx := Task.ok_sound (famX_sound S Qa Qb L y) (tabPats_sound htp) hok hsol
    ⟨_, hmem, x / (y * y), (Nat.mod_add_div x (y * y)).symm⟩
    (hsol.ge hy hXa') (hsol.lt hXb')
  exact excOk8_sound (hexc x hx) hS hy h8 hj

/-- The certificate for one `y`. -/
inductive YC where
  /-- `p ∣ y` -/
  | skip
  /-- an odd prime `l ∣ y` modulo which `S` is a quadratic non-residue -/
  | nonres (l : ℕ)
  /-- the 2-adic obstruction `Roots.noRootsTwo` -/
  | two
  /-- the sieve -/
  | full (c : XC)
  /-- the sieve in table mode -/
  | tab (c : XT)

/-- Check of the certificate for one `y`. -/
noncomputable def YC.ok (p S Qa Qb L : ℕ) (listed tp : List ℕ) (d y : ℕ) (c : YC) : Bool :=
  YC.rec (Nat.beq (Nat.mod y p) 0) (fun l => noRootsOdd S y l) (noRootsTwo S y)
    (fun c => c.ok S Qa Qb L listed y) (fun c => c.ok S Qa Qb L listed tp d y) c

theorem YC.ok_sound {p S Qa Qb L d y : ℕ} {listed tp : List ℕ} {c : YC} (hy : 1 ≤ y)
    (htp : tpOk L tp = true) (h : c.ok p S Qa Qb L listed tp d y = true) :
    YStmt p S Qa Qb L listed y := by
  cases c with
  | skip =>
    intro x q hpy
    have h' : Nat.beq (y % p) 0 = true := h
    rw [Nat.beq_eq] at h'
    exact absurd (Nat.dvd_of_mod_eq_zero h') hpy
  | nonres l =>
    intro x q _ hS
    have h' : noRootsOdd S y l = true := h
    exact absurd (modEq_of_eq hS) (noRoots_of_nonres h' x)
  | two =>
    intro x q _ hS
    have h' : noRootsTwo S y = true := h
    exact absurd (modEq_of_eq hS) (noRoots_two h' x)
  | full c =>
    have h' : c.ok S Qa Qb L listed y = true := h
    exact XC.ok_sound hy h'
  | tab c =>
    have h' : c.ok S Qa Qb L listed tp d y = true := h
    exact XT.ok_sound hy htp h'

/-- Check of the certificates `cs` for `y = y0 + 1, …, y1`; `tp` and `d` are the sieving primes
and the tiling depth of the certificates in table mode. -/
noncomputable def rangeOk (p S Qa Qb L : ℕ) (listed tp : List ℕ) (d y0 y1 : ℕ) (cs : List YC) :
    Bool :=
  Bool.and (tpOk L tp) (Bool.and (Nat.beq (Nat.add y0 (lenR cs)) y1)
    (List.rec (motive := fun _ => ℕ → Bool) (fun _ => true)
      (fun c _ ih y => Bool.and (YC.ok p S Qa Qb L listed tp d y c) (ih (Nat.succ y))) cs
      (Nat.succ y0)))

/-- The statement for `1 ≤ y ≤ n`. -/
def UpTo (p S Qa Qb L : ℕ) (listed : List ℕ) (n : ℕ) : Prop :=
  ∀ y, 1 ≤ y → y ≤ n → YStmt p S Qa Qb L listed y

theorem upTo_zero (p S Qa Qb L : ℕ) (listed : List ℕ) : UpTo p S Qa Qb L listed 0 :=
  fun y h1 h0 => by omega

theorem UpTo.succ {p S Qa Qb L n : ℕ} {listed : List ℕ} (h : UpTo p S Qa Qb L listed n)
    (hn : YStmt p S Qa Qb L listed (n + 1)) : UpTo p S Qa Qb L listed (n + 1) := by
  intro y h1 hy
  rcases Nat.lt_succ_iff_lt_or_eq.1 (Nat.lt_succ_of_le hy) with h' | rfl
  · exact h y h1 (Nat.lt_succ_iff.1 h')
  · exact hn

theorem rangeAux_sound {p S Qa Qb L d : ℕ} {listed tp : List ℕ} (htp : tpOk L tp = true)
    (cs : List YC) :
    ∀ n : ℕ, UpTo p S Qa Qb L listed n →
      List.rec (motive := fun _ => ℕ → Bool) (fun _ => true)
        (fun c _ ih y => Bool.and (YC.ok p S Qa Qb L listed tp d y c) (ih (Nat.succ y))) cs
        (Nat.succ n) = true →
      UpTo p S Qa Qb L listed (n + cs.length) := by
  induction cs with
  | nil => intro n h _; exact h
  | cons c cs ih =>
    intro n h hr
    have hr' : (YC.ok p S Qa Qb L listed tp d (n + 1) c &&
        List.rec (motive := fun _ => ℕ → Bool) (fun _ => true)
          (fun c _ ih y => Bool.and (YC.ok p S Qa Qb L listed tp d y c) (ih (Nat.succ y))) cs
          (Nat.succ (n + 1))) = true := hr
    rw [Bool.and_eq_true] at hr'
    have h1 := ih (n + 1) (h.succ (YC.ok_sound (by omega) htp hr'.1)) hr'.2
    have e : n + (c :: cs).length = n + 1 + cs.length := by
      rw [List.length_cons]; omega
    rw [e]
    exact h1

/-- **Soundness of a range of `y`.** -/
theorem UpTo.range {p S Qa Qb L d n n' : ℕ} {listed tp : List ℕ} {cs : List YC}
    (h : UpTo p S Qa Qb L listed n) (hr : rangeOk p S Qa Qb L listed tp d n n' cs = true) :
    UpTo p S Qa Qb L listed n' := by
  unfold rangeOk at hr
  rw [Bool.and_eq_true, Bool.and_eq_true, Nat.beq_eq, lenR_eq] at hr
  have e : n + cs.length = n' := hr.2.1
  rw [← e]
  exact rangeAux_sound hr.1 cs n h hr.2.2

/-- A prime is done for the range `Qa ≤ q < Qb` when `y ≤ Y` by the size condition and every
`1 ≤ y ≤ Y` is done. -/
theorem low_of_upTo {p Qa Qb Y : ℕ} {listed : List ℕ} (hY : 4 * p ^ 7 < Qa * (Y + 1) ^ 2)
    (h : UpTo p (4 * p ^ 7) Qa Qb p listed Y) : LowStatement p Qa Qb listed :=
  fun x y q hy hpy hS hq hqb h8 hj => h y hy (y_le hY hS hq) x q hpy hS hq hqb h8 hj

end Exp7.SieveLow
