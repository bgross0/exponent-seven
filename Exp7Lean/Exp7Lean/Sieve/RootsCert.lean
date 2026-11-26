import Mathlib
import Exp7Lean.Sieve.RootsBasic
import Exp7Lean.Sieve.RootsCRT
import Exp7Lean.Sieve.RootsTwo

/-!
# Certified enumeration of the square roots of `S` modulo `y ^ 2`

A certificate `Cert` for `(S, y)` consists of

* `e2` : the exponent of `2` in `y`;
* `s0` : when `e2 ≥ 3` and `S / 4 ≡ 1 (mod 8)`, a root of `s ^ 2 ≡ S / 4 (mod 2 ^ (2 * e2 - 2))`
  (ignored otherwise);
* `odd` : the odd prime powers `l ^ e ∥ y`, in some order, each with
  - `r = some r₀` where `r₀ ^ 2 ≡ S (mod l ^ (2 * e))`, together with `inv`, an inverse modulo
    `l ^ (2 * e)` of the product `M` of `2 ^ (2 * e2)` and the preceding `l' ^ (2 * e')`; or
  - `r = none`, claiming that `S` is a quadratic non-residue modulo `l` (`inv` is ignored).

`rootsOk S y cert` checks the certificate (primality by `isOddPrimeF`, roots by squaring,
non-residues by Euler's criterion, coprimality through the supplied inverses, product of the
prime powers equal to `y ^ 2`); `rootsOf S cert` lists the residues modulo `y ^ 2`.

Main results: `rootsOf_complete`, `rootsOf_complete_int`, `rootsOf_complete_dvd`,
`rootsOf_complete_with`, `rootsOf_sound`, `mem_rootsOf_iff`, `rootsOf8_complete`,
`noRoots_of_nonres`, `noRoots_two`, `yRoots_complete`.
The 2-part requires `S ≡ 4 (mod 8)` whenever `y` is even (as for `S = 4 * p ^ 7`, `p` odd);
every odd prime `l ∣ y` with a claimed root must satisfy `l ∤ S`.
-/

namespace Exp7.Roots

/-- An odd prime power `l ^ e ∥ y` with a square root `r` of `S` modulo `l ^ (2 * e)` and an
inverse `inv` of the previously accumulated modulus, or `r = none` if `S` is a quadratic
non-residue modulo `l`. -/
structure OddEntry where
  l : ℕ
  e : ℕ
  r : Option ℕ
  inv : ℕ
  deriving Repr

/-- Certificate for the square roots of `S` modulo `y ^ 2`. -/
structure Cert where
  e2 : ℕ
  s0 : ℕ
  odd : List OddEntry
  deriving Repr

/-! ## The 2-part -/

/-- Roots of `S` modulo `2 ^ (2 * e2)` (for `S ≡ 4 (mod 8)` when `e2 ≥ 1`). -/
def twoList (S : ℕ) : ℕ → ℕ → List ℕ
  | 0, _ => [0]
  | e + 1, s0 => liftTwo (2 * e) (twoRootsOdd (S / 4) (2 * e) s0)

/-- Check for the 2-part of the certificate. -/
def twoOk (S : ℕ) : ℕ → ℕ → Bool
  | 0, _ => true
  | e + 1, s0 => (S % 8).beq 4 && twoRootsOddOk (S / 4) (2 * e) s0

theorem twoList_complete {S e2 s0 : ℕ} (h : twoOk S e2 s0 = true) :
    Complete (2 ^ (2 * e2)) S (twoList S e2 s0) := by
  match e2, h with
  | 0, _ =>
    intro x _
    simp [twoList, Nat.mod_one]
  | e + 1, h =>
    simp only [twoOk, Bool.and_eq_true] at h
    obtain ⟨h8, hok⟩ := h
    have h8' : S % 8 = 4 := Nat.eq_of_beq_eq_true h8
    have hu : (S / 4) % 2 = 1 := by omega
    have hS : 4 * (S / 4) = S := by omega
    have := (complete_twoRootsOdd hu hok).liftTwo
    rw [hS] at this
    have e2 : 2 * (e + 1) = 2 * e + 2 := by ring
    rw [e2]
    exact this

/-! ## The odd part

The recursive functions below are written with raw recursors (`List.rec`, `Option.rec`,
`Bool.rec`) and raw `Nat` operations: the kernel reduces these several times faster than the
output of the equation compiler.  Each comes with readable equations (`*_nil`, `*_cons`, …). -/

/-- The modulus `l ^ (2 * e)` of an entry. -/
def OddEntry.q (en : OddEntry) : ℕ := Nat.pow en.l (Nat.mul (nat_lit 2) en.e)

theorem OddEntry.q_eq (en : OddEntry) : en.q = en.l ^ (2 * en.e) := rfl

/-- Checks for one odd prime power, apart from the primality of `l`: `e ≥ 1` and either
(`r = some r₀`) `l ∤ S`, `inv * M ≡ 1 (mod l ^ (2 * e))` for the modulus `M` accumulated so
far, and `r₀ ^ 2 ≡ S (mod l ^ (2 * e))`; or (`r = none`) Euler's test certifies a non-residue.
See `entryCore_eq_none`, `entryCore_eq_some`. -/
def entryCore (S M : ℕ) (en : OddEntry) : Bool :=
  Bool.rec false
    (Option.rec (motive := fun _ => Bool) (eulerNonRes S en.l)
      (fun r =>
        Bool.rec
          (Bool.rec false (Nat.beq (Nat.mod (Nat.mul r r) en.q) (Nat.mod S en.q))
            (Nat.beq (Nat.mod (Nat.mul en.inv M) en.q) (nat_lit 1)))
          false (Nat.beq (Nat.mod S en.l) (nat_lit 0)))
      en.r)
    (Nat.ble (nat_lit 1) en.e)

private theorem andChain (A B C X : Bool) :
    (Bool.rec false (Bool.rec (Bool.rec false X B) false A) C : Bool) =
      (C && (!A && (B && X))) := by
  cases A <;> cases B <;> cases C <;> rfl

theorem entryCore_eq_none {S M : ℕ} {en : OddEntry} (h : en.r = none) :
    entryCore S M en = (Nat.ble 1 en.e && eulerNonRes S en.l) := by
  unfold entryCore
  rw [h]
  exact boolRec_false_eq_and _ _

theorem entryCore_eq_some {S M : ℕ} {en : OddEntry} {r : ℕ} (h : en.r = some r) :
    entryCore S M en = (Nat.ble 1 en.e && (!(S % en.l).beq 0 &&
      (((en.inv * M) % (en.l ^ (2 * en.e))).beq 1 &&
        (r * r % (en.l ^ (2 * en.e))).beq (S % (en.l ^ (2 * en.e)))))) := by
  unfold entryCore
  rw [h]
  exact andChain _ _ _ _

/-- Final modulus: `M` times the product of all `l ^ (2 * e)`. -/
def modAux (M : ℕ) (es : List OddEntry) : ℕ :=
  List.rec (motive := fun _ => ℕ → ℕ) (fun M => M) (fun en _ ih M => ih (Nat.mul M en.q)) es M

theorem modAux_nil (M : ℕ) : modAux M [] = M := rfl

theorem modAux_cons (M : ℕ) (en : OddEntry) (es : List OddEntry) :
    modAux M (en :: es) = modAux (M * en.l ^ (2 * en.e)) es := rfl

/-- Check of all odd entries, starting from modulus `M`. -/
def oddOkCore (S M : ℕ) (es : List OddEntry) : Bool :=
  List.rec (motive := fun _ => ℕ → Bool) (fun _ => true)
    (fun en _ ih M => Bool.rec false (ih (Nat.mul M en.q)) (entryCore S M en)) es M

theorem oddOkCore_cons (S M : ℕ) (en : OddEntry) (es : List OddEntry) :
    oddOkCore S M (en :: es) = (entryCore S M en && oddOkCore S (M * en.l ^ (2 * en.e)) es) :=
  boolRec_false_eq_and (entryCore S M en) (oddOkCore S (M * en.l ^ (2 * en.e)) es)

/-- CRT-combine a list `L` of residues modulo `M` with the roots `±r` of all entries; a
non-residue entry makes the list empty. -/
def rootsAux (M : ℕ) (L : List ℕ) (es : List OddEntry) : List ℕ :=
  List.rec (motive := fun _ => ℕ → List ℕ → List ℕ) (fun _ L => L)
    (fun en _ ih M L =>
      Option.rec (motive := fun _ => List ℕ) []
        (fun r => ih (Nat.mul M en.q)
          (crtPair M en.q en.inv (Nat.mod r en.q) (Nat.sub en.q (Nat.mod r en.q)) L))
        en.r)
    es M L

theorem rootsAux_nil (M : ℕ) (L : List ℕ) : rootsAux M L [] = L := rfl

theorem rootsAux_cons_none {M : ℕ} {L : List ℕ} {en : OddEntry} {es : List OddEntry}
    (h : en.r = none) : rootsAux M L (en :: es) = [] := by
  change Option.rec (motive := fun _ => List ℕ) [] _ en.r = _
  rw [h]

theorem rootsAux_cons_some {M : ℕ} {L : List ℕ} {en : OddEntry} {es : List OddEntry} {r : ℕ}
    (h : en.r = some r) : rootsAux M L (en :: es) =
      rootsAux (M * en.l ^ (2 * en.e))
        (crtPair M (en.l ^ (2 * en.e)) en.inv (r % en.l ^ (2 * en.e))
          (en.l ^ (2 * en.e) - r % en.l ^ (2 * en.e)) L) es := by
  change Option.rec (motive := fun _ => List ℕ) []
    (fun r => rootsAux (M * en.l ^ (2 * en.e))
        (crtPair M (en.l ^ (2 * en.e)) en.inv (r % en.l ^ (2 * en.e))
          (en.l ^ (2 * en.e) - r % en.l ^ (2 * en.e)) L) es) en.r = _
  rw [h]

theorem dvd_modAux : ∀ (es : List OddEntry) (M : ℕ), M ∣ modAux M es := by
  intro es
  induction es with
  | nil => intro M; exact dvd_rfl
  | cons en es ih => intro M; rw [modAux_cons]; exact (Dvd.intro _ rfl).trans (ih _)

theorem Complete.of_dvd_nil {m n a : ℕ} (h : Complete m a []) (hd : m ∣ n) (L : List ℕ) :
    Complete n a L := fun x hx => absurd (h x (hx.of_dvd hd)) List.not_mem_nil

theorem entryCore_none {S M : ℕ} {en : OddEntry} (hl : en.l.Prime) (hodd : en.l ≠ 2)
    (hr : en.r = none) (h : entryCore S M en = true) :
    Complete (en.l ^ (2 * en.e)) S [] := by
  rw [entryCore_eq_none hr] at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨he, hE⟩ := h
  have he' : 1 ≤ en.e := by simpa using he
  exact complete_of_eulerNonRes hl hodd hE (by omega)

theorem entryCore_some {S M : ℕ} {en : OddEntry} {r : ℕ} (hl : en.l.Prime) (hodd : en.l ≠ 2)
    (hr : en.r = some r) (h : entryCore S M en = true) :
    0 < en.l ^ (2 * en.e) ∧
    en.inv * M % (en.l ^ (2 * en.e)) = 1 % (en.l ^ (2 * en.e)) ∧
    Complete (en.l ^ (2 * en.e)) S
      [r % en.l ^ (2 * en.e), en.l ^ (2 * en.e) - r % en.l ^ (2 * en.e)] := by
  rw [entryCore_eq_some hr] at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨he, hS, hinv, hrr⟩ := h
  have he' : 1 ≤ en.e := by simpa using he
  have hk : 1 ≤ 2 * en.e := by omega
  have hS' : ¬ en.l ∣ S := by
    intro hd
    have : S % en.l = 0 := Nat.mod_eq_zero_of_dvd hd
    rw [this] at hS
    simp at hS
  have hq : 0 < en.l ^ (2 * en.e) := Nat.pow_pos hl.pos
  have hq1 : 1 < en.l ^ (2 * en.e) := Nat.one_lt_pow (by omega) hl.one_lt
  refine ⟨hq, ?_, ?_⟩
  · rw [Nat.eq_of_beq_eq_true hinv, Nat.mod_eq_of_lt hq1]
  · have hr2 : r ^ 2 ≡ S [MOD en.l ^ (2 * en.e)] := by
      rw [pow_two]; exact Nat.eq_of_beq_eq_true hrr
    exact complete_odd_prime_pow hl hodd hk hS' hr2

theorem rootsAux_complete (S : ℕ) : ∀ (es : List OddEntry) (M : ℕ) (L : List ℕ), 0 < M →
    Complete M S L → (∀ en ∈ es, en.l.Prime ∧ en.l ≠ 2) → oddOkCore S M es = true →
    Complete (modAux M es) S (rootsAux M L es) := by
  intro es
  induction es with
  | nil => intro M L _ hL _ _; exact hL
  | cons en es ih =>
    intro M L hM hL hp hok
    rw [oddOkCore_cons, Bool.and_eq_true] at hok
    obtain ⟨hen, hrest⟩ := hok
    obtain ⟨hl, hodd⟩ := hp en List.mem_cons_self
    cases hr : en.r with
    | none =>
      have hloc := entryCore_none hl hodd hr hen
      rw [modAux_cons, rootsAux_cons_none hr]
      exact hloc.of_dvd_nil ((Dvd.intro_left M rfl).trans (dvd_modAux es _)) []
    | some r =>
      obtain ⟨hq, hinv, hloc⟩ := entryCore_some hl hodd hr hen
      rw [modAux_cons, rootsAux_cons_some hr, crtPair_eq_crtList]
      exact ih _ _ (Nat.mul_pos hM hq) (hL.crt hM hq hinv hloc)
        (fun en' h' => hp en' (List.mem_cons_of_mem _ h')) hrest

/-! ## Packaging -/

/-- The residues modulo `y ^ 2` of all `x` with `x ^ 2 ≡ S (mod y ^ 2)`. -/
def rootsOf (S : ℕ) (c : Cert) : List ℕ :=
  rootsAux (2 ^ (2 * c.e2)) (twoList S c.e2 c.s0) c.odd

/-- Certificate check without the primality tests (see `rootsOf_complete_core`). -/
def rootsOkCore (S y : ℕ) (c : Cert) : Bool :=
  twoOk S c.e2 c.s0 && oddOkCore S (2 ^ (2 * c.e2)) c.odd &&
  (modAux (2 ^ (2 * c.e2)) c.odd).beq (y * y)

/-- Primality test `isP` applied to all primes of a certificate. -/
def primesOkWith (isP : ℕ → Bool) (es : List OddEntry) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun en _ ih => Bool.rec false ih (isP en.l)) es

theorem primesOkWith_cons (isP : ℕ → Bool) (en : OddEntry) (es : List OddEntry) :
    primesOkWith isP (en :: es) = (isP en.l && primesOkWith isP es) :=
  boolRec_false_eq_and (isP en.l) (primesOkWith isP es)

/-- Certificate check with a user-supplied odd-primality test `isP`
(e.g. a lookup in a verified table). -/
def rootsOkWith (isP : ℕ → Bool) (S y : ℕ) (c : Cert) : Bool :=
  primesOkWith isP c.odd && rootsOkCore S y c

/-- Full certificate check, using the built-in primality test `isOddPrimeF`. -/
def rootsOk (S y : ℕ) (c : Cert) : Bool := rootsOkWith isOddPrimeF S y c

/-- Completeness, with primality of the certificate's primes supplied as a hypothesis. -/
theorem rootsOf_complete_core {S y : ℕ} {c : Cert} (h : rootsOkCore S y c = true)
    (hp : ∀ en ∈ c.odd, en.l.Prime ∧ en.l ≠ 2) :
    ∀ x : ℕ, x ^ 2 ≡ S [MOD y ^ 2] → x % y ^ 2 ∈ rootsOf S c := by
  unfold rootsOkCore at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨h2, hodd⟩, hmod⟩ := h
  have hy : modAux (2 ^ (2 * c.e2)) c.odd = y ^ 2 := by
    rw [pow_two]; exact Nat.eq_of_beq_eq_true hmod
  have := rootsAux_complete S c.odd (2 ^ (2 * c.e2)) (twoList S c.e2 c.s0)
    (Nat.pow_pos (by norm_num)) (twoList_complete h2) hp hodd
  rw [hy] at this
  exact this

theorem primesOkWith_sound {isP : ℕ → Bool} (hP : ∀ l, isP l = true → l.Prime ∧ l ≠ 2) :
    ∀ es : List OddEntry, primesOkWith isP es = true → ∀ en ∈ es, en.l.Prime ∧ en.l ≠ 2 := by
  intro es
  induction es with
  | nil => intro _ en hen; exact absurd hen List.not_mem_nil
  | cons a es ih =>
    intro h en hen
    rw [primesOkWith_cons, Bool.and_eq_true] at h
    rcases List.mem_cons.mp hen with h1 | h1
    · rw [h1]; exact hP _ h.1
    · exact ih h.2 en h1

/-- Completeness for a user-supplied sound odd-primality test. -/
theorem rootsOf_complete_with {isP : ℕ → Bool} (hP : ∀ l, isP l = true → l.Prime ∧ l ≠ 2)
    {S y : ℕ} {c : Cert} (h : rootsOkWith isP S y c = true) :
    ∀ x : ℕ, x ^ 2 ≡ S [MOD y ^ 2] → x % y ^ 2 ∈ rootsOf S c := by
  unfold rootsOkWith at h
  rw [Bool.and_eq_true] at h
  exact rootsOf_complete_core h.2 (primesOkWith_sound hP _ h.1)

/-- **Main theorem.** If the certificate checks, every natural `x` with
`x ^ 2 ≡ S (mod y ^ 2)` has its residue modulo `y ^ 2` in `rootsOf S cert`. -/
theorem rootsOf_complete {S y : ℕ} {c : Cert} (h : rootsOk S y c = true) :
    ∀ x : ℕ, x ^ 2 ≡ S [MOD y ^ 2] → x % y ^ 2 ∈ rootsOf S c :=
  rootsOf_complete_with (fun _ => isOddPrimeF_sound) h

/-- Integer-divisibility form: `y ^ 2 ∣ S - x ^ 2` in `ℤ`. -/
theorem rootsOf_complete_int {S y : ℕ} {c : Cert} (h : rootsOk S y c = true) (x : ℕ)
    (hx : (y : ℤ) ^ 2 ∣ (S : ℤ) - (x : ℤ) ^ 2) : x % y ^ 2 ∈ rootsOf S c := by
  apply rootsOf_complete h
  rw [Nat.modEq_iff_dvd]
  push_cast
  exact hx

/-- Natural-subtraction form: `y ^ 2 ∣ S - x ^ 2` with `x ^ 2 ≤ S`. -/
theorem rootsOf_complete_dvd {S y : ℕ} {c : Cert} (h : rootsOk S y c = true) (x : ℕ)
    (hle : x ^ 2 ≤ S) (hx : y ^ 2 ∣ S - x ^ 2) : x % y ^ 2 ∈ rootsOf S c :=
  rootsOf_complete h x ((Nat.modEq_iff_dvd' hle).mpr hx)

/-! ## Soundness of the list (optional run-time check) -/

/-- Every element of `L` is a reduced root of `S` modulo `y ^ 2`. -/
def rootsSoundB (S y : ℕ) (L : List ℕ) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun r _ ih =>
      Bool.rec false
        (Bool.rec false ih
          (Nat.beq (Nat.mod (Nat.mul r r) (Nat.mul y y)) (Nat.mod S (Nat.mul y y))))
        (Nat.ble (Nat.succ r) (Nat.mul y y)))
    L

theorem rootsSoundB_cons (S y r : ℕ) (L : List ℕ) : rootsSoundB S y (r :: L) =
    (Nat.blt r (y * y) && ((r * r % (y * y)).beq (S % (y * y)) && rootsSoundB S y L)) := by
  change Bool.rec (motive := fun _ => Bool) false
    (Bool.rec (motive := fun _ => Bool) false (rootsSoundB S y L)
      ((r * r % (y * y)).beq (S % (y * y)))) (Nat.blt r (y * y)) = _
  rw [boolRec_false_eq_and, boolRec_false_eq_and]

theorem rootsOf_sound {S y : ℕ} {L : List ℕ} (h : rootsSoundB S y L = true) :
    ∀ r ∈ L, r < y ^ 2 ∧ r ^ 2 ≡ S [MOD y ^ 2] := by
  induction L with
  | nil => intro r hr; exact absurd hr List.not_mem_nil
  | cons a tl ih =>
    intro r hr
    rw [rootsSoundB_cons] at h
    simp only [Bool.and_eq_true] at h
    obtain ⟨h1, h2, h3⟩ := h
    rcases List.mem_cons.mp hr with h4 | h4
    · subst h4
      rw [pow_two, pow_two]
      exact ⟨by simpa using h1, Nat.eq_of_beq_eq_true h2⟩
    · exact ih h3 r h4

/-- With both checks, `rootsOf` is exactly the set of roots. -/
theorem mem_rootsOf_iff {S y : ℕ} {c : Cert} (h : rootsOk S y c = true)
    (hs : rootsSoundB S y (rootsOf S c) = true) (x : ℕ) :
    x % y ^ 2 ∈ rootsOf S c ↔ x ^ 2 ≡ S [MOD y ^ 2] := by
  refine ⟨fun hx => ?_, rootsOf_complete h x⟩
  have h1 := (rootsOf_sound hs _ hx).2
  exact ((Nat.mod_modEq x (y ^ 2)).pow 2).symm.trans h1

/-! ## Quick non-existence tests -/

/-- If an odd prime `l ∣ y` has `S` as a non-residue, there are no roots at all. -/
def noRootsOdd (S y l : ℕ) : Bool := isOddPrimeF l && (y % l).beq 0 && eulerNonRes S l

theorem noRoots_of_nonres {S y l : ℕ} (h : noRootsOdd S y l = true) (x : ℕ) :
    ¬ x ^ 2 ≡ S [MOD y ^ 2] := by
  unfold noRootsOdd at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨hp, hy⟩, hE⟩ := h
  obtain ⟨hl, hodd⟩ := isOddPrimeF_sound hp
  have hdvd : l ∣ y := Nat.dvd_of_mod_eq_zero (Nat.eq_of_beq_eq_true hy)
  intro hx
  have h1 : x ^ 2 ≡ S [MOD l ^ 1] := by
    rw [pow_one]; exact hx.of_dvd (hdvd.trans (dvd_pow_self y two_ne_zero))
  exact not_sq_of_eulerNonRes hl hodd hE (le_refl 1) x h1

/-- 2-adic obstruction for `S = 4 * u`, `u` odd: `4 ∣ y` forces `u ≡ 1 (mod 4)` and
`8 ∣ y` forces `u ≡ 1 (mod 8)`. -/
def noRootsTwo (S y : ℕ) : Bool :=
  (S % 8).beq 4 &&
  (((y % 4).beq 0 && !((S / 4) % 4).beq 1) || ((y % 8).beq 0 && !((S / 4) % 8).beq 1))

theorem noRoots_two {S y : ℕ} (h : noRootsTwo S y = true) (x : ℕ) :
    ¬ x ^ 2 ≡ S [MOD y ^ 2] := by
  unfold noRootsTwo at h
  simp only [Bool.and_eq_true, Bool.or_eq_true] at h
  obtain ⟨h8, hc⟩ := h
  have h8' : S % 8 = 4 := Nat.eq_of_beq_eq_true h8
  have hu : (S / 4) % 2 = 1 := by omega
  have hS : 4 * (S / 4) = S := by omega
  intro hx
  rcases hc with ⟨hy, hu4⟩ | ⟨hy, hu8⟩
  · have hdvd : 2 ^ 2 ∣ y := Nat.dvd_of_mod_eq_zero (Nat.eq_of_beq_eq_true hy)
    have h1 : x ^ 2 ≡ 4 * (S / 4) [MOD 2 ^ (2 + 2)] := by
      rw [hS]
      refine hx.of_dvd ?_
      have := pow_dvd_pow_of_dvd hdvd 2
      rwa [← pow_mul] at this
    obtain ⟨s, _, hs⟩ := (sq_modEq_four_mul_two_pow _ _ _).mp h1
    refine not_sq_two_pow_of_mod_four hu (le_refl 2) ?_ s hs
    intro h4
    rw [h4] at hu4
    simp at hu4
  · have hdvd : 2 ^ 3 ∣ y := Nat.dvd_of_mod_eq_zero (Nat.eq_of_beq_eq_true hy)
    have h1 : x ^ 2 ≡ 4 * (S / 4) [MOD 2 ^ (4 + 2)] := by
      rw [hS]
      refine hx.of_dvd ?_
      have := pow_dvd_pow_of_dvd hdvd 2
      rwa [← pow_mul] at this
    obtain ⟨s, _, hs⟩ := (sq_modEq_four_mul_two_pow _ _ _).mp h1
    refine not_sq_two_pow_of_mod_eight hu (by norm_num) ?_ s hs
    intro h4
    rw [h4] at hu8
    simp at hu8

/-! ## A uniform per-`y` certificate with fast paths for "no roots" -/

/-- Certificate for one `y`: a cheap reason why `x ^ 2 ≡ S (mod y ^ 2)` has no solution, or a
full `Cert`. -/
inductive YCert where
  /-- an odd prime `l ∣ y` modulo which `S` is a quadratic non-residue -/
  | nonres (l : ℕ)
  /-- the 2-adic obstruction `noRootsTwo` -/
  | two
  /-- a full certificate -/
  | roots (c : Cert)
  deriving Repr

/-- Check of a `YCert`. -/
def yOk (S y : ℕ) : YCert → Bool
  | .nonres l => noRootsOdd S y l
  | .two => noRootsTwo S y
  | .roots c => rootsOk S y c

/-- The list of roots modulo `y ^ 2` described by a `YCert`. -/
def yRoots (S : ℕ) : YCert → List ℕ
  | .nonres _ => []
  | .two => []
  | .roots c => rootsOf S c

/-- Completeness for `YCert`. -/
theorem yRoots_complete {S y : ℕ} {c : YCert} (h : yOk S y c = true) :
    ∀ x : ℕ, x ^ 2 ≡ S [MOD y ^ 2] → x % y ^ 2 ∈ yRoots S c := by
  intro x hx
  cases c with
  | nonres l => exact absurd hx (noRoots_of_nonres h x)
  | two => exact absurd hx (noRoots_two h x)
  | roots c => exact rootsOf_complete h x hx

/-! ## Refinement modulo `8 * y ^ 2` -/

/-- `x :: acc` if `b`, else `acc`. -/
def consIf (b : Bool) (x : ℕ) (acc : List ℕ) : List ℕ :=
  Bool.rec (motive := fun _ => List ℕ) acc (x :: acc) b

theorem mem_consIf_of_mem {b : Bool} {x z : ℕ} {acc : List ℕ} (h : z ∈ acc) :
    z ∈ consIf b x acc := by
  cases b
  · exact h
  · exact List.mem_cons_of_mem _ h

theorem mem_consIf_self {x : ℕ} {acc : List ℕ} : x ∈ consIf true x acc :=
  List.mem_cons_self

/-- Prepend to `acc` the lifts `r + m * t`, `t < c`, that satisfy `P` (raw recursor for
kernel speed; see `liftF_succ`). -/
def liftF (P : ℕ → Bool) (m r c : ℕ) : List ℕ → List ℕ :=
  Nat.rec (motive := fun _ => List ℕ → List ℕ) (fun acc => acc)
    (fun t ih acc =>
      ih (consIf (P (Nat.add r (Nat.mul m t))) (Nat.add r (Nat.mul m t)) acc)) c

theorem liftF_succ (P : ℕ → Bool) (m r c : ℕ) (acc : List ℕ) :
    liftF P m r (c + 1) acc = liftF P m r c (consIf (P (r + m * c)) (r + m * c) acc) := rfl

theorem mem_liftF_of_mem {P : ℕ → Bool} {m r z : ℕ} : ∀ (c : ℕ) (acc : List ℕ), z ∈ acc →
    z ∈ liftF P m r c acc := by
  intro c
  induction c with
  | zero => intro acc h; exact h
  | succ c ih => intro acc h; rw [liftF_succ]; exact ih _ (mem_consIf_of_mem h)

theorem mem_liftF {P : ℕ → Bool} {m r : ℕ} : ∀ (c : ℕ) (acc : List ℕ) (t : ℕ), t < c →
    P (r + m * t) = true → r + m * t ∈ liftF P m r c acc := by
  intro c
  induction c with
  | zero => intro _ t ht; omega
  | succ c ih =>
    intro acc t ht hP
    rw [liftF_succ]
    rcases Nat.lt_succ_iff_lt_or_eq.mp ht with h1 | h1
    · exact ih _ t h1 hP
    · subst h1
      rw [hP]
      exact mem_liftF_of_mem _ _ mem_consIf_self

/-- All lifts `r + m * t` (`r ∈ L`, `t < c`) that satisfy `P`. -/
def liftAll (P : ℕ → Bool) (m c : ℕ) (L : List ℕ) : List ℕ :=
  List.rec (motive := fun _ => List ℕ) [] (fun r _ ih => liftF P m r c ih) L

theorem mem_liftAll {P : ℕ → Bool} {m c r t : ℕ} {L : List ℕ} (hr : r ∈ L) (ht : t < c)
    (hP : P (r + m * t) = true) : r + m * t ∈ liftAll P m c L := by
  induction L with
  | nil => exact absurd hr List.not_mem_nil
  | cons a tl ih =>
    change r + m * t ∈ liftF P m a c (liftAll P m c tl)
    rcases List.mem_cons.mp hr with h1 | h1
    · subst h1; exact mem_liftF _ _ t ht hP
    · exact mem_liftF_of_mem _ _ (ih h1)

/-- Residues modulo `8 * y ^ 2` of the `x` with `x ^ 2 ≡ S - 3 * y ^ 2 (mod 8 * y ^ 2)`,
i.e. with `S - x ^ 2 = q * y ^ 2` and `q ≡ 3 (mod 8)`. -/
def rootsOf8 (S y : ℕ) (c : Cert) : List ℕ :=
  liftAll (fun x => Nat.beq (Nat.mod (Nat.mul x x) (y * y * 8)) ((S + 5 * (y * y)) % (y * y * 8)))
    (y * y) 8 (rootsOf S c)

/-- Completeness modulo `8 * y ^ 2` for the condition `x ^ 2 + 3 * y ^ 2 ≡ S`. -/
theorem rootsOf8_complete {S y : ℕ} {c : Cert} (h : rootsOk S y c = true) (x : ℕ)
    (hx : x ^ 2 + 3 * y ^ 2 ≡ S [MOD 8 * y ^ 2]) : x % (8 * y ^ 2) ∈ rootsOf8 S y c := by
  have eN : 8 * y ^ 2 = y * y * 8 := by ring
  rw [eN] at hx ⊢
  have hx1 : x ^ 2 ≡ S [MOD y ^ 2] := by
    have h1 : x ^ 2 + 3 * y ^ 2 ≡ S [MOD y ^ 2] := hx.of_dvd ⟨8, by ring⟩
    have h2 : x ^ 2 + 3 * y ^ 2 ≡ x ^ 2 [MOD y ^ 2] := by
      simp [Nat.ModEq]
    exact h2.symm.trans h1
  have hmem : x % (y * y) ∈ rootsOf S c := by
    rw [← pow_two]; exact rootsOf_complete h x hx1
  have h3 : x ^ 2 + 3 * y ^ 2 + 5 * (y * y) ≡ S + 5 * (y * y) [MOD y * y * 8] :=
    hx.add_right _
  have h4 : x ^ 2 + 3 * y ^ 2 + 5 * (y * y) = x * x + y * y * 8 := by ring
  have h5 : x * x + y * y * 8 ≡ x * x [MOD y * y * 8] := by simp [Nat.ModEq]
  have h6 : x % (y * y * 8) * (x % (y * y * 8)) ≡ x * x [MOD y * y * 8] :=
    (Nat.mod_modEq _ _).mul (Nat.mod_modEq _ _)
  rw [h4] at h3
  have h7 : x % (y * y * 8) * (x % (y * y * 8)) ≡ S + 5 * (y * y) [MOD y * y * 8] :=
    h6.trans (h5.symm.trans h3)
  have h8 : (x % (y * y * 8) * (x % (y * y * 8))) % (y * y * 8)
      = (S + 5 * (y * y)) % (y * y * 8) := h7
  have e : x % (y * y * 8) = x % (y * y) + y * y * (x / (y * y) % 8) := Nat.mod_mul
  unfold rootsOf8
  rw [e] at h8 ⊢
  refine mem_liftAll hmem (Nat.mod_lt _ (by norm_num)) ?_
  change Nat.beq ((x % (y * y) + y * y * (x / (y * y) % 8)) *
    (x % (y * y) + y * y * (x / (y * y) % 8)) % (y * y * 8)) _ = true
  rw [h8]
  exact Nat.beq_refl _

/-- Completeness modulo `8 * y ^ 2`, quotient form: `S = x ^ 2 + q * y ^ 2`, `q ≡ 3 (mod 8)`. -/
theorem rootsOf8_complete_quot {S y : ℕ} {c : Cert} (h : rootsOk S y c = true) (x q : ℕ)
    (hq : S = x ^ 2 + q * y ^ 2) (hq8 : q % 8 = 3) : x % (8 * y ^ 2) ∈ rootsOf8 S y c := by
  apply rootsOf8_complete h
  have e : q = 8 * (q / 8) + 3 := by omega
  rw [hq, e]
  have e2 : x ^ 2 + (8 * (q / 8) + 3) * y ^ 2 = x ^ 2 + 3 * y ^ 2 + 8 * y ^ 2 * (q / 8) := by
    ring
  rw [e2]
  simp [Nat.ModEq]

end Exp7.Roots
