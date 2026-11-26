import Exp7Lean.SieveKernel

/-!
# Bridge from the packed-bitset sieve to the number-theoretic search statement

Fix `S` (`= 4 p ^ 7`), a lower bound `Q` for `q`, and a bound `L` (`= p`) for the primes `l` whose
Jacobi symbol is prescribed.  For a fixed `y`, `Sol S Q L y x` says that `x` solves
`S = x ^ 2 + q * y ^ 2` for some `q ≥ Q`, `q ≡ 3 (mod 8)`, with `(-q / l) = -1` for all primes
`3 ≤ l < L`.

The checker excludes all `x` as follows.

* **Necessary conditions.**  `condA`: for `m ∣ 8 y ^ 2`, `x ^ 2 + 3 y ^ 2 ≡ S (mod m)`.
  `condB`: for an odd prime `l < L` with `l ∤ y`, `x ^ 2 - S` is a quadratic non-residue mod `l`
  (Euler's criterion, evaluated with `Nat.pow`).
* **Tree of residue classes** (`walk`).  A node is a class `x ≡ base (mod step)`.  A level
  `(ell, m, test)` splits it into the `ell` classes `base + step * c (mod step * ell)` and keeps
  those whose residue mod `m` passes `test` (`m ∣ step * ell`).  This does both the Hensel lifting
  of the roots of `x ^ 2 ≡ S - 3 y ^ 2 (mod 8 y ^ 2)` and the wheel.
* **Leaves** (`leaf`).  A leaf is the block `x = base + step * k`, `k < n`, `x < Xb`.  It is sieved
  as an `n`-bit number by periodic patterns (`Pat`): for a group of primes with product `P`, the
  pattern `tile` has bit `j` set if `step * j` is admissible modulo each prime of the group, and the
  block is `tile >>> phase`, `phase = base * step⁻¹ mod P`.  The leaf is excluded if the `AND` of
  the patterns is `0`.

All functions executed by the kernel are written with raw recursors and raw `Nat` functions, which
the kernel evaluates fastest.  No `native_decide`.
-/

namespace Exp7.Sieve

open Exp7.SieveKernel

/-! ## Solutions and the two necessary conditions -/

/-- `x` is a solution for the fixed `y`. -/
def Sol (S Q L y x : ℕ) : Prop :=
  ∃ q : ℕ, S = x ^ 2 + q * y ^ 2 ∧ Q ≤ q ∧ q % 8 = 3 ∧
    ∀ l : ℕ, l.Prime → 3 ≤ l → l < L → jacobiSym (-(q : ℤ)) l = -1

/-- `y` is bounded: `Q * y ^ 2 ≤ S`. -/
theorem y_le {S Q Y x y q : ℕ} (hY : S < Q * (Y + 1) ^ 2) (hS : S = x ^ 2 + q * y ^ 2)
    (hq : Q ≤ q) : y ≤ Y := by
  by_contra h
  have h1 : Y + 1 ≤ y := by omega
  have h2 : Q * (Y + 1) ^ 2 ≤ q * y ^ 2 := Nat.mul_le_mul hq (Nat.pow_le_pow_left h1 2)
  omega

/-- `x` is bounded: `x ^ 2 ≤ S - Q * y ^ 2`. -/
theorem Sol.lt {S Q L y x Xb : ℕ} (h : Sol S Q L y x) (hX : S - Q * y * y < Xb * Xb) : x < Xb := by
  obtain ⟨q, hS, hQ, -, -⟩ := h
  by_contra hx
  have h1 : Xb * Xb ≤ x * x := Nat.mul_le_mul (by omega) (by omega)
  have h2 : Q * y * y ≤ q * y ^ 2 := by
    rw [pow_two, ← mul_assoc]
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hQ)
  have h3 : x ^ 2 = x * x := pow_two x
  omega

/-- The congruence modulo a divisor `m` of `8 y ^ 2`: `r ^ 2 + 3 y ^ 2 ≡ S`. -/
def condA (S y m r : ℕ) : Bool :=
  Nat.beq (Nat.mod (Nat.add (Nat.mul r r) (Nat.mul 3 (Nat.mul y y))) m) (Nat.mod S m)

theorem condA_iff {S y m r : ℕ} :
    condA S y m r = true ↔ (r * r + 3 * (y * y)) % m = S % m := by
  unfold condA; rw [Nat.beq_eq]; rfl

theorem condA_sound {S y m x q : ℕ} (hS : S = x ^ 2 + q * y ^ 2) (hq : q % 8 = 3)
    (hm : m ∣ 8 * y * y) : condA S y m (x % m) = true := by
  rw [condA_iff]
  obtain ⟨j, rfl⟩ : ∃ j, q = 8 * j + 3 := ⟨q / 8, by omega⟩
  have hS' : S = x * x + 3 * (y * y) + 8 * y * y * j := by rw [hS]; ring
  have h1 : x % m * (x % m) ≡ x * x [MOD m] := (Nat.mod_modEq x m).mul (Nat.mod_modEq x m)
  have h2 : 8 * y * y * j ≡ 0 [MOD m] := Nat.modEq_zero_iff_dvd.2 (hm.mul_right _)
  have h3 : x % m * (x % m) + 3 * (y * y) ≡ x * x + 3 * (y * y) + 8 * y * y * j [MOD m] := by
    have := (h1.add_right (3 * (y * y))).add h2.symm
    simpa using this
  rw [hS']
  exact h3

/-- Euler's criterion for "`r ^ 2 - S` is a quadratic non-residue modulo the odd prime `l`". -/
def condB (S l r : ℕ) : Bool :=
  Nat.beq
    (Nat.mod
      (Nat.pow (Nat.mod (Nat.add (Nat.mul r r) (Nat.sub l (Nat.mod S l))) l) (Nat.div l 2)) l)
    (Nat.sub l 1)

theorem condB_iff {S l r : ℕ} :
    condB S l r = true ↔ ((r * r + (l - S % l)) % l) ^ (l / 2) % l = l - 1 := by
  unfold condB; rw [Nat.beq_eq]; rfl

theorem condB_sound {S y l x q : ℕ} (hS : S = x ^ 2 + q * y ^ 2) (hl : l.Prime) (hl3 : 3 ≤ l)
    (hy : ¬ l ∣ y) (hj : jacobiSym (-(q : ℤ)) l = -1) : condB S l (x % l) = true := by
  have := Fact.mk hl
  rw [condB_iff]
  have hodd : 2 * (l / 2) = l - 1 := by
    obtain ⟨k, rfl⟩ := hl.odd_of_ne_two (by omega)
    omega
  have hleg : legendreSym l (-(q : ℤ)) = -1 := by
    rw [jacobiSym.legendreSym.to_jacobiSym]; exact hj
  have he := legendreSym.eq_pow l (-(q : ℤ))
  rw [hleg] at he
  push_cast at he
  have hy0 : (y : ZMod l) ≠ 0 := by rwa [Ne, ZMod.natCast_eq_zero_iff]
  have hy1 : ((y : ZMod l) ^ 2) ^ (l / 2) = 1 := by
    rw [← pow_mul, hodd]; exact ZMod.pow_card_sub_one_eq_one hy0
  have hSz : (S : ZMod l) = (x : ZMod l) ^ 2 + (q : ZMod l) * (y : ZMod l) ^ 2 := by
    rw [hS]; push_cast; ring
  have hc : (((x % l * (x % l) + (l - S % l)) % l : ℕ) : ZMod l)
      = -(q : ZMod l) * (y : ZMod l) ^ 2 := by
    rw [ZMod.natCast_mod, Nat.cast_add, Nat.cast_mul, ZMod.natCast_mod,
      Nat.cast_sub (Nat.mod_lt S hl.pos).le, ZMod.natCast_mod, ZMod.natCast_self, hSz]
    ring
  have hfin : ((((x % l * (x % l) + (l - S % l)) % l) ^ (l / 2) : ℕ) : ZMod l)
      = ((l - 1 : ℕ) : ZMod l) := by
    rw [Nat.cast_pow, hc, mul_pow, hy1, mul_one, ← he, Nat.cast_sub hl.pos, ZMod.natCast_self]
    simp
  have := (ZMod.natCast_eq_natCast_iff' _ _ _).1 hfin
  rwa [Nat.mod_eq_of_lt (Nat.sub_lt hl.pos Nat.one_pos)] at this

/-! ## Kernel-friendly loops and bit operations -/

/-- `∀ c < n, f c`, as a raw recursor loop. -/
noncomputable def allBelow (n : ℕ) (f : ℕ → Bool) : Bool :=
  Nat.rec true (fun c acc => Bool.and (f c) acc) n

theorem allBelow_iff {n : ℕ} {f : ℕ → Bool} : allBelow n f = true ↔ ∀ c < n, f c = true := by
  induction n with
  | zero => simp [allBelow]
  | succ n ih =>
    have : allBelow (n + 1) f = (f n && allBelow n f) := rfl
    rw [this, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ c hc
      rcases Nat.lt_succ_iff_lt_or_eq.1 hc with h | rfl
      · exact h2 c h
      · exact h1
    · intro h
      exact ⟨h n (Nat.lt_succ_self n), fun c hc => h c (Nat.lt_succ_of_lt hc)⟩

/-- Concatenation of `f c` for `c < n`, as a raw recursor loop. -/
noncomputable def flatBelow (n : ℕ) (f : ℕ → List ℕ) : List ℕ :=
  Nat.rec [] (fun c acc => List.append (f c) acc) n

theorem mem_flatBelow {n : ℕ} {f : ℕ → List ℕ} {b : ℕ} :
    b ∈ flatBelow n f ↔ ∃ c < n, b ∈ f c := by
  induction n with
  | zero => simp [flatBelow]
  | succ n ih =>
    have : flatBelow (n + 1) f = f n ++ flatBelow n f := rfl
    rw [this, List.mem_append, ih]
    constructor
    · rintro (h | ⟨c, hc, h⟩)
      · exact ⟨n, Nat.lt_succ_self n, h⟩
      · exact ⟨c, Nat.lt_succ_of_lt hc, h⟩
    · rintro ⟨c, hc, h⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hc with h' | rfl
      · exact Or.inr ⟨c, h', h⟩
      · exact Or.inl h

/-- Bit test with raw `Nat` functions. -/
def tb (m i : ℕ) : Bool := Nat.beq (Nat.land (Nat.shiftRight m i) 1) 1

theorem tb_eq (m i : ℕ) : tb m i = m.testBit i := by
  rw [Bool.eq_iff_iff, Nat.testBit_eq_decide_div_mod_eq, decide_eq_true_iff]
  change Nat.beq (m >>> i &&& 1) 1 = true ↔ _
  rw [Nat.beq_eq, Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]

/-- The number with bit `i < w` set iff `f i`, as a raw recursor loop. -/
noncomputable def mkBits (w : ℕ) (f : ℕ → Bool) : ℕ :=
  Nat.rec 0 (fun i acc => bif f i then Nat.lor acc (Nat.shiftLeft 1 i) else acc) w

theorem mkBits_testBit {w : ℕ} {f : ℕ → Bool} {i : ℕ} (hi : i < w) (h : f i = true) :
    (mkBits w f).testBit i = true := by
  induction w with
  | zero => omega
  | succ w ih =>
    have e : mkBits (w + 1) f = bif f w then mkBits w f ||| 1 <<< w else mkBits w f := rfl
    rw [e]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h' | rfl
    · cases f w <;> simp [ih h']
    · simp [h]

/-- `AND` of a list of numbers with an initial value. -/
noncomputable def andAll (init : ℕ) (l : List ℕ) : ℕ :=
  List.rec init (fun t _ acc => Nat.land t acc) l

theorem andAll_testBit {init : ℕ} {l : List ℕ} {i : ℕ} (h0 : init.testBit i = true)
    (h : ∀ t ∈ l, t.testBit i = true) : (andAll init l).testBit i = true := by
  induction l with
  | nil => exact h0
  | cons t l ih =>
    have e : andAll init (t :: l) = t &&& andAll init l := rfl
    rw [e, Nat.testBit_and, h t (by simp), ih (fun t ht => h t (by simp [ht]))]
    rfl

/-- Trial division up to `19`, for numbers below `400`. -/
noncomputable def primeT (l : ℕ) : Bool :=
  Bool.and (Nat.ble 2 l) (Bool.and (Nat.ble l 399)
    (allBelow 20 (fun d => Bool.or (Nat.ble d 1) (Bool.or (Nat.ble l d)
      (Bool.not (Nat.beq (Nat.mod l d) 0))))))

theorem primeT_sound {l : ℕ} (h : primeT l = true) : l.Prime := by
  unfold primeT at h
  rw [Bool.and_eq_true, Bool.and_eq_true, Nat.ble_eq, Nat.ble_eq, allBelow_iff] at h
  obtain ⟨h2, h400, hd⟩ := h
  rw [Nat.prime_def_le_sqrt]
  refine ⟨h2, fun m hm2 hms hdvd => ?_⟩
  have hmm : m * m ≤ l := Nat.le_sqrt.1 hms
  have hm20 : m < 20 := by
    by_contra hc
    have : 20 * 20 ≤ m * m := Nat.mul_le_mul (by omega) (by omega)
    omega
  have hml : m < l := by
    have : 2 * m ≤ m * m := Nat.mul_le_mul_right m hm2
    omega
  have := hd m hm20
  rw [Bool.or_eq_true, Bool.or_eq_true, Nat.ble_eq, Nat.ble_eq, Bool.not_eq_true'] at this
  rcases this with h | h | h
  · omega
  · omega
  · have h0 : Nat.beq (l % m) 0 = true := by
      rw [Nat.beq_eq]; exact Nat.mod_eq_zero_of_dvd hdvd
    have h0' : Nat.beq (Nat.mod l m) 0 = true := h0
    rw [h0'] at h
    exact Bool.noConfusion h

set_option linter.style.longLine false in
/-- Bit `l` is set iff `l < 400` is prime (checked against `primeT` in `primeMask_ok`). -/
def primeMask : ℕ :=
  324063050816008373288449518385021207079693320013027172312165032583476835699409335195990986219064399586449133338368813228

/-- Primality test for numbers below `400`: one table lookup. -/
def primeB (l : ℕ) : Bool := Bool.and (Nat.ble l 399) (tb primeMask l)

theorem primeMask_ok :
    allBelow 400 (fun l => Bool.or (Bool.not (tb primeMask l)) (primeT l)) = true := by
  decide +kernel

theorem primeB_sound {l : ℕ} (h : primeB l = true) : l.Prime := by
  unfold primeB at h
  rw [Bool.and_eq_true, Nat.ble_eq] at h
  have := allBelow_iff.1 primeMask_ok l (by omega)
  rw [h.2] at this
  exact primeT_sound (by simpa using this)

/-! ## The tree of residue classes -/

/-- A level of the tree: split into `ell` classes, keep those passing `test` modulo `m`. -/
structure Level where
  ell : ℕ
  m : ℕ
  test : ℕ → Bool

/-- Depth-first walk; `leafF base step` is evaluated at the surviving classes. -/
noncomputable def walk (leafF : ℕ → ℕ → Bool) (lv : List Level) : ℕ → ℕ → Bool :=
  List.rec leafF
    (fun L _ ih base step =>
      allBelow L.ell (fun c =>
        bif L.test (Nat.mod (Nat.add base (Nat.mul step c)) L.m)
        then ih (Nat.add base (Nat.mul step c)) (Nat.mul step L.ell) else true)) lv

theorem walk_cons (leafF : ℕ → ℕ → Bool) (L : Level) (lv : List Level) (base step : ℕ) :
    walk leafF (L :: lv) base step = allBelow L.ell (fun c =>
      bif L.test ((base + step * c) % L.m)
      then walk leafF lv (base + step * c) (step * L.ell) else true) := rfl

/-- The surviving classes (their `base`), in a list. -/
noncomputable def frontier (lv : List Level) : ℕ → ℕ → List ℕ :=
  List.rec (fun base _ => [base])
    (fun L _ ih base step =>
      flatBelow L.ell (fun c =>
        bif L.test (Nat.mod (Nat.add base (Nat.mul step c)) L.m)
        then ih (Nat.add base (Nat.mul step c)) (Nat.mul step L.ell) else [])) lv

theorem frontier_cons (L : Level) (lv : List Level) (base step : ℕ) :
    frontier (L :: lv) base step = flatBelow L.ell (fun c =>
      bif L.test ((base + step * c) % L.m)
      then frontier lv (base + step * c) (step * L.ell) else []) := rfl

/-- The step after all levels. -/
def stepAfter : ℕ → List Level → ℕ
  | step, [] => step
  | step, L :: lv => stepAfter (step * L.ell) lv

/-- A level is sound for the set `P` at the current `step`. -/
def LevelSound (P : ℕ → Prop) (step : ℕ) (L : Level) : Prop :=
  0 < L.ell ∧ L.m ∣ step * L.ell ∧ ∀ x, P x → L.test (x % L.m) = true

def LevelsSound (P : ℕ → Prop) : ℕ → List Level → Prop
  | _, [] => True
  | step, L :: lv => LevelSound P step L ∧ LevelsSound P (step * L.ell) lv

theorem stepAfter_pos {P : ℕ → Prop} {lv : List Level} :
    ∀ {step : ℕ}, LevelsSound P step lv → 0 < step → 0 < stepAfter step lv := by
  induction lv with
  | nil => intro step _ h; exact h
  | cons L lv ih =>
    intro step h hs
    exact ih h.2 (Nat.mul_pos hs h.1.1)

/-- One level: an element of the class `base (mod step)` in `P` lies in a surviving subclass. -/
theorem LevelSound.split {P : ℕ → Prop} {step : ℕ} {L : Level} (h : LevelSound P step L)
    {x base k : ℕ} (hx : P x) (hk : x = base + step * k) :
    k % L.ell < L.ell ∧ L.test ((base + step * (k % L.ell)) % L.m) = true ∧
      x = base + step * (k % L.ell) + step * L.ell * (k / L.ell) := by
  obtain ⟨hpos, hdvd, htest⟩ := h
  have hx' : x = base + step * (k % L.ell) + step * L.ell * (k / L.ell) := by
    rw [hk, add_assoc, mul_assoc, ← mul_add, Nat.mod_add_div]
  refine ⟨Nat.mod_lt _ hpos, ?_, hx'⟩
  have := htest x hx
  obtain ⟨d, hd⟩ := hdvd
  rw [hx', hd, mul_assoc, Nat.add_mul_mod_self_left] at this
  exact this

theorem walk_sound {P : ℕ → Prop} {leafF : ℕ → ℕ → Bool} {lv : List Level} :
    ∀ {step base : ℕ}, LevelsSound P step lv → walk leafF lv base step = true →
      ∀ {x k : ℕ}, P x → x = base + step * k →
        ∃ b k', x = b + stepAfter step lv * k' ∧ leafF b (stepAfter step lv) = true := by
  induction lv with
  | nil =>
    intro step base _ hw x k _ hk
    exact ⟨base, k, hk, hw⟩
  | cons L lv ih =>
    intro step base hs hw x k hx hk
    rw [walk_cons, allBelow_iff] at hw
    obtain ⟨hc, ht, hx'⟩ := hs.1.split hx hk
    have h := hw _ hc
    rw [ht] at h
    exact ih hs.2 h hx hx'

theorem frontier_sound {P : ℕ → Prop} {lv : List Level} :
    ∀ {step base : ℕ}, LevelsSound P step lv →
      ∀ {x k : ℕ}, P x → x = base + step * k →
        ∃ b ∈ frontier lv base step, ∃ k', x = b + stepAfter step lv * k' := by
  induction lv with
  | nil =>
    intro step base _ x k _ hk
    exact ⟨base, List.mem_singleton_self _, k, hk⟩
  | cons L lv ih =>
    intro step base hs x k hx hk
    obtain ⟨hc, ht, hx'⟩ := hs.1.split hx hk
    obtain ⟨b, hb, k', hk'⟩ := ih hs.2 hx hx'
    refine ⟨b, ?_, k', hk'⟩
    rw [frontier_cons, mem_flatBelow]
    refine ⟨_, hc, ?_⟩
    rw [ht]
    exact hb

/-! ## Leaves: packed-bitset sieve of a block -/

/-- A periodic pattern: the block of the class `base` is `tile >>> (base * inv % l)`. -/
structure Pat where
  l : ℕ
  inv : ℕ
  tile : ℕ

/-- `AND` the shifted patterns into `acc`; `true` iff the result is `0` (with early exit). -/
noncomputable def sieve (pats : List Pat) (base : ℕ) : ℕ → Bool :=
  List.rec (fun acc => Nat.beq acc 0)
    (fun p _ ih acc =>
      bif Nat.beq acc 0 then true
      else ih (Nat.land acc (Nat.shiftRight p.tile (Nat.mod (Nat.mul base p.inv) p.l)))) pats

theorem sieve_cons (p : Pat) (pats : List Pat) (base acc : ℕ) :
    sieve (p :: pats) base acc =
      bif Nat.beq acc 0 then true
      else sieve pats base (acc &&& (p.tile >>> (base * p.inv % p.l))) := rfl

theorem beq_zero_false {acc k : ℕ} (h : acc.testBit k = true) : Nat.beq acc 0 = false := by
  cases hb : Nat.beq acc 0
  · rfl
  · rw [Nat.beq_eq] at hb
    rw [hb, Nat.zero_testBit] at h
    exact Bool.noConfusion h

theorem sieve_false {pats : List Pat} {base k : ℕ} :
    ∀ {acc : ℕ}, acc.testBit k = true →
      (∀ p ∈ pats, p.tile.testBit (base * p.inv % p.l + k) = true) →
      sieve pats base acc = false := by
  induction pats with
  | nil =>
    intro acc hacc _
    exact beq_zero_false hacc
  | cons p pats ih =>
    intro acc hacc h
    rw [sieve_cons, beq_zero_false hacc]
    refine ih ?_ (fun p hp => h p (by simp [hp]))
    rw [Nat.testBit_and, hacc, Nat.testBit_shiftRight, h p (by simp)]
    rfl

/-- Number of `k` with `base + step * k < Xb`. -/
def blockLen (Xb base step : ℕ) : ℕ := (Xb - base + (step - 1)) / step

theorem lt_blockLen {Xb base step k : ℕ} (hs : 0 < step) (h : base + step * k < Xb) :
    k < blockLen Xb base step := by
  unfold blockLen
  rw [Nat.lt_iff_add_one_le, Nat.le_div_iff_mul_le hs, Nat.add_mul, Nat.mul_comm k step]
  omega

theorem blockLen_le (Xb base step : ℕ) : blockLen Xb base step ≤ blockLen Xb 0 step := by
  unfold blockLen
  exact Nat.div_le_div_right (by omega)

/-- The block `x = base + step * k < Xb` is empty if the sieve leaves nothing. -/
noncomputable def leaf (pats : List Pat) (Xb : ℕ) (base step : ℕ) : Bool :=
  sieve pats base
    (Nat.sub (Nat.pow 2 (Nat.div (Nat.add (Nat.sub Xb base) (Nat.sub step 1)) step)) 1)

theorem leaf_eq (pats : List Pat) (Xb base step : ℕ) :
    leaf pats Xb base step = sieve pats base (2 ^ blockLen Xb base step - 1) := rfl

/-- A pattern is sound for the set `P`: the bit of every element of `P` in a block of length at
most `nmax` is set. -/
def PatSound (P : ℕ → Prop) (step nmax : ℕ) (p : Pat) : Prop :=
  ∀ x base k, P x → x = base + step * k → k < nmax →
    p.tile.testBit (base * p.inv % p.l + k) = true

theorem leaf_false {P : ℕ → Prop} {pats : List Pat} {Xb base step : ℕ} (hs : 0 < step)
    (hp : ∀ p ∈ pats, PatSound P step (blockLen Xb 0 step) p)
    {x k : ℕ} (hx : P x) (hk : x = base + step * k) (hX : x < Xb) :
    leaf pats Xb base step = false := by
  have hkn : k < blockLen Xb base step := lt_blockLen hs (hk ▸ hX)
  rw [leaf_eq]
  refine sieve_false (k := k) ?_ ?_
  · rw [Nat.testBit_two_pow_sub_one]; exact decide_eq_true hkn
  · intro p hpm
    exact hp p hpm x base k hx hk (lt_of_lt_of_le hkn (blockLen_le _ _ _))

/-! ## Certificates: level and pattern specifications, and their validity -/

/-- Specification of a level: `kind = true` is the non-residue condition modulo the prime `m`,
`kind = false` is the congruence modulo the divisor `m` of `8 y ^ 2`. -/
structure LSpec where
  ell : ℕ
  m : ℕ
  kind : Bool

noncomputable def prepLevel (S y : ℕ) (s : LSpec) : Level :=
  ⟨s.ell, s.m, bif s.kind then (fun r => tb (mkBits s.m (condB S s.m)) r) else condA S y s.m⟩

noncomputable def levelOk (L y step : ℕ) (s : LSpec) : Bool :=
  decide (0 < s.ell ∧ (step * s.ell) % s.m = 0 ∧
    if s.kind = true then primeB s.m = true ∧ 3 ≤ s.m ∧ s.m < L ∧ y % s.m ≠ 0
    else (8 * y * y) % s.m = 0)

noncomputable def levelsOk (L y : ℕ) : ℕ → List LSpec → Bool
  | _, [] => true
  | step, s :: ss => levelOk L y step s && levelsOk L y (step * s.ell) ss

/-- The step after all levels of a specification. -/
def mulEll : ℕ → List LSpec → ℕ
  | step, [] => step
  | step, s :: ss => mulEll (step * s.ell) ss

theorem stepAfter_prep (S y : ℕ) (ss : List LSpec) :
    ∀ step, stepAfter step (ss.map (prepLevel S y)) = mulEll step ss := by
  induction ss with
  | nil => intro step; rfl
  | cons s ss ih => intro step; exact ih _

theorem levelOk_sound {S Q L y step : ℕ} {s : LSpec} (h : levelOk L y step s = true) :
    LevelSound (Sol S Q L y) step (prepLevel S y s) := by
  unfold levelOk at h
  obtain ⟨hpos, hdvd, hk⟩ := of_decide_eq_true h
  refine ⟨hpos, Nat.dvd_of_mod_eq_zero hdvd, ?_⟩
  rintro x ⟨q, hS, -, hq8, hj⟩
  cases hkind : s.kind
  · simp only [hkind, Bool.false_eq_true, ↓reduceIte] at hk
    change (bif s.kind then _ else condA S y s.m) (x % s.m) = true
    rw [hkind]
    exact condA_sound hS hq8 (Nat.dvd_of_mod_eq_zero hk)
  · simp only [hkind, ↓reduceIte] at hk
    obtain ⟨hp, h3, hL, hy⟩ := hk
    have hpr := primeB_sound hp
    change (bif s.kind then (fun r => tb (mkBits s.m (condB S s.m)) r) else _) (x % s.m) = true
    rw [hkind]
    change tb (mkBits s.m (condB S s.m)) (x % s.m) = true
    rw [tb_eq]
    refine mkBits_testBit (Nat.mod_lt _ hpr.pos) ?_
    exact condB_sound hS hpr h3 (fun hd => hy (Nat.mod_eq_zero_of_dvd hd)) (hj _ hpr h3 hL)

theorem levelsOk_sound {S Q L y : ℕ} {ss : List LSpec} :
    ∀ {step : ℕ}, levelsOk L y step ss = true →
      LevelsSound (Sol S Q L y) step (ss.map (prepLevel S y)) := by
  induction ss with
  | nil => intro step _; trivial
  | cons s ss ih =>
    intro step h
    have h' : (levelOk L y step s && levelsOk L y (step * s.ell) ss) = true := h
    rw [Bool.and_eq_true] at h'
    exact ⟨levelOk_sound h'.1, ih h'.2⟩

/-- Specification of a pattern: a group of primes `(l, depth)` with product `P` (a multiple of
each suffices), and `inv = step⁻¹ mod P`. -/
structure GSpec where
  P : ℕ
  inv : ℕ
  comps : List (ℕ × ℕ)

/-- The periodic pattern of one prime, indexed by `j` with `x ≡ step * j`. -/
noncomputable def primeTile (S step : ℕ) (c : ℕ × ℕ) : ℕ :=
  tile c.1 (mkBits c.1 (fun j => condB S c.1 (Nat.mod (Nat.mul step j) c.1))) c.2

noncomputable def prepGroup (S step nmax : ℕ) (g : GSpec) : Pat :=
  ⟨g.P, g.inv, andAll (Nat.sub (Nat.pow 2 (Nat.add g.P nmax)) 1) (g.comps.map (primeTile S step))⟩

noncomputable def groupOk (L y step nmax : ℕ) (g : GSpec) : Bool :=
  decide (0 < g.P ∧ (step * g.inv) % g.P = 1 ∧
    ∀ c ∈ g.comps, primeB c.1 = true ∧ 3 ≤ c.1 ∧ c.1 < L ∧ y % c.1 ≠ 0 ∧ g.P % c.1 = 0 ∧
      g.P + nmax ≤ c.1 * 2 ^ c.2)

theorem groupOk_sound {S Q L y step nmax : ℕ} {g : GSpec} (h : groupOk L y step nmax g = true) :
    PatSound (Sol S Q L y) step nmax (prepGroup S step nmax g) := by
  unfold groupOk at h
  obtain ⟨hP, hinv, hc⟩ := of_decide_eq_true h
  rintro x base k ⟨q, hS, -, -, hj⟩ hxk hk
  change (andAll (2 ^ (g.P + nmax) - 1) (g.comps.map (primeTile S step))).testBit
    (base * g.inv % g.P + k) = true
  have hph : base * g.inv % g.P < g.P := Nat.mod_lt _ hP
  have hP1 : 1 % g.P = 1 := by
    have : 1 < g.P := by have := Nat.mod_lt (step * g.inv) hP; omega
    exact Nat.mod_eq_of_lt this
  have hstep : step * (base * g.inv % g.P) ≡ base [MOD g.P] := by
    have h1 : step * (base * g.inv % g.P) ≡ step * (base * g.inv) [MOD g.P] :=
      (Nat.mod_modEq _ _).mul_left step
    have h2 : step * g.inv ≡ 1 [MOD g.P] := by
      change step * g.inv % g.P = 1 % g.P
      rw [hinv, hP1]
    have h3 : step * (base * g.inv) = base * (step * g.inv) := by ring
    rw [h3] at h1
    simpa using h1.trans (h2.mul_left base)
  refine andAll_testBit ?_ ?_
  · rw [Nat.testBit_two_pow_sub_one]; exact decide_eq_true (by omega)
  · intro t ht
    obtain ⟨c, hcm, rfl⟩ := List.mem_map.1 ht
    obtain ⟨hp, h3, hL, hy, hdvd, hlen⟩ := hc c hcm
    have hpr := primeB_sound hp
    refine tile_keeps _ _ _ _ hpr.pos (by omega) ?_
    refine mkBits_testBit (Nat.mod_lt _ hpr.pos) ?_
    change condB S c.1 (step * ((base * g.inv % g.P + k) % c.1) % c.1) = true
    have hx : step * ((base * g.inv % g.P + k) % c.1) % c.1 = x % c.1 := by
      have h1 : step * ((base * g.inv % g.P + k) % c.1) ≡ step * (base * g.inv % g.P + k)
          [MOD c.1] := (Nat.mod_modEq _ _).mul_left step
      have h2 : step * (base * g.inv % g.P) ≡ base [MOD c.1] :=
        hstep.of_dvd (Nat.dvd_of_mod_eq_zero hdvd)
      have h3 : step * (base * g.inv % g.P + k) ≡ base + step * k [MOD c.1] := by
        rw [mul_add]; exact h2.add_right _
      rw [hxk]
      exact h1.trans h3
    rw [hx]
    exact condB_sound hS hpr h3 (fun hd => hy (Nat.mod_eq_zero_of_dvd hd)) (hj _ hpr h3 hL)

/-- Certificate for one `y`: bound `Xb` for `x`, the levels above (`top`) and below (`rest`) the
frontier at which the work is cut into shards, and the patterns for the leaves. -/
structure YCert where
  y : ℕ
  Xb : ℕ
  top : List LSpec
  rest : List LSpec
  groups : List GSpec

namespace YCert

def stepTop (c : YCert) : ℕ := mulEll 1 c.top

def stepF (c : YCert) : ℕ := mulEll c.stepTop c.rest

def nmax (c : YCert) : ℕ := blockLen c.Xb 0 c.stepF

/-- The classes at which the work is cut into shards. -/
noncomputable def frontier (S : ℕ) (c : YCert) : List ℕ :=
  Sieve.frontier (c.top.map (prepLevel S c.y)) 0 1

/-- Validity of the certificate (cheap): bound for `x`, levels, patterns, the frontier is the
list `fr` (so that the shards need not recompute it), and the number of shards. -/
noncomputable def header (S Q L : ℕ) (c : YCert) (fr : List ℕ) (chunk m : ℕ) : Bool :=
  decide (S - Q * c.y * c.y < c.Xb * c.Xb) && levelsOk L c.y 1 c.top &&
    levelsOk L c.y c.stepTop c.rest && c.groups.all (groupOk L c.y c.stepF c.nmax) &&
    decide (c.frontier S = fr) && Nat.ble fr.length (m * chunk)

/-- Shard `i`: the classes number `i * chunk, …, (i + 1) * chunk - 1` of the frontier `fr` are
empty. -/
noncomputable def shardOk (S : ℕ) (c : YCert) (fr : List ℕ) (chunk i : ℕ) : Bool :=
  ((fr.drop (i * chunk)).take chunk).all (fun b =>
    walk (leaf (c.groups.map (prepGroup S c.stepF c.nmax)) c.Xb)
      (c.rest.map (prepLevel S c.y)) b c.stepTop)

/-- The shards `0, …, k - 1` have been checked. -/
def ShardsUpTo (S : ℕ) (c : YCert) (fr : List ℕ) (chunk k : ℕ) : Prop :=
  ∀ i < k, c.shardOk S fr chunk i = true

theorem shardsUpTo_zero (S : ℕ) (c : YCert) (fr : List ℕ) (chunk : ℕ) :
    c.ShardsUpTo S fr chunk 0 :=
  fun _ h => absurd h (Nat.not_lt_zero _)

theorem ShardsUpTo.succ {S : ℕ} {c : YCert} {fr : List ℕ} {chunk k : ℕ}
    (h : c.ShardsUpTo S fr chunk k) (hk : c.shardOk S fr chunk k = true) :
    c.ShardsUpTo S fr chunk (k + 1) := by
  intro i hi
  rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h' | rfl
  · exact h i h'
  · exact hk

/-- **Soundness of the certificate for one `y`.** -/
theorem sound {S Q L : ℕ} {c : YCert} {fr : List ℕ} {chunk m : ℕ}
    (hh : c.header S Q L fr chunk m = true) (hs : c.ShardsUpTo S fr chunk m) (x : ℕ) :
    ¬ Sol S Q L c.y x := by
  intro hx
  unfold header at hh
  simp only [Bool.and_eq_true, decide_eq_true_eq, Nat.ble_eq, List.all_eq_true] at hh
  obtain ⟨⟨⟨⟨⟨hXb, htop⟩, hrest⟩, hgr⟩, hfr⟩, hlen⟩ := hh
  subst hfr
  have htop' := levelsOk_sound (S := S) (Q := Q) htop
  have hrest' := levelsOk_sound (S := S) (Q := Q) hrest
  have hst : stepAfter 1 (c.top.map (prepLevel S c.y)) = c.stepTop := stepAfter_prep _ _ _ _
  have hsf : stepAfter c.stepTop (c.rest.map (prepLevel S c.y)) = c.stepF := stepAfter_prep _ _ _ _
  have hpos1 : 0 < c.stepTop := hst ▸ stepAfter_pos htop' Nat.one_pos
  have hpos2 : 0 < c.stepF := hsf ▸ stepAfter_pos hrest' hpos1
  -- the class of `x` in the frontier
  obtain ⟨b, hb, k', hk'⟩ := frontier_sound htop' hx (base := 0) (k := x) (by simp)
  rw [hst] at hk'
  -- the shard containing it
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hb
  change j < (c.frontier S).length at hj
  have hc : 0 < chunk := by
    rcases Nat.eq_zero_or_pos chunk with h0 | h0
    · subst h0
      omega
    · exact h0
  have hjm : j / chunk < m := by
    rw [Nat.div_lt_iff_lt_mul hc]
    omega
  have hshard := hs _ hjm
  unfold shardOk at hshard
  rw [List.all_eq_true] at hshard
  have hmem : (c.frontier S)[j] ∈ ((c.frontier S).drop (j / chunk * chunk)).take chunk := by
    have hdm := Nat.div_add_mod j chunk
    have hmod : j % chunk < chunk := Nat.mod_lt _ hc
    have hcomm : chunk * (j / chunk) = j / chunk * chunk := Nat.mul_comm _ _
    rw [List.mem_iff_getElem]
    refine ⟨j % chunk, ?_, ?_⟩
    · rw [List.length_take, List.length_drop]
      omega
    · rw [List.getElem_take, List.getElem_drop]
      congr 1
      omega
  have hw := hshard _ hmem
  obtain ⟨b', k'', hk'', hleaf⟩ := walk_sound hrest' hw hx hk'
  rw [hsf] at hk'' hleaf
  have hfalse := leaf_false (P := Sol S Q L c.y)
    (pats := c.groups.map (prepGroup S c.stepF c.nmax)) hpos2
    (fun p hp => by
      obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hp
      exact groupOk_sound (hgr g hg)) hx hk'' (hx.lt hXb)
  rw [hfalse] at hleaf
  exact Bool.noConfusion hleaf

end YCert

/-- No solution for this `y`. -/
def YOk (S Q L y : ℕ) : Prop := ∀ x, ¬ Sol S Q L y x

theorem YCert.yOk {S Q L y : ℕ} (c : YCert) (hy : c.y = y) {fr : List ℕ} {chunk m : ℕ}
    (hh : c.header S Q L fr chunk m = true) (hs : c.ShardsUpTo S fr chunk m) : YOk S Q L y := by
  subst hy
  exact YCert.sound hh hs

/-- No solution for `1 ≤ y ≤ n`. -/
def YOkUpTo (S Q L n : ℕ) : Prop := ∀ y, 1 ≤ y → y ≤ n → YOk S Q L y

theorem yOkUpTo_zero (S Q L : ℕ) : YOkUpTo S Q L 0 := fun y h1 h0 => by omega

theorem YOkUpTo.succ {S Q L n : ℕ} (h : YOkUpTo S Q L n) (hn : YOk S Q L (n + 1)) :
    YOkUpTo S Q L (n + 1) := by
  intro y h1 hy
  rcases Nat.lt_succ_iff_lt_or_eq.1 (Nat.lt_succ_of_le hy) with h' | rfl
  · exact h y h1 (Nat.lt_succ_iff.1 h')
  · exact hn

/-- The form in which the certificate for one `y` is used. -/
theorem no_solution {S Q L y : ℕ} (c : YCert) (hy : c.y = y) {fr : List ℕ} {chunk m : ℕ}
    (hh : c.header S Q L fr chunk m = true) (hs : c.ShardsUpTo S fr chunk m) (x q : ℕ)
    (hS : S = x ^ 2 + q * y ^ 2) (hQ : Q ≤ q) (h8 : q % 8 = 3)
    (hj : ∀ l : ℕ, l.Prime → 3 ≤ l → l < L → jacobiSym (-(q : ℤ)) l = -1) : False := by
  subst hy
  exact YCert.sound hh hs x ⟨q, hS, hQ, h8, hj⟩

/-! ## The statement for one prime, parametric in the lower bound for `q` -/

/-- The statement proved for one prime `p`, with an arbitrary lower bound `Q` for `q`
(`Exp7.SearchHigh` is `PrimeStatement p (Qlo p)` for the primes `701 ≤ p ≤ 4297`). -/
def PrimeStatement (p Q : ℕ) : Prop :=
  ∀ x y q : ℕ, 1 ≤ y → 4 * p ^ 7 = x ^ 2 + q * y ^ 2 → Q ≤ q → q % 8 = 3 →
    (∀ l : ℕ, l.Prime → 3 ≤ l → l < p → jacobiSym (-(q : ℤ)) l = -1) → False

theorem PrimeStatement.mono {p Q Q' : ℕ} (h : Q ≤ Q') (hp : PrimeStatement p Q) :
    PrimeStatement p Q' :=
  fun x y q hy hS hq => hp x y q hy hS (h.trans hq)

namespace YCert

/-- The whole certificate for one `y` in a single computation (no shards). -/
noncomputable def ok (S Q L : ℕ) (c : YCert) : Bool :=
  c.header S Q L (c.frontier S) (c.frontier S).length 1 &&
    c.shardOk S (c.frontier S) (c.frontier S).length 0

theorem ok_sound {S Q L : ℕ} {c : YCert} (h : c.ok S Q L = true) (x : ℕ) : ¬ Sol S Q L c.y x := by
  unfold ok at h
  rw [Bool.and_eq_true] at h
  exact sound h.1 ((shardsUpTo_zero _ _ _ _).succ h.2) x

end YCert

/-- A prime is done when `y` is bounded by `Y` and every `1 ≤ y ≤ Y` is excluded. -/
theorem prime_of_yOk {p Q Y : ℕ} (hY : 4 * p ^ 7 < Q * (Y + 1) ^ 2)
    (h : YOkUpTo (4 * p ^ 7) Q p Y) : PrimeStatement p Q :=
  fun x y q hy hS hq h8 hj => h y hy (y_le hY hS hq) x ⟨q, hS, hq, h8, hj⟩

/-- Certificate check for a whole prime `p` and an arbitrary lower bound `Q` for `q`, in a single
computation: `y ≤ Y` by the size condition, and each `1 ≤ y ≤ Y` has a certificate in the list.
(For large primes the same check is cut into shards, see `YCert.sound` and `no_solution`.) -/
noncomputable def primeOk (p Q Y : ℕ) (cs : List YCert) : Bool :=
  decide (4 * p ^ 7 < Q * (Y + 1) ^ 2) &&
    allBelow Y (fun i => cs.any (fun c => Nat.beq c.y (i + 1) && c.ok (4 * p ^ 7) Q p))

/-- **Soundness for a whole prime.** -/
theorem primeOk_sound {p Q Y : ℕ} {cs : List YCert} (h : primeOk p Q Y cs = true) :
    PrimeStatement p Q := by
  intro x y q hy hS hq h8 hj
  unfold primeOk at h
  rw [Bool.and_eq_true, allBelow_iff] at h
  have hY : y ≤ Y := y_le (of_decide_eq_true h.1) hS hq
  have h2 := h.2 (y - 1) (by omega)
  rw [List.any_eq_true] at h2
  obtain ⟨c, -, hc⟩ := h2
  rw [Bool.and_eq_true, Nat.beq_eq] at hc
  have hcy : c.y = y := by omega
  refine YCert.ok_sound hc.2 x ?_
  rw [hcy]
  exact ⟨q, hS, hq, h8, hj⟩

end Exp7.Sieve
