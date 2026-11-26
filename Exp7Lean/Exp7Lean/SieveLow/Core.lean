import Exp7Lean.Sieve.Bridge

/-!
# A generic one-dimensional packed-bitset sieve, with a range and with exceptions

`Exp7Lean/Sieve/Bridge.lean` sieves, for one `y`, the `x` with `x < Xb`, with conditions that are
specific to the equation `S = x ^ 2 + q y ^ 2`, and proves that nothing survives.  Here the same
machine is made generic, so that it can be run on three different one-dimensional problems of the
low-range search (see `DESIGN.md`):

* a set `P ⊆ ℕ` is given with a family `F` of periodic necessary conditions (`Fam.Sound`):
  `x ∈ P → F.cond m (x % m)` for every modulus `m` with `F.valid m`;
* the elements of `P` in the window `Xa ≤ x < Xb` are known to lie in the classes
  `b (mod step0)`, `b ∈ bases`;
* each class is split by a wheel (`top`, then `rest`: the classes after `top` are the *frontier*, at
  which the work is cut into shards), and each final class `x = base + step * k` is a block of bits
  that is sieved by the patterns of `groups` (as in `Bridge.lean`);
* a block may keep some bits: they have to be the positions of the listed exceptions `exc`
  (`leafLo`: `acc ||| E = E` where `E` is the mask of the exceptions of the block).

Conclusion (`Task.sound`, `Task.ok_sound`): every `x ∈ P` of the window and of the classes is in
`exc`.  All kernel-evaluated functions use raw recursors and raw `Nat` functions.
-/

namespace Exp7.SieveLow

open Exp7.SieveKernel Exp7.Sieve

/-- A family of periodic conditions: `cond m r` is the condition on the residue `r` modulo `m`,
available for the moduli with `valid m`.  `dil m v` is the dilated table: bit `r * v % m` for each
admissible residue `r` (for `v` inverse to a step `s` modulo `m`, this is the pattern
`j ↦ cond m (s * j % m)`). -/
structure Fam where
  valid : ℕ → Bool
  cond : ℕ → ℕ → Bool
  dil : ℕ → ℕ → ℕ

/-- The conditions of the family are necessary for membership in `P`. -/
def Fam.Sound (F : Fam) (P : ℕ → Prop) : Prop :=
  ∀ m, F.valid m = true → 0 < m ∧ ∀ x, P x →
    F.cond m (x % m) = true ∧ ∀ v, (F.dil m v).testBit (x % m * v % m) = true

/-- The residues `r < l` with `C r`, in a list. -/
noncomputable def resOf (C : ℕ → Bool) (l : ℕ) : List ℕ :=
  Nat.rec [] (fun r acc => bif C r then r :: acc else acc) l

theorem mem_resOf {C : ℕ → Bool} {l r : ℕ} (hr : r < l) (h : C r = true) : r ∈ resOf C l := by
  induction l with
  | zero => omega
  | succ l ih =>
    have e : resOf C (l + 1) = bif C l then l :: resOf C l else resOf C l := rfl
    rw [e]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hr with h' | rfl
    · cases C l
      · exact ih h'
      · exact List.mem_cons_of_mem _ (ih h')
    · rw [h]
      exact List.mem_cons_self

/-- Bit `r * v % l` for each `r` of the list. -/
noncomputable def dilBits (l v : ℕ) (R : List ℕ) : ℕ :=
  List.rec 0 (fun r _ acc => Nat.lor acc (Nat.shiftLeft 1 (Nat.mod (Nat.mul r v) l))) R

theorem dilBits_testBit {l v r : ℕ} {R : List ℕ} (h : r ∈ R) :
    (dilBits l v R).testBit (r * v % l) = true := by
  induction R with
  | nil => exact absurd h List.not_mem_nil
  | cons a R ih =>
    have e : dilBits l v (a :: R) = dilBits l v R ||| 1 <<< (a * v % l) := rfl
    rw [e, Nat.testBit_or]
    rcases List.mem_cons.1 h with rfl | h'
    · rw [Nat.one_shiftLeft, Nat.testBit_two_pow]
      simp
    · rw [ih h']
      rfl

/-- The family of the conditions `cond`: the dilated tables are computed from the list of the
admissible residues, a closed term that the kernel evaluates once per declaration. -/
noncomputable def Fam.ofCond (valid : ℕ → Bool) (cond : ℕ → ℕ → Bool) : Fam :=
  ⟨valid, cond, fun l v => dilBits l v (resOf (cond l) l)⟩

theorem Fam.ofCond_sound {valid : ℕ → Bool} {cond : ℕ → ℕ → Bool} {P : ℕ → Prop}
    (h : ∀ m, valid m = true → 0 < m ∧ ∀ x, P x → cond m (x % m) = true) :
    (Fam.ofCond valid cond).Sound P := by
  intro m hm
  obtain ⟨hpos, hc⟩ := h m hm
  exact ⟨hpos, fun x hx => ⟨hc x hx, fun v =>
    dilBits_testBit (mem_resOf (Nat.mod_lt _ hpos) (hc x hx))⟩⟩

/-! ## Raw loops over lists -/

/-- `∀ a ∈ l, f a`. -/
noncomputable def allL {α : Type} (f : α → Bool) (l : List α) : Bool :=
  List.rec true (fun a _ ih => Bool.and (f a) ih) l

theorem allL_iff {α : Type} {f : α → Bool} {l : List α} :
    allL f l = true ↔ ∀ a ∈ l, f a = true := by
  induction l with
  | nil => simp [allL]
  | cons a l ih =>
    have e : allL f (a :: l) = (f a && allL f l) := rfl
    rw [e, Bool.and_eq_true, ih]
    simp

/-- `∃ a ∈ l, f a`. -/
noncomputable def anyL {α : Type} (f : α → Bool) (l : List α) : Bool :=
  List.rec false (fun a _ ih => Bool.or (f a) ih) l

theorem anyL_iff {α : Type} {f : α → Bool} {l : List α} :
    anyL f l = true ↔ ∃ a ∈ l, f a = true := by
  induction l with
  | nil => simp [anyL]
  | cons a l ih =>
    have e : anyL f (a :: l) = (f a || anyL f l) := rfl
    rw [e, Bool.or_eq_true, ih]
    simp

/-- Membership in a list of numbers. -/
noncomputable def elemL (q : ℕ) (l : List ℕ) : Bool := anyL (Nat.beq q) l

theorem elemL_iff {q : ℕ} {l : List ℕ} : elemL q l = true ↔ q ∈ l := by
  unfold elemL
  rw [anyL_iff]
  constructor
  · rintro ⟨a, ha, h⟩
    rw [Nat.beq_eq] at h
    exact h ▸ ha
  · intro h
    exact ⟨q, h, Nat.beq_refl q⟩

/-- `List.drop`. -/
noncomputable def dropR {α : Type} (n : ℕ) : List α → List α :=
  Nat.rec (fun l => l) (fun _ ih l => List.rec [] (fun _ t _ => ih t) l) n

theorem dropR_eq {α : Type} (n : ℕ) (l : List α) : dropR n l = l.drop n := by
  induction n generalizing l with
  | zero => rfl
  | succ n ih =>
    cases l with
    | nil => rfl
    | cons a t => exact ih t

/-- `∀ a ∈ l.take n, f a`. -/
noncomputable def allTake {α : Type} (f : α → Bool) (n : ℕ) : List α → Bool :=
  Nat.rec (fun _ => true) (fun _ ih l => List.rec true (fun a t _ => Bool.and (f a) (ih t)) l) n

theorem allTake_iff {α : Type} {f : α → Bool} {n : ℕ} {l : List α} :
    allTake f n l = true ↔ ∀ a ∈ l.take n, f a = true := by
  induction n generalizing l with
  | zero => simp [allTake]
  | succ n ih =>
    cases l with
    | nil => simp [allTake]
    | cons a t =>
      have e : allTake f (n + 1) (a :: t) = (f a && allTake f n t) := rfl
      rw [e, Bool.and_eq_true, ih]
      simp

/-- `List.length`. -/
noncomputable def lenR {α : Type} (l : List α) : ℕ := List.rec 0 (fun _ _ ih => Nat.succ ih) l

theorem lenR_eq {α : Type} (l : List α) : lenR l = l.length := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    have e : lenR (a :: l) = Nat.succ (lenR l) := rfl
    rw [e, ih]
    rfl

/-- `List.map`. -/
noncomputable def mapR {α β : Type} (f : α → β) (l : List α) : List β :=
  List.rec [] (fun a _ ih => f a :: ih) l

theorem mapR_eq {α β : Type} (f : α → β) (l : List α) : mapR f l = l.map f := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    have e : mapR f (a :: l) = f a :: mapR f l := rfl
    rw [e, ih]
    rfl

/-- `List.append`. -/
noncomputable def appendR {α : Type} (l₁ l₂ : List α) : List α :=
  List.rec l₂ (fun a _ ih => a :: ih) l₁

theorem appendR_eq {α : Type} (l₁ l₂ : List α) : appendR l₁ l₂ = l₁ ++ l₂ := by
  induction l₁ with
  | nil => rfl
  | cons a l ih =>
    have e : appendR (a :: l) l₂ = a :: appendR l l₂ := rfl
    rw [e, ih]
    rfl

/-- Concatenation of `f b` for `b ∈ l`. -/
noncomputable def flatL (f : ℕ → List ℕ) (l : List ℕ) : List ℕ :=
  List.rec [] (fun b _ acc => appendR (f b) acc) l

theorem mem_flatL {f : ℕ → List ℕ} {l : List ℕ} {x : ℕ} :
    x ∈ flatL f l ↔ ∃ b ∈ l, x ∈ f b := by
  induction l with
  | nil => simp [flatL]
  | cons b l ih =>
    have e : flatL f (b :: l) = appendR (f b) (flatL f l) := rfl
    rw [e, appendR_eq, List.mem_append, ih]
    simp

/-- If the chunks `i < m` of length `chunk` of a list of length at most `m * chunk` all satisfy
`f`, then so does the list. -/
theorem all_of_chunks {α : Type} {f : α → Bool} {l : List α} {chunk m : ℕ}
    (hlen : l.length ≤ m * chunk)
    (h : ∀ i < m, allTake f chunk (dropR (i * chunk) l) = true) : ∀ a ∈ l, f a = true := by
  intro a ha
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 ha
  have hc : 0 < chunk := by
    rcases Nat.eq_zero_or_pos chunk with h0 | h0
    · subst h0
      omega
    · exact h0
  have hjm : j / chunk < m := by
    rw [Nat.div_lt_iff_lt_mul hc]
    omega
  have hs := h _ hjm
  rw [allTake_iff, dropR_eq] at hs
  refine hs _ ?_
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

/-! ## Levels of the wheel -/

/-- The level of the modulus `m`: split into `m` classes, keep those whose residue modulo `m`
satisfies the condition (looked up in a table). -/
noncomputable def prepLevel (F : Fam) (m : ℕ) : Level :=
  ⟨m, m, fun r => tb (mkBits m (F.cond m)) r⟩

/-- The step after the levels `l`. -/
noncomputable def mulAll (step : ℕ) (l : List ℕ) : ℕ :=
  List.rec (fun s => s) (fun m _ ih s => ih (Nat.mul s m)) l step

theorem mulAll_cons (step m : ℕ) (l : List ℕ) : mulAll step (m :: l) = mulAll (step * m) l := rfl

theorem stepAfter_prepLevel (F : Fam) (l : List ℕ) :
    ∀ step, stepAfter step (l.map (prepLevel F)) = mulAll step l := by
  induction l with
  | nil => intro step; rfl
  | cons m l ih => intro step; exact ih _

theorem levelsSound {F : Fam} {P : ℕ → Prop} (hF : F.Sound P) {l : List ℕ} :
    ∀ {step : ℕ}, allL F.valid l = true → LevelsSound P step (l.map (prepLevel F)) := by
  induction l with
  | nil => intro step _; trivial
  | cons m l ih =>
    intro step h
    rw [allL_iff] at h
    obtain ⟨hpos, hc⟩ := hF m (h m List.mem_cons_self)
    refine ⟨⟨hpos, Dvd.intro_left _ rfl, fun x hx => ?_⟩,
      ih (allL_iff.2 fun a ha => h a (List.mem_cons_of_mem _ ha))⟩
    change tb (mkBits m (F.cond m)) (x % m) = true
    rw [tb_eq]
    exact mkBits_testBit (Nat.mod_lt _ hpos) (hc x hx).1

/-- The phase of a block: if `inv` inverts `step` modulo `P` and `c ∣ P`, the residue of
`x = base + step * k` modulo `c` is that of `step * (phase + k)`, `phase = base * inv % P`. -/
theorem phase_mod {step inv P c base k : ℕ} (hP : 0 < P) (hinv : step * inv % P = 1)
    (hdvd : P % c = 0) : step * ((base * inv % P + k) % c) % c = (base + step * k) % c := by
  have hP1 : 1 % P = 1 := by
    have : 1 < P := by have := Nat.mod_lt (step * inv) hP; omega
    exact Nat.mod_eq_of_lt this
  have hstep : step * (base * inv % P) ≡ base [MOD P] := by
    have h1 : step * (base * inv % P) ≡ step * (base * inv) [MOD P] :=
      (Nat.mod_modEq _ _).mul_left step
    have h2 : step * inv ≡ 1 [MOD P] := by
      change step * inv % P = 1 % P
      rw [hinv, hP1]
    have h3 : step * (base * inv) = base * (step * inv) := by ring
    rw [h3] at h1
    simpa using h1.trans (h2.mul_left base)
  have h1 : step * ((base * inv % P + k) % c) ≡ step * (base * inv % P + k) [MOD c] :=
    (Nat.mod_modEq _ _).mul_left step
  have h2 : step * (base * inv % P) ≡ base [MOD c] := hstep.of_dvd (Nat.dvd_of_mod_eq_zero hdvd)
  have h3 : step * (base * inv % P + k) ≡ base + step * k [MOD c] := by
    rw [mul_add]; exact h2.add_right _
  exact h1.trans h3

/-! ## Patterns -/

/-- A group of sieving moduli is a flat list `P :: inv :: d :: ls` (flat lists of numerals are by
far the cheapest literals to elaborate): the moduli `ls` divide `P`, `inv` inverts the step modulo
`P`, and each pattern is tiled `2 ^ d` times. -/
noncomputable def gP (g : List ℕ) : ℕ := List.rec 0 (fun a _ _ => a) g

/-- Tail of a list. -/
noncomputable def tlR (g : List ℕ) : List ℕ := List.rec [] (fun _ t _ => t) g

noncomputable def gInv (g : List ℕ) : ℕ := gP (tlR g)

noncomputable def gD (g : List ℕ) : ℕ := gP (tlR (tlR g))

noncomputable def gLs (g : List ℕ) : List ℕ := tlR (tlR (tlR g))

/-- The periodic pattern of one modulus `l`, indexed by `j` with `x ≡ step * j`, where `inv`
inverts `step`; tiled `2 ^ d` times. -/
noncomputable def primeTileF (F : Fam) (inv d l : ℕ) : ℕ := tile l (F.dil l inv) d

/-- The pattern of a group of moduli. -/
noncomputable def prepGroupF (F : Fam) (nmax : ℕ) (g : List ℕ) : Pat :=
  ⟨gP g, gInv g,
    andAll (Nat.sub (Nat.pow 2 (Nat.add (gP g) nmax)) 1)
      (mapR (primeTileF F (gInv g) (gD g)) (gLs g))⟩

/-- Validity of a group: `inv` inverts `step` modulo `P`, every modulus is valid and divides `P`,
and its tiling covers `P + nmax` bits. -/
noncomputable def groupOkF (F : Fam) (step nmax : ℕ) (g : List ℕ) : Bool :=
  Bool.and (Nat.ble 1 (gP g)) (Bool.and (Nat.beq (Nat.mod (Nat.mul step (gInv g)) (gP g)) 1)
    (allL (fun l : ℕ => Bool.and (F.valid l) (Bool.and (Nat.beq (Nat.mod (gP g) l) 0)
      (Nat.ble (Nat.add (gP g) nmax) (Nat.mul l (Nat.pow 2 (gD g)))))) (gLs g)))

theorem groupOkF_sound {F : Fam} {P : ℕ → Prop} (hF : F.Sound P) {step nmax : ℕ} {g : List ℕ}
    (h : groupOkF F step nmax g = true) : PatSound P step nmax (prepGroupF F nmax g) := by
  unfold groupOkF at h
  rw [Bool.and_eq_true, Bool.and_eq_true, Nat.ble_eq, Nat.beq_eq, allL_iff] at h
  obtain ⟨hP, hinv, hc⟩ := h
  have hinv' : step * gInv g % gP g = 1 := hinv
  intro x base k hx hxk hk
  change (andAll (2 ^ (gP g + nmax) - 1) (mapR (primeTileF F (gInv g) (gD g)) (gLs g))).testBit
    (base * gInv g % gP g + k) = true
  rw [mapR_eq]
  have hph : base * gInv g % gP g < gP g := Nat.mod_lt _ hP
  have hP1 : 1 % gP g = 1 := by
    have : 1 < gP g := by have := Nat.mod_lt (step * gInv g) hP; omega
    exact Nat.mod_eq_of_lt this
  have hinvP : step * gInv g ≡ 1 [MOD gP g] := by
    change step * gInv g % gP g = 1 % gP g
    rw [hinv', hP1]
  refine andAll_testBit ?_ ?_
  · rw [Nat.testBit_two_pow_sub_one]; exact decide_eq_true (by omega)
  · intro t ht
    obtain ⟨l, hlm, rfl⟩ := List.mem_map.1 ht
    have hc' := hc l hlm
    rw [Bool.and_eq_true, Bool.and_eq_true, Nat.beq_eq, Nat.ble_eq] at hc'
    obtain ⟨hv, hdvd, hlen⟩ := hc'
    have hdvd' : gP g % l = 0 := hdvd
    have hlen' : gP g + nmax ≤ l * 2 ^ gD g := hlen
    obtain ⟨hpos, hcond⟩ := hF l hv
    change (tile l (F.dil l (gInv g)) (gD g)).testBit (base * gInv g % gP g + k) = true
    refine tile_keeps _ _ _ _ hpos (by omega) ?_
    have hx' : x % l * gInv g % l = (base * gInv g % gP g + k) % l := by
      rw [hxk, ← phase_mod hP hinv' hdvd', Nat.mod_mul_mod]
      have e : step * ((base * gInv g % gP g + k) % l) * gInv g
          = (base * gInv g % gP g + k) % l * (step * gInv g) := by ring
      have h1 : (base * gInv g % gP g + k) % l * (step * gInv g)
          ≡ (base * gInv g % gP g + k) % l * 1 [MOD l] :=
        (hinvP.of_dvd (Nat.dvd_of_mod_eq_zero hdvd')).mul_left _
      rw [e, h1, mul_one, Nat.mod_mod]
    rw [← hx']
    exact (hcond x hx).2 (gInv g)

/-! ## Leaves with a window and exceptions -/

/-- `AND` of the shifted patterns (stops when the block is empty). -/
noncomputable def sieveN (pats : List Pat) (base : ℕ) : ℕ → ℕ :=
  List.rec (fun acc => acc)
    (fun p _ ih acc =>
      bif Nat.beq acc 0 then 0
      else ih (Nat.land acc (Nat.shiftRight p.tile (Nat.mod (Nat.mul base p.inv) p.l)))) pats

theorem sieveN_cons (p : Pat) (pats : List Pat) (base acc : ℕ) :
    sieveN (p :: pats) base acc =
      bif Nat.beq acc 0 then 0
      else sieveN pats base (acc &&& (p.tile >>> (base * p.inv % p.l))) := rfl

theorem sieveN_testBit {pats : List Pat} {base k : ℕ} :
    ∀ {acc : ℕ}, acc.testBit k = true →
      (∀ p ∈ pats, p.tile.testBit (base * p.inv % p.l + k) = true) →
      (sieveN pats base acc).testBit k = true := by
  induction pats with
  | nil =>
    intro acc hacc _
    exact hacc
  | cons p pats ih =>
    intro acc hacc h
    rw [sieveN_cons, beq_zero_false hacc]
    refine ih ?_ (fun p hp => h p (by simp [hp]))
    rw [Nat.testBit_and, hacc, Nat.testBit_shiftRight, h p (by simp)]
    rfl

/-- The mask of the exceptions `e = base + step * k`: bit `k`. -/
noncomputable def excMask (exc : List ℕ) (base step : ℕ) : ℕ :=
  List.rec 0
    (fun e _ acc =>
      bif Bool.and (Nat.ble base e) (Nat.beq (Nat.mod (Nat.sub e base) step) 0)
      then Nat.lor acc (Nat.shiftLeft 1 (Nat.div (Nat.sub e base) step)) else acc) exc

theorem excMask_cons (e : ℕ) (exc : List ℕ) (base step : ℕ) :
    excMask (e :: exc) base step =
      bif Bool.and (Nat.ble base e) (Nat.beq ((e - base) % step) 0)
      then excMask exc base step ||| 1 <<< ((e - base) / step) else excMask exc base step := rfl

theorem excMask_testBit {exc : List ℕ} {base step k : ℕ}
    (h : (excMask exc base step).testBit k = true) : base + step * k ∈ exc := by
  induction exc with
  | nil =>
    have e : excMask [] base step = 0 := rfl
    rw [e, Nat.zero_testBit] at h
    exact Bool.noConfusion h
  | cons e exc ih =>
    rw [excMask_cons] at h
    cases hc : Bool.and (Nat.ble base e) (Nat.beq ((e - base) % step) 0)
    · rw [hc] at h
      exact List.mem_cons_of_mem _ (ih h)
    · rw [hc] at h
      have hc' : (Nat.ble base e && Nat.beq ((e - base) % step) 0) = true := hc
      rw [Bool.and_eq_true, Nat.ble_eq, Nat.beq_eq] at hc'
      obtain ⟨hbe, hmod⟩ := hc'
      have hmod' : (e - base) % step = 0 := hmod
      change (excMask exc base step ||| 1 <<< ((e - base) / step)).testBit k = true at h
      rw [Nat.testBit_or, Bool.or_eq_true] at h
      rcases h with h | h
      · exact List.mem_cons_of_mem _ (ih h)
      · rw [Nat.one_shiftLeft, Nat.testBit_two_pow, decide_eq_true_eq] at h
        have h2 : step * ((e - base) / step) = e - base :=
          Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hmod')
        rw [← h, h2]
        have : base + (e - base) = e := by omega
        rw [this]
        exact List.mem_cons_self

/-- The block `x = base + step * k`, `Xa ≤ x < Xb`: after the sieve, only bits of listed
exceptions may remain. -/
noncomputable def leafLo (pats : List Pat) (exc : List ℕ) (Xa Xb base step : ℕ) : Bool :=
  (fun b' : ℕ =>
    (fun acc : ℕ =>
      bif Nat.beq acc 0 then true
      else (fun E : ℕ => Nat.beq (Nat.lor acc E) E) (excMask exc b' step))
    (sieveN pats b'
      (Nat.sub (Nat.pow 2 (Nat.div (Nat.add (Nat.sub Xb b') (Nat.sub step 1)) step)) 1)))
  (Nat.add base (Nat.mul step (Nat.div (Nat.add (Nat.sub Xa base) (Nat.sub step 1)) step)))

/-- First element `≥ Xa` of the class `base (mod step)`, above `base`. -/
def firstFrom (Xa base step : ℕ) : ℕ := base + step * ((Xa - base + (step - 1)) / step)

theorem leafLo_eq (pats : List Pat) (exc : List ℕ) (Xa Xb base step : ℕ) :
    leafLo pats exc Xa Xb base step =
      bif Nat.beq (sieveN pats (firstFrom Xa base step)
        (2 ^ blockLen Xb (firstFrom Xa base step) step - 1)) 0 then true
      else Nat.beq (sieveN pats (firstFrom Xa base step)
          (2 ^ blockLen Xb (firstFrom Xa base step) step - 1) |||
        excMask exc (firstFrom Xa base step) step) (excMask exc (firstFrom Xa base step) step) :=
  rfl

theorem le_firstFrom {Xa base step : ℕ} (hs : 0 < step) : Xa ≤ firstFrom Xa base step := by
  unfold firstFrom
  have h := Nat.lt_mul_div_succ (Xa - base + (step - 1)) hs
  have e : step * ((Xa - base + (step - 1)) / step + 1)
      = step * ((Xa - base + (step - 1)) / step) + step := by ring
  omega

theorem firstFrom_decomp {Xa base step x k : ℕ} (hs : 0 < step) (hk : x = base + step * k)
    (ha : Xa ≤ x) : x = firstFrom Xa base step + step * (k - (Xa - base + (step - 1)) / step) := by
  have hle : (Xa - base + (step - 1)) / step ≤ k := by
    have : (Xa - base + (step - 1)) / step < k + 1 := by
      rw [Nat.div_lt_iff_lt_mul hs]
      have e : (k + 1) * step = step * k + step := by ring
      omega
    omega
  unfold firstFrom
  rw [add_assoc, ← mul_add, Nat.add_sub_cancel' hle]
  exact hk

/-- **Soundness of a leaf.** -/
theorem leafLo_sound {P : ℕ → Prop} {pats : List Pat} {exc : List ℕ} {Xa Xb base step : ℕ}
    (hs : 0 < step) (hp : ∀ p ∈ pats, PatSound P step (blockLen Xb Xa step) p)
    (hl : leafLo pats exc Xa Xb base step = true)
    {x k : ℕ} (hx : P x) (hk : x = base + step * k) (ha : Xa ≤ x) (hb : x < Xb) : x ∈ exc := by
  have hk' := firstFrom_decomp hs hk ha
  set b' := firstFrom Xa base step with hb'
  set k' := k - (Xa - base + (step - 1)) / step
  have hkn : k' < blockLen Xb b' step := lt_blockLen hs (hk' ▸ hb)
  have hnm : blockLen Xb b' step ≤ blockLen Xb Xa step := by
    unfold blockLen
    have := le_firstFrom (Xa := Xa) (base := base) hs
    exact Nat.div_le_div_right (by omega)
  have hbit : (sieveN pats b' (2 ^ blockLen Xb b' step - 1)).testBit k' = true := by
    refine sieveN_testBit ?_ ?_
    · rw [Nat.testBit_two_pow_sub_one]; exact decide_eq_true hkn
    · intro p hpm
      exact hp p hpm x b' k' hx hk' (lt_of_lt_of_le hkn hnm)
  rw [leafLo_eq, beq_zero_false hbit] at hl
  have hl' : (sieveN pats b' (2 ^ blockLen Xb b' step - 1) ||| excMask exc b' step)
      = excMask exc b' step := by
    have hl2 : Nat.beq (sieveN pats b' (2 ^ blockLen Xb b' step - 1) ||| excMask exc b' step)
      (excMask exc b' step) = true := hl
    rwa [Nat.beq_eq] at hl2
  have hE : (excMask exc b' step).testBit k' = true := by
    rw [← hl', Nat.testBit_or, hbit]
    rfl
  rw [hk']
  exact excMask_testBit hE

/-! ## Tasks -/

/-- A sieving task: the classes `b (mod step0)` (`b` in a list of bases given separately), the
window `Xa ≤ x < Xb`, the wheel (`top` above the frontier, `rest` below), the groups of sieving
moduli (the lists `P :: inv :: d :: ls` of `gP`, each preceded by a `0`: see `splitZ`), and the
exceptions. -/
structure Task where
  step0 : ℕ
  Xa : ℕ
  Xb : ℕ
  top : List ℕ
  rest : List ℕ
  groups : List ℕ
  exc : List ℕ

/-- Cut a flat list at its zeros: `[0, a, b, 0, c]` is `[[a, b], [c]]` (every part is preceded by
a `0`).  One list literal instead of a list of lists: each list literal costs about 2 ms of
elaboration. -/
noncomputable def splitZ (l : List ℕ) : List (List ℕ) :=
  Prod.snd (List.rec (motive := fun _ => List ℕ × List (List ℕ)) ([], [])
    (fun a _ ih => bif Nat.beq a 0 then ([], ih.1 :: ih.2) else (a :: ih.1, ih.2)) l)

namespace Task

/-- The groups of sieving moduli. -/
noncomputable def grps (t : Task) : List (List ℕ) := splitZ t.groups

noncomputable def stepTop (t : Task) : ℕ := mulAll t.step0 t.top

noncomputable def stepF (t : Task) : ℕ := mulAll t.stepTop t.rest

noncomputable def nmax (t : Task) : ℕ := blockLen t.Xb t.Xa t.stepF

/-- The classes after the levels `top`. -/
noncomputable def frontier (F : Fam) (t : Task) (bases : List ℕ) : List ℕ :=
  flatL (fun b => Sieve.frontier (mapR (prepLevel F) t.top) b t.step0) bases

/-- The check below one class of the frontier.  `extra` are additional patterns (they have to be
sound for the step `t.stepF` and blocks of `t.nmax` bits, see `sound_of_all`). -/
noncomputable def below (F : Fam) (t : Task) (extra : List Pat) (b : ℕ) : Bool :=
  walk (leafLo (appendR extra (mapR (prepGroupF F t.nmax) t.grps)) t.exc t.Xa t.Xb)
    (mapR (prepLevel F) t.rest) b t.stepTop

/-- Validity of the data of the task. -/
noncomputable def valid (F : Fam) (t : Task) : Bool :=
  Bool.and (Nat.ble 1 t.step0) (Bool.and (allL F.valid t.top) (Bool.and (allL F.valid t.rest)
    (allL (groupOkF F t.stepF t.nmax) t.grps)))

/-- The task in one computation. -/
noncomputable def ok (F : Fam) (t : Task) (extra : List Pat) (bases : List ℕ) : Bool :=
  Bool.and (t.valid F) (allL (t.below F extra) (t.frontier F bases))

/-- The cheap part of a task cut into `m` shards of `chunk` classes of the frontier. -/
noncomputable def header (F : Fam) (t : Task) (bases : List ℕ) (chunk m : ℕ) : Bool :=
  Bool.and (t.valid F) (Nat.ble (lenR (t.frontier F bases)) (Nat.mul m chunk))

/-- Shard `i`: the classes number `i * chunk, …, (i + 1) * chunk - 1` of the frontier. -/
noncomputable def shardOk (F : Fam) (t : Task) (extra : List Pat) (bases : List ℕ)
    (chunk i : ℕ) : Bool :=
  allTake (t.below F extra) chunk (dropR (Nat.mul i chunk) (t.frontier F bases))

/-- The shards `0, …, k - 1` have been checked. -/
def ShardsUpTo (F : Fam) (t : Task) (extra : List Pat) (bases : List ℕ) (chunk k : ℕ) : Prop :=
  ∀ i < k, t.shardOk F extra bases chunk i = true

theorem shardsUpTo_zero (F : Fam) (t : Task) (extra : List Pat) (bases : List ℕ) (chunk : ℕ) :
    t.ShardsUpTo F extra bases chunk 0 :=
  fun _ h => absurd h (Nat.not_lt_zero _)

theorem ShardsUpTo.succ {F : Fam} {t : Task} {extra : List Pat} {bases : List ℕ} {chunk k : ℕ}
    (h : t.ShardsUpTo F extra bases chunk k) (hk : t.shardOk F extra bases chunk k = true) :
    t.ShardsUpTo F extra bases chunk (k + 1) := by
  intro i hi
  rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h' | rfl
  · exact h i h'
  · exact hk

theorem sound_of_all {F : Fam} {P : ℕ → Prop} {t : Task} {extra : List Pat} {bases : List ℕ}
    (hF : F.Sound P) (he : ∀ p ∈ extra, PatSound P t.stepF t.nmax p)
    (hv : t.valid F = true) (hall : ∀ b ∈ t.frontier F bases, t.below F extra b = true)
    {x : ℕ} (hx : P x) (hb : ∃ b ∈ bases, ∃ k, x = b + t.step0 * k) (ha : t.Xa ≤ x)
    (hxb : x < t.Xb) : x ∈ t.exc := by
  unfold valid at hv
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Nat.ble_eq] at hv
  obtain ⟨h0, htop, hrest, hgr⟩ := hv
  have htop' : LevelsSound P t.step0 (t.top.map (prepLevel F)) := levelsSound hF htop
  have hrest' : LevelsSound P t.stepTop (t.rest.map (prepLevel F)) := levelsSound hF hrest
  have hst : stepAfter t.step0 (t.top.map (prepLevel F)) = t.stepTop := stepAfter_prepLevel _ _ _
  have hsf : stepAfter t.stepTop (t.rest.map (prepLevel F)) = t.stepF := stepAfter_prepLevel _ _ _
  have hpos1 : 0 < t.stepTop := hst ▸ stepAfter_pos htop' h0
  have hpos2 : 0 < t.stepF := hsf ▸ stepAfter_pos hrest' hpos1
  obtain ⟨b, hbm, k, hk⟩ := hb
  obtain ⟨b', hb', k', hk'⟩ := frontier_sound htop' hx hk
  rw [hst] at hk'
  have hmem : b' ∈ t.frontier F bases := by
    unfold frontier
    rw [mapR_eq]
    exact mem_flatL.2 ⟨b, hbm, hb'⟩
  have hw : walk (leafLo (extra ++ t.grps.map (prepGroupF F t.nmax)) t.exc t.Xa t.Xb)
      (t.rest.map (prepLevel F)) b' t.stepTop = true := by
    have := hall b' hmem
    unfold below at this
    rwa [mapR_eq, mapR_eq, appendR_eq] at this
  obtain ⟨b'', k'', hk'', hleaf⟩ := walk_sound hrest' hw hx hk'
  rw [hsf] at hk'' hleaf
  refine leafLo_sound (P := P) hpos2 (fun p hp => ?_) hleaf hx hk'' ha hxb
  rcases List.mem_append.1 hp with hp | hp
  · exact he p hp
  · obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hp
    exact groupOkF_sound hF (allL_iff.1 hgr g hg)

/-- **Soundness of a task done in one computation.** -/
theorem ok_sound {F : Fam} {P : ℕ → Prop} {t : Task} {extra : List Pat} {bases : List ℕ}
    (hF : F.Sound P) (he : ∀ p ∈ extra, PatSound P t.stepF t.nmax p)
    (h : t.ok F extra bases = true) {x : ℕ} (hx : P x)
    (hb : ∃ b ∈ bases, ∃ k, x = b + t.step0 * k) (ha : t.Xa ≤ x) (hxb : x < t.Xb) :
    x ∈ t.exc := by
  unfold ok at h
  rw [Bool.and_eq_true, allL_iff] at h
  exact sound_of_all hF he h.1 h.2 hx hb ha hxb

/-- **Soundness of a task cut into shards.** -/
theorem sound {F : Fam} {P : ℕ → Prop} {t : Task} {extra : List Pat} {bases : List ℕ}
    {chunk m : ℕ} (hF : F.Sound P) (he : ∀ p ∈ extra, PatSound P t.stepF t.nmax p)
    (hh : t.header F bases chunk m = true) (hs : t.ShardsUpTo F extra bases chunk m)
    {x : ℕ} (hx : P x) (hb : ∃ b ∈ bases, ∃ k, x = b + t.step0 * k) (ha : t.Xa ≤ x)
    (hxb : x < t.Xb) : x ∈ t.exc := by
  unfold header at hh
  rw [Bool.and_eq_true, Nat.ble_eq, lenR_eq] at hh
  exact sound_of_all hF he hh.1 (all_of_chunks hh.2 hs) hx hb ha hxb

end Task

end Exp7.SieveLow
