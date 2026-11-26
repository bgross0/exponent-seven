import Mathlib

/-!
# Square roots modulo prime powers: odd primes, non-residues, kernel-evaluable tests

Part of the `Exp7.Roots` toolkit (see `RootsCert.lean` for the packaged checker).

* `Complete m a L` : every natural `x` with `x ^ 2 ≡ a [MOD m]` has `x % m ∈ L`.
* `sq_modEq_odd_prime_pow` / `complete_odd_prime_pow` : the two roots `±r` modulo an odd
  prime power.
* `powMod`, `eulerNonRes` : fuel-based modular power and Euler's non-residue test, with
  soundness `not_sq_of_eulerNonRes`.
* `isOddPrimeB` : trial-division test for odd primes, with soundness `isOddPrimeB_sound`.
* `isOddPrimeF` : fast test (table below `2048`, one gcd below `2 ^ 22`), with soundness
  `isOddPrimeF_sound`.

All `Bool`/`ℕ` functions are structurally recursive on a fuel argument and use only raw
`Nat` operations, so that the kernel can evaluate them with GMP acceleration.
-/

namespace Exp7.Roots

/-- `L` contains the residue mod `m` of every natural solution of `x ^ 2 ≡ a (mod m)`. -/
def Complete (m a : ℕ) (L : List ℕ) : Prop :=
  ∀ x : ℕ, x ^ 2 ≡ a [MOD m] → x % m ∈ L

theorem Complete.mono {m a : ℕ} {L L' : List ℕ} (h : Complete m a L) (hL : L ⊆ L') :
    Complete m a L' := fun x hx => hL (h x hx)

/-- `Bool.rec` (used in the raw kernel-friendly definitions) is `cond`. -/
theorem boolRec_eq_cond {α : Type} (a b : α) (c : Bool) :
    (Bool.rec a b c : α) = bif c then b else a := by
  cases c <;> rfl

theorem boolRec_false_eq_and (a b : Bool) : (Bool.rec false b a : Bool) = (a && b) := by
  cases a <;> rfl

/-! ## Goal 1: odd prime powers -/

/-- **Odd prime powers (integers).** If `l` is an odd prime, `k ≥ 1`, `l ∤ a` and
`r ^ 2 ≡ a (mod l ^ k)`, then every `x` with `x ^ 2 ≡ a (mod l ^ k)` is `≡ r` or `≡ -r`. -/
theorem sq_modEq_odd_prime_pow {l : ℕ} (hl : l.Prime) (hodd : l ≠ 2) {k : ℕ} (hk : 1 ≤ k)
    {a r x : ℤ} (ha : ¬ (l : ℤ) ∣ a) (hr : r ^ 2 ≡ a [ZMOD (l : ℤ) ^ k])
    (hx : x ^ 2 ≡ a [ZMOD (l : ℤ) ^ k]) :
    x ≡ r [ZMOD (l : ℤ) ^ k] ∨ x ≡ -r [ZMOD (l : ℤ) ^ k] := by
  have hp : Prime (l : ℤ) := Nat.prime_iff_prime_int.mp hl
  have h1 : (l : ℤ) ^ k ∣ (x - r) * (x + r) := by
    have h := (hr.trans hx.symm).dvd
    have e : (x - r) * (x + r) = x ^ 2 - r ^ 2 := by ring
    rw [e]; exact h
  have hlk : (l : ℤ) ∣ (l : ℤ) ^ k := dvd_pow_self _ (by omega)
  by_cases hd : (l : ℤ) ∣ x - r
  · have hnd : ¬ (l : ℤ) ∣ x + r := by
      intro hd2
      have h2r : (l : ℤ) ∣ 2 * r := by
        have h := dvd_sub hd2 hd
        have e : x + r - (x - r) = 2 * r := by ring
        rwa [e] at h
      have hl2 : ¬ (l : ℤ) ∣ 2 := by
        intro h
        have h' : l ∣ 2 := by exact_mod_cast h
        exact hodd ((Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).mp h')
      have hlr : (l : ℤ) ∣ r := (hp.dvd_or_dvd h2r).resolve_left hl2
      have hla : (l : ℤ) ∣ a - r ^ 2 := hlk.trans hr.dvd
      have : (l : ℤ) ∣ a := by
        have h := dvd_add hla (dvd_pow hlr (two_ne_zero))
        have e : a - r ^ 2 + r ^ 2 = a := by ring
        rwa [e] at h
      exact ha this
    left
    have h2 := hp.pow_dvd_of_dvd_mul_right k hnd h1
    exact (Int.modEq_iff_dvd.mpr h2).symm
  · right
    have h2 := hp.pow_dvd_of_dvd_mul_left k hd h1
    have e : x + r = x - (-r) := by ring
    rw [e] at h2
    exact (Int.modEq_iff_dvd.mpr h2).symm

/-- If `q ∣ x + r` (in `ℤ`) then `x % q = (q - r % q) % q`. -/
theorem mod_eq_neg_of_dvd_add {q x r : ℕ} (hq : 0 < q) (h : (q : ℤ) ∣ (x : ℤ) + r) :
    x % q = (q - r % q) % q := by
  have hlt : r % q < q := Nat.mod_lt _ hq
  have hmod : x ≡ q - r % q [MOD q] := by
    rw [Nat.modEq_iff_dvd]
    obtain ⟨c, hc⟩ := h
    have hr : (r : ℤ) = q * ((r : ℤ) / q) + (r : ℤ) % q := (Int.mul_ediv_add_emod _ _).symm
    refine ⟨1 - c + (r : ℤ) / q, ?_⟩
    push_cast [Nat.cast_sub hlt.le]
    linarith
  exact hmod

/-- **Odd prime powers (naturals, list form).** -/
theorem complete_odd_prime_pow {l : ℕ} (hl : l.Prime) (hodd : l ≠ 2) {k : ℕ} (hk : 1 ≤ k)
    {a r : ℕ} (ha : ¬ l ∣ a) (hr : r ^ 2 ≡ a [MOD l ^ k]) :
    Complete (l ^ k) a [r % l ^ k, l ^ k - r % l ^ k] := by
  intro x hx
  have hq : 0 < l ^ k := Nat.pow_pos hl.pos
  have haZ : ¬ (l : ℤ) ∣ (a : ℤ) := by
    intro h; exact ha (by exact_mod_cast h)
  have hrZ : (r : ℤ) ^ 2 ≡ (a : ℤ) [ZMOD (l : ℤ) ^ k] := by
    have := (Int.natCast_modEq_iff).mpr hr
    simpa using this
  have hxZ : (x : ℤ) ^ 2 ≡ (a : ℤ) [ZMOD (l : ℤ) ^ k] := by
    have := (Int.natCast_modEq_iff).mpr hx
    simpa using this
  rcases sq_modEq_odd_prime_pow hl hodd hk haZ hrZ hxZ with h | h
  · have h' : x ≡ r [MOD l ^ k] := by
      apply (Int.natCast_modEq_iff).mp
      simpa using h
    have : x % l ^ k = r % l ^ k := h'
    simp [this]
  · have hdvd : ((l ^ k : ℕ) : ℤ) ∣ (x : ℤ) + r := by
      have := h.symm.dvd
      simpa using this
    have h1 := mod_eq_neg_of_dvd_add hq hdvd
    have hlt : r % l ^ k < l ^ k := Nat.mod_lt _ hq
    have hne : r % l ^ k ≠ 0 := by
      intro h0
      have hlr : l ∣ r := (dvd_pow_self l (by omega : k ≠ 0)).trans (Nat.dvd_of_mod_eq_zero h0)
      have hmod : r ^ 2 ≡ a [MOD l] := hr.of_dvd (dvd_pow_self l (by omega : k ≠ 0))
      have : l ∣ a := (hmod.dvd_iff dvd_rfl).mp (dvd_pow hlr two_ne_zero)
      exact ha this
    rw [Nat.mod_eq_of_lt (Nat.sub_lt hq (Nat.pos_of_ne_zero hne))] at h1
    simp [h1]

/-! ## Goal 2: non-residues and Euler's criterion -/

/-- Fuel-based square-and-multiply: returns `acc * b ^ e` modulo `m` when `e < 2 ^ fuel`.
Written with raw recursors and raw `Nat` operations for fast kernel reduction; see
`powModAux_zero` and `powModAux_succ` for the readable recursion equations. -/
def powModAux (m fuel : ℕ) : ℕ → ℕ → ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ → ℕ) (fun _ _ acc => acc)
    (fun _ ih b e acc =>
      Bool.rec
        (ih (Nat.mod (Nat.mul b b) m) (Nat.div e (nat_lit 2))
          (Bool.rec acc (Nat.mod (Nat.mul acc b) m) (Nat.beq (Nat.mod e (nat_lit 2)) (nat_lit 1))))
        acc (Nat.beq e (nat_lit 0)))
    fuel

theorem powModAux_zero (m b e acc : ℕ) : powModAux m 0 b e acc = acc := rfl

theorem powModAux_succ (m f b e acc : ℕ) : powModAux m (f + 1) b e acc =
    bif e.beq 0 then acc
    else powModAux m f (b * b % m) (e / 2) (bif (e % 2).beq 1 then acc * b % m else acc) := by
  change Bool.rec (motive := fun _ => ℕ)
    (powModAux m f (b * b % m) (e / 2)
      (Bool.rec (motive := fun _ => ℕ) acc (acc * b % m) ((e % 2).beq 1)))
    acc (e.beq 0) = _
  rw [boolRec_eq_cond, boolRec_eq_cond]

theorem powModAux_spec (m : ℕ) : ∀ (f b e acc : ℕ), e < 2 ^ f →
    powModAux m f b e acc ≡ acc * b ^ e [MOD m] := by
  intro f
  induction f with
  | zero =>
    intro b e acc he
    have : e = 0 := by simpa using he
    subst this
    simp [powModAux_zero, Nat.ModEq]
  | succ f ih =>
    intro b e acc he
    rw [powModAux_succ]
    by_cases h0 : e = 0
    · subst h0; simp [Nat.ModEq]
    · have hb : e.beq 0 = false := by
        rw [Bool.eq_false_iff]; intro h; exact h0 (Nat.eq_of_beq_eq_true h)
      rw [hb, Bool.cond_false]
      have he2 : e / 2 < 2 ^ f := by
        rw [pow_succ] at he; omega
      have hbb : (b * b % m) ^ (e / 2) ≡ b ^ (2 * (e / 2)) [MOD m] := by
        have : b * b % m ≡ b ^ 2 [MOD m] := by
          rw [pow_two]; exact Nat.mod_modEq _ _
        rw [pow_mul]; exact this.pow _
      refine (ih _ _ _ he2).trans ?_
      by_cases hodd : e % 2 = 1
      · have hc : (e % 2).beq 1 = true := by rw [hodd]; rfl
        rw [hc, Bool.cond_true]
        have he' : e = 2 * (e / 2) + 1 := by omega
        have : acc * b ^ e = acc * b * b ^ (2 * (e / 2)) := by
          conv_lhs => rw [he']
          ring
        rw [this]
        exact ((Nat.mod_modEq _ _).mul hbb)
      · have hc : (e % 2).beq 1 = false := by
          rw [Bool.eq_false_iff]; intro h; exact hodd (Nat.eq_of_beq_eq_true h)
        rw [hc, Bool.cond_false]
        have he' : e = 2 * (e / 2) := by omega
        conv_rhs => rw [he']
        exact (Nat.ModEq.refl acc).mul hbb

/-- Modular power `b ^ e mod m` (kernel friendly). -/
def powMod (b e m : ℕ) : ℕ := powModAux m (e + 1) (b % m) e 1 % m

theorem powMod_eq (b e m : ℕ) : powMod b e m = b ^ e % m := by
  unfold powMod
  have h := powModAux_spec m (e + 1) (b % m) e 1
    (lt_trans Nat.lt_two_pow_self (Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self e)))
  have h2 : 1 * (b % m) ^ e ≡ b ^ e [MOD m] := by
    rw [one_mul]; exact (Nat.mod_modEq b m).pow e
  exact h.trans h2

/-- Euler's criterion as a Boolean non-residue test: `a ^ ((l - 1) / 2) ≡ -1 (mod l)`. -/
def eulerNonRes (a l : ℕ) : Bool := (powMod a ((l - 1) / 2) l).beq (l - 1)

/-- **Non-residues.** If `l` is an odd prime and Euler's test reports a non-residue, then
`x ^ 2 ≡ a (mod l ^ k)` has no solution for `k ≥ 1`. -/
theorem not_sq_of_eulerNonRes {l a : ℕ} (hl : l.Prime) (hodd : l ≠ 2)
    (h : eulerNonRes a l = true) {k : ℕ} (hk : 1 ≤ k) (x : ℕ) : ¬ x ^ 2 ≡ a [MOD l ^ k] := by
  intro hx
  have : Fact l.Prime := ⟨hl⟩
  have hl2 : 2 ≤ l := hl.two_le
  have hl3 : l % 2 = 1 := by
    rcases hl.eq_two_or_odd with h2 | h2
    · exact absurd h2 hodd
    · exact h2
  have hxl : x ^ 2 ≡ a [MOD l] := hx.of_dvd (dvd_pow_self l (by omega : k ≠ 0))
  have he : a ^ ((l - 1) / 2) % l = l - 1 := by
    have := Nat.eq_of_beq_eq_true h
    rwa [powMod_eq] at this
  have hz : ((a : ZMod l)) ^ ((l - 1) / 2) = ((l - 1 : ℕ) : ZMod l) := by
    have h1 : a ^ ((l - 1) / 2) ≡ l - 1 [MOD l] := by
      unfold Nat.ModEq
      rw [he, Nat.mod_eq_of_lt (by omega)]
    have := (ZMod.natCast_eq_natCast_iff _ _ _).mpr h1
    simpa using this
  have hneg : ((l - 1 : ℕ) : ZMod l) = -1 := by
    rw [Nat.cast_sub (by omega)]
    simp
  have hxa : ((x : ZMod l)) ^ 2 = (a : ZMod l) := by
    have := (ZMod.natCast_eq_natCast_iff _ _ _).mpr hxl
    simpa using this
  have hpow : ((x : ZMod l)) ^ (l - 1) = -1 := by
    have e : l - 1 = 2 * ((l - 1) / 2) := by omega
    rw [e, pow_mul, hxa, hz, hneg]
  have hne : (-1 : ZMod l) ≠ 1 := by
    intro h1
    have h2 : (2 : ZMod l) = 0 := by
      have : (1 : ZMod l) + 1 = 0 := by
        nth_rewrite 1 [← h1]; ring
      rw [← this]; norm_num
    have h3 : ((2 : ℕ) : ZMod l) = 0 := by exact_mod_cast h2
    rw [ZMod.natCast_eq_zero_iff] at h3
    exact hodd ((Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).mp h3)
  by_cases hx0 : (x : ZMod l) = 0
  · rw [hx0, zero_pow (by omega)] at hpow
    have : (1 : ZMod l) = 0 := by
      have := congrArg (fun t => -t) hpow
      simpa using this.symm
    exact one_ne_zero this
  · rw [ZMod.pow_card_sub_one_eq_one hx0] at hpow
    exact hne hpow.symm

theorem complete_of_eulerNonRes {l a : ℕ} (hl : l.Prime) (hodd : l ≠ 2)
    (h : eulerNonRes a l = true) {k : ℕ} (hk : 1 ≤ k) : Complete (l ^ k) a [] :=
  fun x hx => absurd hx (not_sq_of_eulerNonRes hl hodd h hk x)

/-! ## Primality test by odd trial division -/

/-- `noDivOdd n fuel d = true` implies that no odd `c ≥ d` with `c * c ≤ n` divides `n`
(for odd `d`).  Returns `false` if the fuel runs out.  Raw recursors for kernel speed; see
`noDivOdd_zero`, `noDivOdd_succ`. -/
def noDivOdd (n fuel : ℕ) : ℕ → Bool :=
  Nat.rec (motive := fun _ => ℕ → Bool) (fun _ => false)
    (fun _ ih d =>
      Bool.rec
        (Bool.rec (ih (Nat.add d (nat_lit 2))) false (Nat.beq (Nat.mod n d) (nat_lit 0)))
        true (Nat.ble (Nat.succ n) (Nat.mul d d)))
    fuel

theorem noDivOdd_zero (n d : ℕ) : noDivOdd n 0 d = false := rfl

theorem noDivOdd_succ (n f d : ℕ) : noDivOdd n (f + 1) d =
    (bif Nat.blt n (d * d) then true
    else bif (n % d).beq 0 then false
    else noDivOdd n f (d + 2)) := by
  change Bool.rec (motive := fun _ => Bool)
    (Bool.rec (motive := fun _ => Bool) (noDivOdd n f (d + 2)) false ((n % d).beq 0)) true
    (Nat.blt n (d * d)) = _
  rw [boolRec_eq_cond, boolRec_eq_cond]

theorem noDivOdd_sound (n : ℕ) : ∀ (f d : ℕ), d % 2 = 1 → noDivOdd n f d = true →
    ∀ c, c % 2 = 1 → d ≤ c → c * c ≤ n → ¬ c ∣ n := by
  intro f
  induction f with
  | zero => intro d _ h; simp [noDivOdd_zero] at h
  | succ f ih =>
    intro d hd h c hc hdc hcc hdvd
    rw [noDivOdd_succ] at h
    by_cases h1 : n < d * d
    · have : d * d ≤ c * c := Nat.mul_le_mul hdc hdc
      omega
    · have hb : Nat.blt n (d * d) = false := by
        rw [Bool.eq_false_iff]; intro hh; exact h1 (by simpa using hh)
      rw [hb, Bool.cond_false] at h
      by_cases h2 : n % d = 0
      · have hb2 : (n % d).beq 0 = true := by rw [h2]; rfl
        rw [hb2, Bool.cond_true] at h
        exact absurd h (by simp)
      · have hb2 : (n % d).beq 0 = false := by
          rw [Bool.eq_false_iff]; intro hh; exact h2 (Nat.eq_of_beq_eq_true hh)
        rw [hb2, Bool.cond_false] at h
        by_cases hcd : c = d
        · subst hcd; exact h2 (Nat.mod_eq_zero_of_dvd hdvd)
        · exact ih (d + 2) (by omega) h c hc (by omega) hcc hdvd

/-- Kernel-evaluable test: `n` is an odd prime. -/
def isOddPrimeB (n : ℕ) : Bool :=
  (n % 2).beq 1 && Nat.ble 3 n && noDivOdd n n 3

theorem isOddPrimeB_sound {n : ℕ} (h : isOddPrimeB n = true) : n.Prime ∧ n ≠ 2 := by
  unfold isOddPrimeB at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  have hodd : n % 2 = 1 := Nat.eq_of_beq_eq_true h1
  have h3n : 3 ≤ n := by simpa using h2
  refine ⟨?_, by omega⟩
  rw [Nat.prime_def_le_sqrt]
  refine ⟨by omega, ?_⟩
  intro m hm hms hdvd
  have hmm : m * m ≤ n := Nat.le_sqrt.mp hms
  by_cases hmo : m % 2 = 1
  · exact noDivOdd_sound n n 3 (by norm_num) h3 m hmo (by omega) hmm hdvd
  · have h2m : 2 ∣ m := Nat.dvd_of_mod_eq_zero (by omega)
    have : 2 ∣ n := h2m.trans hdvd
    omega

/-! ## Fast primality test below `2 ^ 22` (one gcd) -/

/-- `allBelow P n` checks `P k` for all `k < n`. -/
def allBelow (P : ℕ → Bool) : ℕ → Bool
  | 0 => true
  | n + 1 => P n && allBelow P n

theorem allBelow_spec {P : ℕ → Bool} : ∀ {n : ℕ}, allBelow P n = true → ∀ k < n, P k = true := by
  intro n
  induction n with
  | zero => intro _ k hk; omega
  | succ n ih =>
    intro h k hk
    simp only [allBelow, Bool.and_eq_true] at h
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with h1 | h1
    · exact ih h.2 k h1
    · rw [h1]; exact h.1

set_option linter.style.longLine false in
/-- The product of all odd numbers `3 ≤ d < 2048`. -/
def oddProd2048 : ℕ := 1717192632498306186840864835241869577707131861959612864748921578685369140248119017622847804764949683481847236882229362038708895582247416806587103623268522632662601978852625474121901293049560875878205182269122358565058872855782267144358639153005379254546671282232814904681773469208927548424409560797775274266524295823885370064942778988941385832524228388881662253042412784044882262683018330119843357286801059463540365315571097756970548130980969994696598312864113156229635783621241054298260805978838585549754654982755168870988127536347250711729304911277809336858689566108357873808898214074482538389373606832887689982667780213516159503262074467181728402108623990433576866858727722479980104734526526199244638376029846607852253779339166433189992642813180894943372501552259800223053223793048505666015707156783066088492895567232968939573531325870833254102866279106640145453988081446420844393608155140136440473474497176935792134133770415907155120230789114579772730348260566395777849290882469454787606493143309091102820138949936703059726543200226650393916470801480625820931334312261672734614814429429737259995036584306691254845779650142245665754497485909648044998617835878541814884192134461303464323856409687220154081304104612359473477387408207323981700075429861952625567556403493126750656080758202341466170979736152044869199395222467177796778125671100488931437075606131788651030874674482459913005779232307437455925388179139177228064881944966422919275409964420811777401337219658861697704045416694070742876684925047276276720512029229920234282083393414859966394400854468921133415994811494004592742536936431886657593344189674226457912268377009709875386658457647747237442293233610712853579545957210576219649330752532852780940482672561068530030673500833728663699551721846460661694387767743925815936932610763641047352547006443870376850515594987643545916170518557951304643950076651080685615824384215977306646934520152584158362336860367655603365080186242989255561324552070427092949695884348304123042806373788328870325880853792460089135853471606315898457242358776401882821031473228736550912553782968010424962923484869528602139600955006261687499677935676774652490638230049786440511272630057903979775680345193745836049398160450768537386900035926692961141804748808588489908947283358910152757593669944931111803615101583415023167459928888392958625351355673479599638668073955114991612407242457200954418055949738784988715399478011086380865491673523450844021008286953002900046240695832062088772046961973476066014524322287338550470765888306803560681202074683084467257254751932593469683641594770418233366376599606188270204350895171551612956102329792155263782177682825348651249424067491277108871487190714944683890334335023491678001665875860702504258383654534383034731934246605095986317523600155931262681794117812375631566074576666349246002130266843977242287535434987425999813987457111432238878892635204748022253560047184592911963114101638050446041461327695287764072418212890625

set_option linter.style.longLine false in
/-- Bit `l` is set iff `l` is an odd prime below `2048`. -/
def primeMask2048 : ℕ := 63196217514619685787302661944283627187480419032319820369017850665328321138708391315200183959507999056023352639375846703234831001873166395556955644493858061439808708910934156148183046598761628011780268338219791422514227681445909709648670979243590805462655306771032202820077139493529183977397365147098062663022532814175064567798686854251762647113947230088557214201782733277971254644853105063950192427823002366063866805552748617765139883929239541449093372319343685321581363697099596177954105829051640519504929052531195879727266309174681254395317624664765523960588612557182115629928513422897626942842560083486994737320

theorem oddProd2048_dvd {d : ℕ} (hodd : d % 2 = 1) (h3 : 3 ≤ d) (hd : d < 2048) :
    d ∣ oddProd2048 := by
  have h : allBelow (fun d => (d % 2).beq 0 || Nat.blt d 3 || (oddProd2048 % d).beq 0) 2048
      = true := by decide +kernel
  have := allBelow_spec h d hd
  simp only [Bool.or_eq_true] at this
  rcases this with (h1 | h1) | h1
  · have := Nat.eq_of_beq_eq_true h1; omega
  · have : d < 3 := by simpa using h1
    omega
  · exact Nat.dvd_of_mod_eq_zero (Nat.eq_of_beq_eq_true h1)

theorem primeMask2048_sound {l : ℕ} (hl : l < 2048)
    (h : ((primeMask2048 / 2 ^ l) % 2).beq 1 = true) : isOddPrimeB l = true := by
  have h0 : allBelow (fun l => !((primeMask2048 / 2 ^ l) % 2).beq 1 || isOddPrimeB l) 2048
      = true := by decide +kernel
  have := allBelow_spec h0 l hl
  rw [h] at this
  simpa using this

/-- Fast kernel-evaluable test that `l` is an odd prime: table lookup below `2048`, a single
gcd with `oddProd2048` below `2 ^ 22 = 4194304`, trial division above.  Raw operations for
kernel speed; see `isOddPrimeF_eq`. -/
def isOddPrimeF (l : ℕ) : Bool :=
  Bool.rec
    (Bool.rec (isOddPrimeB l)
      (Bool.rec false (Nat.beq (Nat.gcd l oddProd2048) (nat_lit 1))
        (Nat.beq (Nat.mod l (nat_lit 2)) (nat_lit 1)))
      (Nat.ble (Nat.succ l) (nat_lit 4194304)))
    (Nat.beq (Nat.mod (Nat.div primeMask2048 (Nat.pow (nat_lit 2) l)) (nat_lit 2)) (nat_lit 1))
    (Nat.ble (Nat.succ l) (nat_lit 2048))

theorem isOddPrimeF_eq (l : ℕ) : isOddPrimeF l =
    (bif Nat.blt l 2048 then ((primeMask2048 / 2 ^ l) % 2).beq 1
    else bif Nat.blt l 4194304 then (l % 2).beq 1 && (Nat.gcd l oddProd2048).beq 1
    else isOddPrimeB l) := by
  change Bool.rec (motive := fun _ => Bool)
    (Bool.rec (motive := fun _ => Bool) (isOddPrimeB l)
      (Bool.rec (motive := fun _ => Bool) false ((Nat.gcd l oddProd2048).beq 1) ((l % 2).beq 1))
      (Nat.blt l 4194304))
    (((primeMask2048 / 2 ^ l) % 2).beq 1) (Nat.blt l 2048) = _
  rw [boolRec_eq_cond, boolRec_eq_cond, boolRec_eq_cond]
  cases (l % 2).beq 1 <;> rfl

theorem isOddPrimeF_sound {n : ℕ} (h : isOddPrimeF n = true) : n.Prime ∧ n ≠ 2 := by
  rw [isOddPrimeF_eq] at h
  by_cases h1 : n < 2048
  · have hb : Nat.blt n 2048 = true := by simpa using h1
    rw [hb, Bool.cond_true] at h
    exact isOddPrimeB_sound (primeMask2048_sound h1 h)
  · have hb : Nat.blt n 2048 = false := by
      rw [Bool.eq_false_iff]; intro hh; exact h1 (by simpa using hh)
    rw [hb, Bool.cond_false] at h
    by_cases h2 : n < 4194304
    · have hb2 : Nat.blt n 4194304 = true := by simpa using h2
      rw [hb2, Bool.cond_true, Bool.and_eq_true] at h
      obtain ⟨ho, hg⟩ := h
      have hodd : n % 2 = 1 := Nat.eq_of_beq_eq_true ho
      have hgcd : Nat.gcd n oddProd2048 = 1 := Nat.eq_of_beq_eq_true hg
      refine ⟨?_, by omega⟩
      rw [Nat.prime_def_le_sqrt]
      refine ⟨by omega, ?_⟩
      intro m hm hms hdvd
      have hmm : m * m ≤ n := Nat.le_sqrt.mp hms
      have hm2048 : m < 2048 := by
        by_contra hge
        have hge' : 2048 ≤ m := by omega
        have := Nat.mul_le_mul hge' hge'
        omega
      by_cases hmo : m % 2 = 1
      · have h1 : m ∣ Nat.gcd n oddProd2048 :=
          Nat.dvd_gcd hdvd (oddProd2048_dvd hmo (by omega) hm2048)
        rw [hgcd] at h1
        have := Nat.dvd_one.mp h1
        omega
      · have h2m : 2 ∣ m := Nat.dvd_of_mod_eq_zero (by omega)
        have : 2 ∣ n := h2m.trans hdvd
        omega
    · have hb2 : Nat.blt n 4194304 = false := by
        rw [Bool.eq_false_iff]; intro hh; exact h2 (by simpa using hh)
      rw [hb2, Bool.cond_false] at h
      exact isOddPrimeB_sound h

end Exp7.Roots
