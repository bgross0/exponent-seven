import Exp7Lean.Above

/-!
Exponent 7: Theorem D, the classification for all `q ≤ 10^32` without the EKN table.

The 124 extra certificate rows below are generated from `lowrange/certificate_full.json`.
The fields of `LowInputs` are the steps of Section 3 of the note that are not formalized:

* `normEqPrim` — Step 1 with the remark that `p ∤ y` for odd `p` (proved in `Step1.lean`).
* `certLow`    — the 124 extra certificate rows (explicit formula under GRH; rows verified outside
                 Lean by both verifiers).
* `direct`     — class groups of the 4808 primes `q ≡ 3 (mod 4)` below `10^5` (`lowrange/direct.py`).
* `searchLow`  — the search `lowsearch` over the 401 primes `3 ≤ p < 2760` together with the
                 classification of its 6608 survivors (`lowrange/classify.py`): the only prime
                 survivor with class group of exponent 7 is `118843`.
* `exp118843`  — the class group of `ℚ(√-118843)` has exponent 7.
-/

namespace Exp7

open Classical

/-- Below `B` the class groups are computed directly. -/
def B : ℕ := 10 ^ 5

/-- The 124 extra ladder rows, from `Q ≈ 2.3·10^20` down to `Q = B`. -/
def lowRows : List Row := [
  ⟨232467204893061316608, 2729⟩,
  ⟨174325810809008226304, 2698⟩,
  ⟨130725916062860509184, 2667⟩,
  ⟨98030607465219751936, 2636⟩,
  ⟨73512584875511316480, 2605⟩,
  ⟨55126661711206604800, 2574⟩,
  ⟨41339164397063045120, 2544⟩,
  ⟨31000000000000000000, 2514⟩,
  ⟨23246720489306132480, 2484⟩,
  ⟨17432581080900820992, 2455⟩,
  ⟨13072591606286051328, 2426⟩,
  ⟨9803060746521976832, 2397⟩,
  ⟨7351258487551130624, 2368⟩,
  ⟨5512666171120660480, 2339⟩,
  ⟨4133916439706304512, 2310⟩,
  ⟨3100000000000000000, 2281⟩,
  ⟨2324672048930613248, 2253⟩,
  ⟨1743258108090082048, 2224⟩,
  ⟨1307259160628604928, 2196⟩,
  ⟨980306074652197504, 2168⟩,
  ⟨735125848755113088, 2140⟩,
  ⟨551266617112066112, 2112⟩,
  ⟨413391643970630464, 2085⟩,
  ⟨310000000000000000, 2058⟩,
  ⟨232467204893061280, 2030⟩,
  ⟨174325810809008224, 2003⟩,
  ⟨130725916062860512, 1976⟩,
  ⟨98030607465219760, 1949⟩,
  ⟨73512584875511312, 1923⟩,
  ⟨55126661711206608, 1896⟩,
  ⟨41339164397063048, 1870⟩,
  ⟨31000000000000000, 1844⟩,
  ⟨23246720489306132, 1818⟩,
  ⟨17432581080900822, 1793⟩,
  ⟨13072591606286050, 1768⟩,
  ⟨9803060746521976, 1743⟩,
  ⟨7351258487551132, 1719⟩,
  ⟨5512666171120661, 1694⟩,
  ⟨4133916439706304, 1670⟩,
  ⟨3100000000000000, 1646⟩,
  ⟨2324672048930613, 1622⟩,
  ⟨1743258108090082, 1599⟩,
  ⟨1307259160628605, 1575⟩,
  ⟨980306074652197, 1551⟩,
  ⟨735125848755113, 1528⟩,
  ⟨551266617112066, 1504⟩,
  ⟨413391643970630, 1481⟩,
  ⟨310000000000000, 1458⟩,
  ⟨232467204893061, 1435⟩,
  ⟨174325810809008, 1411⟩,
  ⟨130725916062860, 1388⟩,
  ⟨98030607465219, 1365⟩,
  ⟨73512584875511, 1343⟩,
  ⟨55126661711206, 1321⟩,
  ⟨41339164397063, 1300⟩,
  ⟨31000000000000, 1278⟩,
  ⟨23246720489306, 1257⟩,
  ⟨17432581080900, 1235⟩,
  ⟨13072591606286, 1214⟩,
  ⟨9803060746521, 1193⟩,
  ⟨7351258487551, 1172⟩,
  ⟨5512666171120, 1152⟩,
  ⟨4133916439706, 1131⟩,
  ⟨3100000000000, 1112⟩,
  ⟨2324672048930, 1092⟩,
  ⟨1743258108090, 1072⟩,
  ⟨1307259160628, 1052⟩,
  ⟨980306074652, 1033⟩,
  ⟨735125848755, 1013⟩,
  ⟨551266617112, 994⟩,
  ⟨413391643970, 974⟩,
  ⟨310000000000, 955⟩,
  ⟨232467204893, 936⟩,
  ⟨174325810809, 917⟩,
  ⟨130725916062, 899⟩,
  ⟨98030607465, 881⟩,
  ⟨73512584875, 863⟩,
  ⟨55126661711, 845⟩,
  ⟨41339164397, 827⟩,
  ⟨31000000000, 810⟩,
  ⟨23246720489, 792⟩,
  ⟨17432581080, 775⟩,
  ⟨13072591606, 758⟩,
  ⟨9803060746, 742⟩,
  ⟨7351258487, 725⟩,
  ⟨5512666171, 709⟩,
  ⟨4133916439, 693⟩,
  ⟨3100000000, 677⟩,
  ⟨2324672048, 662⟩,
  ⟨1743258108, 647⟩,
  ⟨1307259160, 631⟩,
  ⟨980306074, 616⟩,
  ⟨735125848, 601⟩,
  ⟨551266617, 585⟩,
  ⟨413391643, 570⟩,
  ⟨310000000, 554⟩,
  ⟨232467204, 539⟩,
  ⟨174325810, 525⟩,
  ⟨130725916, 511⟩,
  ⟨98030607, 498⟩,
  ⟨73512584, 484⟩,
  ⟨55126661, 471⟩,
  ⟨41339164, 458⟩,
  ⟨31000000, 445⟩,
  ⟨23246720, 432⟩,
  ⟨17432581, 419⟩,
  ⟨13072591, 406⟩,
  ⟨9803060, 394⟩,
  ⟨7351258, 381⟩,
  ⟨5512666, 369⟩,
  ⟨4133916, 357⟩,
  ⟨3100000, 345⟩,
  ⟨2324672, 333⟩,
  ⟨1743258, 321⟩,
  ⟨1307259, 310⟩,
  ⟨980306, 299⟩,
  ⟨735125, 288⟩,
  ⟨551266, 279⟩,
  ⟨413391, 269⟩,
  ⟨310000, 258⟩,
  ⟨232467, 248⟩,
  ⟨174325, 238⟩,
  ⟨130725, 228⟩,
  ⟨100000, 218⟩
]

def fullRows : List Row := allRows ++ lowRows

/-- The lower bound for `q` used by `lowsearch` for the candidate least split prime `p`. -/
def QloFull (p : ℕ) : ℕ :=
  (fullRows.filter (fun r => r.X ≤ p)).foldr (fun r acc => max r.Q acc) B

/-- The inputs for the range `q < 3.1·10^20`, established outside Lean. -/
structure LowInputs (IsExp7 : ℕ → Prop) : Prop where
  normEqPrim : ∀ q, q.Prime → q % 4 = 3 → IsExp7 q → ∀ p, p.Prime → p ≠ 2 → p ≠ q → Splits q p →
    ∃ x y : ℕ, 1 ≤ y ∧ ¬ p ∣ y ∧ 4 * p ^ 7 = x ^ 2 + q * y ^ 2
  certLow : ∀ r ∈ lowRows, ∀ q, q.Prime → q % 4 = 3 → r.X < q → q ≤ r.Q →
    ∃ p, p.Prime ∧ p < r.X ∧ Splits q p
  direct : ∀ q, q.Prime → q % 4 = 3 → q < B → (IsExp7 q ↔ q ∈ known)
  searchLow : ∀ p, p.Prime → 3 ≤ p → p < 2760 → ∀ x y q : ℕ, 1 ≤ y → ¬ p ∣ y →
    4 * p ^ 7 = x ^ 2 + q * y ^ 2 → QloFull p ≤ q → q < QLOW → q % 8 = 3 →
    (∀ l, l.Prime → 3 ≤ l → l < p → jacobiSym (-(q : ℤ)) l = -1) →
    q.Prime → IsExp7 q → q = 118843
  exp118843 : IsExp7 118843

set_option maxRecDepth 8000 in
lemma lowRows_X_le : ∀ r ∈ lowRows, r.X ≤ 6362 := by decide

lemma fullRows_X_le : ∀ r ∈ fullRows, r.X ≤ 6362 := by
  intro r hr
  rcases List.mem_append.mp hr with h | h
  · exact allRows_X_le r h
  · exact lowRows_X_le r h

lemma QloFull_le {p q : ℕ} (hB : B ≤ q) (h : ∀ r ∈ fullRows, r.X ≤ p → r.Q ≤ q) :
    QloFull p ≤ q := by
  unfold QloFull
  refine foldr_max_le _ hB ?_
  intro r hr
  rw [List.mem_filter] at hr
  exact h r hr.1 (by simpa using hr.2)

/-- **Theorem D** (from the inputs): for a prime `q ≡ 3 (mod 4)` with `q ≤ 10^32`, the class group
of `ℚ(√-q)` has exponent 7 if and only if `q` is one of the 33 listed primes. No published table
is assumed. -/
theorem theoremD {IsExp7 : ℕ → Prop} (H : Inputs IsExp7) (L : LowInputs IsExp7) {q : ℕ}
    (hq : q.Prime) (h4 : q % 4 = 3) (hhi : q ≤ QTOP) : IsExp7 q ↔ q ∈ known := by
  by_cases hB : q < B
  · exact L.direct q hq h4 hB
  have hBq : B ≤ q := by omega
  have hBval : B = 100000 := by norm_num [B]
  by_cases hlow : QLOW ≤ q
  · have hk : q ∉ known := fun h => by have := known_lt q h; omega
    simp only [hk, iff_false]
    exact theoremA H hq h4 hlow hhi
  have hqlt : q < QLOW := by omega
  constructor
  · intro hE
    have certFull : ∀ r ∈ fullRows, q ≤ r.Q → ∃ p, p.Prime ∧ p < r.X ∧ Splits q p := by
      intro r hr hQ
      have hX : r.X < q := by
        have := fullRows_X_le r hr
        omega
      rcases List.mem_append.mp hr with h | h
      · exact H.cert r h q hq h4 hX hQ
      · exact L.certLow r h q hq h4 hX hQ
    have hrow : (⟨310000000000000000000, 2760⟩ : Row) ∈ fullRows :=
      List.mem_append_left _ (List.mem_append_right _ (by simp [ladderRows]))
    obtain ⟨p0, hp0, hp0lt, hs0⟩ := certFull _ hrow (by simpa [QLOW] using hqlt.le)
    have hp0lt' : p0 < 2760 := hp0lt
    have hex : ∃ p, p.Prime ∧ Splits q p := ⟨p0, hp0, hs0⟩
    set p := Nat.find hex with hpdef
    obtain ⟨hp, hs⟩ : p.Prime ∧ Splits q p := Nat.find_spec hex
    have hmin : ∀ m < p, ¬ (m.Prime ∧ Splits q m) := fun m hm => Nat.find_min hex hm
    have hplt : p < 2760 := lt_of_le_of_lt (Nat.find_min' hex ⟨hp0, hs0⟩) hp0lt'
    have hpq : p ≠ q := by omega
    have hp2 : p ≠ 2 := by
      intro h2
      have hle := le_of_splits H hq h4 hE hp hpq hs
      rw [h2] at hle
      norm_num at hle
      omega
    have hp3 : 3 ≤ p := by have := hp.two_le; omega
    have h8 : q % 8 = 3 := by
      have hn2 : ¬ Splits q 2 := fun h => hmin 2 (by omega) ⟨Nat.prime_two, h⟩
      rw [splits_two_iff] at hn2
      omega
    obtain ⟨x, y, hy, hpy, he⟩ := L.normEqPrim q hq h4 hE p hp hp2 hpq hs
    have key : q = 118843 := by
      refine L.searchLow p hp hp3 hplt x y q hy hpy he ?_ hqlt h8 ?_ hq hE
      · refine QloFull_le hBq (fun r hr hXp => ?_)
        by_contra hQ
        rw [not_le] at hQ
        obtain ⟨p', hp', hp'X, hs'⟩ := certFull r hr hQ.le
        exact hmin p' (by omega) ⟨hp', hs'⟩
      · intro l hl hl3 hlp
        have hns : ¬ Splits q l := fun h => hmin l hlp ⟨hl, h⟩
        rw [splits_odd_iff q (by omega)] at hns
        have hlq : l ≠ q := by omega
        have hcop : (-(q : ℤ)).gcd l = 1 := by
          rw [Int.neg_gcd, Int.gcd_natCast_natCast]
          exact (Nat.coprime_primes hq hl).mpr (Ne.symm hlq)
        rcases jacobiSym.eq_one_or_neg_one hcop with h | h
        · exact absurd h hns
        · exact h
    rw [key]
    decide
  · intro hk
    have h118 : q = 118843 := by
      simp only [known, List.mem_cons, List.mem_nil_iff, or_false] at hk
      omega
    rw [h118]
    exact L.exp118843

end Exp7
