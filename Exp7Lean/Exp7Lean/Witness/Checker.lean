import Exp7Lean.Step1

/-!
Exponent 7: witnesses against exponent 7, checked by kernel arithmetic.

If the class group of `ℚ(√-q)` has exponent 7 and the prime `l ≠ q` splits, then
`4 l^7 = x^2 + q y^2` has a solution with `y ≥ 1` (and `l ∤ y` for odd `l`); this is
`normEq_classGroup`. So a split prime `l` for which the equation has no such solution is a
*witness* that the exponent is not 7.

This file contains

* `not_isExp7_of_no_solution`, `not_isExp7_of_no_prim_solution`: the two forms of the criterion;
* Boolean checkers `notSqB`, `noSol`, `noSolPrim`, `primeB`, `splitsB`, `witB`, `entryOK`,
  `checkZip`, `checkRange`, each with a soundness lemma.

The checkers are meant to be evaluated by the kernel (`decide +kernel`). They are written with the
`Nat` functions that the kernel evaluates on literals with GMP (`Nat.add`, `Nat.sub`, `Nat.mul`,
`Nat.div`, `Nat.mod`, `Nat.pow`, `Nat.land`, `Nat.shiftRight`, `Nat.beq`, `Nat.ble`), applied
directly rather than through the notation type classes, and with structural recursion only.

Nothing here relies on the correctness of a square root algorithm: `notSqB` is true only if `n`
is a non-residue for one of four fixed moduli, or if `r^2 < n < (r+1)^2` for the candidate `r`
produced by Newton's iteration, and that is all the soundness proof uses.
-/

namespace Exp7

/-! ### The criterion -/

/-- A split prime `l` with no solution of `4 l^7 = x^2 + q y^2`, `y ≥ 1`, shows that the class
group of `ℚ(√-q)` does not have exponent 7. -/
theorem not_isExp7_of_no_solution (q l : ℕ) (hq : q.Prime) (h4 : q % 4 = 3) (hl : l.Prime)
    (hlq : l ≠ q) (hs : Splits q l)
    (hno : ∀ x y : ℕ, 1 ≤ y → 4 * l ^ 7 ≠ x ^ 2 + q * y ^ 2) : ¬ IsExp7 q := by
  intro hE
  obtain ⟨x, y, hy, -, he⟩ := normEq_classGroup q hq h4 hE l hl hlq hs
  exact hno x y hy he

/-- The same for an odd split prime `l`, where only solutions with `l ∤ y` have to be excluded. -/
theorem not_isExp7_of_no_prim_solution (q l : ℕ) (hq : q.Prime) (h4 : q % 4 = 3) (hl : l.Prime)
    (hlq : l ≠ q) (hl2 : l ≠ 2) (hs : Splits q l)
    (hno : ∀ x y : ℕ, 1 ≤ y → ¬ l ∣ y → 4 * l ^ 7 ≠ x ^ 2 + q * y ^ 2) : ¬ IsExp7 q := by
  intro hE
  obtain ⟨x, y, hy, hprim, he⟩ := normEq_classGroup q hq h4 hE l hl hlq hs
  exact hno x y hy (hprim hl2) he

/-! ### Quadratic non-residues -/

/-- Bit `i` of `mask`. -/
def maskBit (mask i : ℕ) : ℕ := Nat.land (Nat.shiftRight mask i) 1

/-- Bit `n mod m` of `mask` is zero. -/
def nonRes (mask m n : ℕ) : Bool := Nat.beq (maskBit mask (Nat.mod n m)) 0

/-- Bit `r^2 mod m` of `mask` is one for all `r < k`. -/
def maskLoop (mask m : ℕ) : ℕ → Bool
  | 0 => true
  | r + 1 => Nat.beq (maskBit mask (Nat.mod (Nat.mul r r) m)) 1 && maskLoop mask m r

/-- `mask` has a one at every square modulo `m`. -/
def maskOK (mask m : ℕ) : Bool := Nat.blt 0 m && maskLoop mask m m

lemma maskLoop_sound (mask m : ℕ) : ∀ k, maskLoop mask m k = true →
    ∀ r, r < k → maskBit mask (r * r % m) = 1 := by
  intro k
  induction k with
  | zero => intro _ r hr; omega
  | succ k ih =>
    intro h r hr
    simp only [maskLoop, Bool.and_eq_true] at h
    rcases Nat.lt_succ_iff_lt_or_eq.mp hr with h1 | rfl
    · exact ih h.2 r h1
    · exact Nat.eq_of_beq_eq_true h.1

lemma nonRes_sound {mask m n : ℕ} (hm : maskOK mask m = true) (h : nonRes mask m n = true)
    (x : ℕ) : n ≠ x ^ 2 := by
  simp only [maskOK, Bool.and_eq_true, Nat.blt_eq] at hm
  rintro rfl
  have h1 := maskLoop_sound mask m m hm.2 (x % m) (Nat.mod_lt _ hm.1)
  have h2 : maskBit mask (x ^ 2 % m) = 0 := Nat.eq_of_beq_eq_true h
  have e : x ^ 2 % m = x % m * (x % m) % m := by rw [pow_two, Nat.mul_mod]
  rw [e, h1] at h2
  exact absurd h2 one_ne_zero

set_option linter.style.longLine false in
/-- The squares modulo 3465, as a bit mask. -/
def sqMask3465 : ℕ := 0x4100080000000080100800004020000120400010800906000800000000800000004000c00100100002014800004020000100020800100004080400000020804110020000000080100000904020020004002100000800000800006100820004800080020020080822804000004010020000110004100000880100000100800004020000104000800000804004810000400820000000000000422100000804010024000000180120800180000000100002010800102020020000000900400804000420004100020000800000000004100830004000000080420000120804004000800020080100010100000820104402900000006004000104100800000800084400020000820000100020010020102000804000020880100000100c009000004001040000020000800040200005008000048000000200241000200000100a0000000100020004084000000120400100800006000820004000100000000080c2010400080001000000401002410081080010000400002200002000011402080012000000081080002082010000010000080200400010400002000401008442000018080200410002001002010213

set_option linter.style.longLine false in
/-- The squares modulo 4199, as a bit mask. -/
def sqMask4199 : ℕ := 0x4000002001c0004000002010004010000009002201160000c8846020203005000280500200000240026001040068002410108402040001130080604064028001000026001104002000500b00c10040202109001800030601a00080880001000040004000088059002c22018000884040020a3041002c0041000980060000008094004011001000084c020401109082200560020810440002000044042005010900802400620030180688024021000000810001b00002002400b8085002022201100800c40460b0011000820018000582001101080400408030100014044402208005900ac0401020080004102088040026821410008800e0204020090804001002200106c0004001000062015408208c04402021120180408050029000000016000b04002000000200c4802010011908900042440b8005008020001000c02040101a0051000c20018101480080221020400088040102010006400208805000a83001000088484202021041026801400008102c00140000040000130083004064024001301086041540020010408300012040002005003800080601220290880080006020004808800419000d02040000a8005002023001100c004c0421a0051000c04010005000081020080c000c811010800004e402201005180a80400220010480012081040062003418108802402100000188004130023011040034001300082201500820c5846030213

set_option linter.style.longLine false in
/-- The squares modulo 20677, as a bit mask. -/
def sqMask20677 : ℕ := 0xc088080110100804a600000428002010009020090000c4420002001000020088000c20089000020520200220084000188000010800041a1041202080801104c00020c1000542110000014800600e04804828000050112002088004844008880422410204020400280108484000c000200000010011020100140000100480042118100101a000288144004018040022110020940000002000a0030040800800081000012104000b0a40241440102010980114102040a0448000012d000201080018040400080a204031100000800811009008000300006404100d080880580204008620200c42400002840002082000144120018030000510a00100004082080204001200220014081400800810218000620100060080010101040242120444300002800200100440000805800184011203086080004144090a2000101000222008810208240010000204a000002820008050040000484004024290000112000204240004040000e01110200068004080408086002048020002100c000100300024402000c000020019208031420000860004502180000310800400a000108200000510100020281001440002400024400241204006801180040014002204040810081880003180000040400000108000110c08068010001c0182000205000021000010c2008900100002428000c004010088000090820041040402092800111808008a04082000125002209080030044400081820001050224380000480100880020200021c0005202880684004008400200c1100002300010000640010c500008218120500a000200c4400000a04104200202014091000804000050004410000030008010100000a4608040c5000023010011000604008c680010105000e004090104504000a0800007000008008010000840030430044a404002c09088051000002022000064200200010000204b00084602000a0100000006881088340800c0020040200220004080090e0003020804160000002008001214900028a1004442100200304000408c000800080018431120220a0000140008808020010004120001280000804001c0022040001102910400030c00401c0480402118000031600028c044834008000423510200060004180008084100408028000801c01120010002000200044100209290010590240880440040000c0022190800100040000812200211c00002800812000000042202004034100c1028103801040002422044408000a18000030800080485200082280025108000600c0000802a00020000208210890008804810050004202000060000000000400800200448700100f000011084400000c382010705000a086000100c44008a38000050002241088000800000000602408214002420088040004002480000140001000112010004a40000640000a011100000200008874008040000100200200084080000a04024800041c10c0202100801310400020e00041c0090201110000408604080c280050121000a20881009440000080224402000000082001100840010022004040510290808011180040380000002000000121c00021c1000142102400034000601e000008200820402040022800040140810904000b0200041400100002080114908048200000400120002010000010044008001a001001902022800800001008802200002014100000289060030080800a2048120000a304000708400014c40000003800043020012044448200280002030002100481040880480025000400200001008001000300024402004c400002d01201008420000c4600010604100a082000104940018870000450800000008102180400200202440014000c008810110140024240005640810081000802009000042420008000002000488048050001840020420040200000080108a040100002012008020208200010000000880004582000205204800008c00880c280050531000a002800410c0080c81020000041204080800084000008022200000d00210028012040040ac000000011010033120000940400102180000311100401a000108200080412040062100001140912000000a0860041400402090000011100008a04482408109002319000000040408080a005010d00062000801801000002002000610000908209010010480042a004c40400080800015082000104000008220020120800021480000002204120300003014881008100800042000432000040000810102000a02180404200002600001108400400c8100002300020800608010cd400882580014408020200c000010040010420000201400200188904005408048000052021102810008020400000c4400002011000020600108c640810000000e024002100400001880400060024080081000018001304300028400004c01002053100006002008844200050410100a20a8004048000288522400004100008280100c0400040202040005100810e8113100040b4040004200810021080802981008042100000324002408c000400000018432000220900081100900080000900402010410020808001058004008000004081240003080800180400080818205031500220800007008008042302000404100438080048410480806a200801c0002200001600040004c1000182101005302000014c400008080002110020901000000890400001a000022100020000810002040a4030044c100000b000001000400004c48201a5010203080010008504088a680014108000e00c8100902000000002448610000808809010054082002004464011028010080000200008600000e000000020480000c300090600201a024000100c080088300020c0224041081200010081010e00028210041420100042000006088048148000040130020820a000414c000a8052001002012000860000040400100220000004102000a81020800009c0080042100100330408060c00401c0080400131000429600000c200830020000a22900001040100180000002402400000000921801150020082040000080000021190000380040080000005021c0022380001500900000030200641c100028289020400000022820440340008104011300040014042001020810041080002108008008220000520002100489040090001005a004220100000008800002040800100040400002e002010080000008820001a704120f08401010cc000808380014700002a004800210a40000030200040400242888004005008000600410009022000208020484008c400000c0101000202000084640010e00004a0000201008000188f0400440a04100001202190081200a00020810045c0080201100800200400894c08001850102020080104104000a8842005002400040148001840000000022040401000908a011100004030008044200010010100804980040382002004224000029c00001c200090432040a020000411c08108810002084224040000200010001490a008a000804000010022000000280004000812004231002203000815009000802100004438100128208000410480062200001140002000010608640814802001802010213

set_option linter.style.longLine false in
/-- The squares modulo 64, as a bit mask. -/
def sqMask64 : ℕ := 0x202021202030213

lemma sqMask3465_ok : maskOK sqMask3465 3465 = true := by decide +kernel

lemma sqMask4199_ok : maskOK sqMask4199 4199 = true := by decide +kernel

lemma sqMask20677_ok : maskOK sqMask20677 20677 = true := by decide +kernel

lemma sqMask64_ok : maskOK sqMask64 64 = true := by decide +kernel

/-! ### Perfect squares -/

/-- One step of Newton's iteration for `√n`. -/
def newt (n x : ℕ) : ℕ := Nat.div (Nat.add x (Nat.div n x)) 2

/-- Newton's iteration from `x`, as long as it decreases. Started at `x ≥ ⌊√n⌋` (with enough
fuel) it ends at `⌊√n⌋`; nothing is proved about it. -/
def sqrtDown (n : ℕ) : ℕ → ℕ → ℕ
  | 0, x => x
  | k + 1, x => bif Nat.blt (newt n x) x then sqrtDown n k (newt n x) else x

/-- `r^2 < n < (r+1)^2`. -/
def strictBetween (n r : ℕ) : Bool :=
  Nat.blt (Nat.mul r r) n && Nat.blt n (Nat.mul (Nat.succ r) (Nat.succ r))

/-- A certificate that `n` is not a perfect square: `n` is a non-residue modulo `3465`, `4199`,
`20677` or `64`, or it lies strictly between two consecutive squares, found by Newton's iteration
started at the hint `x0` (any `x0 ≥ ⌊√n⌋`). -/
def notSqB (x0 n : ℕ) : Bool :=
  nonRes sqMask3465 3465 n || (nonRes sqMask4199 4199 n || (nonRes sqMask20677 20677 n ||
    (nonRes sqMask64 64 n || strictBetween n (sqrtDown n 200 x0))))

lemma strictBetween_sound {n r : ℕ} (h : strictBetween n r = true) (x : ℕ) : n ≠ x ^ 2 := by
  simp only [strictBetween, Bool.and_eq_true, Nat.blt_eq] at h
  have h1 : r * r < n := h.1
  have h2 : n < (r + 1) * (r + 1) := h.2
  rintro rfl
  have h3 : r < x := by
    by_contra hc
    have : x ≤ r := not_lt.mp hc
    nlinarith [Nat.mul_le_mul this this]
  have h4 : x < r + 1 := by
    by_contra hc
    have : r + 1 ≤ x := not_lt.mp hc
    nlinarith [Nat.mul_le_mul this this]
  omega

/-- Soundness of `notSqB`: the number is not a perfect square. -/
theorem notSqB_sound {x0 n : ℕ} (h : notSqB x0 n = true) (x : ℕ) : n ≠ x ^ 2 := by
  simp only [notSqB, Bool.or_eq_true] at h
  rcases h with h | h | h | h | h
  · exact nonRes_sound sqMask3465_ok h x
  · exact nonRes_sound sqMask4199_ok h x
  · exact nonRes_sound sqMask20677_ok h x
  · exact nonRes_sound sqMask64_ok h x
  · exact strictBetween_sound h x

/-! ### The norm equation -/

/-- For every `y ≥ y₀` not divisible by `m`, the number `N - q y^2` is negative or not a perfect
square. The loop runs over `y = y₀, y₀ + 1, …` and stops with `true` when `q y^2 > N`; the first
argument is fuel. -/
def noSolUp (q N m x0 : ℕ) : ℕ → ℕ → Bool
  | 0, _ => false
  | k + 1, y =>
    bif Nat.blt N (Nat.mul q (Nat.mul y y)) then true else
      (notSqB x0 (Nat.sub N (Nat.mul q (Nat.mul y y))) || Nat.beq (Nat.mod y m) 0) &&
        noSolUp q N m x0 k (Nat.succ y)

lemma noSolUp_sound (q N m x0 : ℕ) : ∀ k y0, noSolUp q N m x0 k y0 = true →
    ∀ x y : ℕ, y0 ≤ y → ¬ m ∣ y → N ≠ x ^ 2 + q * y ^ 2 := by
  intro k
  induction k with
  | zero => intro y0 h; simp [noSolUp] at h
  | succ k ih =>
    intro y0 h x y hy hm he
    rw [noSolUp] at h
    by_cases hb : Nat.blt N (Nat.mul q (Nat.mul y0 y0)) = true
    · have hb' : N < q * (y0 * y0) := by rw [← Nat.blt_eq]; exact hb
      have h1 : q * (y0 * y0) ≤ q * (y * y) := Nat.mul_le_mul_left q (Nat.mul_le_mul hy hy)
      rw [pow_two y] at he
      omega
    · rw [Bool.not_eq_true] at hb
      rw [hb, Bool.cond_false, Bool.and_eq_true, Bool.or_eq_true] at h
      rcases Nat.eq_or_lt_of_le hy with rfl | hlt
      · rcases h.1 with h1 | h1
        · have h2 : N - q * (y0 * y0) ≠ x ^ 2 := notSqB_sound h1 x
          rw [pow_two y0] at he
          omega
        · exact hm (Nat.dvd_of_mod_eq_zero (Nat.eq_of_beq_eq_true h1))
      · exact ih (y0 + 1) h.2 x y hlt hm he

/-- No solution of `4 l^7 = x^2 + q y^2` with `y ≥ 1`. -/
def noSol (q l : ℕ) : Bool :=
  noSolUp q (Nat.mul 4 (Nat.pow l 7)) 0 (Nat.mul 2 (Nat.pow l 4))
    (Nat.succ (Nat.mul 4 (Nat.pow l 7))) 1

/-- No solution of `4 l^7 = x^2 + q y^2` with `y ≥ 1` and `l ∤ y`. -/
def noSolPrim (q l : ℕ) : Bool :=
  noSolUp q (Nat.mul 4 (Nat.pow l 7)) l (Nat.mul 2 (Nat.pow l 4))
    (Nat.succ (Nat.mul 4 (Nat.pow l 7))) 1

/-- Soundness of `noSol`. -/
theorem noSol_sound {q l : ℕ} (h : noSol q l = true) :
    ∀ x y : ℕ, 1 ≤ y → 4 * l ^ 7 ≠ x ^ 2 + q * y ^ 2 := by
  intro x y hy
  have h' : noSolUp q (4 * l ^ 7) 0 (2 * l ^ 4) (4 * l ^ 7 + 1) 1 = true := h
  refine noSolUp_sound q (4 * l ^ 7) 0 _ _ 1 h' x y hy ?_
  rw [Nat.zero_dvd]
  omega

/-- Soundness of `noSolPrim`. -/
theorem noSolPrim_sound {q l : ℕ} (h : noSolPrim q l = true) :
    ∀ x y : ℕ, 1 ≤ y → ¬ l ∣ y → 4 * l ^ 7 ≠ x ^ 2 + q * y ^ 2 := by
  intro x y hy hly
  have h' : noSolUp q (4 * l ^ 7) l (2 * l ^ 4) (4 * l ^ 7 + 1) 1 = true := h
  exact noSolUp_sound q (4 * l ^ 7) l _ _ 1 h' x y hy hly

/-! ### Primality by trial division -/

/-- No `m` with `d ≤ m`, `m^2 ≤ n` divides `n` (the first argument is fuel). -/
def primeLoop (n : ℕ) : ℕ → ℕ → Bool
  | 0, _ => false
  | k + 1, d => bif Nat.blt n (Nat.mul d d) then true else
      bif Nat.beq (Nat.mod n d) 0 then false else primeLoop n k (Nat.succ d)

/-- Primality by trial division. -/
def primeB (n : ℕ) : Bool := Nat.ble 2 n && primeLoop n n 2

lemma primeLoop_sound (n : ℕ) : ∀ k d, primeLoop n k d = true →
    ∀ m, d ≤ m → m * m ≤ n → ¬ m ∣ n := by
  intro k
  induction k with
  | zero => intro d h; simp [primeLoop] at h
  | succ k ih =>
    intro d h m hdm hmn hdvd
    rw [primeLoop] at h
    by_cases h1 : Nat.blt n (Nat.mul d d) = true
    · have h1' : n < d * d := by rw [← Nat.blt_eq]; exact h1
      have : d * d ≤ m * m := Nat.mul_le_mul hdm hdm
      omega
    · rw [Bool.not_eq_true] at h1
      rw [h1, Bool.cond_false] at h
      by_cases h2 : Nat.beq (Nat.mod n d) 0 = true
      · rw [h2, Bool.cond_true] at h
        exact absurd h (by simp)
      · rw [Bool.not_eq_true] at h2
        rw [h2, Bool.cond_false] at h
        rcases Nat.lt_or_ge d m with hlt | hge
        · exact ih (d + 1) h m hlt hmn hdvd
        · have hmd : m = d := by omega
          subst hmd
          have h3 : Nat.mod n m = 0 := Nat.mod_eq_zero_of_dvd hdvd
          rw [h3] at h2
          exact absurd h2 (by decide)

/-- Soundness of `primeB`. -/
theorem primeB_sound {n : ℕ} (h : primeB n = true) : n.Prime := by
  simp only [primeB, Bool.and_eq_true, Nat.ble_eq] at h
  rw [Nat.prime_def_le_sqrt]
  exact ⟨h.1, fun m hm hms => primeLoop_sound n n 2 h.2 m hm (Nat.le_sqrt.mp hms)⟩

/-! ### Splitting -/

/-- `l` splits in `ℚ(√-q)`: `q ≡ 7 (mod 8)` for `l = 2`, Euler's criterion
`(-q)^((l-1)/2) ≡ 1 (mod l)` for odd `l`. -/
def splitsB (q l : ℕ) : Bool :=
  bif Nat.beq l 2 then Nat.beq (Nat.mod q 8) 7 else
    Nat.beq (Nat.mod (Nat.pow (Nat.sub l (Nat.mod q l)) (Nat.div l 2)) l) 1

/-- Soundness of `splitsB`. -/
theorem splitsB_sound {q l : ℕ} (hl : l.Prime) (h : splitsB q l = true) : Splits q l := by
  unfold splitsB at h
  by_cases h2 : l = 2
  · subst h2
    rw [splits_two_iff]
    exact Nat.eq_of_beq_eq_true h
  · have hb : Nat.beq l 2 = false := by
      rw [← Bool.not_eq_true, Nat.beq_eq]
      exact h2
    rw [hb, Bool.cond_false] at h
    have h' : (l - q % l) ^ (l / 2) % l = 1 := Nat.eq_of_beq_eq_true h
    rw [splits_odd_iff q h2]
    have := Fact.mk hl
    have hlpos : 0 < l := hl.pos
    have hmod : q % l ≤ l := (Nat.mod_lt q hlpos).le
    -- the residue of `-q`
    have hcast : ((l - q % l : ℕ) : ZMod l) = ((-(q : ℤ) : ℤ) : ZMod l) := by
      rw [Nat.cast_sub hmod]
      push_cast
      rw [ZMod.natCast_self, ZMod.natCast_mod, zero_sub]
    have hpow : ((-(q : ℤ) : ℤ) : ZMod l) ^ (l / 2) = 1 := by
      rw [← hcast, ← Nat.cast_pow, ← ZMod.natCast_mod, h', Nat.cast_one]
    have hhalf : l / 2 ≠ 0 := by
      have := hl.two_le
      omega
    have hne : ((-(q : ℤ) : ℤ) : ZMod l) ≠ 0 := by
      intro h0
      rw [h0, zero_pow hhalf] at hpow
      exact zero_ne_one hpow
    rw [← jacobiSym.legendreSym.to_jacobiSym, legendreSym.eq_one_iff l hne]
    exact (ZMod.euler_criterion l hne).mpr hpow

/-! ### Witnesses -/

/-- `l` is a witness that the class group of `ℚ(√-q)` does not have exponent 7: `l` is a prime
not dividing `q`, it splits, and `4 l^7 = x^2 + q y^2` has no solution with `y ≥ 1` (for `l = 2`),
or none with `y ≥ 1` and `l ∤ y` (for odd `l`). -/
def witB (q l : ℕ) : Bool :=
  Nat.ble 1 (Nat.mod q l) && (primeB l && (splitsB q l &&
    (bif Nat.beq l 2 then noSol q l else noSolPrim q l)))

/-- Soundness of `witB`. -/
theorem not_isExp7_of_witB {q l : ℕ} (h : witB q l = true) : ¬ IsExp7 q := by
  intro hE
  obtain ⟨hq, h4, -⟩ := id hE
  simp only [witB, Bool.and_eq_true, Nat.ble_eq] at h
  obtain ⟨hmod, hlB, hsB, hno⟩ := h
  have hmod' : 1 ≤ q % l := hmod
  have hl := primeB_sound hlB
  have hs := splitsB_sound hl hsB
  have hlq : l ≠ q := by
    rintro rfl
    rw [Nat.mod_self] at hmod'
    omega
  by_cases h2 : l = 2
  · have hb : Nat.beq l 2 = true := by rw [Nat.beq_eq]; exact h2
    rw [hb, Bool.cond_true] at hno
    exact not_isExp7_of_no_solution q l hq h4 hl hlq hs (noSol_sound hno) hE
  · have hb : Nat.beq l 2 = false := by
      rw [← Bool.not_eq_true, Nat.beq_eq]
      exact h2
    rw [hb, Bool.cond_false] at hno
    exact not_isExp7_of_no_prim_solution q l hq h4 hl hlq h2 hs (noSolPrim_sound hno) hE

/-! ### Tables -/

/-- One table entry `e` for the number `n`:
* `e = 0`: `n` is in the list `excl` of exceptions;
* `e ∣ n`: `e` is a proper divisor of `n` (so `n` is not prime);
* otherwise `e` is a witness for `n`. -/
def entryOK (excl : List ℕ) (n e : ℕ) : Bool :=
  bif Nat.beq e 0 then excl.contains n else
    bif Nat.beq (Nat.mod n e) 0 then Nat.blt 1 e && Nat.blt e n else witB n e

/-- Soundness of `entryOK`: exponent 7 forces `n` to be one of the exceptions. -/
theorem mem_excl_of_entryOK {excl : List ℕ} {n e : ℕ} (h : entryOK excl n e = true)
    (hE : IsExp7 n) : n ∈ excl := by
  unfold entryOK at h
  by_cases h0 : Nat.beq e 0 = true
  · rw [h0, Bool.cond_true] at h
    simpa using h
  · rw [Bool.not_eq_true] at h0
    rw [h0, Bool.cond_false] at h
    by_cases h1 : Nat.beq (Nat.mod n e) 0 = true
    · rw [h1, Bool.cond_true] at h
      simp only [Bool.and_eq_true, Nat.blt_eq] at h
      have h1' : n % e = 0 := Nat.eq_of_beq_eq_true h1
      obtain ⟨hq, -, -⟩ := id hE
      rcases (Nat.dvd_prime hq).mp (Nat.dvd_of_mod_eq_zero h1') with he | he <;> omega
    · rw [Bool.not_eq_true] at h1
      rw [h1, Bool.cond_false] at h
      exact absurd hE (not_isExp7_of_witB h)

/-- Check a list of numbers against a list of entries. -/
def checkZip (excl : List ℕ) : List ℕ → List ℕ → Bool
  | [], _ => true
  | _ :: _, [] => false
  | n :: ns, e :: es => entryOK excl n e && checkZip excl ns es

theorem mem_excl_of_checkZip {excl : List ℕ} : ∀ (ns es : List ℕ),
    checkZip excl ns es = true → ∀ n ∈ ns, IsExp7 n → n ∈ excl := by
  intro ns
  induction ns with
  | nil => intro es _ n hn; simp at hn
  | cons a ns ih =>
    intro es h n hn hE
    cases es with
    | nil => simp [checkZip] at h
    | cons e es =>
      simp only [checkZip, Bool.and_eq_true] at h
      rcases List.mem_cons.mp hn with rfl | hn'
      · exact mem_excl_of_entryOK h.1 hE
      · exact ih es h.2 n hn' hE

/-- Check the numbers `n, n + 4, n + 8, …` against a list of entries. -/
def checkRange (excl : List ℕ) : ℕ → List ℕ → Bool
  | _, [] => true
  | n, e :: es => entryOK excl n e && checkRange excl (Nat.add n 4) es

theorem mem_excl_of_checkRange {excl : List ℕ} : ∀ (es : List ℕ) (n : ℕ),
    checkRange excl n es = true → ∀ k, k < es.length → IsExp7 (n + 4 * k) → n + 4 * k ∈ excl := by
  intro es
  induction es with
  | nil => intro n _ k hk; simp at hk
  | cons e es ih =>
    intro n h k hk hE
    simp only [checkRange, Bool.and_eq_true] at h
    cases k with
    | zero => exact mem_excl_of_entryOK h.1 (by simpa using hE)
    | succ k =>
      have hk' : k < es.length := by simpa using hk
      have e1 : n + 4 * (k + 1) = n + 4 + 4 * k := by ring
      rw [e1] at hE ⊢
      exact ih (n + 4) h.2 k hk' hE

end Exp7
