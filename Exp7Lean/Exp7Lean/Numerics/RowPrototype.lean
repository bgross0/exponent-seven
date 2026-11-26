import Exp7Lean.Numerics.BenchTable

/-!
# Timing prototype for the certificate rows (NOT a verified statement about real numbers)

The functions below mirror `kernel_verify.py : rigorous_margin` in fixed point at scale `10^20`:
`marginLo R` is intended to be a lower bound of

    2 ∑_{p^k < X} (-1)^k log p · f(log p^k) / √(p^k) - J⁺ - log Q + log π + γ - π/2 + 3 log 2

for the row `R = (Q, X, v)`; the autocorrelation numerators `∑_k v_k v_{k+j}` are supplied packed
in one natural number (base `2^64`, offset `2^62`).  **No soundness theorem is proved here**: the
file exists to measure what the kernel needs for one row (`row*_check` are honest kernel
evaluations of these integer functions, nothing more) and to serve as a starting point for the
verified row evaluator.  The values agree with the interval-arithmetic lower bounds stored in
`certificate.json` to about `1e-16`.

Two styles are compared on the `J⁺` loop: ordinary notation with `ℤ` (`jLoop`, 0.75 s for 1008
terms) and raw `Nat` operations (`jLoopR`, 0.10 s); `row0_J_eq` checks they agree.
-/

namespace Exp7.Num.RowProto

structure Row where
  Q : ℕ
  X : ℕ
  sq : ℕ
  pack : ℕ

def DD : ℕ := 100000000000000000000

/-- `cn[j]` from the packed table (base `2^64`, offset `2^62`). -/
def getC (pack j : ℕ) : ℤ :=
  Int.sub (Int.ofNat (Nat.mod (Nat.div pack (Nat.pow 18446744073709551616 j)) 18446744073709551616))
    4611686018427387904

/-- lower bound (scale `10^20`) of `2 (-1)^k log p f(log p^k) / √(p^k)`. -/
def termLo (X LX LXhi sq pack p L S k : ℕ) : ℤ :=
  let n := p ^ k
  let jlo := 64 * k * L / LXhi
  let jhi := 64 * k * (L + 16) / LX
  let j := if jlo = jhi then jlo else if X ^ jhi ≤ n ^ 64 then jhi else jlo
  let hlo : ℤ := max 0 ((64 * k * L * DD / LXhi : ℕ) - (j * DD : ℕ))
  let hhi : ℤ := min (DD : ℤ) ((cdiv (64 * k * (L + 16) * DD) LX : ℕ) - (j * DD : ℕ))
  let c0 := getC pack j
  let dl := getC pack (j + 1) - c0
  let flo := c0 * DD + min (hlo * dl) (hhi * dl)
  let fhi := c0 * DD + max (hlo * dl) (hhi * dl)
  let glo := if k % 2 = 0 then flo else -fhi
  let wlo : ℕ := if k % 2 = 0 then L * DD else L * S
  let whi : ℕ := if k % 2 = 0 then (L + 16) * DD else (L + 16) * (S + 1)
  let den : ℕ := p ^ ((k + 1) / 2) * sq * DD * DD
  if 0 ≤ glo then (2 * glo * wlo) / (den : ℤ) else (2 * glo * whi) / (den : ℤ)

/-- sum over `k ≥ 1` with `p^k < X` (early exit). -/
def primeLo (X LX LXhi sq pack p L S : ℕ) : ℤ :=
  Nat.rec (motive := fun _ => ℤ) 0
    (fun i ih => cond (Nat.ble X (Nat.pow p (Nat.sub 13 i))) 0
      (Int.add (termLo X LX LXhi sq pack p L S (Nat.sub 13 i)) ih)) 13

/-- the prime-power sum, folded over the certified table. -/
def totalLo (X LX LXhi sq pack : ℕ) : ℤ :=
  List.rec (motive := fun _ => ℤ) 0
    (fun e _ ih => cond (Nat.ble (Nat.succ e.1) X)
      (Int.add (primeLo X LX LXhi sq pack e.1 e.2.1 e.2.2) ih) ih) primeTable6400

/-- one term of the `J` sum (upper bound, scale `10^20`), `m = 16 j + i`. -/
def jTerm (stepHi sq pack A B m : ℕ) : ℕ :=
  let j := m / 16
  let i := m % 16
  let c0 := getC pack j
  let dl := getC pack (j + 1) - c0
  let om : ℤ := 32 * (sq : ℤ) - 32 * c0 - dl * (2 * i + 1)
  let aHi := cdiv (2 * A * DD) (DD - B)
  cdiv (stepHi * aHi * om.toNat) (DD * 32 * sq)

/-- state `(A, B, acc)` after the terms `m = 16, …, 16 + cnt - 1`;
`A ≥ r^(3m)`, `B ≥ r^(4m)` are running products. -/
def jLoop (stepHi sq pack r3 r4 A0 B0 cnt : ℕ) : ℕ × ℕ × ℕ :=
  Nat.rec (motive := fun _ => ℕ × ℕ × ℕ) (A0, B0, 0)
    (fun i ih => (fmulHi DD ih.1 r3, fmulHi DD ih.2.1 r4,
      Nat.add ih.2.2 (jTerm stepHi sq pack ih.1 ih.2.1 (Nat.add 16 i)))) cnt

def jHi (X LX LXhi sq pack : ℕ) : ℕ :=
  let rhi := expNegHi DD 10 0 (LX / 2048)
  let r3 := fpowHi DD rhi 3
  let r4 := fpowHi DD rhi 4
  let stepHi := cdiv LXhi 1024
  let first := cdiv ((sq - (getC pack 1).toNat) * DD) sq
  let tail := cdiv (4 * X * DD * DD) (3 * sqrtLo20 X * (X * X - 1))
  first + (jLoop stepHi sq pack r3 r4 (fpowHi DD r3 16) (fpowHi DD r4 16) 1008).2.2 + tail

/-- lower bound (scale `10^20`) of the margin of a row. -/
def marginLo (R : Row) : ℤ :=
  match R with
  | ⟨Q, X, sq, pack⟩ =>
    totalLo X (logLo P20 X) (logHi P20 X) sq pack - (jHi X (logLo P20 X) (logHi P20 X) sq pack : ℤ)
      - (logHi P20w Q : ℤ) + 223059076563587229937

def totalOnly (R : Row) : ℤ :=
  match R with
  | ⟨_, X, sq, pack⟩ => totalLo X (logLo P20 X) (logHi P20 X) sq pack

def jOnly (R : Row) : ℕ :=
  match R with
  | ⟨_, X, sq, pack⟩ => jHi X (logLo P20 X) (logHi P20 X) sq pack

/-- raw-`Nat` variant of `getC`, returning `cn[j] + 2^62`. -/
def getN (pack j : ℕ) : ℕ :=
  Nat.mod (Nat.div pack (Nat.pow 18446744073709551616 j)) 18446744073709551616

/-- raw-`Nat` variant of `jTerm`. -/
def jTermR (stepHi sq pack A B m : ℕ) : ℕ :=
  cdiv (Nat.mul (Nat.mul stepHi (cdiv (Nat.mul (Nat.mul 2 A) 100000000000000000000)
      (Nat.sub 100000000000000000000 B)))
    (Nat.sub (Nat.add (Nat.add (Nat.mul 32 sq) 147573952589676412928)
        (Nat.mul (getN pack (Nat.div m 16)) (Nat.succ (Nat.mul 2 (Nat.mod m 16)))))
      (Nat.add (Nat.mul 32 (getN pack (Nat.div m 16)))
        (Nat.mul (getN pack (Nat.succ (Nat.div m 16))) (Nat.succ (Nat.mul 2 (Nat.mod m 16)))))))
    (Nat.mul 3200000000000000000000 sq)

/-- raw-`Nat` variant of `jLoop`. -/
def jLoopR (stepHi sq pack r3 r4 A0 B0 cnt : ℕ) : ℕ × ℕ × ℕ :=
  Nat.rec (motive := fun _ => ℕ × ℕ × ℕ) (A0, B0, 0)
    (fun i ih => (fmulHi 100000000000000000000 ih.1 r3, fmulHi 100000000000000000000 ih.2.1 r4,
      Nat.add ih.2.2 (jTermR stepHi sq pack ih.1 ih.2.1 (Nat.add 16 i)))) cnt

/-- raw-`Nat` variant of `jHi`. -/
def jHiR (X LX LXhi sq pack : ℕ) : ℕ :=
  let rhi := expNegHi DD 10 0 (LX / 2048)
  let r3 := fpowHi DD rhi 3
  let r4 := fpowHi DD rhi 4
  let stepHi := cdiv LXhi 1024
  let first := cdiv ((sq - (getC pack 1).toNat) * DD) sq
  let tail := cdiv (4 * X * DD * DD) (3 * sqrtLo20 X * (X * X - 1))
  first + (jLoopR stepHi sq pack r3 r4 (fpowHi DD r3 16) (fpowHi DD r4 16) 1008).2.2 + tail

def jOnlyR (R : Row) : ℕ :=
  match R with
  | ⟨_, X, sq, pack⟩ => jHiR X (logLo P20 X) (logHi P20 X) sq pack

set_option linter.style.longLine false in
/-- Row 0 of `certificate.json` (`bootstrap`): `Q = 10^32`, `X = 6362`. -/
def row0 : Row :=
  ⟨100000000000000000000000000000000, 6362, 148861952392,
   4816393602214054671661176439579913370034569708457812429089697930105561972358414308149969116043330390520575062012790598238952514727261873157151567511947941876659431131498132307802526294137611205611692449247729636393340854317413304668559774530051863183659472228811919297534987113996185783835795667818166268903765014358455271361557933793158982300006700237876335470290292069998226077536170435198441262293912546190302273861525666393429104408309894536769566664805127890122969026439711325028214045021415590213886944917967228865278365686098392774090617849102511308109111001982556212527788835309402019093182669043776288399246101069469476340285042421662259050809032615591192533400101711160352809957494085838324403957809595238768157229042576816723349329733056671038605404819413500174596550388617202796806525202115006935564431689805198105064569015545961496261480577679411945432148621438071043648911005307665483350140135549265542946086641865676953552187475022061862646086415151153818432722864202927084916958680707402567251871689958347434007040732411876408757299492829799309506587289850760124475540277886672426667366601716112957750177486399554572198403838918774493966210941901350577694816046347467052964756198492808481606413650458828533996335611405146800251050205576⟩

set_option linter.style.longLine false in
/-- Row 50 of `certificate.json` (`ladder`): `Q = 310000000000000000000`, `X = 2760`. -/
def row50 : Row :=
  ⟨310000000000000000000, 2760, 161966068266,
   4816393602214054671661176439579913370034569708457029787405469165047778343658798054468026536309338908979022499275511171847724784990701514639505301172833867492868508413662675438899052960688731968946992194637411884849302132118959365116971980448585893244955167139520551922185990740307510466943840966682474442962955454833980672168723396005384690445430615506866019351550523731853349896712991237221701340375153775425758584072597415849895717249397309017948934148392157646920775625632091880161454233011615434217031714420254623217102707734580796612409455827269108529577671216167078896889020784929019564706248881103065426154171308008594176484552454624263785563953555297516015513115691742739487300185117833623549331842616368768173723432582804648899783768617979523901841959313612380405179065320483729955075836180216724411489161449542937593873959583110649355840229051811513777094540316675619277917191331866516664098918363513407507922123998012864865000695074068356025806509043533079004588628220688819004007394639440106079608891692602863075497552186641311269339563531843142793800920910696113665555251863006777196484392671331023894141885763806452965611226535922121652858370552812695687870180602489882431762876526679988235191951401308878985716529486733316650947706753578⟩

set_option maxRecDepth 100000 in
/-- Row 0 (`X = 6362`, `Q = 10^32`): margin `> 0.0126693058699149`
(`certificate.json` has `0.01266930586991506`).  Kernel time about 2.5 s. -/
theorem row0_check : 1266930586991490000 ≤ marginLo row0 := by decide +kernel

set_option maxRecDepth 100000 in
/-- Row 50 (`X = 2760`, `Q = 3.1e20`): margin `> 0.018147958062913`.  Kernel time about 1.6 s. -/
theorem row50_check : 1814795806291300000 ≤ marginLo row50 := by decide +kernel

set_option maxRecDepth 100000 in
/-- The prime-power part of row 0 alone (about 1.45 s: 870 terms in ordinary notation). -/
theorem row0_total_check : 0 ≤ totalOnly row0 := by decide +kernel

set_option maxRecDepth 100000 in
/-- The `J⁺` part of row 0 in raw `Nat` style (about 0.10 s for 1008 terms). -/
theorem row0_JR_check : jOnlyR row0 ≤ 10000000000000000000000 := by decide +kernel

set_option maxRecDepth 100000 in
/-- The two styles of the `J⁺` loop agree on row 0 (about 0.85 s, dominated by `jLoop`). -/
theorem row0_J_eq : jOnlyR row0 = jOnly row0 := by decide +kernel

end Exp7.Num.RowProto
