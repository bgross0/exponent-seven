import Exp7Lean.Rows.Check

/-! Integer certificates for the 64-cell Haar row at `X = 30000`. -/

namespace Exp7.Rows.Bridge30000

open Exp7.Num

-- The two long reductions can release their kernel caches between declarations.
set_option Elab.async false

def vector : List ℤ := List.replicate 32 1 ++ List.replicate 32 (-1)

/-- In cell j the correlation numerator is 64 − 3j through j = 32, then j − 64. -/
def pack : ℕ := (List.range 65).foldr (fun j tail =>
  (if j ≤ 32 then 2 ^ 62 + 64 - 3 * j else 2 ^ 62 + j - 64) + 2 ^ 64 * tail) 0

theorem pack_checked : packCheck vector pack = true := by decide +kernel

def entries : List (ℕ × ℕ × ℕ) :=
  (primesBelow 30000).map fun p => (p, logLo P20 p, sqrtLo20 p)

def widthOK (p : ℕ) : Bool :=
  Nat.ble (logHi P26 p) ((logLo P20 p + 16) * 1000000) &&
  Nat.ble (sqrtHi20 p) (sqrtLo20 p + 1)

set_option maxRecDepth 200000 in
theorem widths_checked : listAll widthOK (primesBelow 30000) = true := by decide +kernel

/-- k = 1,…,14 includes the contribution at 2^14. -/
def primeTotal : ℤ :=
  tableSumZ (fun p L S => primeLo 30000 (logLo P20 30000) (logHi P20 30000) 64 pack p L S 14 1)
    30000 entries

set_option maxRecDepth 200000 in
theorem primeTotal_eq : primeTotal = 9924256547414500872107 := by decide +kernel

theorem margin_eq :
    marginLower (2 ^ 135) 30000 (logLo P20 30000) (logHi P20 30000) 64 pack primeTotal =
      752277024130489382120 := by
  rw [primeTotal_eq]
  decide +kernel

end Exp7.Rows.Bridge30000
