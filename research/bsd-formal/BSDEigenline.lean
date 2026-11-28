import BSDFiniteWitness
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open Matrix
open scoped Matrix

namespace BSDEigenline

theorem projection_mulVec {K : Type*} [Field K] {n : Type*}
    [Fintype n] [DecidableEq n] (v x : n → K) (i₀ : n) :
    (Matrix.vecMulVec v (Pi.single i₀ 1)) *ᵥ x = x i₀ • v := by
  ext i
  simp [Matrix.mulVec, dotProduct, Matrix.vecMulVec, Pi.single_apply, mul_comm]

/-- A supplied correction matrix certifies the entire nullspace. -/
theorem nullvector_eq_of_correction {K : Type*} [Field K] {n : Type*}
    [Fintype n] [DecidableEq n] (M B : Matrix n n K) (v x : n → K)
    (i₀ : n) (d : K) (hd : d ≠ 0)
    (hcert : B * M = d • (1 - Matrix.vecMulVec v (Pi.single i₀ 1)))
    (hx : M *ᵥ x = 0) : x = x i₀ • v := by
  have h := congrArg (fun C : Matrix n n K => C *ᵥ x) hcert
  rw [← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero,
    Matrix.smul_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec,
    projection_mulVec] at h
  exact sub_eq_zero.mp ((smul_eq_zero.mp h.symm).resolve_left hd)

/-- The reverse inclusion requires checking the displayed vector is null. -/
theorem ker_eq_span_of_correction {K : Type*} [Field K] {n : Type*}
    [Fintype n] [DecidableEq n] (M B : Matrix n n K) (v : n → K)
    (i₀ : n) (d : K) (hd : d ≠ 0)
    (hcert : B * M = d • (1 - Matrix.vecMulVec v (Pi.single i₀ 1)))
    (hv : M *ᵥ v = 0) :
    LinearMap.ker M.mulVecLin = Submodule.span K {v} := by
  ext x
  constructor
  · intro hx
    refine Submodule.mem_span_singleton.mpr ⟨x i₀, ?_⟩
    exact (nullvector_eq_of_correction M B v x i₀ d hd hcert hx).symm
  · intro hx
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
    change M *ᵥ (a • v) = 0
    rw [Matrix.mulVec_smul, hv, smul_zero]



/-! The following objects are the rational matrix and vector obtained directly
from the integer tables in `BSDFiniteWitness`.  The certificate proves finite
linear algebra; arithmetic identification with a Brandt module or modular form
is not asserted here. -/

set_option maxRecDepth 20000
set_option maxHeartbeats 0

def matrix433Q : Matrix (Fin 36) (Fin 36) ℚ := fun i j =>
  ((BSDFiniteWitness.matrix433[i.val]!)[j.val]! : ℕ)

def vector433Q : Fin 36 → ℚ := fun i =>
  (BSDFiniteWitness.eigenfunction433[i.val]! : ℤ)

def shifted433 : Matrix (Fin 36) (Fin 36) ℚ := matrix433Q + 1

/-- Integral numerator of a correction matrix.  Its entries have absolute
value at most 95; the common denominator of the underlying inverse is 32.
Discovery used exact elimination; the following matrix identity is checked
independently by Lean's kernel. -/
def correctionNumerator433 : List (List ℤ) :=
  [[32, 32, -32, -32, -32, -32, 0, 0, 0, -32, -32, 0, 32, 32, 0, 0, 64, 0, 0, -64, -32, -32, 0, 0, 0, 32, 32, 32, 32, 0, 0, 0, -32, -32, 32, 32],
   [32, 32, -32, -32, -32, -32, 16, -16, 0, -32, -32, 0, 32, 32, 0, 0, 64, -16, 16, -64, -32, -32, 0, 0, 0, 48, 16, 32, 32, 0, 0, 0, -32, -32, 48, 16],
   [-32, -32, 20, 52, 12, 12, -14, 18, 18, 44, 12, -6, -24, -24, -6, -6, -50, 26, -6, 54, 28, 28, -6, -6, -6, -32, 0, -8, -40, -6, 2, 2, 20, 20, -40, -8],
   [-32, -32, 52, 20, 12, 12, 2, 2, 18, 12, 44, -6, -24, -24, -6, -6, -50, 10, 10, 54, 28, 28, -6, -6, -6, -16, -16, -40, -8, -6, 2, 2, 20, 20, -24, -24],
   [-32, -32, 12, 12, -12, -12, 14, 14, 6, 4, 4, -2, 8, 8, -18, -18, 10, 38, 6, -14, 4, 4, -2, -2, -18, 8, 8, 8, 8, -2, 6, 6, -4, -4, 0, 0],
   [-32, -32, 12, 12, -12, -12, -2, 30, 6, 4, 4, -2, 8, 8, -18, -18, 10, 22, 22, -14, 4, 4, -2, -2, -18, -8, 24, 8, 8, -2, 6, 6, -4, -4, -16, 16],
   [0, 16, -14, 2, 14, -2, -11, 21, -15, 6, -10, 5, -4, 12, -3, -3, 7, -7, -7, -13, -10, 6, 5, 5, -3, -12, 4, 12, -4, 5, 1, 1, 10, -6, -8, 8],
   [0, -16, 18, 2, 14, 30, 21, -11, -15, 6, 22, 5, -4, -20, -3, -3, -25, -7, -7, 19, 22, 6, 5, 5, -3, -12, -28, -20, -4, 5, 1, 1, 10, 26, -8, -24],
   [0, 0, 18, 18, 6, 6, -15, -15, 21, 30, 30, -7, -36, -36, 9, 9, -69, -3, -3, 63, 30, 30, 9, 9, 9, -12, -12, -36, -36, 9, -3, -3, 18, 18, -24, -24],
   [-32, -32, 44, 12, 4, 4, 6, 6, 30, -12, 52, -10, -24, -24, -10, 22, -30, 14, 14, 58, 20, 20, -10, -10, -10, -8, -8, -24, -24, -10, 14, -18, 12, 12, -16, -16],
   [-32, -32, 12, 44, 4, 4, -10, 22, 30, 52, -12, -10, -24, -24, 22, -10, -30, 30, -2, 58, 20, 20, -10, -10, -10, -24, 8, -24, -24, -10, -18, 14, 12, 12, -32, 0],
   [0, 0, -6, -6, -2, -2, 5, 5, -7, -10, -10, 13, 12, 12, -3, -3, 23, 1, 1, -21, -10, -10, -3, -3, -3, 4, 4, 12, 12, -3, 1, 1, -6, -6, 8, 8],
   [32, 32, -24, -24, 8, 8, -4, -4, -36, -24, -24, 12, 0, 32, 12, 12, 36, -36, -4, -28, -24, -24, -4, 28, 12, 0, 0, 16, 16, -4, -4, -4, -8, -8, 16, 16],
   [32, 32, -24, -24, 8, 8, 12, -20, -36, -24, -24, 12, 32, 0, 12, 12, 36, -20, -20, -28, -24, -24, 28, -4, 12, 16, -16, 16, 16, -4, -4, -4, -8, -8, 32, 0],
   [0, 0, -6, -6, -18, -18, -3, -3, 9, -10, 22, -3, 12, 12, -3, -3, -9, 9, 9, -21, 6, 6, -3, -3, -3, 12, 12, 12, 12, -3, 1, 1, -6, -6, 0, 0],
   [0, 0, -6, -6, -18, -18, -3, -3, 9, 22, -10, -3, 12, 12, -3, -3, -9, 9, 9, -21, 6, 6, -3, -3, -3, 12, 12, 12, 12, -3, 1, 1, -6, -6, 0, 0],
   [64, 64, -50, -50, 10, 10, 7, -25, -69, -30, -30, 23, 36, 36, -9, -9, 69, -53, -21, -95, -46, -46, 23, 23, 23, 20, -12, 36, 36, 23, 3, 3, -18, -18, 48, 16],
   [0, -16, 26, 10, 38, 22, -7, -7, -3, 14, 30, 1, -36, -20, 9, 9, -53, -19, 13, 55, 14, 30, 1, 1, 9, -20, -36, -36, -20, 1, -3, -3, 34, 18, -16, -32],
   [0, 16, -6, 10, 6, 22, -7, -7, -3, 14, -2, 1, -4, -20, 9, 9, -21, 13, -19, 23, 14, -2, 1, 1, 9, -20, -4, -4, -20, 1, -3, -3, 2, 18, -16, 0],
   [-64, -64, 54, 54, -14, -14, -13, 19, 63, 58, 58, -21, -28, -28, -21, -21, -95, 55, 23, 77, 58, 58, -21, -21, -21, -20, 12, -44, -44, 11, 7, 7, 22, 22, -56, -24],
   [-32, -32, 28, 28, 4, 4, -10, 22, 30, 20, 20, -10, -24, -24, 6, 6, -46, 14, 14, 58, 20, 20, -10, -10, 6, -8, -8, -24, -24, -10, -2, -2, 12, 12, -16, -16],
   [-32, -32, 28, 28, 4, 4, 6, 6, 30, 20, 20, -10, -24, -24, 6, 6, -46, 30, -2, 58, 20, 20, -10, -10, 6, -24, 8, -24, -24, -10, -2, -2, 12, 12, -32, 0],
   [0, 0, -6, -6, -2, -2, 5, 5, 9, -10, -10, -3, -4, 28, -3, -3, 23, 1, 1, -21, -10, -10, -3, -3, -3, 4, 4, 12, 12, -3, 1, 1, -6, -6, 8, 8],
   [0, 0, -6, -6, -2, -2, 5, 5, 9, -10, -10, -3, 28, -4, -3, -3, 23, 1, 1, -21, -10, -10, -3, -3, -3, 4, 4, 12, 12, -3, 1, 1, -6, -6, 8, 8],
   [0, 0, -6, -6, -18, -18, -3, -3, 9, -10, -10, -3, 12, 12, -3, -3, 23, 9, 9, -21, 6, 6, -3, -3, -3, 12, 12, 12, 12, -3, 1, 1, -6, -6, 0, 0],
   [32, 48, -32, -16, 8, -8, -12, -12, -12, -8, -24, 4, 0, 16, 12, 12, 20, -20, -20, -20, -8, -24, 4, 4, 12, 8, 24, 16, 0, 4, -4, -4, -24, -8, 8, 24],
   [32, 16, 0, -16, 8, 24, 4, -28, -12, -8, 8, 4, 0, -16, 12, 12, -12, -36, -4, 12, -8, 8, 4, 4, 12, 24, -24, -16, 0, 4, -4, -4, 8, -8, 24, -24],
   [32, 32, -8, -40, 8, 8, 12, -20, -36, -24, -24, 12, 16, 16, 12, 12, 36, -36, -4, -44, -24, -24, 12, 12, 12, 16, -16, 16, 16, 12, -4, -4, -8, -8, 32, 0],
   [32, 32, -40, -8, 8, 8, -4, -4, -36, -24, -24, 12, 16, 16, 12, 12, 36, -20, -20, -44, -24, -24, 12, 12, 12, 0, 0, 16, 16, 12, -4, -4, -8, -8, 16, 16],
   [0, 0, -6, -6, -2, -2, 5, 5, 9, -10, -10, -3, -4, -4, -3, -3, 23, 1, 1, 11, -10, -10, -3, -3, -3, 4, 4, 12, 12, -3, 1, 1, -6, -6, 8, 8],
   [0, 0, 2, 2, 6, 6, 1, 1, -3, 14, -18, 1, -4, -4, 1, 1, 3, -3, -3, 7, -2, -2, 1, 1, 1, -4, -4, -4, -4, 1, -11, 21, 2, 2, 0, 0],
   [0, 0, 2, 2, 6, 6, 1, 1, -3, -18, 14, 1, -4, -4, 1, 1, 3, -3, -3, 7, -2, -2, 1, 1, 1, -4, -4, -4, -4, 1, 21, -11, 2, 2, 0, 0],
   [-32, -32, 20, 20, -4, -4, 10, 10, 18, 12, 12, -6, -8, -8, -6, -6, -18, 34, 2, 22, 12, 12, -6, -6, -6, -24, 8, -8, -8, -6, 2, 2, 20, 20, -16, -16],
   [-32, -32, 20, 20, -4, -4, -6, 26, 18, 12, 12, -6, -8, -8, -6, -6, -18, 18, 18, 22, 12, 12, -6, -6, -6, -8, -8, -8, -8, -6, 2, 2, 20, 20, -32, 0],
   [32, 48, -40, -24, 0, -16, -8, -8, -24, -16, -32, 8, 16, 32, 0, 0, 48, -16, -16, -56, -16, -32, 8, 8, 0, 8, 24, 32, 16, 8, 0, 0, -16, -32, 24, 40],
   [32, 16, -8, -24, 0, 16, 8, -24, -24, -16, 0, 8, 16, 0, 0, 0, 16, -32, 0, -24, -16, 0, 8, 8, 0, 24, -24, 0, 16, 8, 0, 0, -16, 0, 40, -8]]

def correction433 : Matrix (Fin 36) (Fin 36) ℚ := fun i j =>
  ((correctionNumerator433[i.val]!)[j.val]! : ℤ)

/-- Every entry of the exact rational correction identity. -/
theorem correction433_entries : ∀ i j : Fin 36,
    (correction433 * shifted433) i j =
    ((32 : ℚ) • (1 - Matrix.vecMulVec vector433Q (Pi.single 0 1))) i j := by
  decide +kernel

/-- The complete correction certificate for the displayed 36-by-36 matrix. -/
theorem correction433_identity :
    correction433 * shifted433 =
    (32 : ℚ) • (1 - Matrix.vecMulVec vector433Q (Pi.single 0 1)) := by
  ext i j
  exact correction433_entries i j

theorem vector433Q_null_entries : ∀ i : Fin 36, (shifted433 *ᵥ vector433Q) i = 0 := by
  decide +kernel

theorem vector433Q_null : shifted433 *ᵥ vector433Q = 0 := by
  ext i
  exact vector433Q_null_entries i

theorem vector433Q_zero_coordinate : vector433Q 0 = 1 := by
  decide +kernel

theorem vector433Q_ne_zero : vector433Q ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  rw [vector433Q_zero_coordinate] at h0
  exact one_ne_zero h0

/-- Every null vector is the scalar multiple determined by coordinate zero. -/
theorem nullvector433_unique (x : Fin 36 → ℚ) (hx : shifted433 *ᵥ x = 0) :
    x = x 0 • vector433Q :=
  nullvector_eq_of_correction shifted433 correction433 vector433Q x 0 32
    (by norm_num) correction433_identity hx

/-- The exact nullspace, not merely an exhibited null vector. -/
theorem kernel433_eq_span :
    LinearMap.ker shifted433.mulVecLin = Submodule.span ℚ {vector433Q} :=
  ker_eq_span_of_correction shifted433 correction433 vector433Q 0 32
    (by norm_num) correction433_identity vector433Q_null

/-- The minus-one eigenspace of the displayed matrix has dimension one. -/
theorem kernel433_finrank_one :
    Module.finrank ℚ (LinearMap.ker shifted433.mulVecLin) = 1 := by
  rw [kernel433_eq_span]
  exact finrank_span_singleton vector433Q_ne_zero

end BSDEigenline
