import Exp7Lean.Analytic.Autocorr
import Exp7Lean.Numerics.PrimeSum

/-!
Certificate rows, step 2: the autocorrelation numerators `∑_k v_k v_{k+j}` of an integer vector,
computed in the kernel and compared with a packed table (base `2^64`, offset `2^62`).

`PackOK v sq pack` is the interface used by the evaluators: for `j ≤ 64`,
`getN pack j = sq * corr v j + 2^62`.
-/

namespace Exp7.Rows

open Exp7.Num

/-- Dot product of two integer lists (truncated to the shorter one); raw recursors. -/
def dotZ (a b : List ℤ) : ℤ :=
  List.rec (motive := fun _ => List ℤ → ℤ) (fun _ => 0)
    (fun x _ ih b => List.rec (motive := fun _ => ℤ) 0
      (fun y ys _ => Int.add (Int.mul x y) (ih ys)) b) a b

theorem dotZ_nil (b : List ℤ) : dotZ [] b = 0 := rfl
theorem dotZ_cons_nil (x : ℤ) (a : List ℤ) : dotZ (x :: a) [] = 0 := rfl
theorem dotZ_cons_cons (x y : ℤ) (a b : List ℤ) :
    dotZ (x :: a) (y :: b) = x * y + dotZ a b := rfl

theorem dotZ_eq (a b : List ℤ) :
    dotZ a b = ∑ k ∈ Finset.range a.length, a.getD k 0 * b.getD k 0 := by
  induction a generalizing b with
  | nil => simp [dotZ_nil]
  | cons x a ih =>
    cases b with
    | nil => simp [dotZ_cons_nil]
    | cons y b =>
      rw [dotZ_cons_cons, ih, List.length_cons, Finset.sum_range_succ']
      simp [add_comm]

/-- `List.tail`, raw. -/
def tailR (l : List ℤ) : List ℤ := List.rec (motive := fun _ => List ℤ) [] (fun _ t _ => t) l

/-- `List.drop`, raw. -/
def dropR (j : ℕ) (l : List ℤ) : List ℤ :=
  Nat.rec (motive := fun _ => List ℤ) l (fun _ ih => tailR ih) j

theorem tailR_eq (l : List ℤ) : tailR l = l.tail := by cases l <;> rfl

theorem dropR_eq (j : ℕ) (l : List ℤ) : dropR j l = l.drop j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    change tailR (dropR j l) = _
    rw [ih, tailR_eq, List.tail_drop]

/-- `∑_k v_k v_{k+j}`. -/
def cnum (v : List ℤ) (j : ℕ) : ℤ := dotZ v (dropR j v)

theorem cnum_eq (v : List ℤ) (j : ℕ) :
    cnum v j = ∑ k ∈ Finset.range v.length, v.getD k 0 * v.getD (k + j) 0 := by
  unfold cnum
  rw [dotZ_eq, dropR_eq]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  simp [List.getD_eq_getElem?_getD, List.getElem?_drop, add_comm]

theorem getD_map_cast (v : List ℤ) (k : ℕ) :
    (v.map (fun z : ℤ => (z : ℝ))).getD k 0 = ((v.getD k 0 : ℤ) : ℝ) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases v[k]? <;> simp

/-- The real autocorrelation of the cast vector, from the integer numerators. -/
theorem corr_cast (v : List ℤ) (j : ℕ) :
    corr (v.map (fun z : ℤ => (z : ℝ))) j = (cnum v j : ℝ) / (cnum v 0 : ℝ) := by
  unfold corr
  rw [← sum_range_shift_eq, cnum_eq, cnum_eq, List.length_map]
  push_cast
  congr 1
  · exact Finset.sum_congr rfl fun k _ => by rw [getD_map_cast, getD_map_cast]
  · exact Finset.sum_congr rfl fun k _ => by rw [getD_map_cast, add_zero, sq]

theorem exists_ne_zero_of_cnum (v : List ℤ) (h : cnum v 0 ≠ 0) :
    ∃ t ∈ v.map (fun z : ℤ => (z : ℝ)), t ≠ 0 := by
  by_contra hcon
  push Not at hcon
  apply h
  rw [cnum_eq]
  apply Finset.sum_eq_zero
  intro k hk
  have hk' : k < v.length := Finset.mem_range.mp hk
  have h0 : ((v[k] : ℤ) : ℝ) = 0 :=
    hcon _ (List.mem_map.mpr ⟨v[k], List.getElem_mem hk', rfl⟩)
  have h1 : v[k] = 0 := by exact_mod_cast h0
  rw [List.getD_eq_getElem _ _ hk', h1, zero_mul]

/-! ### The packed table -/

/-- The `j`-th base-`2^64` digit of `pack`. -/
def getN (pack j : ℕ) : ℕ :=
  Nat.mod (Nat.div pack (Nat.pow 18446744073709551616 j)) 18446744073709551616

/-- Kernel check: the digits `0, …, 64` of `pack` are `cnum v j + 2^62`. -/
def corrCheck (v : List ℤ) (pack : ℕ) : Bool :=
  allBelow (fun j => decide (Int.ofNat (getN pack j) = Int.add (cnum v j) 4611686018427387904)) 65

theorem corrCheck_spec {v : List ℤ} {pack : ℕ} (h : corrCheck v pack = true) {j : ℕ}
    (hj : j ≤ 64) : ((getN pack j : ℕ) : ℤ) = cnum v j + 4611686018427387904 := by
  have := (allBelow_iff _ _).mp h j (by omega)
  exact of_decide_eq_true this

/-- The interface between the vector and the evaluators. -/
structure PackOK (v : List ℝ) (sq pack : ℕ) : Prop where
  len : v.length = 64
  sqpos : 0 < sq
  ne : ∃ t ∈ v, t ≠ 0
  c : ∀ j ≤ 64, ((getN pack j : ℕ) : ℝ) = sq * corr v j + 4611686018427387904

/-- The complete check of the packed table. -/
def packCheck (v : List ℤ) (pack : ℕ) : Bool :=
  Nat.beq (List.length v) 64 && (corrCheck v pack &&
    Nat.ble 4611686018427387905 (getN pack 0))

theorem packOK_of_check {v : List ℤ} {pack : ℕ} (h : packCheck v pack = true) :
    PackOK (v.map (fun z : ℤ => (z : ℝ))) (Nat.sub (getN pack 0) 4611686018427387904) pack := by
  unfold packCheck at h
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨h1, h2, h3⟩ := h
  have hlen : v.length = 64 := Nat.eq_of_beq_eq_true h1
  have h0 : 4611686018427387905 ≤ getN pack 0 := Nat.le_of_ble_eq_true h3
  have hc0 := corrCheck_spec h2 (j := 0) (by norm_num)
  have hsq : ((getN pack 0 - 4611686018427387904 : ℕ) : ℤ) = cnum v 0 := by
    omega
  have hsqpos : 0 < getN pack 0 - 4611686018427387904 := by omega
  have hne0 : cnum v 0 ≠ 0 := by omega
  have hsqR : ((getN pack 0 - 4611686018427387904 : ℕ) : ℝ) = ((cnum v 0 : ℤ) : ℝ) := by
    exact_mod_cast hsq
  have hne0R : ((cnum v 0 : ℤ) : ℝ) ≠ 0 := by exact_mod_cast hne0
  refine ⟨by rw [List.length_map, hlen], hsqpos, exists_ne_zero_of_cnum v hne0, ?_⟩
  intro j hj
  have hcj := corrCheck_spec h2 hj
  have hcjR : ((getN pack j : ℕ) : ℝ) = ((cnum v j : ℤ) : ℝ) + 4611686018427387904 := by
    exact_mod_cast hcj
  change _ = ((getN pack 0 - 4611686018427387904 : ℕ) : ℝ) * _ + _
  rw [hcjR, hsqR, corr_cast, mul_div_cancel₀ _ hne0R]

end Exp7.Rows
