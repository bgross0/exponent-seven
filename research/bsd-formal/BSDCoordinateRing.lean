import BSDFiniteWitness
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Ring semantics of the finite E433 coordinate arithmetic

The finite certificate uses natural-number pairs for coordinates modulo `m`,
with the second basis element squaring to five. This module proves that every
arithmetic operation and polynomial evaluation used there has its intended
meaning in any commutative ring where `m = 0` and `u^2 = 5`.

These are algebraic soundness theorems. They do not identify a polynomial with
an arithmetic CM construction or prove a geometric modular correspondence.
-/

namespace BSDCoordinateRing

open BSDFiniteWitness

variable {R : Type*} [CommRing R]

/-- Interpret a coordinate pair in a ring with a chosen quadratic generator. -/
def evalPair (u : R) (x : Pair) : R := (x.1 : R) + (x.2 : R) * u

/-- Reduction of natural numbers modulo an annihilated modulus preserves
its image in the coefficient ring. -/
theorem nat_mod_cast (m n : ℕ) (hm : (m : R) = 0) :
    ((n % m : ℕ) : R) = (n : R) := by
  have h := congrArg (fun a : ℕ => (a : R)) (Nat.mod_add_div n m)
  simpa [Nat.cast_add, Nat.cast_mul, hm] using h

/-- The same statement for signed integer coefficients. -/
theorem int_mod_cast (m : ℕ) (n : ℤ) (hm : (m : R) = 0) :
    ((n % (m : ℤ) : ℤ) : R) = (n : R) := by
  have h := congrArg (fun a : ℤ => (a : R)) (Int.emod_add_mul_ediv n (m : ℤ))
  simpa [Int.cast_add, Int.cast_mul, hm] using h

/-- The positive modulus makes conversion of the signed remainder to a
natural number sound. -/
theorem int_mod_toNat_cast (m : ℕ) (n : ℤ)
    (hm : (m : R) = 0) (hmpos : 0 < m) :
    (((n % (m : ℤ)).toNat : ℕ) : R) = (n : R) := by
  have hmne : (m : ℤ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hmpos
  have hnonneg := Int.emod_nonneg n hmne
  calc
    (((n % (m : ℤ)).toNat : ℕ) : R) = ((n % (m : ℤ) : ℤ) : R) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg hnonneg]
    _ = (n : R) := int_mod_cast m n hm

theorem evalPair_zero (u : R) : evalPair u (0, 0) = 0 := by simp [evalPair]

theorem evalPair_one (u : R) : evalPair u (1, 0) = 1 := by simp [evalPair]

theorem evalPair_addMod (m : ℕ) (hm : (m : R) = 0) (u : R) (x y : Pair) :
    evalPair u (addMod m x y) = evalPair u x + evalPair u y := by
  simp only [evalPair, addMod, nat_mod_cast m _ hm, Nat.cast_add]
  ring

theorem evalPair_mulMod (m : ℕ) (hm : (m : R) = 0) (u : R)
    (hu : u ^ 2 = 5) (x y : Pair) :
    evalPair u (mulMod m x y) = evalPair u x * evalPair u y := by
  simp only [evalPair, mulMod, nat_mod_cast m _ hm, Nat.cast_add, Nat.cast_mul,
    Nat.cast_ofNat]
  calc
    _ = ((x.1 : R) + (x.2 : R) * u) * ((y.1 : R) + (y.2 : R) * u) +
        (x.2 : R) * (y.2 : R) * (5 - u ^ 2) := by ring
    _ = _ := by rw [hu]; ring

theorem evalPair_scaleMod (m : ℕ) (hm : (m : R) = 0) (hmpos : 0 < m)
    (u : R) (c : ℤ) (x : Pair) :
    evalPair u (scaleMod m c x) = (c : R) * evalPair u x := by
  simp only [evalPair, scaleMod, int_mod_toNat_cast m _ hm hmpos, Int.cast_mul,
    Int.cast_natCast]
  ring

/-- Soundness of the integer linear-combination accumulator. -/
theorem evalPair_linMod_foldl (m : ℕ) (hm : (m : R) = 0) (hmpos : 0 < m)
    (u : R) (ts : List (ℤ × Pair)) (acc : Pair) :
    evalPair u (ts.foldl (fun a t => addMod m a (scaleMod m t.1 t.2)) acc) =
      evalPair u acc + (ts.map (fun t => (t.1 : R) * evalPair u t.2)).sum := by
  induction ts generalizing acc with
  | nil => simp
  | cons t ts ih =>
    simp only [List.foldl_cons, ih, evalPair_addMod m hm,
      evalPair_scaleMod m hm hmpos, List.map_cons, List.sum_cons]
    ring

theorem evalPair_linMod (m : ℕ) (hm : (m : R) = 0) (hmpos : 0 < m)
    (u : R) (ts : List (ℤ × Pair)) :
    evalPair u (linMod m ts) =
      (ts.map (fun t => (t.1 : R) * evalPair u t.2)).sum := by
  simpa [linMod, evalPair_zero] using evalPair_linMod_foldl m hm hmpos u ts (0, 0)

/-- The actual Mathlib polynomial whose coefficients are the interpreted
coordinate list, ordered from constant coefficient upwards. -/
noncomputable def coefficientPolynomial (u : R) (cs : List Pair) : Polynomial R :=
  cs.foldr (fun c f => Polynomial.C (evalPair u c) + Polynomial.X * f) 0

/-- The finite Horner evaluator agrees with evaluation of a Mathlib polynomial
in any ring satisfying the two stated relations. -/
theorem evalPair_evaluateMod (m : ℕ) (hm : (m : R) = 0) (u : R)
    (hu : u ^ 2 = 5) (cs : List Pair) (x : Pair) :
    evalPair u (evaluateMod m cs x) =
      (coefficientPolynomial u cs).eval (evalPair u x) := by
  induction cs with
  | nil => simp [evaluateMod, coefficientPolynomial, evalPair_zero]
  | cons c cs ih =>
    change evalPair u (addMod m (mulMod m (evaluateMod m cs x) x) c) = _
    rw [evalPair_addMod m hm, evalPair_mulMod m hm u hu, ih]
    simp only [coefficientPolynomial, List.foldr_cons, Polynomial.eval_add,
      Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_X]
    ring

/-- The explicit level-two modular-polynomial expression. Its arithmetic
modular interpretation is not assumed by the coordinate soundness proof. -/
def classicalPhi2 (x y : R) : R :=
  x ^ 3 + y ^ 3 - x ^ 2 * y ^ 2 + 1488 * (x ^ 2 * y + x * y ^ 2) -
    162000 * (x ^ 2 + y ^ 2) + 40773375 * x * y +
    8748000000 * (x + y) - 157464000000000

/-- The literal finite Phi_2 evaluator is precisely this polynomial expression
in every coefficient ring with the required modulus and quadratic relation. -/
theorem evalPair_phi2Mod (m : ℕ) (hm : (m : R) = 0) (hmpos : 0 < m)
    (u : R) (hu : u ^ 2 = 5) (x y : Pair) :
    evalPair u (phi2Mod m x y) = classicalPhi2 (evalPair u x) (evalPair u y) := by
  rw [phi2Mod, evalPair_evaluateMod m hm u hu]
  simp only [phi2Coefficients, coefficientPolynomial, List.foldr_cons, List.foldr_nil,
    Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_X,
    Polynomial.eval_zero, evalPair_linMod m hm hmpos, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, evalPair_mulMod m hm u hu, evalPair_one]
  push_cast
  unfold classicalPhi2
  ring

/-- A kernel-checked zero congruence supplies a genuine polynomial zero in any
intended quotient ring with the stated relations. -/
theorem classicalPhi2_eq_zero_of_finite_witness
    (m : ℕ) (hm : (m : R) = 0) (hmpos : 0 < m)
    (u : R) (hu : u ^ 2 = 5) (x y : Pair)
    (hzero : phi2Mod m x y = (0, 0)) :
    classicalPhi2 (evalPair u x) (evalPair u y) = 0 := by
  rw [← evalPair_phi2Mod m hm hmpos u hu x y, hzero, evalPair_zero]

/-- The canonical quadratic coordinate ring `(Z/mZ)[u]/(u²-5)`. -/
noncomputable def quadraticPolynomial (m : ℕ) : Polynomial (ZMod m) :=
  Polynomial.X ^ 2 - Polynomial.C 5

abbrev QuadraticResidue (m : ℕ) := AdjoinRoot (quadraticPolynomial m)

noncomputable def quadraticRoot (m : ℕ) : QuadraticResidue m :=
  AdjoinRoot.root (quadraticPolynomial m)

theorem quadraticResidue_modulus_zero (m : ℕ) : (m : QuadraticResidue m) = 0 := by
  have h := congrArg (AdjoinRoot.of (quadraticPolynomial m)) (ZMod.natCast_self m)
  simpa only [map_natCast, map_zero] using h

theorem quadraticRoot_sq (m : ℕ) : quadraticRoot m ^ 2 = 5 := by
  have h : (Polynomial.X ^ 2 - Polynomial.C (5 : ZMod m)).eval₂
      (AdjoinRoot.of (quadraticPolynomial m)) (quadraticRoot m) = 0 :=
    AdjoinRoot.eval₂_root (quadraticPolynomial m)
  rw [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
    Polynomial.eval₂_C, map_ofNat] at h
  exact sub_eq_zero.mp h

/-- A concrete quotient-ring form of the witness implication. In particular,
this applies at both moduli 433 and 433^4 used by the finite certificate. -/
theorem classicalPhi2_zero_in_quadraticResidue
    (m : ℕ) (hmpos : 0 < m) (x y : Pair)
    (hzero : phi2Mod m x y = (0, 0)) :
    classicalPhi2 (evalPair (quadraticRoot m) x) (evalPair (quadraticRoot m) y) = 0 := by
  exact classicalPhi2_eq_zero_of_finite_witness m (quadraticResidue_modulus_zero m)
    hmpos (quadraticRoot m) (quadraticRoot_sq m) x y hzero

end BSDCoordinateRing
