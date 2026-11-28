import BSDHenselLift
import Mathlib.NumberTheory.Zsqrtd.Basic
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.Data.Nat.ModEq

/-!
# Distinctness of roots from distinct quadratic residues

Congruence in the completed quadratic order is detected by the two integer
coordinates modulo the defining ideal. This connects the kernel-checked
distinct finite root table to distinct roots in the actual completion.
-/

namespace BSDHenselDistinct

open BSDFiniteWitness BSDCoordinateRing BSDHenselWitness BSDHenselSemantics
open BSDHenselLift

/-- Divisibility by a rational integer in `Z[sqrt(5)]` forces divisibility
of both integer coordinates, and therefore equality of their residues. -/
theorem coordinate_residues_eq_of_order_dvd (n : ℕ) (x y : Pair)
    (h : (n : Zsqrtd (5 : ℤ)) ∣
      evalPair Zsqrtd.sqrtd x - evalPair Zsqrtd.sqrtd y) :
    (x.1 % n, x.2 % n) = (y.1 % n, y.2 % n) := by
  obtain ⟨z, hz⟩ := h
  have hre : (n : ℤ) ∣ (x.1 : ℤ) - (y.1 : ℤ) := by
    refine ⟨z.re, ?_⟩
    simpa [evalPair, sub_eq_add_neg] using congrArg Zsqrtd.re hz
  have him : (n : ℤ) ∣ (x.2 : ℤ) - (y.2 : ℤ) := by
    refine ⟨z.im, ?_⟩
    simpa [evalPair, sub_eq_add_neg] using congrArg Zsqrtd.im hz
  exact Prod.ext (Nat.modEq_iff_dvd.mpr hre).symm (Nat.modEq_iff_dvd.mpr him).symm

/-- The finite quotient of the explicit quadratic order preserves its two
coordinates, so equal quotient values have equal coordinate residues. -/
theorem coordinate_residues_eq_of_quotient_eq (n : ℕ) (x y : Pair)
    (h : Ideal.Quotient.mk (Ideal.span {(n : Zsqrtd (5 : ℤ))})
        (evalPair Zsqrtd.sqrtd x) =
      Ideal.Quotient.mk (Ideal.span {(n : Zsqrtd (5 : ℤ))})
        (evalPair Zsqrtd.sqrtd y)) :
    (x.1 % n, x.2 % n) = (y.1 % n, y.2 % n) := by
  apply coordinate_residues_eq_of_order_dvd n x y
  apply (Ideal.Quotient.eq_zero_iff_dvd _ _).mp
  rw [map_sub, h, sub_self]

/-- Congruence in the concrete completion implies congruence of the original
integer coordinates modulo `433^4`. -/
theorem coordinate_residues_eq_of_completed_mem (x y : Pair)
    (h : evalPair quadraticGenerator x - evalPair quadraticGenerator y ∈ completedIdeal) :
    (x.1 % (433 ^ 4), x.2 % (433 ^ 4)) =
      (y.1 % (433 ^ 4), y.2 % (433 ^ 4)) := by
  have hk : evalPair quadraticGenerator x - evalPair quadraticGenerator y ∈
      RingHom.ker (AdicCompletion.evalOneₐ completionIdeal).toRingHom := by
    rw [AdicCompletion.ker_evalOneₐ_eq_map completionIdeal
      (Submodule.fg_span_singleton _)]
    exact h
  have hmap (a : Pair) :
      AdicCompletion.evalOneₐ completionIdeal (evalPair quadraticGenerator a) =
        Ideal.Quotient.mk completionIdeal (evalPair Zsqrtd.sqrtd a) := by
    rw [show evalPair quadraticGenerator a =
      algebraMap QuadraticOrder QuadraticCompletion (evalPair Zsqrtd.sqrtd a) by
        exact (map_evalPair _ _ _).symm]
    rfl
  change AdicCompletion.evalOneₐ completionIdeal (_ - _) = 0 at hk
  rw [map_sub, hmap x, hmap y] at hk
  apply coordinate_residues_eq_of_quotient_eq (433 ^ 4) x y
  exact sub_eq_zero.mp hk

/-- A bounded index into a mapped list evaluates to the mapped entry. -/
theorem mapped_getElem! {α β : Type*} [Inhabited α] [Inhabited β]
    (xs : List α) (f : α → β) (i : ℕ) (hi : i < xs.length) :
    (xs.map f)[i]! = f (xs[i]!) := by
  rw [getElem!_pos _ i (by simpa using hi), List.getElem_map, getElem!_pos _ i hi]

/-- The existing distinct canonical residue table makes the indexed residue
family injective, without rerunning a quadratic pairwise numerical check. -/
theorem indexed_map_injective_of_nodup {α β : Type*} [Inhabited α] [Inhabited β]
    (xs : List α) (f : α → β) (n : ℕ)
    (hlen : xs.length = n) (hnd : (xs.map f).Nodup) :
    Function.Injective (fun i : Fin n => f (xs[i.val]!)) := by
  intro i j hij
  have hi : i.val < xs.length := by simp [hlen]
  have hj : j.val < xs.length := by simp [hlen]
  have he : (xs.map f)[i.val]! = (xs.map f)[j.val]! := by
    rw [mapped_getElem! _ _ _ hi, mapped_getElem! _ _ _ hj]
    exact hij
  apply Fin.ext
  exact (hnd.getElem!_inj (by simpa using hi) (by simpa using hj)).mp he

/-- Distinct degree-seven labels have distinct residues in the checked table. -/
theorem rootLifts71_residue_injective : Function.Injective (fun i : Fin 7 =>
    ((rootLifts71[i.val]!).1 % (433 ^ 4), (rootLifts71[i.val]!).2 % (433 ^ 4))) := by
  apply indexed_map_injective_of_nodup rootLifts71
    (fun x : Pair => (x.1 % (433 ^ 4), x.2 % (433 ^ 4))) 7 rootLifts71_binding.1
  rw [rootLifts71_binding.2.2]
  exact cm71Roots433_distinct.2.1

/-- Distinct degree-140 labels have distinct residues in the checked table. -/
theorem rootLifts44375_residue_injective : Function.Injective (fun i : Fin 140 =>
    ((rootLifts44375[i.val]!).1 % (433 ^ 4), (rootLifts44375[i.val]!).2 % (433 ^ 4))) := by
  apply indexed_map_injective_of_nodup rootLifts44375
    (fun x : Pair => (x.1 % (433 ^ 4), x.2 % (433 ^ 4))) 140 rootLifts44375_binding.1
  rw [rootLifts44375_binding.2.2]
  exact cm433Roots_distinct.2.1

/-- All seven roots chosen in the actual completion are distinct. -/
theorem root71_injective : Function.Injective root71 := by
  intro i j hij
  apply rootLifts71_residue_injective
  apply coordinate_residues_eq_of_completed_mem
  have h := completedIdeal.sub_mem (root71_spec j).2 (root71_spec i).2
  rw [← hij] at h
  convert h using 1; abel

/-- All 140 roots chosen in the actual completion are distinct. -/
theorem root44375_injective : Function.Injective root44375 := by
  intro i j hij
  apply rootLifts44375_residue_injective
  apply coordinate_residues_eq_of_completed_mem
  have h := completedIdeal.sub_mem (root44375_spec j).2 (root44375_spec i).2
  rw [← hij] at h
  convert h using 1; abel

/-- The degree-seven polynomial has a family of seven distinct actual roots
with their original certified residues. -/
theorem candidate71_distinct_roots :
    ∃ roots : Fin 7 → QuadraticCompletion, Function.Injective roots ∧
      ∀ i, (integerPolynomial QuadraticCompletion candidate71Coefficients).IsRoot (roots i) ∧
        roots i - evalPair quadraticGenerator rootLifts71[i.val]! ∈ completedIdeal := by
  exact ⟨root71, root71_injective, root71_spec⟩

/-- The degree-140 polynomial has a family of 140 distinct actual roots
with their original certified residues. -/
theorem candidate44375_distinct_roots :
    ∃ roots : Fin 140 → QuadraticCompletion, Function.Injective roots ∧
      ∀ i, (integerPolynomial QuadraticCompletion candidate44375Coefficients).IsRoot (roots i) ∧
        roots i - evalPair quadraticGenerator rootLifts44375[i.val]! ∈ completedIdeal := by
  exact ⟨root44375, root44375_injective, root44375_spec⟩

/-- Reducing both coordinates preserves their value in a ring annihilated
by the modulus. -/
theorem evalPair_reduce {R : Type*} [CommRing R] (n : ℕ)
    (hn : (n : R) = 0) (u : R) (x : Pair) :
    evalPair u (x.1 % n, x.2 % n) = evalPair u x := by
  simp only [evalPair, nat_mod_cast n _ hn]

/-- The high-precision approximation for each degree-seven label reduces
to its original canonical finite table entry. -/
theorem rootLifts71_canonical_residue (i : Fin 7) :
    ((rootLifts71[i.val]!).1 % (433 ^ 4), (rootLifts71[i.val]!).2 % (433 ^ 4)) =
      cm71Roots433[i.val]! := by
  have hi : i.val < rootLifts71.length := by rw [rootLifts71_binding.1]; exact i.isLt
  have h := congrArg (fun xs : List Pair => xs[i.val]!) rootLifts71_binding.2.2
  rw [mapped_getElem! _ _ _ hi] at h
  exact h

/-- The same exact binding for every degree-140 approximation. -/
theorem rootLifts44375_canonical_residue (i : Fin 140) :
    ((rootLifts44375[i.val]!).1 % (433 ^ 4), (rootLifts44375[i.val]!).2 % (433 ^ 4)) =
      cm433Roots[i.val]! := by
  have hi : i.val < rootLifts44375.length := by
    rw [rootLifts44375_binding.1]; exact i.isLt
  have h := congrArg (fun xs : List Pair => xs[i.val]!) rootLifts44375_binding.2.2
  rw [mapped_getElem! _ _ _ hi] at h
  exact h

/-- The actual chosen degree-seven root has exactly its canonical table
value in the quotient of the completion. -/
theorem root71_canonical_residue (i : Fin 7) :
    Ideal.Quotient.mk completedIdeal (root71 i) =
      evalPair (Ideal.Quotient.mk completedIdeal quadraticGenerator) cm71Roots433[i.val]! := by
  have h := Ideal.Quotient.eq_zero_iff_mem.mpr (root71_spec i).2
  rw [map_sub, sub_eq_zero] at h
  rw [h, map_evalPair]
  rw [← evalPair_reduce (433 ^ 4) quotient_modulus_zero _ rootLifts71[i.val]!,
    rootLifts71_canonical_residue]

/-- The actual chosen degree-140 root has exactly its canonical table
value in the quotient of the completion. -/
theorem root44375_canonical_residue (i : Fin 140) :
    Ideal.Quotient.mk completedIdeal (root44375 i) =
      evalPair (Ideal.Quotient.mk completedIdeal quadraticGenerator) cm433Roots[i.val]! := by
  have h := Ideal.Quotient.eq_zero_iff_mem.mpr (root44375_spec i).2
  rw [map_sub, sub_eq_zero] at h
  rw [h, map_evalPair]
  rw [← evalPair_reduce (433 ^ 4) quotient_modulus_zero _ rootLifts44375[i.val]!,
    rootLifts44375_canonical_residue]

end BSDHenselDistinct
