/-
The Newton-iteration proof is adapted from Mathlib/RingTheory/Henselian.lean.
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in Mathlib's LICENSE file.
-/
import Mathlib.NumberTheory.Zsqrtd.Basic
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.Henselian
import BSDHenselWitness
import BSDCoordinateRing
import BSDHenselSemantics

/-!
# Actual Hensel roots in the completed quadratic order

The completion used here is the (433^4)-adic completion of Z[sqrt(5)].
This is a concrete nontrivial commutative ring, not an assumed extension.
The simple-root existence proof below is the monicity-free Newton argument
from Mathlib/RingTheory/Henselian.lean (Johan Commelin, Apache 2.0).
-/

noncomputable section
open Polynomial IsLocalRing Function List
open scoped Ring
namespace BSDHenselLift

/-- The Newton argument for an adically complete ring does not need the
polynomial to be monic. -/
theorem simple_root_in_complete_ring {R : Type*} [CommRing R]
    (I : Ideal R) [IsAdicComplete I R] (f : Polynomial R) (a₀ : R)
    (h₁ : f.eval a₀ ∈ I)
    (h₂ : IsUnit (Ideal.Quotient.mk I (f.derivative.eval a₀))) :
    ∃ a : R, f.IsRoot a ∧ a - a₀ ∈ I := by
  classical
    let f' := derivative f
    -- we define a sequence `c n` by starting at `a₀` and then continually
    -- applying the function sending `b` to `b - f(b)/f'(b)` (Newton's method).
    -- Note that `f'.eval b` is a unit, because `b` has the same residue as `a₀` modulo `I`.
    let c : ℕ → R := fun n => Nat.recOn n a₀ fun _ b => b - f.eval b * (f'.eval b)⁻¹ʳ
    have hc : ∀ n, c (n + 1) = c n - f.eval (c n) * (f'.eval (c n))⁻¹ʳ := by
      intro n
      simp only [c]
    -- we now spend some time determining properties of the sequence `c : ℕ → R`
    -- `hc_mod`: for every `n`, we have `c n ≡ a₀ [SMOD I]`
    -- `hf'c`  : for every `n`, `f'.eval (c n)` is a unit
    -- `hfcI`  : for every `n`, `f.eval (c n)` is contained in `I ^ (n+1)`
    have hc_mod : ∀ n, c n ≡ a₀ [SMOD I] := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih => ?_
      rw [hc, sub_eq_add_neg, ← add_zero a₀]
      refine ih.add ?_
      rw [SModEq.zero, Ideal.neg_mem_iff]
      refine I.mul_mem_right _ ?_
      rw [← SModEq.zero] at h₁ ⊢
      exact (ih.eval f).trans h₁
    have hf'c : ∀ n, IsUnit (f'.eval (c n)) := by
      intro n
      have := isLocalHom_of_le_jacobson (IsAdicComplete.le_jacobson I)
      apply IsUnit.of_map (Ideal.Quotient.mk I)
      convert h₂ using 1
      exact SModEq.def.mp ((hc_mod n).eval _)
    have hfcI : ∀ n, f.eval (c n) ∈ I ^ (n + 1) := by
      intro n
      induction n with
      | zero => simpa only [Nat.rec_zero, zero_add, pow_one] using! h₁
      | succ n ih => ?_
      rw [← taylor_eval_sub (c n), hc, sub_eq_add_neg, sub_eq_add_neg,
        add_neg_cancel_comm]
      rw [eval_eq_sum, sum_over_range' _ _ _ (lt_add_of_pos_right _ zero_lt_two), ←
        Finset.sum_range_add_sum_Ico _ (Nat.le_add_left _ _)]
      swap
      · intro i
        rw [zero_mul]
      refine Ideal.add_mem _ ?_ ?_
      · rw [← one_add_one_eq_two, Finset.sum_range_succ, Finset.range_one, Finset.sum_singleton,
          taylor_coeff_zero, taylor_coeff_one, pow_zero, pow_one, mul_one, mul_neg,
          mul_left_comm, Ring.mul_inverse_cancel _ (hf'c n), mul_one, add_neg_cancel]
        exact Ideal.zero_mem _
      · refine Submodule.sum_mem _ ?_
        simp only [Finset.mem_Ico]
        rintro i ⟨h2i, _⟩
        have aux : n + 2 ≤ i * (n + 1) := by trans 2 * (n + 1) <;> nlinarith only [h2i]
        refine Ideal.mul_mem_left _ _ (Ideal.pow_le_pow_right aux ?_)
        rw [pow_mul']
        exact Ideal.pow_mem_pow ((Ideal.neg_mem_iff _).2 <| Ideal.mul_mem_right _ _ ih) _
    -- we are now in the position to show that `c : ℕ → R` is a Cauchy sequence
    have aux : ∀ m n, m ≤ n → c m ≡ c n [SMOD (I ^ m • ⊤ : Ideal R)] := by
      intro m n hmn
      rw [← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one]
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
      clear hmn
      induction k with
      | zero => rw [add_zero]
      | succ k ih => ?_
      rw [← add_assoc, hc, ← add_zero (c m), sub_eq_add_neg]
      refine ih.add ?_
      symm
      rw [SModEq.zero, Ideal.neg_mem_iff]
      refine Ideal.mul_mem_right _ _ (Ideal.pow_le_pow_right ?_ (hfcI _))
      rw [add_assoc]
      exact le_self_add
    -- hence the sequence converges to some limit point `a`, which is the `a` we are looking for
    obtain ⟨a, ha⟩ := IsPrecomplete.prec' c (aux _ _)
    refine ⟨a, ?_, ?_⟩
    · show f.IsRoot a
      suffices ∀ n, f.eval a ≡ 0 [SMOD (I ^ n • ⊤ : Ideal R)] by exact IsHausdorff.haus' _ this
      intro n
      specialize ha n
      rw [← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one] at ha ⊢
      refine (ha.symm.eval f).trans ?_
      rw [SModEq.zero]
      exact Ideal.pow_le_pow_right le_self_add (hfcI _)
    · show a - a₀ ∈ I
      specialize ha (0 + 1)
      rw [hc, pow_one, ← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one, sub_eq_add_neg] at ha
      rw [← SModEq.sub_mem, ← add_zero a₀]
      refine ha.symm.trans (SModEq.rfl.add ?_)
      rw [SModEq.zero, Ideal.neg_mem_iff]
      exact Ideal.mul_mem_right _ _ h₁

/-- Strong Hensel lifting after factoring the derivative scale. The conclusion
retains the root's congruence to the supplied approximation. -/
theorem scaled_root_in_complete_ring {R : Type*} [CommRing R]
    (I : Ideal R) [IsAdicComplete I R] (f : Polynomial R)
    (a d e v : R) (he : e ∈ I)
    (hf : f.eval a = d ^ 2 * e)
    (hdf : f.derivative.eval a = d * v)
    (hv : IsUnit (Ideal.Quotient.mk I v)) :
    ∃ z : R, f.IsRoot z ∧ z - a ∈ I := by
  classical
  let g := taylor a f - C (f.eval a) - C (f.derivative.eval a) * X
  have hg : (X : Polynomial R) ^ 2 ∣ g := by
    apply X_pow_dvd_iff.mpr
    intro n hn
    interval_cases n <;>
      simp [g, taylor_coeff_zero, taylor_coeff_one]
  obtain ⟨h, hh⟩ := hg
  have ht : taylor a f = C (d ^ 2 * e) + C (d * v) * X + X ^ 2 * h := by
    rw [← hh]
    dsimp [g]
    rw [← hf, ← hdf]
    ring
  let q : Polynomial R := C e + C v * X + X ^ 2 * h.comp (C d * X)
  have hq0 : q.eval 0 = e := by simp [q]
  have hq1 : q.derivative.eval 0 = v := by simp [q, derivative_mul]
  obtain ⟨y, hy, hyI⟩ := simple_root_in_complete_ring I q 0
    (by simpa [hq0] using he) (by simpa [hq1] using hv)
  refine ⟨a + d * y, ?_, ?_⟩
  · change f.eval (a + d * y) = 0
    have hEval := congrArg (fun k : Polynomial R => k.eval (d * y)) ht
    simp only [taylor_eval, eval_add, eval_C, eval_mul, eval_X, eval_pow] at hEval
    have hy' : e + v * y + y ^ 2 * h.eval (d * y) = 0 := by
      simpa [q] using hy
    rw [add_comm a (d * y), hEval]
    calc
      d ^ 2 * e + d * v * (d * y) + (d * y) ^ 2 * h.eval (d * y)
          = d ^ 2 * (e + v * y + y ^ 2 * h.eval (d * y)) := by ring
      _ = 0 := by rw [hy', mul_zero]
  · have : y ∈ I := by simpa using hyI
    simpa only [add_sub_cancel_left] using I.mul_mem_left d this


/-- A quadratic coordinate with norm coprime to the modulus is a unit in
any ring annihilated by that modulus. -/
theorem evalPair_isUnit_of_norm_coprime {R : Type*} [CommRing R]
    (u : R) (hu : u ^ 2 = 5) (v : BSDFiniteWitness.Pair)
    (hm : ((433 ^ 4 : ℕ) : R) = 0)
    (hc : Nat.Coprime (BSDHenselSemantics.quadraticNormResidue v) (433 ^ 4)) :
    IsUnit (BSDCoordinateRing.evalPair u v) := by
  have hc' := hc.isCoprime.map (Int.castRingHom R)
  have hn : IsUnit ((BSDHenselSemantics.quadraticNormResidue v : ℕ) : R) := by
    simpa only [map_natCast, hm, isCoprime_zero_right] using hc'
  have hnorm : IsUnit ((v.1 : R) ^ 2 - 5 * (v.2 : R) ^ 2) := by
    unfold BSDHenselSemantics.quadraticNormResidue at hn
    change IsUnit ((((((v.1 : ℤ) ^ 2 - 5 * (v.2 : ℤ) ^ 2) %
      ((433 ^ 4 : ℕ) : ℤ)).toNat : ℕ) : R)) at hn
    rw [BSDCoordinateRing.int_mod_toNat_cast (433 ^ 4) _ hm (by norm_num)] at hn
    simpa only [Int.cast_sub, Int.cast_pow, Int.cast_mul, Int.cast_ofNat,
      Int.cast_natCast] using hn
  obtain ⟨b, hb⟩ := isUnit_iff_exists_inv.mp hnorm
  apply IsUnit.of_mul_eq_one (((v.1 : R) - (v.2 : R) * u) * b)
  dsimp [BSDCoordinateRing.evalPair]
  calc
    ((v.1 : R) + (v.2 : R) * u) * (((v.1 : R) - (v.2 : R) * u) * b)
        = ((v.1 : R) ^ 2 - (v.2 : R) ^ 2 * u ^ 2) * b := by ring
    _ = 1 := by rw [hu]; convert hb using 1; ring


abbrev QuadraticOrder := Zsqrtd (5 : ℤ)

def completionIdeal : Ideal QuadraticOrder :=
  Ideal.span {(433 ^ 4 : QuadraticOrder)}

abbrev QuadraticCompletion := AdicCompletion completionIdeal QuadraticOrder

def completedIdeal : Ideal QuadraticCompletion :=
  completionIdeal.map (algebraMap QuadraticOrder QuadraticCompletion)

instance complete : IsAdicComplete completedIdeal QuadraticCompletion :=
  AdicCompletion.isAdicComplete_self completionIdeal (Submodule.fg_span_singleton _)

theorem completionIdeal_ne_top : completionIdeal ≠ ⊤ := by
  intro h
  have hmem : (1 : QuadraticOrder) ∈ completionIdeal := by rw [h]; trivial
  rw [completionIdeal, Ideal.mem_span_singleton] at hmem
  obtain ⟨x, hx⟩ := hmem
  have hre := congrArg Zsqrtd.re hx
  norm_num at hre
  omega

instance : Nontrivial QuadraticCompletion := by
  let : Nontrivial (QuadraticOrder ⧸ completionIdeal) :=
    Ideal.Quotient.nontrivial_iff.mpr completionIdeal_ne_top
  exact (AdicCompletion.evalOneₐ completionIdeal).toRingHom.domain_nontrivial


def quadraticGenerator : QuadraticCompletion :=
  algebraMap QuadraticOrder QuadraticCompletion Zsqrtd.sqrtd

theorem quadraticGenerator_sq : quadraticGenerator ^ 2 = 5 := by
  unfold quadraticGenerator
  rw [← map_pow, pow_two, Zsqrtd.dmuld]
  exact map_ofNat _ 5

theorem completedIdeal_eq_span : completedIdeal =
    Ideal.span {(433 ^ 4 : QuadraticCompletion)} := by
  simp only [completedIdeal, completionIdeal, Ideal.map_span, Set.image_singleton,
    map_pow, map_ofNat]

theorem quotient_modulus_zero :
    ((433 ^ 4 : ℕ) : QuadraticCompletion ⧸ completedIdeal) = 0 := by
  have h : (433 ^ 4 : QuadraticCompletion) ∈ completedIdeal := by
    rw [completedIdeal_eq_span]
    exact Ideal.subset_span (by simp)
  simpa only [map_pow, map_ofNat, Nat.cast_pow, Nat.cast_ofNat] using
    (Ideal.Quotient.eq_zero_iff_mem.mpr h)


/-- The verified finite derivative unit and residual divisibility produce an
actual root of the full polynomial in the concrete quadratic completion. -/
theorem root_exists_of_lifting_inputs (cs : List ℤ) (x : BSDFiniteWitness.Pair) (s : ℕ)
    (hres : (433 : QuadraticCompletion) ^ (2 * s + 4) ∣
      (BSDHenselSemantics.integerPolynomial QuadraticCompletion cs).eval
        (BSDCoordinateRing.evalPair quadraticGenerator x))
    (hder : ∃ v : QuadraticCompletion,
      (BSDHenselSemantics.integerPolynomial QuadraticCompletion cs).derivative.eval
        (BSDCoordinateRing.evalPair quadraticGenerator x) = (433 : QuadraticCompletion) ^ s * v ∧
      (433 : QuadraticCompletion) ^ 4 ∣ v - BSDCoordinateRing.evalPair quadraticGenerator
        (BSDHenselSemantics.normalizedDerivativeResidue cs x s))
    (hunit : Nat.Coprime (BSDHenselSemantics.quadraticNormResidue
      (BSDHenselSemantics.normalizedDerivativeResidue cs x s)) (433 ^ 4)) :
    ∃ z : QuadraticCompletion,
      (BSDHenselSemantics.integerPolynomial QuadraticCompletion cs).IsRoot z ∧
      z - BSDCoordinateRing.evalPair quadraticGenerator x ∈ completedIdeal := by
  obtain ⟨t, ht⟩ := hres
  obtain ⟨v, hv, hvmod⟩ := hder
  let q : QuadraticCompletion →+* QuadraticCompletion ⧸ completedIdeal :=
    Ideal.Quotient.mk completedIdeal
  have huq : (q quadraticGenerator) ^ 2 = 5 := by
    rw [← map_pow, quadraticGenerator_sq, map_ofNat]
  have hvq : q v = BSDCoordinateRing.evalPair (q quadraticGenerator)
      (BSDHenselSemantics.normalizedDerivativeResidue cs x s) := by
    rw [← BSDHenselSemantics.map_evalPair]
    apply sub_eq_zero.mp
    rw [← map_sub]
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    rw [completedIdeal_eq_span, Ideal.mem_span_singleton]
    exact hvmod
  have hqv : IsUnit (q v) := by
    rw [hvq]
    exact evalPair_isUnit_of_norm_coprime _ huq _ quotient_modulus_zero hunit
  apply scaled_root_in_complete_ring completedIdeal
    (BSDHenselSemantics.integerPolynomial QuadraticCompletion cs)
    (BSDCoordinateRing.evalPair quadraticGenerator x)
    ((433 : QuadraticCompletion) ^ s) ((433 : QuadraticCompletion) ^ 4 * t) v
  · rw [completedIdeal_eq_span, Ideal.mem_span_singleton]
    exact ⟨t, rfl⟩
  · rw [ht, pow_add, pow_mul']
    ring
  · exact hv
  · exact hqv

/-- Each of the seven certified approximations gives an actual root,
with its original residue retained modulo 433^4. -/
theorem root71_exists (i : Fin 7) :
    ∃ z : QuadraticCompletion,
      (BSDHenselSemantics.integerPolynomial QuadraticCompletion
        BSDHenselWitness.candidate71Coefficients).IsRoot z ∧
      z - BSDCoordinateRing.evalPair quadraticGenerator
        BSDHenselWitness.rootLifts71[i.val]! ∈ completedIdeal := by
  obtain ⟨hr, hd⟩ := BSDHenselSemantics.candidate71_lifting_inputs
    quadraticGenerator quadraticGenerator_sq i
  exact root_exists_of_lifting_inputs _ _ _ hr hd
    (BSDHenselSemantics.normalizedDerivative71_coprime i)

/-- Each of the 140 certified approximations gives an actual root of the
full degree-140 polynomial in the same concrete complete ring. -/
theorem root44375_exists (i : Fin 140) :
    ∃ z : QuadraticCompletion,
      (BSDHenselSemantics.integerPolynomial QuadraticCompletion
        BSDHenselWitness.candidate44375Coefficients).IsRoot z ∧
      z - BSDCoordinateRing.evalPair quadraticGenerator
        BSDHenselWitness.rootLifts44375[i.val]! ∈ completedIdeal := by
  obtain ⟨hr, hd⟩ := BSDHenselSemantics.candidate44375_lifting_inputs
    quadraticGenerator quadraticGenerator_sq i
  exact root_exists_of_lifting_inputs _ _ _ hr hd
    (BSDHenselSemantics.normalizedDerivative44375_coprime i)

/-- A choice of the actual root associated with each degree-seven label. -/
def root71 (i : Fin 7) : QuadraticCompletion := Classical.choose (root71_exists i)

/-- A choice of the actual root associated with each degree-140 label. -/
def root44375 (i : Fin 140) : QuadraticCompletion := Classical.choose (root44375_exists i)

theorem root71_spec (i : Fin 7) :
    (BSDHenselSemantics.integerPolynomial QuadraticCompletion
      BSDHenselWitness.candidate71Coefficients).IsRoot (root71 i) ∧
    root71 i - BSDCoordinateRing.evalPair quadraticGenerator
      BSDHenselWitness.rootLifts71[i.val]! ∈ completedIdeal :=
  Classical.choose_spec (root71_exists i)

theorem root44375_spec (i : Fin 140) :
    (BSDHenselSemantics.integerPolynomial QuadraticCompletion
      BSDHenselWitness.candidate44375Coefficients).IsRoot (root44375 i) ∧
    root44375 i - BSDCoordinateRing.evalPair quadraticGenerator
      BSDHenselWitness.rootLifts44375[i.val]! ∈ completedIdeal :=
  Classical.choose_spec (root44375_exists i)


end BSDHenselLift
