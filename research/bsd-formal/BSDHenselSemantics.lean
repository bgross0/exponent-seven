import BSDHenselWitness
import BSDCoordinateRing
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.Tactic

/-!
# Polynomial meaning of the strong-Hensel numerical witnesses

The integer coefficient and derivative lists used by `BSDHenselWitness`
are interpreted here as genuine Mathlib polynomials. Finite coordinate
evaluation is transported to polynomial evaluation modulo a principal ideal.
No CM interpretation of the candidate polynomials is assumed.
-/

namespace BSDHenselSemantics

set_option maxRecDepth 20000
set_option maxHeartbeats 0

open BSDFiniteWitness BSDHenselWitness BSDCoordinateRing Polynomial

variable {R S : Type*} [CommRing R] [CommRing S]

/-- A full signed integer coefficient list, ordered from degree zero upwards,
as an actual polynomial over a commutative ring. -/
noncomputable def integerPolynomial (R : Type*) [CommRing R] (cs : List ℤ) : Polynomial R :=
  cs.foldr (fun (c : ℤ) f => Polynomial.C (c : R) + Polynomial.X * f) 0

@[simp] theorem integerPolynomial_nil : integerPolynomial R [] = 0 := rfl

@[simp] theorem integerPolynomial_cons (c : ℤ) (cs : List ℤ) :
    integerPolynomial R (c :: cs) = C (c : R) + X * integerPolynomial R cs := rfl

/-- Interpretation commutes with every coefficient-ring homomorphism. -/
theorem integerPolynomial_map (f : R →+* S) (cs : List ℤ) :
    (integerPolynomial R cs).map f = integerPolynomial S cs := by
  induction cs with
  | nil => simp
  | cons c cs ih => simp [ih]

/-- Offset-weighted coefficients represent `n P + X P'`. -/
theorem integerPolynomial_weighted (cs : List ℤ) (n : ℕ) :
    integerPolynomial R ((cs.zipIdx n).map fun ci => (ci.2 : ℤ) * ci.1) =
      C (n : R) * integerPolynomial R cs +
        X * (integerPolynomial R cs).derivative := by
  induction cs generalizing n with
  | nil => simp
  | cons c cs ih =>
    simp only [List.zipIdx_cons, List.map_cons, integerPolynomial_cons, ih,
      derivative_add, derivative_C, derivative_mul, derivative_X, zero_add, one_mul]
    simp only [Int.cast_mul, Int.cast_natCast, Nat.cast_add, Nat.cast_one,
      map_mul, map_add, map_one]
    ring

/-- The derivative coefficient list in the numerical certificate is exactly
the formal derivative of the genuine polynomial, over every commutative ring. -/
theorem integerPolynomial_formalDerivative (cs : List ℤ) :
    integerPolynomial R (formalDerivative cs) =
      (integerPolynomial R cs).derivative := by
  cases cs with
  | nil => simp [formalDerivative]
  | cons c cs =>
    simp only [formalDerivative, List.zipIdx_cons, List.drop_succ_cons,
      List.drop_zero, Nat.zero_add]
    rw [integerPolynomial_weighted]
    simp

/-- Coordinate interpretation commutes with a ring homomorphism. -/
theorem map_evalPair (f : R →+* S) (u : R) (x : Pair) :
    f (evalPair u x) = evalPair (f u) x := by
  simp [evalPair]

/-- The reduced integer coefficient list defines the expected polynomial in
every ring annihilated by the witness modulus. -/
theorem coefficientPolynomial_integerCoefficientsMod
    (hm : (modulus : R) = 0) (u : R) (cs : List ℤ) :
    coefficientPolynomial u (integerCoefficientsMod cs) = integerPolynomial R cs := by
  induction cs with
  | nil => simp [integerCoefficientsMod, coefficientPolynomial]
  | cons c cs ih =>
    simp only [integerCoefficientsMod, List.map_cons, coefficientPolynomial,
      List.foldr_cons, integerPolynomial_cons] at ih ⊢
    rw [ih]
    have hp : 0 < modulus := by norm_num [modulus]
    simp [evalPair, int_mod_toNat_cast modulus c hm hp]

/-- A finite coordinate evaluation is a genuine polynomial evaluation in
every quotient where `433^25 = 0` and the quadratic generator squares to five. -/
theorem evaluateMod_semantics (hm : (modulus : R) = 0)
    (u : R) (hu : u ^ 2 = 5) (cs : List ℤ) (x : Pair) :
    evalPair u (evaluateMod modulus (integerCoefficientsMod cs) x) =
      (integerPolynomial R cs).eval (evalPair u x) := by
  rw [evalPair_evaluateMod modulus hm u hu,
    coefficientPolynomial_integerCoefficientsMod hm]

/-- In particular, the certificate's derivative evaluation is an evaluation
of Mathlib's actual polynomial derivative. -/
theorem evaluateMod_derivative_semantics (hm : (modulus : R) = 0)
    (u : R) (hu : u ^ 2 = 5) (cs : List ℤ) (x : Pair) :
    evalPair u
      (evaluateMod modulus (integerCoefficientsMod (formalDerivative cs)) x) =
      (integerPolynomial R cs).derivative.eval (evalPair u x) := by
  rw [evaluateMod_semantics hm u hu, integerPolynomial_formalDerivative]

/-- Evaluation of an integer coefficient list commutes with ring maps. -/
theorem map_integerPolynomial_eval (f : R →+* S) (cs : List ℤ) (x : R) :
    f ((integerPolynomial R cs).eval x) =
      (integerPolynomial S cs).eval (f x) := by
  induction cs with
  | nil => simp
  | cons c cs ih => simp [ih]

/-- The error in finite evaluation is divisible by the full witness modulus,
in the ring itself, without assuming that the ring has finite characteristic. -/
theorem evaluateMod_difference_dvd (u : R) (hu : u ^ 2 = 5)
    (cs : List ℤ) (x : Pair) :
    (modulus : R) ∣ (integerPolynomial R cs).eval (evalPair u x) -
      evalPair u (evaluateMod modulus (integerCoefficientsMod cs) x) := by
  let I : Ideal R := Ideal.span {(modulus : R)}
  let q : R →+* R ⧸ I := Ideal.Quotient.mk I
  have hm : (modulus : R ⧸ I) = 0 := by
    simpa only [map_natCast] using Ideal.Quotient.mk_singleton_self (modulus : R)
  have hu' : q u ^ 2 = 5 := by
    rw [← map_pow, hu, map_ofNat]
  have h := evaluateMod_semantics hm (q u) hu' cs x
  apply (Ideal.Quotient.eq_zero_iff_dvd (modulus : R) _).mp
  change q (_ - _) = 0
  simp only [map_sub, map_integerPolynomial_eval, map_evalPair]
  exact sub_eq_zero.mpr h.symm

/-- Natural-number divisibility remains valid after casting to any ring. -/
theorem natCast_dvd (n k : ℕ) (h : n ∣ k) : (n : R) ∣ (k : R) := by
  obtain ⟨a, ha⟩ := h
  refine ⟨(a : R), ?_⟩
  simpa only [Nat.cast_mul] using congrArg (fun z : ℕ => (z : R)) ha

/-- Coordinate divisibility implies divisibility of the represented element. -/
theorem evalPair_dvd (n : ℕ) (u : R) (x : Pair)
    (ha : n ∣ x.1) (hb : n ∣ x.2) : (n : R) ∣ evalPair u x := by
  exact dvd_add (natCast_dvd n x.1 ha)
    (dvd_mul_of_dvd_left (natCast_dvd n x.2 hb) u)

/-- Divisibility of the finite residue transfers to actual polynomial
evaluation at the supplied integer coordinate approximation. -/
theorem polynomial_eval_dvd_of_residue (n : ℕ) (hn : n ∣ modulus)
    (u : R) (hu : u ^ 2 = 5) (cs : List ℤ) (x : Pair)
    (ha : n ∣ (evaluateMod modulus (integerCoefficientsMod cs) x).1)
    (hb : n ∣ (evaluateMod modulus (integerCoefficientsMod cs) x).2) :
    (n : R) ∣ (integerPolynomial R cs).eval (evalPair u x) := by
  have herror := (natCast_dvd (R := R) n modulus hn).trans
    (evaluateMod_difference_dvd u hu cs x)
  have hres := evalPair_dvd n u _ ha hb
  simpa only [sub_add_cancel] using dvd_add herror hres

/-- Exact division of both finite coordinates divides their represented value. -/
theorem evalPair_coordinate_division (d : ℕ) (u : R) (v : Pair)
    (ha : d ∣ v.1) (hb : d ∣ v.2) :
    evalPair u v = (d : R) * evalPair u (v.1 / d, v.2 / d) := by
  have ha' : (v.1 : R) = (d : R) * ((v.1 / d : ℕ) : R) := by
    simpa only [Nat.cast_mul] using
      congrArg (fun z : ℕ => (z : R)) (Nat.mul_div_cancel' ha).symm
  have hb' : (v.2 : R) = (d : R) * ((v.2 / d : ℕ) : R) := by
    simpa only [Nat.cast_mul] using
      congrArg (fun z : ℕ => (z : R)) (Nat.mul_div_cancel' hb).symm
  simp only [evalPair]
  rw [ha', hb']
  ring

/-- The actual divided value is congruent to the coordinatewise divided
finite residue modulo `433^25 / d`. This supplies the normalized derivative
needed in strong Hensel, rather than only its undivided residue. -/
theorem exists_scaled_polynomial_eval (d : ℕ) (hd : d ∣ modulus)
    (u : R) (hu : u ^ 2 = 5) (cs : List ℤ) (x : Pair)
    (ha : d ∣ (evaluateMod modulus (integerCoefficientsMod cs) x).1)
    (hb : d ∣ (evaluateMod modulus (integerCoefficientsMod cs) x).2) :
    ∃ z : R,
      (integerPolynomial R cs).eval (evalPair u x) = (d : R) * z ∧
      ((modulus / d : ℕ) : R) ∣ z -
        evalPair u
          ((evaluateMod modulus (integerCoefficientsMod cs) x).1 / d,
           (evaluateMod modulus (integerCoefficientsMod cs) x).2 / d) := by
  let v := evaluateMod modulus (integerCoefficientsMod cs) x
  obtain ⟨t, ht⟩ := evaluateMod_difference_dvd u hu cs x
  let v0 := evalPair u (v.1 / d, v.2 / d)
  refine ⟨v0 + ((modulus / d : ℕ) : R) * t, ?_, ?_⟩
  · have hm : (modulus : R) = (d : R) * ((modulus / d : ℕ) : R) := by
      simpa only [Nat.cast_mul] using
        congrArg (fun z : ℕ => (z : R)) (Nat.mul_div_cancel' hd).symm
    have hv := evalPair_coordinate_division d u v ha hb
    change (integerPolynomial R cs).eval (evalPair u x) - evalPair u v = _ at ht
    rw [hv, hm] at ht
    dsimp only [v0]
    linear_combination ht
  · refine ⟨t, ?_⟩
    dsimp only [v0]
    ring

/-- The normalized derivative residue, before passage to the completion. -/
def normalizedDerivativeResidue (cs : List ℤ) (x : Pair) (s : ℕ) : Pair :=
  let dv := evaluateMod modulus (integerCoefficientsMod (formalDerivative cs)) x
  (dv.1 / 433 ^ s, dv.2 / 433 ^ s)

/-- The quadratic norm reduced to a natural residue modulo `433^4`. -/
def quadraticNormResidue (v : Pair) : ℕ :=
  ((((v.1 : ℤ) ^ 2 - 5 * (v.2 : ℤ) ^ 2) % (433 ^ 4 : ℤ))).toNat

/-- All seven normalized derivatives have norm coprime to `433^4`.
This is an explicit unit certificate, not a valuation inference. -/
theorem normalizedDerivative71_coprime : ∀ i : Fin 7,
    Nat.Coprime
      (quadraticNormResidue
        (normalizedDerivativeResidue candidate71Coefficients rootLifts71[i.val]!
          derivativeValuations71[i.val]!))
      (433 ^ 4) := by
  intro i
  unfold normalizedDerivativeResidue
  rw [derivative71_reduction]
  revert i
  decide +kernel

/-- The same norm-unit certificate for every one of the 140 roots. -/
theorem normalizedDerivative44375_coprime : ∀ i : Fin 140,
    Nat.Coprime
      (quadraticNormResidue
        (normalizedDerivativeResidue candidate44375Coefficients rootLifts44375[i.val]!
          derivativeValuations44375[i.val]!))
      (433 ^ 4) := by
  intro i
  unfold normalizedDerivativeResidue
  rw [derivative44375_reduction]
  revert i
  decide +kernel

/-- The numerical data leave four powers of precision even after division
by the square of the derivative scale. -/
theorem derivative71_precision : ∀ i : Fin 7,
    2 * derivativeValuations71[i.val]! + 4 ≤ 24 := by
  decide +kernel

theorem derivative44375_precision : ∀ i : Fin 140,
    2 * derivativeValuations44375[i.val]! + 4 ≤ 24 := by
  decide +kernel

/-- The checked finite premises imply actual divisibility of the full
polynomial and an actual derivative factor with a controlled normalized
residue. These are the ring-theoretic inputs to a strong Hensel argument. -/
theorem numericalPremises_lifting_inputs (u : R) (hu : u ^ 2 = 5)
    (cs : List ℤ) (x : Pair) (s : ℕ)
    (h : numericalPremises (integerCoefficientsMod cs)
      (integerCoefficientsMod (formalDerivative cs)) x s)
    (hprecision : 2 * s + 4 ≤ 24) :
    ((433 : R) ^ (2 * s + 4) ∣ (integerPolynomial R cs).eval (evalPair u x)) ∧
    ∃ z : R,
      (integerPolynomial R cs).derivative.eval (evalPair u x) = (433 : R) ^ s * z ∧
      (433 : R) ^ 4 ∣ z - evalPair u (normalizedDerivativeResidue cs x s) := by
  obtain ⟨hr1, hr2, _, hd1, hd2, _, hs, _⟩ := h
  have hr1' := Nat.dvd_of_mod_eq_zero hr1
  have hr2' := Nat.dvd_of_mod_eq_zero hr2
  have hd1' := Nat.dvd_of_mod_eq_zero hd1
  have hd2' := Nat.dvd_of_mod_eq_zero hd2
  constructor
  · have hn : 433 ^ (2 * s + 4) ∣ modulus :=
      Nat.pow_dvd_pow 433 (by omega)
    have he := polynomial_eval_dvd_of_residue (433 ^ (2 * s + 4)) hn u hu cs x
      ((Nat.pow_dvd_pow 433 hprecision).trans hr1')
      ((Nat.pow_dvd_pow 433 hprecision).trans hr2')
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using he
  · have hsM : 433 ^ s ∣ modulus := Nat.pow_dvd_pow 433 (by omega)
    obtain ⟨z, hz, he⟩ := exists_scaled_polynomial_eval (433 ^ s) hsM
      u hu (formalDerivative cs) x hd1' hd2'
    refine ⟨z, ?_, ?_⟩
    · simpa only [integerPolynomial_formalDerivative, Nat.cast_pow, Nat.cast_ofNat] using hz
    · have hdiv : 433 ^ 4 ∣ modulus / 433 ^ s := by
        rw [modulus, Nat.pow_div (by omega : s ≤ 25) (by decide : 0 < 433)]
        exact Nat.pow_dvd_pow 433 (by omega)
      have ht := (natCast_dvd (R := R) _ _ hdiv).trans he
      simpa only [normalizedDerivativeResidue, Nat.cast_pow, Nat.cast_ofNat] using ht

/-- All seven full degree-seven polynomial evaluations have the required
actual strong-lifting inputs in any target quadratic ring. -/
theorem candidate71_lifting_inputs (u : R) (hu : u ^ 2 = 5) (i : Fin 7) :
    ((433 : R) ^ (2 * derivativeValuations71[i.val]! + 4) ∣
      (integerPolynomial R candidate71Coefficients).eval (evalPair u rootLifts71[i.val]!)) ∧
    ∃ z : R,
      (integerPolynomial R candidate71Coefficients).derivative.eval
        (evalPair u rootLifts71[i.val]!) = (433 : R) ^ derivativeValuations71[i.val]! * z ∧
      (433 : R) ^ 4 ∣ z - evalPair u
        (normalizedDerivativeResidue candidate71Coefficients rootLifts71[i.val]!
          derivativeValuations71[i.val]!) := by
  exact numericalPremises_lifting_inputs u hu _ _ _
    (rootLifts71_numerical i) (derivative71_precision i)

/-- All 140 full degree-140 polynomial evaluations have the same actual
strong-lifting inputs. -/
theorem candidate44375_lifting_inputs (u : R) (hu : u ^ 2 = 5) (i : Fin 140) :
    ((433 : R) ^ (2 * derivativeValuations44375[i.val]! + 4) ∣
      (integerPolynomial R candidate44375Coefficients).eval
        (evalPair u rootLifts44375[i.val]!)) ∧
    ∃ z : R,
      (integerPolynomial R candidate44375Coefficients).derivative.eval
        (evalPair u rootLifts44375[i.val]!) = (433 : R) ^ derivativeValuations44375[i.val]! * z ∧
      (433 : R) ^ 4 ∣ z - evalPair u
        (normalizedDerivativeResidue candidate44375Coefficients rootLifts44375[i.val]!
          derivativeValuations44375[i.val]!) := by
  exact numericalPremises_lifting_inputs u hu _ _ _
    (rootLifts44375_numerical i) (derivative44375_precision i)

/-- A final coefficient equal to one proves monicity and the exact degree
of the interpreted polynomial. The target ring need only be nontrivial. -/
theorem integerPolynomial_monic_natDegree [Nontrivial R]
    (cs : List ℤ) (h : cs.getLast? = some 1) :
    (integerPolynomial R cs).Monic ∧
      (integerPolynomial R cs).natDegree + 1 = cs.length := by
  induction cs with
  | nil => simp at h
  | cons c cs ih =>
    cases cs with
    | nil =>
      have hc : c = 1 := by simpa using h
      subst c
      simp
    | cons d ds =>
      have ht : (d :: ds).getLast? = some 1 := by simpa using h
      obtain ⟨hm, hdegree⟩ := ih ht
      have hXm : (X * integerPolynomial R (d :: ds)).Monic := monic_X.mul hm
      have hpos : 0 < (X * integerPolynomial R (d :: ds)).degree := by
        rw [degree_eq_natDegree hXm.ne_zero, natDegree_X_mul hm.ne_zero]
        exact_mod_cast Nat.zero_lt_succ _
      constructor
      · exact hXm.add_of_right (degree_C_le.trans_lt hpos)
      · rw [integerPolynomial_cons, natDegree_C_add, natDegree_X_mul hm.ne_zero]
        simpa using congrArg (fun n : ℕ => n + 1) hdegree

/-- The full degree-seven candidate is an actual monic polynomial. -/
theorem candidate71_monic [Nontrivial R] :
    (integerPolynomial R candidate71Coefficients).Monic :=
  (integerPolynomial_monic_natDegree _ candidate71_degree_data.2).1

/-- The full candidate's actual polynomial degree is seven. -/
theorem candidate71_natDegree [Nontrivial R] :
    (integerPolynomial R candidate71Coefficients).natDegree = 7 := by
  have h := (integerPolynomial_monic_natDegree (R := R) _ candidate71_degree_data.2).2
  rw [candidate71_degree_data.1] at h
  omega

/-- The full degree-140 candidate is an actual monic polynomial. -/
theorem candidate44375_monic [Nontrivial R] :
    (integerPolynomial R candidate44375Coefficients).Monic :=
  (integerPolynomial_monic_natDegree _ candidate44375_degree_data.2).1

/-- The full candidate's actual polynomial degree is 140. -/
theorem candidate44375_natDegree [Nontrivial R] :
    (integerPolynomial R candidate44375Coefficients).natDegree = 140 := by
  have h := (integerPolynomial_monic_natDegree (R := R) _ candidate44375_degree_data.2).2
  rw [candidate44375_degree_data.1] at h
  omega

end BSDHenselSemantics
