import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Exact finite separation and the final Kummer dimension argument

These results prove algebraic implications used by the BSD research project.
They do not define an arithmetic Selmer group, construct a global class, prove
an arithmetic comparison, or establish finiteness of a Tate--Shafarevich group.
The supplied subspace and localization map must be identified with those
arithmetic objects separately.
-/

namespace BSDLocalization

section Separation

variable {R : Type*} [CommRing R]

/-- The alternating determinant in a fixed common coordinate basis. -/
def det (a b : R × R) : R := a.1 * b.2 - a.2 * b.1

/-- Integral coordinate errors divisible by `m` give a determinant error
also divisible by `m`. No claim about the provenance of those bounds is made. -/
theorem det_sub_dvd_of_coordinate_errors
    (m : R) (A B a b ea eb : R × R)
    (hA : A = a + m • ea) (hB : B = b + m • eb) :
    m ∣ det A B - det a b := by
  refine ⟨ea.1 * b.2 + a.1 * eb.2 + m * ea.1 * eb.2 -
    ea.2 * b.1 - a.2 * eb.1 - m * ea.2 * eb.1, ?_⟩
  rw [hA, hB]
  simp only [det, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul]
  ring

/-- A nonzero finite residue certifies a nonzero true determinant, once the
coordinate error identities have been established in the integral ring. -/
theorem det_ne_zero_of_finite_certificate
    (m : R) (A B a b ea eb : R × R)
    (hA : A = a + m • ea) (hB : B = b + m • eb)
    (hresidue : ¬ m ∣ det a b) : det A B ≠ 0 := by
  intro hz
  apply hresidue
  have hd := det_sub_dvd_of_coordinate_errors m A B a b ea eb hA hB
  simpa [hz] using hd

/-- The same certificate can be expressed using any actual reduction ring
homomorphism. Its existence and the coordinate identities are explicit;
unverified strings naming a coefficient field do not provide them. -/
theorem det_ne_zero_of_reduction
    {k : Type*} [CommRing k] (rho : R →+* k)
    (A B : R × R) (a b : k × k)
    (hA : (rho A.1, rho A.2) = a) (hB : (rho B.1, rho B.2) = b)
    (hresidue : det a b ≠ 0) : det A B ≠ 0 := by
  intro hz
  apply hresidue
  have heval : rho (det A B) = det a b := by
    simp only [det, map_sub, map_mul]
    change det (rho A.1, rho A.2) (rho B.1, rho B.2) = det a b
    rw [hA, hB]
  rw [← heval, hz, map_zero]

/-- Nonzero determinant excludes proportionality. -/
theorem not_proportional_of_det_ne_zero (a b : R × R)
    (h : det a b ≠ 0) : ¬ ∃ c : R, a = c • b := by
  rintro ⟨c, rfl⟩
  apply h
  simp only [det, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

/-- Nonzero determinant proves inequality of the two generated submodules. -/
theorem span_ne_span_of_det_ne_zero (a b : R × R)
    (h : det a b ≠ 0) :
    Submodule.span R {a} ≠ Submodule.span R {b} := by
  intro heq
  have ha : a ∈ Submodule.span R {b} := by
    rw [← heq]
    exact Submodule.mem_span_singleton_self a
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp ha
  exact not_proportional_of_det_ne_zero a b h ⟨c, hc.symm⟩

/-- The project's exact first-pilot finite direction residue. -/
theorem pilot_det_residue :
    det ((5 : ℤ), 21) (5, 86) % 125 = 75 := by
  norm_num [det]

/-- The determinant has exactly two factors of five. -/
theorem pilot_det_precision :
    (25 : ℤ) ∣ det ((5 : ℤ), 21) (5, 86) ∧
      ¬ (125 : ℤ) ∣ det ((5 : ℤ), 21) (5, 86) := by
  norm_num [det]

/-- A directly kernel-checkable reduction-ring form of the pilot residue. -/
theorem pilot_det_zmod_ne_zero :
    det ((5 : ZMod 125), 21) (5, 86) ≠ 0 := by
  decide +kernel

/-- The explicit pilot certificate applies to any integral coefficient ring
with a supplied reduction map and the proved coordinate reductions. -/
theorem pilot_det_ne_zero_of_reduction
    (rho : R →+* ZMod 125) (A B : R × R)
    (hA : (rho A.1, rho A.2) = (5, 21))
    (hB : (rho B.1, rho B.2) = (5, 86)) : det A B ≠ 0 := by
  exact det_ne_zero_of_reduction rho A B (5, 21) (5, 86) hA hB
    pilot_det_zmod_ne_zero

/-- The rational-coordinate pilot residue stays nonzero in every coefficient
quotient of characteristic 125, including unramified extension quotients. -/
theorem pilot_det_ne_zero_in_characteristic_125
    (k : Type*) [CommRing k] [CharP k 125] :
    det ((5 : k), 21) (5, 86) ≠ 0 := by
  have h : det ((5 : k), 21) (5, 86) = (325 : k) := by
    norm_num [det]
  rw [h]
  intro hz
  have hd : 125 ∣ 325 := (CharP.cast_eq_zero_iff k 125 325).mp hz
  norm_num at hd

/-- The explicit pilot direction test for a genuine integral coefficient
ring and its proved characteristic-125 quotient. No residue-field degree
one hypothesis is imposed. -/
theorem pilot_det_ne_zero_of_extension_reduction
    {k : Type*} [CommRing k] [CharP k 125]
    (rho : R →+* k) (A B : R × R)
    (hA : (rho A.1, rho A.2) = (5, 21))
    (hB : (rho B.1, rho B.2) = (5, 86)) : det A B ≠ 0 := by
  exact det_ne_zero_of_reduction rho A B (5, 21) (5, 86) hA hB
    (pilot_det_ne_zero_in_characteristic_125 k)

end Separation

section Regulator

variable {K : Type*} [Field K]

/-- Coefficients of the full two-coordinate regulator; using only one
coordinate would not justify the transversality test. -/
noncomputable def coeffPair (n : ℕ) (v : PowerSeries K × PowerSeries K) : K × K :=
  (PowerSeries.coeff n v.1, PowerSeries.coeff n v.2)

/-- The quadratic coefficient of a regulator divisible by `X²` is the
constant coefficient of the quotient, in both coordinates. -/
theorem coeffPair_two_X_sq_smul (v : PowerSeries K × PowerSeries K) :
    coeffPair 2 ((PowerSeries.X : PowerSeries K) ^ 2 • v) = coeffPair 0 v := by
  simp [coeffPair, smul_eq_mul, PowerSeries.coeff_X_pow_mul']

/-- Finiteness expressed by a zero regulator constant coefficient, followed
by one division parameter, supplies the two exact lower zeros. -/
theorem coeffPair_lt_two_X_smul (v : PowerSeries K × PowerSeries K)
    (hfinite : coeffPair 0 v = 0) :
    ∀ i, i < 2 → coeffPair i ((PowerSeries.X : PowerSeries K) • v) = 0 := by
  intro i hi
  rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
  · simp [coeffPair, smul_eq_mul]
  · simpa [coeffPair, smul_eq_mul] using hfinite

/-- A regular scalar row of exact order `d` forces the full regulator's
degree-`d` coefficient to be nonzero, provided its earlier coefficients vanish
exactly. Both coordinates of the row are power series, so poles are excluded. -/
theorem coeffPair_ne_zero_of_regular_row_order
    (v mu : PowerSeries K × PowerSeries K) (d : ℕ)
    (hvanish : ∀ i, i < d → coeffPair i v = 0)
    (horder : (mu.1 * v.1 + mu.2 * v.2).order = d) :
    coeffPair d v ≠ 0 := by
  intro hz
  have hcoeff : ∀ i, i < d + 1 → coeffPair i v = 0 := by
    intro i hi
    by_cases hid : i < d
    · exact hvanish i hid
    · have hieq : i = d := by omega
      simpa [hieq] using hz
  have hfst : (PowerSeries.X : PowerSeries K) ^ (d + 1) ∣ v.1 := by
    apply PowerSeries.X_pow_dvd_iff.mpr
    intro i hi
    simpa [coeffPair] using congrArg Prod.fst (hcoeff i hi)
  have hsnd : (PowerSeries.X : PowerSeries K) ^ (d + 1) ∣ v.2 := by
    apply PowerSeries.X_pow_dvd_iff.mpr
    intro i hi
    simpa [coeffPair] using congrArg Prod.snd (hcoeff i hi)
  have hrow : (PowerSeries.X : PowerSeries K) ^ (d + 1) ∣
      mu.1 * v.1 + mu.2 * v.2 :=
    dvd_add (dvd_mul_of_dvd_right hfst mu.1) (dvd_mul_of_dvd_right hsnd mu.2)
  exact (PowerSeries.order_eq_nat.mp horder).1
    (PowerSeries.X_pow_dvd_iff.mp hrow d (Nat.lt_succ_self d))

/-- An augmentation-unit factor preserves exact theta order in the specified
regular row. This supplies the nonzero full regulator coefficient independently
of the projective comparison. -/
theorem coeffPair_ne_zero_of_theta_identity
    (v mu : PowerSeries K × PowerSeries K) (theta u : PowerSeries K) (d : ℕ)
    (hvanish : ∀ i, i < d → coeffPair i v = 0)
    (hidentity : mu.1 * v.1 + mu.2 * v.2 = u * theta)
    (hu : u.constantCoeff ≠ 0) (htheta : theta.order = d) :
    coeffPair d v ≠ 0 := by
  apply coeffPair_ne_zero_of_regular_row_order v mu d hvanish
  have huorder : u.order = 0 := by
    apply PowerSeries.order_eq_nat.mpr
    refine ⟨?_, ?_⟩
    · simpa using hu
    · intro i hi
      omega
  rw [hidentity, PowerSeries.order_mul, huorder, htheta, zero_add]

/-- Equality of two nonzero leading directions transfers separation from the
exceptional line. This is the final coefficient-level consequence required
from the full analytic projective comparison. -/
theorem det_ne_zero_of_projective_comparison
    (v a zeta : K × K) (hv : v ≠ 0)
    (hcompare : det v a = 0) (hsep : det a zeta ≠ 0) :
    det v zeta ≠ 0 := by
  intro hz
  have h1 : v.1 * det a zeta = 0 := by
    calc
      v.1 * det a zeta = a.1 * det v zeta - zeta.1 * det v a := by
        simp only [det]
        ring
      _ = 0 := by rw [hz, hcompare]; ring
  have h2 : v.2 * det a zeta = 0 := by
    calc
      v.2 * det a zeta = a.2 * det v zeta - zeta.2 * det v a := by
        simp only [det]
        ring
      _ = 0 := by rw [hz, hcompare]; ring
  apply hv
  apply Prod.ext
  · exact (mul_eq_zero.mp h1).resolve_right hsep
  · exact (mul_eq_zero.mp h2).resolve_right hsep

variable {M H : Type*} [AddCommGroup M] [Module (PowerSeries K) M] [Zero H]

/-- The algebraic core of quadratic transversality. If specialization zero
permits division by `X`, and the regulator's base image lies on the exceptional
line, a transverse quadratic coefficient of `P(X*x)` forces `sp(x) ≠ 0`.
The division property and base-image statement are explicit arithmetic inputs.
No freeness of `M` or determinant-order assertion is used. -/
theorem specialization_ne_zero_of_quadratic_separation
    (sp : M → H) (P : M →ₗ[PowerSeries K] (PowerSeries K × PowerSeries K))
    (zeta : K × K)
    (hdivision : ∀ w : M, sp w = 0 → ∃ u : M, w = (PowerSeries.X : PowerSeries K) • u)
    (hbase : ∀ w : M, det (coeffPair 0 (P w)) zeta = 0)
    (x y : M) (hy : y = (PowerSeries.X : PowerSeries K) • x)
    (hsep : det (coeffPair 2 (P y)) zeta ≠ 0) : sp x ≠ 0 := by
  intro hx
  obtain ⟨w, hw⟩ := hdivision x hx
  have hy2 : y = (PowerSeries.X : PowerSeries K) ^ 2 • w := by
    rw [hy, hw, ← mul_smul, pow_two]
  apply hsep
  rw [hy2, map_smul, coeffPair_two_X_sq_smul]
  exact hbase w

/-- A leading comparison and a nonzero true regulator coefficient feed into
the core transversality theorem. The nonzero coefficient must come from a
separate exact-order result; it is not inferred from projective comparison. -/
theorem specialization_ne_zero_of_leading_comparison
    (sp : M → H) (P : M →ₗ[PowerSeries K] (PowerSeries K × PowerSeries K))
    (a zeta : K × K)
    (hdivision : ∀ w : M, sp w = 0 → ∃ u : M, w = (PowerSeries.X : PowerSeries K) • u)
    (hbase : ∀ w : M, det (coeffPair 0 (P w)) zeta = 0)
    (x y : M) (hy : y = (PowerSeries.X : PowerSeries K) • x)
    (hlead : coeffPair 2 (P y) ≠ 0)
    (hcompare : det (coeffPair 2 (P y)) a = 0)
    (hsep : det a zeta ≠ 0) : sp x ≠ 0 := by
  apply specialization_ne_zero_of_quadratic_separation sp P zeta hdivision hbase x y hy
  exact det_ne_zero_of_projective_comparison _ a zeta hlead hcompare hsep

/-- An injective finite logarithm transfers nonzero specialization to nonzero
logarithm. Here `H` is the finite local space; injectivity on an arithmetic
global Selmer group is neither required nor asserted. -/
theorem logarithm_ne_zero_of_quadratic_separation
    {L : Type*} [Zero L]
    (sp : M → H) (ell : H → L) (hell : Function.Injective ell) (hell0 : ell 0 = 0)
    (P : M →ₗ[PowerSeries K] (PowerSeries K × PowerSeries K))
    (zeta : K × K)
    (hdivision : ∀ w : M, sp w = 0 → ∃ u : M, w = (PowerSeries.X : PowerSeries K) • u)
    (hbase : ∀ w : M, det (coeffPair 0 (P w)) zeta = 0)
    (x y : M) (hy : y = (PowerSeries.X : PowerSeries K) • x)
    (hsep : det (coeffPair 2 (P y)) zeta ≠ 0) : ell (sp x) ≠ 0 := by
  intro hz
  apply specialization_ne_zero_of_quadratic_separation sp P zeta hdivision hbase x y hy hsep
  apply hell
  exact hz.trans hell0.symm

/-- The formal local theorem combining the theta identity, its exact order,
the leading projective comparison, and transversality. All identities refer to
the same full regulator `P` and class `y = X*x`. Arithmetic construction of
these data and the comparison identities are explicit remaining obligations. -/
theorem logarithm_ne_zero_of_theta_and_leading_comparison
    {L : Type*} [Zero L]
    (sp : M → H) (ell : H → L) (hell : Function.Injective ell) (hell0 : ell 0 = 0)
    (P : M →ₗ[PowerSeries K] (PowerSeries K × PowerSeries K))
    (a zeta : K × K)
    (hdivision : ∀ w : M, sp w = 0 → ∃ u : M, w = (PowerSeries.X : PowerSeries K) • u)
    (hbase : ∀ w : M, det (coeffPair 0 (P w)) zeta = 0)
    (x y : M) (hy : y = (PowerSeries.X : PowerSeries K) • x)
    (hfinite : coeffPair 0 (P x) = 0)
    (mu : PowerSeries K × PowerSeries K) (theta u : PowerSeries K)
    (hidentity : mu.1 * (P y).1 + mu.2 * (P y).2 = u * theta)
    (hu : u.constantCoeff ≠ 0) (htheta : theta.order = 2)
    (hcompare : det (coeffPair 2 (P y)) a = 0)
    (hsep : det a zeta ≠ 0) : ell (sp x) ≠ 0 := by
  have hvanish : ∀ i, i < 2 → coeffPair i (P y) = 0 := by
    rw [hy, map_smul]
    exact coeffPair_lt_two_X_smul (P x) hfinite
  have hlead : coeffPair 2 (P y) ≠ 0 :=
    coeffPair_ne_zero_of_theta_identity (P y) mu theta u 2 hvanish hidentity hu htheta
  apply logarithm_ne_zero_of_quadratic_separation sp ell hell hell0 P zeta
    hdivision hbase x y hy
  exact det_ne_zero_of_projective_comparison _ a zeta hlead hcompare hsep

end Regulator

section Dimension

variable {K S : Type*} [Field K] [AddCommGroup S] [Module K S]
  [FiniteDimensional K S]

/-- Two independent vectors in a subspace of an ambient space of dimension at
most two exhaust the ambient space. This is the linear algebra used after
rational-point independence and the Selmer bound have both been established. -/
theorem subspace_eq_top_of_two_independent
    (M : Submodule K S) (v : Fin 2 → M)
    (hv : LinearIndependent K v) (hbound : Module.finrank K S ≤ 2) :
    M = ⊤ ∧ Module.finrank K M = 2 ∧ Module.finrank K S = 2 := by
  have hlower : 2 ≤ Module.finrank K M := by
    simpa using hv.fintype_card_le_finrank
  have hsub : Module.finrank K M ≤ Module.finrank K S := M.finrank_le
  have hM : Module.finrank K M = 2 := by omega
  have hS : Module.finrank K S = 2 := by omega
  exact ⟨Submodule.eq_top_of_finrank_eq (hM.trans hS.symm), hM, hS⟩

omit [FiniteDimensional K S] in
/-- A nonzero strict vector and a vector with nonzero localization are
independent. The strict vector and the localization witness are different
inputs; neither can replace the other. -/
theorem strict_and_localized_independent
    (ell : S →ₗ[K] K) (k x : S)
    (hk : k ≠ 0) (hk0 : ell k = 0) (hx : ell x ≠ 0) :
    LinearIndependent K ![x, k] := by
  rw [linearIndependent_fin2]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  refine ⟨hk, ?_⟩
  intro a ha
  apply hx
  have he := congrArg ell ha
  simpa [hk0] using he.symm

/-- Once a nonzero strict class and an independent localization witness both
lie in the proposed Kummer subspace, a two-dimensional ambient bound exhausts
that subspace. Membership is an explicit hypothesis, not a conclusion of a
finite theta calculation. -/
theorem subspace_eq_top_of_strict_and_localized
    (M : Submodule K S) (ell : S →ₗ[K] K) (k x : M)
    (hk : k ≠ 0) (hk0 : ell (k : S) = 0) (hx : ell (x : S) ≠ 0)
    (hbound : Module.finrank K S ≤ 2) :
    M = ⊤ ∧ Module.finrank K M = 2 ∧ Module.finrank K S = 2 := by
  apply subspace_eq_top_of_two_independent M ![x, k] ?_ hbound
  exact strict_and_localized_independent (ell.comp M.subtype) k x hk hk0 hx

/-- A second form of the strict-Kummer implication: one nonzero strict class
suffices if localization on the proposed Kummer subspace is known to be
injective whenever that subspace has dimension one. The latter is the separate
arithmetic logarithm input; it is not inferred from the Selmer dimension. -/
theorem subspace_eq_top_of_strict_and_rank_one_injectivity
    (M : Submodule K S) (ell : S →ₗ[K] K) (k : M)
    (hk : k ≠ 0) (hk0 : ell (k : S) = 0)
    (hline : Module.finrank K M = 1 → Function.Injective (ell.comp M.subtype))
    (hbound : Module.finrank K S ≤ 2) :
    M = ⊤ ∧ Module.finrank K M = 2 ∧ Module.finrank K S = 2 := by
  have hnotzero : Module.finrank K M ≠ 0 := by
    intro hz
    have : Subsingleton M := (Module.finrank_zero_iff (R := K)).mp hz
    exact hk (Subsingleton.elim k 0)
  have hnotone : Module.finrank K M ≠ 1 := by
    intro hone
    apply hk
    apply hline hone
    simpa using hk0
  have hsub : Module.finrank K M ≤ Module.finrank K S := M.finrank_le
  have hM : Module.finrank K M = 2 := by omega
  have hS : Module.finrank K S = 2 := by omega
  exact ⟨Submodule.eq_top_of_finrank_eq (hM.trans hS.symm), hM, hS⟩

/-- If a surjective quotient map has kernel equal to the proposed Kummer
subspace, the preceding dimension certificate forces its target to be zero.
Identifying this target with the rational Tate module of Sha is an additional
arithmetic obligation. -/
theorem quotient_zero_of_two_independent
    {A : Type*} [AddCommGroup A] [Module K A]
    (M : Submodule K S) (v : Fin 2 → M)
    (hv : LinearIndependent K v) (hbound : Module.finrank K S ≤ 2)
    (q : S →ₗ[K] A) (hker : q.ker = M) (hq : Function.Surjective q) :
    ∀ a : A, a = 0 := by
  have hM := (subspace_eq_top_of_two_independent M v hv hbound).1
  intro a
  obtain ⟨s, rfl⟩ := hq a
  have hs : s ∈ q.ker := by rw [hker, hM]; trivial
  exact hs

end Dimension

end BSDLocalization
