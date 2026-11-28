import BSDThetaCertificate
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Ring.GeomSum

/-!
# Construction from compatible finite theta representatives

The input is a tower of finite polynomials with the actual cyclic quotient
compatibility. Completeness of the 5-adic integers constructs the infinite
series coefficient by coefficient. No infinite series or approximation
identity is supplied as an input. Arithmetic construction of the finite
family and its distribution relation remains an explicit obligation.
-/

namespace BSDThetaLimit

open PowerSeries

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- Representatives in the variable `T = gamma - 1`, indexed so that level
`n` has cyclic quotient order `5^n`. Thus ring class conductor 25 contributes
at index one in the pilot. -/
def Compatible (G : ℕ → Polynomial ℤ_[5]) : Prop :=
  ∀ m n, m ≤ n → BSDRankTwo.omegaPoly (R := ℤ_[5]) 5 m ∣ G n - G m

/-- Cyclic compatibility forces the coefficient precision given by the
prime-power binomial bound, including the precision loss at high degrees. -/
theorem compatible_coeff_dvd {G : ℕ → Polynomial ℤ_[5]} (hG : Compatible G)
    {m n a s k : ℕ} (hmn : m ≤ n) (hlevel : a + s ≤ m)
    (hk : k < 5 ^ (s + 1)) :
    (5 : ℤ_[5]) ^ a ∣ (G n).coeff k - (G m).coeff k := by
  obtain ⟨Q, hQ⟩ := hG m n hmn
  have h : ((G n - G m : Polynomial ℤ_[5]) : PowerSeries ℤ_[5]) =
      (BSDRankTwo.omegaPoly (R := ℤ_[5]) 5 m : PowerSeries ℤ_[5]) * (Q : PowerSeries ℤ_[5]) := by
    exact_mod_cast hQ
  have hd := BSDRankTwo.coeff_mul_dvd
    (BSDRankTwo.omegaPoly (R := ℤ_[5]) 5 m : PowerSeries ℤ_[5]) (Q : PowerSeries ℤ_[5])
    ((5 : ℤ_[5]) ^ a) k (by
      intro i hi
      simpa using BSDRankTwo.omega_coeff_dvd (R := ℤ_[5]) (p := 5)
        (n := m) (m := a) (s := s) (k := i) (by decide) hlevel (by omega))
  rw [← h] at hd
  simpa using hd

/-- The diagonal shift of the coefficient index supplies an ordinary
5-adic Cauchy sequence at each degree. -/
theorem shifted_coeff_cauchy {G : ℕ → Polynomial ℤ_[5]} (hG : Compatible G)
    (k : ℕ) :
    ∀ {m n : ℕ}, m ≤ n →
      (5 : ℤ_[5]) ^ m ∣ (G (n + k)).coeff k - (G (m + k)).coeff k := by
  intro m n hmn
  apply compatible_coeff_dvd hG (Nat.add_le_add_right hmn k) (le_refl _)
  exact lt_of_lt_of_le (Nat.lt_pow_self (n := k) (by decide : 1 < 5))
    (Nat.pow_le_pow_right (by decide) (Nat.le_succ k))

/-- Every coefficient is produced by completeness of the actual 5-adic
integers, with certified precision relative to the finite representatives. -/
theorem exists_coefficient_limit {G : ℕ → Polynomial ℤ_[5]}
    (hG : Compatible G) (k : ℕ) :
    ∃ a : ℤ_[5], ∀ m : ℕ,
      (5 : ℤ_[5]) ^ m ∣ a - (G (m + k)).coeff k := by
  let I : Ideal ℤ_[5] := IsLocalRing.maximalIdeal ℤ_[5]
  have hs : ∀ {m n : ℕ}, m ≤ n →
      (G (m + k)).coeff k ≡ (G (n + k)).coeff k
        [SMOD (I ^ m • ⊤ : Submodule ℤ_[5] ℤ_[5])] := by
    intro m n hmn
    simpa only [I, ← Ideal.one_eq_top, smul_eq_mul, mul_one, SModEq.sub_mem,
      PadicInt.maximalIdeal_eq_span_p, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton, Nat.cast_ofNat] using
      (dvd_sub_comm.mp (shifted_coeff_cauchy hG k hmn))
  obtain ⟨a, ha⟩ := IsPrecomplete.prec (I := I) (M := ℤ_[5]) inferInstance hs
  refine ⟨a, fun m => ?_⟩
  apply dvd_sub_comm.mp
  simpa only [I, ← Ideal.one_eq_top, smul_eq_mul, mul_one, SModEq.sub_mem,
    PadicInt.maximalIdeal_eq_span_p, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton, Nat.cast_ofNat] using ha m

/-- The infinite series constructed from the compatible finite family. -/
noncomputable def thetaLimit (G : ℕ → Polynomial ℤ_[5]) (hG : Compatible G) :
    PowerSeries ℤ_[5] :=
  PowerSeries.mk fun k => Classical.choose (exists_coefficient_limit hG k)

/-- The constructed series has the promised precision at every degree. -/
theorem thetaLimit_coeff_dvd (G : ℕ → Polynomial ℤ_[5]) (hG : Compatible G)
    (m k : ℕ) :
    (5 : ℤ_[5]) ^ m ∣ PowerSeries.coeff k (thetaLimit G hG) - (G (m + k)).coeff k := by
  simpa only [thetaLimit, PowerSeries.coeff_mk] using
    Classical.choose_spec (exists_coefficient_limit hG k) m

/-- Any finite level supplies the full certified coefficient window of the
constructed limit, not just the diagonal sequence used in its definition. -/
theorem thetaLimit_coeff_precision (G : ℕ → Polynomial ℤ_[5]) (hG : Compatible G)
    {n a s k : ℕ} (hlevel : a + s ≤ n) (hk : k < 5 ^ (s + 1)) :
    (5 : ℤ_[5]) ^ a ∣ PowerSeries.coeff k (thetaLimit G hG) - (G n).coeff k := by
  let b := max a n
  have hab : a ≤ b := le_max_left _ _
  have hnb : n ≤ b + k := (le_max_right _ _).trans (Nat.le_add_right _ _)
  have hlim : (5 : ℤ_[5]) ^ a ∣
      PowerSeries.coeff k (thetaLimit G hG) - (G (b + k)).coeff k :=
    dvd_trans (pow_dvd_pow (5 : ℤ_[5]) hab) (thetaLimit_coeff_dvd G hG b k)
  have hfinite := compatible_coeff_dvd hG hnb hlevel hk
  simpa using dvd_add hlim hfinite

/-- Divisibility by every power of five detects equality in the actual
5-adic integers. -/
theorem eq_of_forall_pow_dvd_sub (x y : ℤ_[5])
    (h : ∀ n : ℕ, (5 : ℤ_[5]) ^ n ∣ x - y) : x = y := by
  apply (IsHausdorff.eq_iff_smodEq
    (I := IsLocalRing.maximalIdeal ℤ_[5]) (M := ℤ_[5])).2
  intro n
  simpa only [← Ideal.one_eq_top, smul_eq_mul, mul_one, SModEq.sub_mem,
    PadicInt.maximalIdeal_eq_span_p, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton, Nat.cast_ofNat] using h n

/-- The constructed limit is unique among series with these finite-level
coefficient approximations. -/
theorem thetaLimit_unique (G : ℕ → Polynomial ℤ_[5]) (hG : Compatible G)
    (F : PowerSeries ℤ_[5])
    (hF : ∀ m k : ℕ, (5 : ℤ_[5]) ^ m ∣
      PowerSeries.coeff k F - (G (m + k)).coeff k) :
    F = thetaLimit G hG := by
  apply PowerSeries.ext
  intro k
  apply eq_of_forall_pow_dvd_sub
  intro m
  simpa using dvd_sub (hF m k) (thetaLimit_coeff_dvd G hG m k)

/-- Cyclic compatibility includes the augmentation map at level zero. -/
theorem compatible_constantCoeff_eq {G : ℕ → Polynomial ℤ_[5]}
    (hG : Compatible G) (n : ℕ) : (G n).coeff 0 = (G 0).coeff 0 := by
  obtain ⟨Q, hQ⟩ := hG 0 n (Nat.zero_le _)
  have h := congrArg (fun P : Polynomial ℤ_[5] => P.coeff 0) hQ
  apply sub_eq_zero.mp
  simpa [BSDRankTwo.omegaPoly, Polynomial.coeff_mul] using h

/-- The augmentation of the constructed limit equals the level-zero
augmentation exactly. -/
theorem thetaLimit_constantCoeff (G : ℕ → Polynomial ℤ_[5])
    (hG : Compatible G) : (thetaLimit G hG).constantCoeff = (G 0).coeff 0 := by
  apply eq_of_forall_pow_dvd_sub
  intro m
  have h := thetaLimit_coeff_dvd G hG m 0
  simpa [compatible_constantCoeff_eq hG] using h

/-- Exact vanishing of the finite augmentations transfers to the constructed
infinite series. This is an exact equality, not a finite-precision test. -/
theorem thetaLimit_constantCoeff_zero (G : ℕ → Polynomial ℤ_[5])
    (hG : Compatible G) (hzero : ∀ n, (G n).coeff 0 = 0) :
    (thetaLimit G hG).constantCoeff = 0 := by
  apply eq_of_forall_pow_dvd_sub
  intro m
  simpa [hzero] using thetaLimit_coeff_dvd G hG m 0

/-- A finite coefficient congruence is converted into an actual integral
power-series decomposition, with both multipliers constructed in the same
coefficient ring. -/
theorem exists_omega_five_decomposition {R : Type*} [CommRing R]
    (D : PowerSeries R)
    (hD : ∀ k : ℕ, k < 5 → (5 : R) ∣ PowerSeries.coeff k D) :
    ∃ H J : PowerSeries R,
      D = (BSDRankTwo.omegaPoly (R := R) 5 1 : PowerSeries R) * H +
        PowerSeries.C (5 : R) * J := by
  classical
  let J : PowerSeries R := PowerSeries.mk fun k =>
    if hk : k < 5 then Classical.choose (hD k hk) else 0
  have hd : (PowerSeries.X : PowerSeries R) ^ 5 ∣ D - PowerSeries.C 5 * J := by
    apply PowerSeries.X_pow_dvd_iff.2
    intro k hk
    simp only [map_sub, PowerSeries.coeff_C_mul, J, PowerSeries.coeff_mk, dite_eq_left hk]
    exact sub_eq_zero.mpr (Classical.choose_spec (hD k hk))
  obtain ⟨H, hH⟩ := hd
  let K : PowerSeries R := PowerSeries.X + 2 * PowerSeries.X ^ 2 +
    2 * PowerSeries.X ^ 3 + PowerSeries.X ^ 4
  have homega : (BSDRankTwo.omegaPoly (R := R) 5 1 : PowerSeries R) =
      PowerSeries.X ^ 5 + PowerSeries.C (5 : R) * K := by
    simp only [BSDRankTwo.omegaPoly, Nat.pow_one, Polynomial.coe_sub,
      Polynomial.coe_pow, Polynomial.coe_add, Polynomial.coe_one, Polynomial.coe_X]
    simp only [map_ofNat, K]
    ring
  refine ⟨H, J - K * H, ?_⟩
  rw [homega]
  calc
    D = PowerSeries.X ^ 5 * H + PowerSeries.C 5 * J := by
      linear_combination hH
    _ = (PowerSeries.X ^ 5 + PowerSeries.C (5 : R) * K) * H +
        PowerSeries.C (5 : R) * (J - K * H) := by ring

/-- The original finite-approximation hypothesis is now a conclusion from
finite cyclic compatibility and 5-adic completeness. -/
theorem thetaLimit_finite_approximation (G : ℕ → Polynomial ℤ_[5])
    (hG : Compatible G) :
    ∃ H J : PowerSeries ℤ_[5],
      thetaLimit G hG - (G 1 : PowerSeries ℤ_[5]) =
        (BSDRankTwo.omegaPoly (R := ℤ_[5]) 5 1 : PowerSeries ℤ_[5]) * H +
          PowerSeries.C (5 : ℤ_[5]) * J := by
  apply exists_omega_five_decomposition
  intro k hk
  simpa using thetaLimit_coeff_precision G hG (n := 1) (a := 1)
    (s := 0) (k := k) (by decide) (by simpa using hk)

/-- The constructed limit satisfies the complete E433 order/unit
certificate once the first finite representative and exact symmetry are
identified arithmetically. No infinite approximation identity is assumed. -/
theorem thetaLimit_five_adic_certificate
    (G : ℕ → Polynomial ℤ_[5]) (hG : Compatible G)
    (U : PowerSeries ℤ_[5]) (u c : ℤ_[5])
    (hfirst : (G 1 : PowerSeries ℤ_[5]) = BSDThetaCertificate.regularized433 u c)
    (hzero : (thetaLimit G hG).constantCoeff = 0)
    (hU : U.constantCoeff = 1)
    (hsym : thetaLimit G hG = U * (thetaLimit G hG).subst
      (BSDRankTwo.inversionSeries (R := ℤ_[5])))
    (hu : IsUnit u) :
    (thetaLimit G hG).order = 2 ∧
      ∃ V : PowerSeries ℤ_[5], thetaLimit G hG = PowerSeries.X ^ 2 * V ∧
        IsUnit V.constantCoeff := by
  obtain ⟨H, J, happrox⟩ := thetaLimit_finite_approximation G hG
  rw [hfirst] at happrox
  exact BSDThetaCertificate.five_adic_certificate
    (thetaLimit G hG) U H J u c hzero hU hsym hu happrox

/-- Polynomial representative of inversion in the finite cyclic quotient.
Unlike formal inversion, this is a finite polynomial at every level. -/
noncomputable def cyclicInverse (n : ℕ) : Polynomial ℤ_[5] :=
  (1 + Polynomial.X) ^ (5 ^ n - 1) - 1

/-- Finite quotient symmetry, stated entirely as polynomial identities.
The multiplier may depend on the level and represents the cycle-origin
translation. Its augmentation is one. -/
def FiniteSymmetric (G : ℕ → Polynomial ℤ_[5]) : Prop :=
  ∀ n, ∃ U : Polynomial ℤ_[5], U.coeff 0 = 1 ∧
    BSDRankTwo.omegaPoly (R := ℤ_[5]) 5 n ∣ G n - U * (G n).comp (cyclicInverse n)

/-- The finite inverse has zero constant coefficient. -/
theorem cyclicInverse_coeff_zero (n : ℕ) : (cyclicInverse n).coeff 0 = 0 := by
  simp [cyclicInverse, Polynomial.coeff_one_add_X_pow]

/-- Its linear coefficient is the integer `5^n - 1`. -/
theorem cyclicInverse_coeff_one (n : ℕ) :
    (cyclicInverse n).coeff 1 = (5 : ℤ_[5]) ^ n - 1 := by
  have hp : 1 ≤ 5 ^ n := Nat.one_le_pow n 5 (by decide)
  simp [cyclicInverse, Polynomial.coeff_one_add_X_pow, Polynomial.coeff_one, Nat.cast_sub hp]

/-- Linear composition with zero constant coefficient has the chain-rule
formula, proved here for actual finite polynomials. -/
theorem coeff_one_comp_of_coeff_zero {R : Type*} [CommRing R]
    (P Q : Polynomial R) (hQ : Q.coeff 0 = 0) :
    (P.comp Q).coeff 1 = P.coeff 1 * Q.coeff 1 := by
  calc
    (P.comp Q).coeff 1 = (P.comp Q).derivative.eval 0 := by
      simp [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_derivative]
    _ = P.derivative.eval (Q.eval 0) * Q.derivative.eval 0 := by
      simp [Polynomial.derivative_comp, mul_comm]
    _ = P.coeff 1 * Q.coeff 1 := by
      simp [← Polynomial.coeff_zero_eq_eval_zero, hQ, Polynomial.coeff_derivative]

/-- The linear coefficient of every cyclic relation at level n is divisible
by `5^n`, including after multiplication by an arbitrary polynomial. -/
theorem omega_dvd_linear {n : ℕ} {D : Polynomial ℤ_[5]}
    (hD : BSDRankTwo.omegaPoly (R := ℤ_[5]) 5 n ∣ D) :
    (5 : ℤ_[5]) ^ n ∣ D.coeff 1 := by
  obtain ⟨Q, rfl⟩ := hD
  rw [Polynomial.coeff_mul]
  apply Finset.dvd_sum
  intro ij hij
  have hs := Finset.mem_antidiagonal.mp hij
  have hd := BSDRankTwo.omega_coeff_dvd (R := ℤ_[5]) (p := 5)
    (n := n) (m := n) (s := 0) (k := ij.1) (by decide) (by omega) (by
      norm_num
      omega)
  exact dvd_mul_of_dvd_left (by simpa using hd) _

/-- Finite inversion symmetry forces twice the finite linear coefficient
to vanish to the full level precision, once the finite augmentation is zero. -/
theorem finiteSymmetric_linear_dvd {G : ℕ → Polynomial ℤ_[5]}
    (hG : Compatible G) (hsym : FiniteSymmetric G)
    (hzero : (G 0).coeff 0 = 0) (n : ℕ) :
    (5 : ℤ_[5]) ^ n ∣ (G n).coeff 1 + (G n).coeff 1 := by
  obtain ⟨U, hU, hdiv⟩ := hsym n
  have hz : (G n).coeff 0 = 0 := (compatible_constantCoeff_eq hG n).trans hzero
  have hcomp0 : ((G n).comp (cyclicInverse n)).coeff 0 = 0 := by
    rw [Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_comp,
      ← Polynomial.coeff_zero_eq_eval_zero, cyclicInverse_coeff_zero,
      ← Polynomial.coeff_zero_eq_eval_zero]
    exact hz
  have hcomp1 := coeff_one_comp_of_coeff_zero (G n) (cyclicInverse n)
    (cyclicInverse_coeff_zero n)
  rw [cyclicInverse_coeff_one] at hcomp1
  have hd := omega_dvd_linear hdiv
  rw [Polynomial.coeff_sub, Polynomial.mul_coeff_one] at hd
  simp only [hcomp0, hcomp1, hU, one_mul, mul_zero, add_zero] at hd
  have heq : (G n).coeff 1 - (G n).coeff 1 * ((5 : ℤ_[5]) ^ n - 1) +
      (5 : ℤ_[5]) ^ n * (G n).coeff 1 = (G n).coeff 1 + (G n).coeff 1 := by ring
  rw [← heq]
  exact dvd_add hd (dvd_mul_right _ _)

/-- Exact linear vanishing for the constructed infinite series is derived
from the finite polynomial symmetries at all levels. -/
theorem thetaLimit_coeff_one_zero (G : ℕ → Polynomial ℤ_[5])
    (hG : Compatible G) (hsym : FiniteSymmetric G)
    (hzero : (G 0).coeff 0 = 0) :
    PowerSeries.coeff 1 (thetaLimit G hG) = 0 := by
  apply add_self_eq_zero.mp
  apply eq_of_forall_pow_dvd_sub
  intro n
  have hl := thetaLimit_coeff_precision G hG (n := n) (a := n)
    (s := 0) (k := 1) (by omega) (by decide)
  have hf := finiteSymmetric_linear_dvd hG hsym hzero n
  have h := dvd_add (dvd_add hl hl) hf
  simpa only [sub_zero] using (show (5 : ℤ_[5]) ^ n ∣
    PowerSeries.coeff 1 (thetaLimit G hG) + PowerSeries.coeff 1 (thetaLimit G hG) by
      convert h using 1; ring)

/-- A certificate entirely in terms of a compatible finite tower, its
finite inversion symmetries, its level-zero augmentation and exact first-level
value. The infinite theta series is constructed, and both low-order exact
zeros and the integral approximation identity are proved. Exact compatibility
and zero augmentation force `c = 0` under this exact first-level equality;
see `trace_scale_zero_of_exact_first_level`. The more flexible
`finite_tower_certificate_mod_five` permits arbitrary trace scale. -/
theorem finite_tower_certificate
    (G : ℕ → Polynomial ℤ_[5]) (hG : Compatible G)
    (hsym : FiniteSymmetric G) (hzero : (G 0).coeff 0 = 0)
    (u c : ℤ_[5]) (hu : IsUnit u)
    (hfirst : (G 1 : PowerSeries ℤ_[5]) = BSDThetaCertificate.regularized433 u c) :
    (thetaLimit G hG).order = 2 ∧
      ∃ V : PowerSeries ℤ_[5], thetaLimit G hG = PowerSeries.X ^ 2 * V ∧
        IsUnit V.constantCoeff := by
  obtain ⟨H, J, happrox⟩ := thetaLimit_finite_approximation G hG
  rw [hfirst] at happrox
  have hF0 : (thetaLimit G hG).constantCoeff = 0 :=
    (thetaLimit_constantCoeff G hG).trans hzero
  have hF1 := thetaLimit_coeff_one_zero G hG hsym hzero
  have hdiv : (PowerSeries.X : PowerSeries ℤ_[5]) ^ 2 ∣ thetaLimit G hG := by
    apply PowerSeries.X_pow_dvd_iff.2
    intro k hk
    rcases (show k = 0 ∨ k = 1 by omega) with rfl | rfl
    · simpa using hF0
    · exact hF1
  have h5 : ¬ IsUnit (5 : ℤ_[5]) := PadicInt.irreducible_p.not_isUnit
  constructor
  · exact BSDRankTwo.exact_order_two_of_certificate
      (p := 5) (n := 1) (m := 1) (by decide) (by decide) (by omega)
      (thetaLimit G hG) (BSDThetaCertificate.regularized433 u c) H J
      (by simpa using happrox) hdiv
      (by simpa using (BSDThetaCertificate.regularized433_quadratic_nondivisible_of_unit
        u c h5 hu))
  · obtain ⟨V, hV⟩ := hdiv
    refine ⟨V, hV, ?_⟩
    have hunit := BSDThetaCertificate.quadratic_unit_of_regularized433
      (thetaLimit G hG) H J u c h5 hu happrox
    rw [hV] at hunit
    have hcoeff : PowerSeries.coeff 2 (PowerSeries.X ^ 2 * V) = V.constantCoeff := by
      simpa using PowerSeries.coeff_X_pow_mul V 2 0
    rwa [hcoeff] at hunit

/-- Cyclic quotient relations divide each other along the tower. -/
theorem omega_dvd_omega {m n : ℕ} (hmn : m ≤ n) :
    BSDRankTwo.omegaPoly (R := ℤ_[5]) 5 m ∣
      BSDRankTwo.omegaPoly (R := ℤ_[5]) 5 n := by
  exact dvd_pow_sub_one_of_dvd (pow_dvd_pow 5 hmn)

/-- It suffices to prove the arithmetic distribution relation between
successive finite levels. All-pairs compatibility follows by induction. -/
theorem compatible_of_successive (G : ℕ → Polynomial ℤ_[5])
    (hG : ∀ n, BSDRankTwo.omegaPoly (R := ℤ_[5]) 5 n ∣ G (n + 1) - G n) :
    Compatible G := by
  intro m n hmn
  induction n, hmn using Nat.le_induction with
  | base => simp
  | succ n hmn ih =>
      have hstep := dvd_trans (omega_dvd_omega hmn) (hG n)
      simpa using dvd_add hstep ih

/-- A constant representative family is compatible. This useful control
case also checks that the inverse-limit construction fixes polynomials. -/
theorem constant_compatible (P : Polynomial ℤ_[5]) : Compatible (fun _ => P) := by
  intro m n hmn
  simp

/-- The construction agrees with an actual polynomial on a constant tower. -/
theorem thetaLimit_constant (P : Polynomial ℤ_[5]) :
    thetaLimit (fun _ => P) (constant_compatible P) = (P : PowerSeries ℤ_[5]) := by
  symm
  apply thetaLimit_unique
  intro m k
  simp

/-- A finite polynomial witness for the raw cycle-origin multiplier.
The proof is an identity modulo each finite cyclic relation, not an assumed
infinite functional equation. -/
theorem raw_finite_symmetric :
    FiniteSymmetric (fun _ => (Polynomial.X ^ 2 + Polynomial.X ^ 3 : Polynomial ℤ_[5])) := by
  intro n
  let g : Polynomial ℤ_[5] := 1 + Polynomial.X
  let b : Polynomial ℤ_[5] := g ^ (5 ^ n - 1)
  refine ⟨g ^ 4, ?_, ?_⟩
  · simp [g, Polynomial.coeff_zero_eq_eval_zero]
  have hpow : g ^ (5 ^ n) = g * b := by
    dsimp [b]
    rw [← pow_succ']
    congr 1
    have hpos : 0 < 5 ^ n := pow_pos (by decide) _
    omega
  have homega : BSDRankTwo.omegaPoly (R := ℤ_[5]) 5 n = g * b - 1 := by
    change g ^ (5 ^ n) - 1 = g * b - 1
    rw [hpow]
  have hcomp : (Polynomial.X ^ 2 + Polynomial.X ^ 3 : Polynomial ℤ_[5]).comp
      (cyclicInverse n) = b * (b - 1) ^ 2 := by
    simp only [Polynomial.add_comp, Polynomial.pow_comp, Polynomial.X_comp]
    change (b - 1) ^ 2 + (b - 1) ^ 3 = b * (b - 1) ^ 2
    ring
  have hraw : (Polynomial.X ^ 2 + Polynomial.X ^ 3 : Polynomial ℤ_[5]) =
      g * (g - 1) ^ 2 := by dsimp [g]; ring
  rw [hcomp, hraw, homega]
  refine ⟨-g * (g * b) ^ 2 + (2 * g ^ 2 - g) * (g * b) +
    (-g ^ 3 + 2 * g ^ 2 - g), ?_⟩
  ring

/-- The complete finite-tower assumptions have an explicit joint witness.
This is a control example; arithmetic identification of the CM tower is a
separate theorem, not supplied by this example. -/
theorem raw_finite_tower_inputs :
    let G : ℕ → Polynomial ℤ_[5] := fun _ => Polynomial.X ^ 2 + Polynomial.X ^ 3
    Compatible G ∧ FiniteSymmetric G ∧ (G 0).coeff 0 = 0 ∧
      (G 1 : PowerSeries ℤ_[5]) = BSDThetaCertificate.regularized433 1 0 := by
  dsimp only
  refine ⟨constant_compatible _, raw_finite_symmetric, ?_, ?_⟩
  · simp
  · simp [BSDThetaCertificate.regularized433, BSDThetaCertificate.finite433_shift]

/-- Exact tower compatibility and zero augmentation force the trace scale
to vanish if the first-level regularization is identified exactly. This
makes explicit the restriction implicit in `finite_tower_certificate`. -/
theorem trace_scale_zero_of_exact_first_level
    (G : ℕ → Polynomial ℤ_[5]) (hG : Compatible G)
    (hzero : (G 0).coeff 0 = 0) (u c : ℤ_[5])
    (hfirst : (G 1 : PowerSeries ℤ_[5]) = BSDThetaCertificate.regularized433 u c) :
    c = 0 := by
  have hz : (BSDThetaCertificate.regularized433 u c).constantCoeff = 0 := by
    rw [← hfirst]
    simpa using (compatible_constantCoeff_eq hG 1).trans hzero
  have hc : (5 : ℤ_[5]) * c = 0 := by
    simpa [BSDThetaCertificate.regularized433, BSDThetaCertificate.finite433_shift,
      BSDThetaCertificate.normFive_shift, map_ofNat, mul_comm] using hz
  exact (mul_eq_zero.mp hc).resolve_left (by norm_num)

/-- A finite coefficient congruence supplies the integral approximation
needed by the certificate. The trace scale can be arbitrary: the constant
trace contribution is itself divisible by five. -/
theorem thetaLimit_regularized_approximation_mod_five
    (G : ℕ → Polynomial ℤ_[5]) (hG : Compatible G) (u c : ℤ_[5])
    (hfirst : ∀ k : ℕ, k < 5 → (5 : ℤ_[5]) ∣
      (G 1).coeff k - PowerSeries.coeff k (BSDThetaCertificate.regularized433 u c)) :
    ∃ H J : PowerSeries ℤ_[5],
      thetaLimit G hG - BSDThetaCertificate.regularized433 u c =
        (BSDRankTwo.omegaPoly (R := ℤ_[5]) 5 1 : PowerSeries ℤ_[5]) * H +
          PowerSeries.C (5 : ℤ_[5]) * J := by
  apply exists_omega_five_decomposition
  intro k hk
  have hlim : (5 : ℤ_[5]) ∣
      PowerSeries.coeff k (thetaLimit G hG) - (G 1).coeff k := by
    simpa using thetaLimit_coeff_precision G hG (n := 1) (a := 1)
      (s := 0) (k := k) (by decide) (by simpa using hk)
  simpa using dvd_add hlim (hfirst k hk)

/-- The finite-tower order/unit certificate needs only the first-level
coefficients modulo five through degree four. Consequently the trace scale
is unrestricted. The infinite series, its exact two lower zeros, and its
integral finite approximation are all conclusions of the finite inputs. -/
theorem finite_tower_certificate_mod_five
    (G : ℕ → Polynomial ℤ_[5]) (hG : Compatible G)
    (hsym : FiniteSymmetric G) (hzero : (G 0).coeff 0 = 0)
    (u c : ℤ_[5]) (hu : IsUnit u)
    (hfirst : ∀ k : ℕ, k < 5 → (5 : ℤ_[5]) ∣
      (G 1).coeff k - PowerSeries.coeff k (BSDThetaCertificate.regularized433 u c)) :
    (thetaLimit G hG).order = 2 ∧
      ∃ V : PowerSeries ℤ_[5], thetaLimit G hG = PowerSeries.X ^ 2 * V ∧
        IsUnit V.constantCoeff := by
  obtain ⟨H, J, happrox⟩ := thetaLimit_regularized_approximation_mod_five G hG u c hfirst
  have hF0 : (thetaLimit G hG).constantCoeff = 0 :=
    (thetaLimit_constantCoeff G hG).trans hzero
  have hF1 := thetaLimit_coeff_one_zero G hG hsym hzero
  have hdiv : (PowerSeries.X : PowerSeries ℤ_[5]) ^ 2 ∣ thetaLimit G hG := by
    apply PowerSeries.X_pow_dvd_iff.2
    intro k hk
    rcases (show k = 0 ∨ k = 1 by omega) with rfl | rfl
    · simpa using hF0
    · exact hF1
  have h5 : ¬ IsUnit (5 : ℤ_[5]) := PadicInt.irreducible_p.not_isUnit
  constructor
  · exact BSDRankTwo.exact_order_two_of_certificate
      (p := 5) (n := 1) (m := 1) (by decide) (by decide) (by omega)
      (thetaLimit G hG) (BSDThetaCertificate.regularized433 u c) H J
      (by simpa using happrox) hdiv
      (by simpa using (BSDThetaCertificate.regularized433_quadratic_nondivisible_of_unit
        u c h5 hu))
  · obtain ⟨V, hV⟩ := hdiv
    refine ⟨V, hV, ?_⟩
    have hunit := BSDThetaCertificate.quadratic_unit_of_regularized433
      (thetaLimit G hG) H J u c h5 hu happrox
    rw [hV] at hunit
    have hcoeff : PowerSeries.coeff 2 (PowerSeries.X ^ 2 * V) = V.constantCoeff := by
      simpa using PowerSeries.coeff_X_pow_mul V 2 0
    rwa [hcoeff] at hunit

/-- An explicit polynomial control family allowing every trace scale.
It is a consistency witness, not an identification with the arithmetic CM
tower. -/
noncomputable def controlPolynomial (u c : ℤ_[5]) : Polynomial ℤ_[5] :=
  Polynomial.C u * (Polynomial.X ^ 2 + Polynomial.X ^ 3) -
    Polynomial.C c * Polynomial.X ^ 4

/-- The arbitrary-trace control family obeys the correct finite polynomial
symmetry with the raw-origin multiplier `(1+T)^4` at every level. -/
theorem control_finite_symmetric (u c : ℤ_[5]) :
    FiniteSymmetric (fun _ => controlPolynomial u c) := by
  intro n
  let g : Polynomial ℤ_[5] := 1 + Polynomial.X
  let b : Polynomial ℤ_[5] := g ^ (5 ^ n - 1)
  refine ⟨g ^ 4, ?_, ?_⟩
  · simp [g, Polynomial.coeff_zero_eq_eval_zero]
  have hpow : g ^ (5 ^ n) = g * b := by
    dsimp [b]
    rw [← pow_succ']
    congr 1
    have hpos : 0 < 5 ^ n := pow_pos (by decide) _
    omega
  have homega : BSDRankTwo.omegaPoly (R := ℤ_[5]) 5 n = g * b - 1 := by
    change g ^ (5 ^ n) - 1 = g * b - 1
    rw [hpow]
  have hcomp : (controlPolynomial u c).comp (cyclicInverse n) =
      Polynomial.C u * (b * (b - 1) ^ 2) - Polynomial.C c * (b - 1) ^ 4 := by
    simp only [controlPolynomial, Polynomial.sub_comp, Polynomial.mul_comp,
      Polynomial.C_comp, Polynomial.add_comp, Polynomial.pow_comp, Polynomial.X_comp]
    change Polynomial.C u * ((b - 1) ^ 2 + (b - 1) ^ 3) -
      Polynomial.C c * (b - 1) ^ 4 = _
    ring
  have hraw : controlPolynomial u c =
      Polynomial.C u * (g * (g - 1) ^ 2) - Polynomial.C c * (g - 1) ^ 4 := by
    dsimp [controlPolynomial, g]
    ring
  rw [hcomp, hraw, homega]
  refine ⟨Polynomial.C u *
      (-g * (g * b) ^ 2 + (2 * g ^ 2 - g) * (g * b) +
        (-g ^ 3 + 2 * g ^ 2 - g)) -
      Polynomial.C c * ((g - 1) - g * (b - 1)) *
        ((g - 1) ^ 2 + (g * (b - 1)) ^ 2), ?_⟩
  ring

/-- Joint nonvacuity of the modulo-five interface for arbitrary `u` and `c`.
The unit condition on `u` is needed only to infer the order-two conclusion.
Every finite level is the explicit polynomial `u(T²+T³)-cT⁴`. -/
theorem control_finite_tower_inputs (u c : ℤ_[5]) :
    let G : ℕ → Polynomial ℤ_[5] := fun _ => controlPolynomial u c
    Compatible G ∧ FiniteSymmetric G ∧ (G 0).coeff 0 = 0 ∧
      ∀ k : ℕ, k < 5 → (5 : ℤ_[5]) ∣
        (G 1).coeff k - PowerSeries.coeff k (BSDThetaCertificate.regularized433 u c) := by
  dsimp only
  refine ⟨constant_compatible _, control_finite_symmetric u c, ?_, ?_⟩
  · simp [controlPolynomial]
  · intro k _
    let J : PowerSeries ℤ_[5] := PowerSeries.C c *
      (1 + 2 * PowerSeries.X + 2 * PowerSeries.X ^ 2 + PowerSeries.X ^ 3)
    have hdiff : (controlPolynomial u c : PowerSeries ℤ_[5]) -
        BSDThetaCertificate.regularized433 u c = PowerSeries.C (5 : ℤ_[5]) * J := by
      simp only [controlPolynomial, Polynomial.coe_sub, Polynomial.coe_mul,
        Polynomial.coe_C, Polynomial.coe_add, Polynomial.coe_pow, Polynomial.coe_X,
        BSDThetaCertificate.regularized433, BSDThetaCertificate.finite433_shift,
        BSDThetaCertificate.normFive_shift, J, map_ofNat]
      ring
    have hcoeff := congrArg (PowerSeries.coeff k) hdiff
    simp only [map_sub, Polynomial.coeff_coe, PowerSeries.coeff_C_mul] at hcoeff
    exact ⟨PowerSeries.coeff k J, hcoeff⟩

end BSDThetaLimit
