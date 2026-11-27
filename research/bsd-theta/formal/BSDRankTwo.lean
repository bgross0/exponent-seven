import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# Sound finite-level coefficient certificates

These are algebraic certificate lemmas. They do not assert BSD, nonvanishing
of an arithmetic theta element, or any property of a Selmer group.
Exact lower-order vanishing and the finite-level approximation identity are
explicit hypotheses of the final certificate theorem.
-/

namespace BSDRankTwo

/-- A precision/truncation bound for the binomial coefficients of a prime-power
level. The parameter `s` allows coefficients of degree below `p^(s+1)` at
precision `p^m`, provided the level is at least `m+s`. -/
theorem prime_pow_dvd_choose
    {p n m s k : ℕ} (hp : p.Prime) (hlevel : m + s ≤ n)
    (hk0 : 0 < k) (hk : k < p ^ (s + 1)) :
    p ^ m ∣ (p ^ n).choose k := by
  by_cases hm : m = 0
  · simp [hm]
  have hsn : s + 1 ≤ n := by omega
  have hkn : k ≤ p ^ n :=
    hk.le.trans (Nat.pow_le_pow_right hp.pos hsn)
  have hkne : k ≠ 0 := Nat.ne_of_gt hk0
  have hval : k.factorization p ≤ s := by
    by_contra h
    have hdiv : p ^ (s + 1) ∣ k :=
      (hp.pow_dvd_iff_le_factorization hkne).2 (by omega)
    exact (not_le_of_gt hk) (Nat.le_of_dvd hk0 hdiv)
  apply (hp.pow_dvd_iff_le_factorization (Nat.choose_ne_zero hkn)).2
  have hsum := Nat.factorization_choose_prime_pow_add_factorization hp hkn hkne
  omega

/-- For degrees strictly below `p`, no precision is lost. -/
theorem prime_pow_dvd_choose_low
    {p n m k : ℕ} (hp : p.Prime) (hlevel : m ≤ n)
    (hk0 : 0 < k) (hk : k < p) :
    p ^ m ∣ (p ^ n).choose k := by
  apply prime_pow_dvd_choose (s := 0) hp (by simpa using hlevel) hk0
  simpa using hk

/-- The first omitted coefficient has valuation `m-1`: the general truncation
bound is sharp over the integers. -/
theorem first_omitted_coefficient_valuation
    {p n m : ℕ} (hp : p.Prime) (hm : 0 < m) (hlevel : m ≤ n) :
    ((p ^ n).choose (p ^ (n - m + 1))).factorization p = m - 1 := by
  have hexp : n - m + 1 ≤ n := by omega
  have hkn : p ^ (n - m + 1) ≤ p ^ n := Nat.pow_le_pow_right hp.pos hexp
  rw [Nat.factorization_choose_prime_pow hp hkn (pow_ne_zero _ hp.ne_zero),
    Nat.factorization_pow_self hp]
  omega

section Coefficients

variable {R : Type*} [CommRing R]

/-- Substitution by a series with zero constant coefficient acts on the
linear coefficient by multiplication by its own linear coefficient. -/
theorem coeff_one_subst_of_constantCoeff_zero
    (F B : PowerSeries R) (hB : B.constantCoeff = 0) :
    PowerSeries.coeff 1 (F.subst B) =
      PowerSeries.coeff 1 F * PowerSeries.coeff 1 B := by
  rw [PowerSeries.coeff_subst' (PowerSeries.HasSubst.of_constantCoeff_zero hB),
    finsum_eq_single _ 1]
  · simp
  · rintro (_ | _ | n) hn <;> simp_all [PowerSeries.coeff_one_pow]

/-- The plus-sign functional equation kills the linear coefficient once its
zeroth coefficient is exactly zero. The explicit `h_two` hypothesis says that the
coefficient ring has no additive two-torsion. The intended substitution is
`B = (1+T)^(-1)-1`, whose constant and linear coefficients are `0` and `-1`.
This theorem formalizes substitution itself, with those two properties
stated as hypotheses; it does not assume a finite-precision zero is exact. -/
theorem coeff_one_eq_zero_of_substitution_symmetry
    (F U B : PowerSeries R)
    (h_two : ∀ a : R, a + a = 0 → a = 0)
    (hF : F.constantCoeff = 0) (hU : U.constantCoeff = 1)
    (hB : B.constantCoeff = 0) (hB1 : PowerSeries.coeff 1 B = -1)
    (hsym : F = U * F.subst B) :
    PowerSeries.coeff 1 F = 0 := by
  have hsubst0 : PowerSeries.constantCoeff (F.subst B) = 0 :=
    PowerSeries.constantCoeff_subst_eq_zero hB F hF
  have hlinear : PowerSeries.coeff 1 F = -PowerSeries.coeff 1 F := by
    calc
      PowerSeries.coeff 1 F = PowerSeries.coeff 1 (U * F.subst B) :=
        congrArg (PowerSeries.coeff 1) hsym
      _ = -PowerSeries.coeff 1 F := by
        rw [PowerSeries.coeff_one_mul, hsubst0,
          coeff_one_subst_of_constantCoeff_zero F B hB]
        simp [hU, hB1]
  apply h_two
  calc
    PowerSeries.coeff 1 F + PowerSeries.coeff 1 F =
        -PowerSeries.coeff 1 F + PowerSeries.coeff 1 F :=
      congrArg (fun a => a + PowerSeries.coeff 1 F) hlinear
    _ = 0 := neg_add_cancel _

/-- Exact zero constant coefficient and plus-sign substitution symmetry
provide the exact `T^2` divisibility required by the order certificate. -/
theorem X_sq_dvd_of_substitution_symmetry
    (F U B : PowerSeries R)
    (h_two : ∀ a : R, a + a = 0 → a = 0)
    (hF : F.constantCoeff = 0) (hU : U.constantCoeff = 1)
    (hB : B.constantCoeff = 0) (hB1 : PowerSeries.coeff 1 B = -1)
    (hsym : F = U * F.subst B) :
    (PowerSeries.X : PowerSeries R) ^ 2 ∣ F := by
  apply PowerSeries.X_pow_dvd_iff.2
  intro i hi
  have hlinear := coeff_one_eq_zero_of_substitution_symmetry F U B
    h_two hF hU hB hB1 hsym
  rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
  · simpa using hF
  · exact hlinear

/-- The group-inversion substitution `(1+T)^(-1)-1`, using the inverse of a
power series with unit constant coefficient. -/
noncomputable def inversionSeries : PowerSeries R :=
  PowerSeries.invOfUnit (1 + PowerSeries.X) (1 : Rˣ) - 1

theorem inversionSeries_constantCoeff :
    PowerSeries.constantCoeff (inversionSeries (R := R)) = 0 := by
  simp [inversionSeries]

theorem inversionSeries_coeff_one :
    PowerSeries.coeff 1 (inversionSeries (R := R)) = -1 := by
  have hprod := PowerSeries.mul_invOfUnit
    (1 + PowerSeries.X : PowerSeries R) (1 : Rˣ) (by simp)
  have hlinear := congrArg (PowerSeries.coeff 1) hprod
  rw [PowerSeries.coeff_one_mul] at hlinear
  have heq : 1 + PowerSeries.coeff 1
      (PowerSeries.invOfUnit (1 + PowerSeries.X) (1 : Rˣ)) = 0 := by
    simpa using hlinear
  simpa [inversionSeries] using eq_neg_of_add_eq_zero_right heq

/-- The exact involution-symmetry criterion with the genuine group-inversion
series, requiring only that the coefficient ring have no additive two-torsion. -/
theorem X_sq_dvd_of_inversion_symmetry
    (F U : PowerSeries R)
    (h_two : ∀ a : R, a + a = 0 → a = 0)
    (hF : F.constantCoeff = 0) (hU : U.constantCoeff = 1)
    (hsym : F = U * F.subst (inversionSeries (R := R))) :
    (PowerSeries.X : PowerSeries R) ^ 2 ∣ F := by
  exact X_sq_dvd_of_substitution_symmetry F U inversionSeries h_two hF hU
    inversionSeries_constantCoeff inversionSeries_coeff_one hsym

/-- The finite-level relation for a cyclic group of order `p^n`. -/
noncomputable def omegaPoly (p n : ℕ) : Polynomial R :=
  (1 + Polynomial.X) ^ (p ^ n) - 1

/-- Every coefficient in the certified truncation of `omegaPoly` is divisible
by the required precision. The constant coefficient is zero. -/
theorem omega_coeff_dvd
    {p n m s k : ℕ} (hp : p.Prime) (hlevel : m + s ≤ n)
    (hk : k < p ^ (s + 1)) :
    ((p ^ m : ℕ) : R) ∣ (omegaPoly (R := R) p n).coeff k := by
  by_cases hk0 : k = 0
  · simp [omegaPoly, hk0, Polynomial.coeff_one_add_X_pow]
  rw [omegaPoly, Polynomial.coeff_sub, Polynomial.coeff_one_add_X_pow]
  simp only [Polynomial.coeff_one, ite_eq_right hk0, sub_zero]
  obtain ⟨q, hq⟩ := prime_pow_dvd_choose hp hlevel (Nat.pos_of_ne_zero hk0) hk
  exact ⟨(q : R), by rw [hq, Nat.cast_mul]⟩

/-- A Cauchy-product coefficient inherits divisibility from all coefficients
of one factor which can contribute to it. -/
theorem coeff_mul_dvd
    (A H : PowerSeries R) (a : R) (k : ℕ)
    (hA : ∀ i, i ≤ k → a ∣ PowerSeries.coeff i A) :
    a ∣ PowerSeries.coeff k (A * H) := by
  rw [PowerSeries.coeff_mul]
  apply Finset.dvd_sum
  intro ij hij
  have hsum := Finset.mem_antidiagonal.mp hij
  exact dvd_mul_of_dvd_left (hA ij.1 (by omega)) _

/-- Finite-level representatives, even with a `p^m` error, determine every
coefficient in the certified truncation modulo `p^m`.

This is stated over an arbitrary commutative ring, so it applies to the
integers, the p-adic integers, and integral coefficient extensions. The
approximation multipliers are required to lie in that same ring. -/
theorem finite_level_coeff_dvd
    {p n m s k : ℕ} (hp : p.Prime) (hlevel : m + s ≤ n)
    (hk : k < p ^ (s + 1))
    (F G H J : PowerSeries R)
    (happrox : F - G = (omegaPoly (R := R) p n : PowerSeries R) * H +
      PowerSeries.C ((p ^ m : ℕ) : R) * J) :
    ((p ^ m : ℕ) : R) ∣ PowerSeries.coeff k F - PowerSeries.coeff k G := by
  have hmul : ((p ^ m : ℕ) : R) ∣
      PowerSeries.coeff k ((omegaPoly (R := R) p n : PowerSeries R) * H) := by
    apply coeff_mul_dvd
    intro i hi
    rw [Polynomial.coeff_coe]
    exact omega_coeff_dvd hp hlevel (hi.trans_lt hk)
  have hcoeff : PowerSeries.coeff k (F - G) =
      PowerSeries.coeff k F - PowerSeries.coeff k G := map_sub _ _ _
  rw [← hcoeff, happrox, map_add, PowerSeries.coeff_C_mul]
  exact dvd_add hmul (dvd_mul_right _ _)

/-- A nonzero residue for the leading candidate coefficient, together with
exact vanishing of all earlier coefficients, certifies the exact order.
The residue condition is expressed as nondivisibility by `p^m`. -/
theorem exact_order_of_certificate
    {p n m s d : ℕ} (hp : p.Prime) (hlevel : m + s ≤ n)
    (hd : d < p ^ (s + 1))
    (F G H J : PowerSeries R)
    (happrox : F - G = (omegaPoly (R := R) p n : PowerSeries R) * H +
      PowerSeries.C ((p ^ m : ℕ) : R) * J)
    (hvanish : ∀ i, i < d → PowerSeries.coeff i F = 0)
    (hresidue : ¬ ((p ^ m : ℕ) : R) ∣ PowerSeries.coeff d G) :
    F.order = d := by
  apply PowerSeries.order_eq_nat.2
  refine ⟨?_, hvanish⟩
  intro hzero
  apply hresidue
  have hcongr := finite_level_coeff_dvd hp hlevel hd F G H J happrox
  simpa [hzero] using hcongr

/-- For odd primes, level `n >= m` suffices to certify quadratic order. -/
theorem exact_order_two_of_certificate
    {p n m : ℕ} (hp : p.Prime) (hp2 : 2 < p) (hlevel : m ≤ n)
    (F G H J : PowerSeries R)
    (happrox : F - G = (omegaPoly (R := R) p n : PowerSeries R) * H +
      PowerSeries.C ((p ^ m : ℕ) : R) * J)
    (hvanish : (PowerSeries.X : PowerSeries R) ^ 2 ∣ F)
    (hresidue : ¬ ((p ^ m : ℕ) : R) ∣ PowerSeries.coeff 2 G) :
    F.order = 2 := by
  exact exact_order_of_certificate (s := 0) hp (by simpa using hlevel)
    (by simpa using hp2) F G H J happrox
    (PowerSeries.X_pow_dvd_iff.1 hvanish) hresidue

/-- At the prime two, one additional level restores quadratic precision. -/
theorem exact_order_two_at_two
    {n m : ℕ} (hlevel : m + 1 ≤ n)
    (F G H J : PowerSeries R)
    (happrox : F - G = (omegaPoly (R := R) 2 n : PowerSeries R) * H +
      PowerSeries.C ((2 ^ m : ℕ) : R) * J)
    (hvanish : (PowerSeries.X : PowerSeries R) ^ 2 ∣ F)
    (hresidue : ¬ ((2 ^ m : ℕ) : R) ∣ PowerSeries.coeff 2 G) :
    F.order = 2 := by
  exact exact_order_of_certificate (s := 1) Nat.prime_two hlevel
    (by decide) F G H J happrox
    (PowerSeries.X_pow_dvd_iff.1 hvanish) hresidue

end Coefficients

end BSDRankTwo
