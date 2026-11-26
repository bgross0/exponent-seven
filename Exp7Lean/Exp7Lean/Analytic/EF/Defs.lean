import Exp7Lean.Analytic.Statement

/-!
# Explicit formula blueprint: definitions

Blueprint file (see `BLUEPRINT.md` in this directory). Definitions only, no `sorry`.

Notation of the blueprint. `χ = chi q`, `Λ_q(s) = q^{s/2} · completedLFunction χ s`,
`m(ρ) = mult q ρ` the multiplicity of `ρ` as a zero of the completed `L`-function,
`h` the (cosine) Fourier transform of the test function `f`.

For `δ > 0` the *damped* explicit formula reads `zeroSideR q h δ = arithSideR q f X δ`, where

* `zeroSideR q h δ  = ∑_ρ m(ρ) · (1/π) ∫ h(t) · δ / (δ² + (t - Im ρ)²) dt`,
* `arithSideR q f X δ = log(q/π) + Re ψ(3/4 + δ/2) + ∫₀^∞ 2 e^{-(3/2+δ)u}/(1 - e^{-2u}) (1 - f u) du
    - 2 ∑_{n<X} Λ(n) χ(n) f(log n) n^{-1/2-δ}`.

At `δ = 0` the right-hand side is `log(q/π) + ψ(3/4) + J_f - primeSum q f X`.
-/

namespace Exp7.EF

open Real MeasureTheory

/-- `f` is an admissible test function with (cosine) Fourier transform `h`:
`h ≥ 0` is continuous with `h(t) ≤ C/(1+t²)`, `f(u) = (1/2π) ∫ h(t) cos(tu) dt`, `f(0) = 1`,
and `f` vanishes on `[L, ∞)`.  (Then `f` is automatically even, continuous, `|f| ≤ 1`,
and `0 ≤ 1 - f(u) ≤ C'|u|`.) -/
structure WeilAdmissible (f : ℝ → ℝ) (L : ℝ) (h : ℝ → ℝ) : Prop where
  cont : Continuous h
  nonneg : ∀ t, 0 ≤ h t
  decay : ∃ C : ℝ, ∀ t, h t ≤ C / (1 + t ^ 2)
  inv : ∀ u, f u = 1 / (2 * π) * ∫ t, h t * Real.cos (t * u)
  zero : f 0 = 1
  supp : ∀ u, L ≤ u → f u = 0

/-- Multiplicity of `ρ` as a zero of the completed `L`-function of `chi q`
(`0` if `ρ` is not a zero).  For `chi q ≠ 1` the support is the set of nontrivial zeros. -/
noncomputable def mult (q : ℕ) [Fact q.Prime] (ρ : ℂ) : ℕ :=
  analyticOrderNatAt (chi q).completedLFunction ρ

/-- The Poisson kernel `δ / (δ² + x²) = Re (1 / (δ + i x))`. -/
noncomputable def poissonKer (δ x : ℝ) : ℝ := δ / (δ ^ 2 + x ^ 2)

/-- Real zero side: `∑_ρ m(ρ) · (1/π) ∫ h(t) · δ / (δ² + (t - Im ρ)²) dt`. -/
noncomputable def zeroSideR (q : ℕ) [Fact q.Prime] (h : ℝ → ℝ) (δ : ℝ) : ℝ :=
  ∑' ρ : ℂ, (mult q ρ : ℝ) * (1 / π * ∫ t : ℝ, h t * poissonKer δ (t - ρ.im))

/-- The damped archimedean integrand `2 e^{-(3/2+δ)u} / (1 - e^{-2u}) · (1 - f u)`. -/
noncomputable def archIntegrand (f : ℝ → ℝ) (δ u : ℝ) : ℝ :=
  2 * exp (-(3 / 2 + δ) * u) / (1 - exp (-2 * u)) * (1 - f u)

/-- Real damped archimedean term `Re ψ(3/4 + δ/2) + ∫₀^∞ 2 e^{-(3/2+δ)u}/(1-e^{-2u}) (1 - f u) du`. -/
noncomputable def archTermR (f : ℝ → ℝ) (δ : ℝ) : ℝ :=
  (Complex.digamma ((3 / 4 + δ / 2 : ℝ) : ℂ)).re + ∫ u in Set.Ioi (0 : ℝ), archIntegrand f δ u

/-- The real coefficient `Λ(n) χ(n)`, `χ(n) = (n/q)`. -/
noncomputable def coeff (q : ℕ) [Fact q.Prime] (n : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt n * (legendreSym q n : ℝ)

/-- Real damped prime sum `2 ∑_{n<X} Λ(n) χ(n) f(log n) n^{-1/2-δ}`. -/
noncomputable def primeTermR (q : ℕ) [Fact q.Prime] (f : ℝ → ℝ) (X : ℕ) (δ : ℝ) : ℝ :=
  2 * ∑ n ∈ Finset.range X, coeff q n * f (log n) * (n : ℝ) ^ (-(1 / 2 : ℝ) - δ)

/-- `-Re (L'/L)(1/2 + δ + it, χ) = ∑_n Λ(n) χ(n) n^{-1/2-δ} cos(t log n)` (for `δ > 1/2`). -/
noncomputable def dirichletR (q : ℕ) [Fact q.Prime] (δ t : ℝ) : ℝ :=
  ∑' n : ℕ, coeff q n * (n : ℝ) ^ (-(1 / 2 : ℝ) - δ) * Real.cos (t * log n)

/-- `∑_ρ m(ρ) · δ / (δ² + (t - Im ρ)²)`; under GRH this is `Re (Λ_q'/Λ_q)(1/2 + δ + it)`. -/
noncomputable def zerosKer (q : ℕ) [Fact q.Prime] (δ t : ℝ) : ℝ :=
  ∑' ρ : ℂ, (mult q ρ : ℝ) * poissonKer δ (t - ρ.im)

/-- Real arithmetic side of the damped explicit formula. -/
noncomputable def arithSideR (q : ℕ) [Fact q.Prime] (f : ℝ → ℝ) (X : ℕ) (δ : ℝ) : ℝ :=
  log (q / π) + archTermR f δ - primeTermR q f X δ

/-! ### Complex versions (holomorphic in the damping parameter `δ`, `Re δ > 0`) -/

/-- Complex zero side: `∑_ρ m(ρ) · (1/π) ∫ h(t) · δ / (δ² + (t - Im ρ)²) dt` for complex `δ`. -/
noncomputable def zeroSide (q : ℕ) [Fact q.Prime] (h : ℝ → ℝ) (δ : ℂ) : ℂ :=
  ∑' ρ : ℂ, (mult q ρ : ℂ) *
    (1 / π * ∫ t : ℝ, (h t : ℂ) * (δ / (δ ^ 2 + ((t - ρ.im : ℝ) : ℂ) ^ 2)))

/-- Complex damped archimedean term. -/
noncomputable def archTerm (f : ℝ → ℝ) (δ : ℂ) : ℂ :=
  Complex.digamma (3 / 4 + δ / 2) +
    ∫ u in Set.Ioi (0 : ℝ),
      2 * Complex.exp (-(3 / 2 + δ) * u) / (1 - Complex.exp (-2 * u)) * ((1 - f u : ℝ) : ℂ)

/-- Complex damped prime sum. -/
noncomputable def primeTerm (q : ℕ) [Fact q.Prime] (f : ℝ → ℝ) (X : ℕ) (δ : ℂ) : ℂ :=
  2 * ∑ n ∈ Finset.range X, ((coeff q n * f (log n) : ℝ) : ℂ) * (n : ℂ) ^ (-(1 / 2 : ℂ) - δ)

/-- Complex arithmetic side of the damped explicit formula. -/
noncomputable def arithSide (q : ℕ) [Fact q.Prime] (f : ℝ → ℝ) (X : ℕ) (δ : ℂ) : ℂ :=
  (log (q / π) : ℝ) + archTerm f δ - primeTerm q f X δ

/-- The open right half-plane of damping parameters. -/
def rightHalfPlane : Set ℂ := {δ : ℂ | 0 < δ.re}

end Exp7.EF
