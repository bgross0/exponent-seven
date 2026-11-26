import Exp7Lean.Final

/-!
Exponent 7: the analytic input, stated precisely.

This file contains definitions and one `Prop`, `ExplicitFormulaBound`. Nothing here is assumed or
proved: the statement is what Steps 2–3 of the note use. It is the Guinand–Weil explicit formula
for the odd real primitive character modulo a prime `q ≡ 3 (mod 4)`, applied to the normalised
autocorrelation `f` of a step function `g` supported in `[0, log X]`, together with positivity of
the sum over zeros under GRH:

    2 ∑_{n < X} Λ(n) χ(n) f(log n) / √n  ≤  log(q/π) + ψ(3/4) + J_f,
    J_f = ∫_0^∞ 2 e^{-3u/2} / (1 - e^{-2u}) · (1 - f(u)) du.
-/

namespace Exp7

open Real MeasureTheory

/-- The step function with values `v` on `v.length` equal cells of `[0, L)`, zero elsewhere. -/
noncomputable def stepFn (L : ℝ) (v : List ℝ) (t : ℝ) : ℝ :=
  if 0 ≤ t ∧ t < L then v.getD ⌊t * v.length / L⌋₊ 0 else 0

/-- Normalised autocorrelation of `g`: `f(u) = ∫ g(t) g(t+u) dt / ∫ g(t)^2 dt`. -/
noncomputable def autocorr (g : ℝ → ℝ) (u : ℝ) : ℝ :=
  (∫ t, g t * g (t + u)) / ∫ t, g t ^ 2

/-- The archimedean term `J_f`. -/
noncomputable def Jterm (f : ℝ → ℝ) : ℝ :=
  ∫ u in Set.Ioi (0 : ℝ), 2 * exp (-(3 / 2) * u) / (1 - exp (-2 * u)) * (1 - f u)

/-- `ψ(3/4) = -γ + π/2 - 3 log 2`, the digamma function at `3/4`. -/
noncomputable def psi34 : ℝ := -eulerMascheroniConstant + π / 2 - 3 * log 2

/-- The real primitive character modulo a prime `q`, `n ↦ (n/q)`, with values in `ℂ`. -/
noncomputable def chi (q : ℕ) [Fact q.Prime] : DirichletCharacter ℂ q :=
  (quadraticChar (ZMod q)).ringHomComp (Int.castRingHom ℂ)

/-- GRH for `L(s, χ_q)`: every zero in the critical strip has real part `1/2`. -/
def GRHFor (q : ℕ) [Fact q.Prime] : Prop :=
  ∀ s : ℂ, 0 < s.re → s.re < 1 → DirichletCharacter.LFunction (chi q) s = 0 → s.re = 1 / 2

/-- The prime-power side of the explicit formula for the test function `f`, cut at `X`. -/
noncomputable def primeSum (q : ℕ) [Fact q.Prime] (f : ℝ → ℝ) (X : ℕ) : ℝ :=
  2 * ∑ n ∈ Finset.range X,
    ArithmeticFunction.vonMangoldt n * (legendreSym q n : ℝ) * f (log n) / sqrt n

/-- The explicit-formula inequality used by every certificate row. -/
def ExplicitFormulaBound : Prop :=
  ∀ (q : ℕ) [Fact q.Prime], q % 4 = 3 → GRHFor q → ∀ (X : ℕ) (v : List ℝ), 2 ≤ X →
    (∃ t ∈ v, t ≠ 0) →
    primeSum q (autocorr (stepFn (log X) v)) X ≤
      log (q / π) + psi34 + Jterm (autocorr (stepFn (log X) v))

/-- GRH for all the characters used: the hypothesis of Theorem A. -/
def GRHPrimeConductor : Prop :=
  ∀ (q : ℕ) [Fact q.Prime], q % 4 = 3 → GRHFor q

end Exp7
