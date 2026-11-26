import Exp7Lean.Analytic.EF.Defs

/-!
# Explicit formula blueprint: the Hadamard input

Leaves **H1, H2** of `BLUEPRINT.md`: the real-part partial-fraction expansion of `Λ'/Λ(s, χ)` over
the nontrivial zeros, for a primitive nonprincipal Dirichlet character.  This is the *only* deep
input of the whole blueprint (Hadamard factorisation of an entire function of order 1 plus the
functional equation).

**Not in Mathlib.**  Both statements below are copied verbatim (same names, same hypotheses, Mathlib
vocabulary only) from the Tau Ceti library, file
`TauCeti/NumberTheory/LFunctions/Zeros/Completion/Dirichlet/Hadamard.lean`
(`DirichletCharacter.re_logDeriv_LFunction_add_eq_tsum`,
`DirichletCharacter.summable_norm_analyticOrderNatAt_completedLFunction_mul_re_one_div_sub`),
commit `6d810e58e90dc1a8f89e5cb6056ee36c26da67d3`, which is pinned to the *same* Mathlib commit as this
project.  If that library is added as a dependency the two `sorry`s become one-line `exact`s.
The in-house alternative is decomposed in `HadamardFallback.lean`.

Here `χ.gammaFactor s = Γ_ℝ(s + 1) = π^{-(s+1)/2} Γ((s+1)/2)` for odd `χ`, so the left-hand side of
H1 is `Re (L'/L)(s) + ½ log (N/π) + ½ Re ψ((s+1)/2)`.
-/

namespace Exp7.EF

open Complex

variable {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)

/-- **H1** (XL in-house / import). Unpaired real-part partial fractions for a primitive nonprincipal
character: on `0 < Re s`, away from the zeros of `L(s, χ)`,
`Re (L'/L)(s, χ) + ½ log N + Re (γ'/γ)(s, χ) = ∑_ρ m_ρ Re (1 / (s - ρ))`, `m_ρ` the multiplicity
of `ρ` as a zero of the completed `L`-function. -/
theorem re_logDeriv_LFunction_add_eq_tsum (hχ : χ.IsPrimitive) (hne : χ ≠ 1) {s : ℂ}
    (hs : 0 < s.re) (hL : χ.LFunction s ≠ 0) :
    (logDeriv χ.LFunction s).re + Real.log N / 2 + (logDeriv χ.gammaFactor s).re =
      ∑' ρ : ℂ, (analyticOrderNatAt χ.completedLFunction ρ : ℝ) * (1 / (s - ρ)).re := by
  sorry

/-- **H2** (XL in-house / import). Absolute summability of the series in H1, for every `s`. -/
theorem summable_norm_analyticOrderNatAt_completedLFunction_mul_re_one_div_sub
    (hχ : χ.IsPrimitive) (hne : χ ≠ 1) (s : ℂ) :
    Summable (fun ρ : ℂ ↦
      ‖(analyticOrderNatAt χ.completedLFunction ρ : ℝ) * (1 / (s - ρ)).re‖) := by
  sorry

end Exp7.EF
