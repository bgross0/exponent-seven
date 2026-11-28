import Exp7Lean.Arithmetic.InertThreshold

/-!
# The four zero-obstruction rows: exact arithmetic coverage

These are the endpoints and cutoffs in the integer verifier. Only coverage,
the norm cutoff and the resulting inert prime sum are proved here. The
positive analytic margins in the Python output are not imported as axioms.
-/

namespace Exp7.Frontier

structure ZeroRow where
  X : ℕ
  Qmin : ℕ
  Qmax : ℕ
  deriving DecidableEq

def row19000 : ZeroRow := ⟨19000, 39 * 10 ^ 29, 10 ^ 32⟩
def row30000 : ZeroRow := ⟨30000, 10 ^ 32, 10 ^ 40⟩
def row100000 : ZeroRow := ⟨100000, 10 ^ 40, 10 ^ 60⟩
def row1000000 : ZeroRow := ⟨1000000, 10 ^ 60, 10 ^ 162⟩

def zeroRows : List ZeroRow := [row19000, row30000, row100000, row1000000]

theorem zeroRows_cutoff : ∀ r ∈ zeroRows, 2 ≤ r.X ∧ 4 * r.X ^ 7 < r.Qmin := by
  intro r hr
  simp only [zeroRows, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;>
    norm_num [row19000, row30000, row100000, row1000000]

/-- Closed adjacent intervals cover the full range, including every boundary. -/
theorem zeroRows_cover {q : ℕ} (hlo : 39 * 10 ^ 29 ≤ q) (hhi : q ≤ 10 ^ 162) :
    ∃ r ∈ zeroRows, r.Qmin ≤ q ∧ q ≤ r.Qmax := by
  by_cases h32 : q ≤ 10 ^ 32
  · exact ⟨row19000, by simp [zeroRows], hlo, h32⟩
  by_cases h40 : q ≤ 10 ^ 40
  · exact ⟨row30000, by simp [zeroRows], (not_le.mp h32).le, h40⟩
  by_cases h60 : q ≤ 10 ^ 60
  · exact ⟨row100000, by simp [zeroRows], (not_le.mp h40).le, h60⟩
  exact ⟨row1000000, by simp [zeroRows], (not_le.mp h60).le, hhi⟩

/-- Each hypothetical exponent-seven field in the covered range supplies an
actual row whose prime sum is inert, for every test function. -/
theorem exists_inert_zeroRow {q : ℕ} [Fact q.Prime] (hE : IsExp7 q)
    (hlo : 39 * 10 ^ 29 ≤ q) (hhi : q ≤ 10 ^ 162) :
    ∃ r ∈ zeroRows, r.Qmin ≤ q ∧ q ≤ r.Qmax ∧ 4 * r.X ^ 7 < q ∧
      ∀ f : ℝ → ℝ, primeSum q f r.X = inertSum f r.X := by
  obtain ⟨r, hr, hmin, hmax⟩ := zeroRows_cover hlo hhi
  have hcut := lt_of_lt_of_le (zeroRows_cutoff r hr).2 hmin
  exact ⟨r, hr, hmin, hmax, hcut, fun f ↦ hE.primeSum_eq_inertSum_of_cutoff hcut f⟩

end Exp7.Frontier
