import Exp7Lean.SieveKernel

/-!
A low-search bridge: append a pattern retaining every index NOT in the
exception list, then reuse the existing high-search exclude_block theorem.
Draft; originating environment has no Lean compiler. No new axioms.
-/

namespace Exp7.SieveKernel

/-- Semantic exception pattern. For efficient production, replace its bits by
a sparse mask and prove the same forward bit property. -/
def exceptionPattern (n : ℕ) (ks : List ℕ) : Pattern :=
  ⟨n, makeBits n (fun i => decide (i ∉ ks)), 0, 0⟩

theorem exceptionPattern_covers (n : ℕ) (ks : List ℕ) (hn : 0 < n) :
    (exceptionPattern n ks).covers n := by
  simp [exceptionPattern, Pattern.covers, hn]

theorem exceptionPattern_keeps (n : ℕ) (ks : List ℕ) (i : ℕ)
    (hi : i < n) (hk : i ∉ ks) :
    (exceptionPattern n ks).bits.testBit
        (((exceptionPattern n ks).phase + i) % (exceptionPattern n ks).period) = true := by
  change (makeBits n (fun k => decide (k ∉ ks))).testBit ((0 + i) % n) = true
  simpa [Nat.mod_eq_of_lt hi] using
    makeBits_keeps n (fun k => decide (k ∉ ks)) i hi (decide_eq_true hk)

/-- Any pattern with the required one-sided property can serve as an exception
mask. Its implementation need not use the dense semantic constructor above. -/
theorem block_only_listed (ps : List Pattern) (ex : Pattern) (n : ℕ)
    (ks : List ℕ) (hc : ∀ p ∈ ps, p.covers n) (hexc : ex.covers n)
    (hkeep : ∀ i < n, i ∉ ks →
      ex.bits.testBit ((ex.phase + i) % ex.period) = true)
    (hz : intersect (ex :: ps) n = 0) :
    ∀ i < n, (∀ p ∈ ps, p.bits.testBit ((p.phase + i) % p.period) = true) →
      i ∈ ks := by
  intro i hi h
  by_contra hk
  have hC : ∀ p ∈ ex :: ps, p.covers n := by
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact hexc
    · exact hc p hp
  have hI : ∀ p ∈ ex :: ps, p.bits.testBit ((p.phase + i) % p.period) = true := by
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact hkeep i hi hk
    · exact h p hp
  exact exclude_block (ex :: ps) n hC hz i hi hI

theorem block_only_listed_semantic (ps : List Pattern) (n : ℕ) (ks : List ℕ)
    (hn : 0 < n) (hc : ∀ p ∈ ps, p.covers n)
    (hz : intersect (exceptionPattern n ks :: ps) n = 0) :
    ∀ i < n, (∀ p ∈ ps, p.bits.testBit ((p.phase + i) % p.period) = true) →
      i ∈ ks :=
  block_only_listed ps (exceptionPattern n ks) n ks hc
    (exceptionPattern_covers n ks hn) (exceptionPattern_keeps n ks) hz

end Exp7.SieveKernel
