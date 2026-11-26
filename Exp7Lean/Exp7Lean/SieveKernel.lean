import Mathlib

/-! Draft verified packed-bitset search primitives. To be compiled against the pinned
Mathlib before use. No custom axioms or native_decide. The final production certificate
and the arithmetic connection to Inputs.search are intentionally not asserted here. -/
namespace Exp7.SieveKernel

/-- 2^depth copies of a mask, with successive copies separated by w bits. -/
def tile (w mask : ℕ) : ℕ → ℕ
  | 0 => mask
  | depth + 1 =>
    let b := tile w mask depth
    b ||| (b <<< (w * 2 ^ depth))

/-- For sound exclusion we only need the forward bit implication. Extra bits in
an oversized base mask are harmless (they can only make exclusion harder). -/
theorem tile_keeps (w mask depth i : ℕ) (hw : 0 < w)
    (hi : i < w * 2 ^ depth) (h : mask.testBit (i % w) = true) :
    (tile w mask depth).testBit i = true := by
  induction depth generalizing i with
  | zero =>
    simp only [pow_zero, mul_one] at hi
    simpa [tile, Nat.mod_eq_of_lt hi] using h
  | succ d ih =>
    have hsize : w * 2 ^ (d + 1) = w * 2 ^ d + w * 2 ^ d := by simp only [pow_succ]; ring
    rw [hsize] at hi
    simp only [tile, Nat.testBit_or, Nat.testBit_shiftLeft]
    by_cases hlt : i < w * 2 ^ d
    · rw [ih i hlt h]
      simp
    · have hs : w * 2 ^ d ≤ i := by omega
      have ht : i - w * 2 ^ d < w * 2 ^ d := by omega
      have he : i - w * 2 ^ d + w * 2 ^ d = i := by omega
      have hm : (i - w * 2 ^ d) % w = i % w := by
        conv_rhs => rw [← he]
        simp [Nat.add_mod, Nat.mul_mod]
      have h' : mask.testBit ((i - w * 2 ^ d) % w) = true := by
        rwa [hm]
      rw [ih _ ht h']
      simp [hs]

structure Pattern where
  period : ℕ
  bits : ℕ
  phase : ℕ
  depth : ℕ
  deriving Repr, DecidableEq

/-- A finite periodic pattern, shifted so bit zero corresponds to phase. -/
def Pattern.mask (p : Pattern) : ℕ :=
  tile p.period p.bits p.depth >>> p.phase

/-- Every allowed index is retained by this pattern, if tiling covers the block. -/
theorem Pattern.keeps (p : Pattern) (i : ℕ)
    (hw : 0 < p.period) (hi : p.phase + i < p.period * 2 ^ p.depth)
    (h : p.bits.testBit ((p.phase + i) % p.period) = true) :
    p.mask.testBit i = true := by
  rw [Pattern.mask, Nat.testBit_shiftRight]
  exact tile_keeps _ _ _ _ hw hi h

/-- A block of n positions, filtered by periodic patterns. A zero result rules
out every index that passes every pattern. -/
def intersect : List Pattern → ℕ → ℕ
  | [], n => 2 ^ n - 1
  | p :: ps, n => p.mask &&& intersect ps n

/-- Well-formedness is a finite, inexpensive arithmetic check per pattern. -/
def Pattern.covers (p : Pattern) (n : ℕ) : Prop :=
  0 < p.period ∧ p.phase + n ≤ p.period * 2 ^ p.depth

instance (p : Pattern) (n : ℕ) : Decidable (p.covers n) :=
  inferInstanceAs (Decidable (0 < p.period ∧ p.phase + n ≤ p.period * 2 ^ p.depth))

theorem intersect_keeps (ps : List Pattern) (n i : ℕ) (hi : i < n)
    (hc : ∀ p ∈ ps, p.covers n)
    (h : ∀ p ∈ ps, p.bits.testBit ((p.phase + i) % p.period) = true) :
    (intersect ps n).testBit i = true := by
  induction ps with
  | nil => simp [intersect, hi]
  | cons p ps ih =>
    have hp := hc p (by simp)
    have hp' := h p (by simp)
    have ht : p.phase + i < p.period * 2 ^ p.depth := by
      exact lt_of_lt_of_le (Nat.add_lt_add_left hi _) hp.2
    rw [intersect, Nat.testBit_and, p.keeps i hp.1 ht hp']
    have hrest := ih (fun p hp => hc p (by simp [hp]))
      (fun p hp => h p (by simp [hp]))
    simp [hrest]

/-- Soundness of the packed-block checker. No computational hypothesis except
its actual zero bitmask and well-formed pattern bounds is needed. -/
theorem exclude_block (ps : List Pattern) (n : ℕ)
    (hc : ∀ p ∈ ps, p.covers n) (hz : intersect ps n = 0) :
    ∀ i < n, ¬ (∀ p ∈ ps, p.bits.testBit ((p.phase + i) % p.period) = true) := by
  intro i hi h
  have hh := intersect_keeps ps n i hi hc h
  rw [hz, Nat.zero_testBit] at hh
  contradiction

/-- A reusable bridge from periodic predicates to packed patterns. The table
itself is generated, not trusted; Mathlib supplies the bit-index theorem. -/
def makeBits (w : ℕ) (f : ℕ → Bool) : ℕ :=
  Nat.ofBits (fun i : Fin w => f i.val)

theorem makeBits_keeps (w : ℕ) (f : ℕ → Bool) (r : ℕ)
    (hr : r < w) (h : f r = true) : (makeBits w f).testBit r = true := by
  unfold makeBits
  rw [Nat.testBit_ofBits_lt _ _ hr]
  exact h

/-- Euclidean decomposition is enough to establish coverage of the CRT wheel;
no CRT implementation or generated residue list needs to be trusted. -/
theorem wheel_decomposition (t W : ℕ) (hW : 0 < W) :
    ∃ r k : ℕ, r < W ∧ t = r + W * k := by
  exact ⟨t % W, t / W, Nat.mod_lt _ hW, (Nat.mod_add_div t W).symm⟩

/-- Toy kernel-only test: the two patterns permit complementary parity classes. -/
example : intersect [⟨2, 1, 0, 4⟩, ⟨2, 2, 0, 4⟩] 32 = 0 := by decide

#print axioms exclude_block
#print axioms makeBits_keeps
#print axioms wheel_decomposition

end Exp7.SieveKernel
