import Mathlib
import Exp7Lean.Sieve.RootsBasic

/-!
# CRT gluing of square-root lists

* `invMod a m` : fuel-based modular inverse (extended Euclid on naturals), with
  `invMod_spec : 0 < m → a.Coprime m → invMod a m * a % m = 1 % m`.
* `crt m₁ m₂ inv r₁ r₂` : the CRT combination, with specification `crt_modEq_left`,
  `crt_modEq_right`, `crt_lt`, `mod_mul_eq_crt`, valid as soon as `inv * m₁ % m₂ = 1 % m₂`
  (a condition a `Bool` checker can test directly).
* `crtList`, `crtPair`, `Complete.crt`, `crt_glue` : gluing of complete root lists.
-/

namespace Exp7.Roots

/-! ## Modular inverse -/

/-- Extended Euclid on naturals, coefficients kept reduced modulo `m`.
Invariant: `t0 * a ≡ r0` and `t1 * a ≡ r1 (mod m)`. -/
def invAux (m : ℕ) : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, _, _, t0, _ => t0
  | f + 1, r0, r1, t0, t1 =>
    bif r1.beq 0 then t0
    else invAux m f r1 (r0 % r1) t1 ((t0 + (m - (r0 / r1 * t1) % m)) % m)

/-- `invMod a m` is an inverse of `a` modulo `m` whenever `a` and `m` are coprime. -/
def invMod (a m : ℕ) : ℕ := invAux m m m (a % m) 0 1

theorem invAux_spec (a m : ℕ) (hm : 0 < m) : ∀ (f r0 r1 t0 t1 : ℕ), r1 ≤ f →
    t0 * a ≡ r0 [MOD m] → t1 * a ≡ r1 [MOD m] →
    invAux m f r0 r1 t0 t1 * a ≡ Nat.gcd r0 r1 [MOD m] := by
  intro f
  induction f with
  | zero =>
    intro r0 r1 t0 t1 hr h0 _
    have : r1 = 0 := by omega
    subst this
    simpa [invAux] using h0
  | succ f ih =>
    intro r0 r1 t0 t1 hr h0 h1
    unfold invAux
    by_cases hz : r1 = 0
    · subst hz
      simpa using h0
    · have hb : r1.beq 0 = false := by
        rw [Bool.eq_false_iff]; intro h; exact hz (Nat.eq_of_beq_eq_true h)
      rw [hb, Bool.cond_false]
      have hlt : r0 % r1 < r1 := Nat.mod_lt _ (Nat.pos_of_ne_zero hz)
      have hg : Nat.gcd r0 r1 = Nat.gcd r1 (r0 % r1) := by
        rw [Nat.gcd_comm r0 r1, Nat.gcd_rec r1 r0, Nat.gcd_comm]
      rw [hg]
      refine ih r1 (r0 % r1) t1 _ (by omega) h1 ?_
      set q := r0 / r1 with hq
      have hqm : (q * t1) % m ≤ m := (Nat.mod_lt _ hm).le
      -- cancel `q * r1` on both sides
      apply Nat.ModEq.add_right_cancel' (q * r1)
      have hR : r0 % r1 + q * r1 = r0 := by
        rw [hq, mul_comm]; exact Nat.mod_add_div r0 r1
      rw [hR]
      have e1 : (t0 + (m - q * t1 % m)) % m * a + q * r1
          ≡ (t0 + (m - q * t1 % m)) * a + q * (t1 * a) [MOD m] :=
        ((Nat.mod_modEq _ _).mul_right a).add (h1.symm.mul_left q)
      have e2 : (t0 + (m - q * t1 % m)) * a + q * (t1 * a)
          = t0 * a + ((m - q * t1 % m) + q * t1) * a := by ring
      have e3 : (m - q * t1 % m) + q * t1 ≡ 0 [MOD m] := by
        have : (m - q * t1 % m) + q * t1 ≡ (m - q * t1 % m) + q * t1 % m [MOD m] :=
          (Nat.ModEq.refl _).add (Nat.mod_modEq _ _).symm
        refine this.trans ?_
        rw [Nat.sub_add_cancel hqm]
        simp [Nat.ModEq]
      have e4 : t0 * a + ((m - q * t1 % m) + q * t1) * a ≡ r0 + 0 * a [MOD m] :=
        h0.add (e3.mul_right a)
      rw [e2] at e1
      simpa using e1.trans e4

theorem invMod_spec {a m : ℕ} (hm : 0 < m) (h : Nat.Coprime a m) :
    invMod a m * a % m = 1 % m := by
  have h0 : 0 * a ≡ m [MOD m] := by simp [Nat.ModEq]
  have h1 : 1 * a ≡ a % m [MOD m] := by rw [one_mul]; exact (Nat.mod_modEq a m).symm
  have := invAux_spec a m hm m m (a % m) 0 1 (Nat.mod_lt _ hm).le h0 h1
  have hg : Nat.gcd m (a % m) = 1 := by
    rw [Nat.gcd_comm, ← Nat.gcd_rec, Nat.gcd_comm]; exact h
  rw [hg] at this
  exact this

/-! ## The CRT combination -/

/-- CRT combination: the residue modulo `m₁ * m₂` that is `≡ r₁ (mod m₁)` and `≡ r₂ (mod m₂)`,
given `inv` with `inv * m₁ ≡ 1 (mod m₂)`. -/
def crt (m₁ m₂ inv r₁ r₂ : ℕ) : ℕ :=
  Nat.add r₁ (Nat.mul m₁ (Nat.mod (Nat.mul inv (Nat.add r₂ (Nat.sub m₂ (Nat.mod r₁ m₂)))) m₂))

/-- Readable form of `crt` (which is written with raw `Nat` operations for the kernel). -/
theorem crt_eq (m₁ m₂ inv r₁ r₂ : ℕ) :
    crt m₁ m₂ inv r₁ r₂ = r₁ + m₁ * ((inv * (r₂ + (m₂ - r₁ % m₂))) % m₂) := rfl

theorem crt_modEq_left (m₁ m₂ inv r₁ r₂ : ℕ) : crt m₁ m₂ inv r₁ r₂ ≡ r₁ [MOD m₁] := by
  rw [crt_eq]
  simp [Nat.ModEq]

theorem crt_modEq_right {m₁ m₂ inv : ℕ} (hm₂ : 0 < m₂) (hinv : inv * m₁ % m₂ = 1 % m₂)
    (r₁ r₂ : ℕ) : crt m₁ m₂ inv r₁ r₂ ≡ r₂ [MOD m₂] := by
  rw [crt_eq]
  set c := r₂ + (m₂ - r₁ % m₂) with hc
  have hlt : r₁ % m₂ < m₂ := Nat.mod_lt _ hm₂
  have h1 : m₁ * ((inv * c) % m₂) ≡ m₁ * (inv * c) [MOD m₂] := (Nat.mod_modEq _ _).mul_left _
  have h2 : m₁ * (inv * c) = (inv * m₁) * c := by ring
  have h3 : inv * m₁ ≡ 1 [MOD m₂] := hinv
  have h4 : m₁ * ((inv * c) % m₂) ≡ c [MOD m₂] := by
    rw [h2] at h1
    simpa using h1.trans (h3.mul_right c)
  have h5 : r₁ + m₁ * ((inv * c) % m₂) ≡ r₁ % m₂ + c [MOD m₂] :=
    (Nat.mod_modEq _ _).symm.add h4
  refine h5.trans ?_
  have e : r₁ % m₂ + c = r₂ + m₂ := by rw [hc]; omega
  rw [e]
  simp [Nat.ModEq]

theorem crt_lt {m₁ m₂ : ℕ} (inv : ℕ) {r₁ : ℕ} (r₂ : ℕ) (h₁ : r₁ < m₁) (hm₂ : 0 < m₂) :
    crt m₁ m₂ inv r₁ r₂ < m₁ * m₂ := by
  rw [crt_eq]
  have ht : (inv * (r₂ + (m₂ - r₁ % m₂))) % m₂ ≤ m₂ - 1 :=
    Nat.le_sub_one_of_lt (Nat.mod_lt _ hm₂)
  calc r₁ + m₁ * ((inv * (r₂ + (m₂ - r₁ % m₂))) % m₂)
      ≤ r₁ + m₁ * (m₂ - 1) := Nat.add_le_add_left (Nat.mul_le_mul_left _ ht) _
    _ < m₁ + m₁ * (m₂ - 1) := Nat.add_lt_add_right h₁ _
    _ = m₁ * m₂ := by
        obtain ⟨n, rfl⟩ : ∃ n, m₂ = n + 1 := ⟨m₂ - 1, by omega⟩
        simp [Nat.mul_succ, Nat.add_comm]

theorem coprime_of_inv {m₁ m₂ inv : ℕ} (hinv : inv * m₁ % m₂ = 1 % m₂) : Nat.Coprime m₁ m₂ := by
  have hg1 : Nat.gcd m₁ m₂ ∣ m₂ := Nat.gcd_dvd_right _ _
  have hg2 : Nat.gcd m₁ m₂ ∣ inv * m₁ := (Nat.gcd_dvd_left _ _).mul_left _
  have hg3 : Nat.gcd m₁ m₂ ∣ 1 % m₂ := by
    rw [← hinv]; exact (Nat.dvd_mod_iff hg1).mpr hg2
  have hg4 : Nat.gcd m₁ m₂ ∣ 1 := (Nat.dvd_mod_iff hg1).mp hg3
  exact Nat.dvd_one.mp hg4

/-- Two congruences determine the congruence class modulo the product. -/
theorem modEq_crt {m₁ m₂ inv : ℕ} (hm₂ : 0 < m₂) (hinv : inv * m₁ % m₂ = 1 % m₂)
    {x r₁ r₂ : ℕ} (h₁ : x ≡ r₁ [MOD m₁]) (h₂ : x ≡ r₂ [MOD m₂]) :
    x ≡ crt m₁ m₂ inv r₁ r₂ [MOD m₁ * m₂] :=
  (Nat.modEq_and_modEq_iff_modEq_mul (coprime_of_inv hinv)).mp
    ⟨h₁.trans (crt_modEq_left m₁ m₂ inv r₁ r₂).symm,
     h₂.trans (crt_modEq_right hm₂ hinv r₁ r₂).symm⟩

/-- `x % (m₁ * m₂)` is the CRT combination of `x % m₁` and `x % m₂`. -/
theorem mod_mul_eq_crt {m₁ m₂ inv : ℕ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂)
    (hinv : inv * m₁ % m₂ = 1 % m₂) (x : ℕ) :
    x % (m₁ * m₂) = crt m₁ m₂ inv (x % m₁) (x % m₂) := by
  have h := modEq_crt hm₂ hinv (Nat.mod_modEq x m₁).symm (Nat.mod_modEq x m₂).symm
  have hlt := crt_lt inv (x % m₂) (Nat.mod_lt x hm₁) hm₂
  have h' : x % (m₁ * m₂) = crt m₁ m₂ inv (x % m₁) (x % m₂) % (m₁ * m₂) := h
  rwa [Nat.mod_eq_of_lt hlt] at h'

/-- All CRT combinations of a list of residues mod `m₁` with a list of residues mod `m₂`. -/
def crtList (m₁ m₂ inv : ℕ) (L₁ L₂ : List ℕ) : List ℕ :=
  L₁.flatMap fun r₁ => L₂.map fun r₂ => crt m₁ m₂ inv r₁ r₂

theorem mem_crtList {m₁ m₂ inv : ℕ} {L₁ L₂ : List ℕ} {r₁ r₂ : ℕ} (h₁ : r₁ ∈ L₁) (h₂ : r₂ ∈ L₂) :
    crt m₁ m₂ inv r₁ r₂ ∈ crtList m₁ m₂ inv L₁ L₂ := by
  unfold crtList
  exact List.mem_flatMap.mpr ⟨r₁, h₁, List.mem_map.mpr ⟨r₂, h₂, rfl⟩⟩

/-- Specialisation of `crtList` to a two-element second list, as a direct `List.rec`
(fast in the kernel): each `r₁ ∈ L` yields `crt r₁ a` and `crt r₁ b`. -/
def crtPair (m₁ m₂ inv a b : ℕ) (L : List ℕ) : List ℕ :=
  List.rec (motive := fun _ => List ℕ) []
    (fun r₁ _ ih => crt m₁ m₂ inv r₁ a :: crt m₁ m₂ inv r₁ b :: ih) L

theorem crtPair_eq_crtList (m₁ m₂ inv a b : ℕ) (L : List ℕ) :
    crtPair m₁ m₂ inv a b L = crtList m₁ m₂ inv L [a, b] := by
  induction L with
  | nil => rfl
  | cons r₁ tl ih =>
    change crt m₁ m₂ inv r₁ a :: crt m₁ m₂ inv r₁ b :: crtPair m₁ m₂ inv a b tl = _
    rw [ih]
    simp [crtList]

/-- **CRT gluing (certificate form).** -/
theorem Complete.crt {m₁ m₂ inv a : ℕ} {L₁ L₂ : List ℕ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂)
    (hinv : inv * m₁ % m₂ = 1 % m₂) (h₁ : Complete m₁ a L₁) (h₂ : Complete m₂ a L₂) :
    Complete (m₁ * m₂) a (crtList m₁ m₂ inv L₁ L₂) := by
  intro x hx
  rw [mod_mul_eq_crt hm₁ hm₂ hinv x]
  exact mem_crtList (h₁ x (hx.of_dvd (Dvd.intro _ rfl))) (h₂ x (hx.of_dvd (Dvd.intro_left _ rfl)))

/-- **CRT gluing (Goal 4).** If `m₁`, `m₂` are coprime and every solution of `x² ≡ a` modulo
`mᵢ` is congruent to some element of `Lᵢ` modulo `mᵢ`, then every solution modulo `m₁ * m₂` is
congruent modulo `m₁ * m₂` to one of the CRT combinations. -/
theorem crt_glue {m₁ m₂ a : ℕ} {L₁ L₂ : List ℕ} (hcop : Nat.Coprime m₁ m₂) (hm₂ : 0 < m₂)
    (h₁ : ∀ x : ℕ, x ^ 2 ≡ a [MOD m₁] → ∃ r ∈ L₁, x ≡ r [MOD m₁])
    (h₂ : ∀ x : ℕ, x ^ 2 ≡ a [MOD m₂] → ∃ r ∈ L₂, x ≡ r [MOD m₂]) :
    ∀ x : ℕ, x ^ 2 ≡ a [MOD m₁ * m₂] →
      ∃ r ∈ crtList m₁ m₂ (invMod m₁ m₂) L₁ L₂, x ≡ r [MOD m₁ * m₂] := by
  intro x hx
  obtain ⟨r₁, hr₁, hx₁⟩ := h₁ x (hx.of_dvd (Dvd.intro _ rfl))
  obtain ⟨r₂, hr₂, hx₂⟩ := h₂ x (hx.of_dvd (Dvd.intro_left _ rfl))
  exact ⟨_, mem_crtList hr₁ hr₂, modEq_crt hm₂ (invMod_spec hm₂ hcop) hx₁ hx₂⟩

end Exp7.Roots
