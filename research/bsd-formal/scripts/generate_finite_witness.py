#!/usr/bin/env python3
"""Render exact public E433 certificate data as kernel-checkable Lean assertions.

This renderer is not trusted: the resulting Lean theorems check the literal
data, and a separate source digest identifies which input was rendered.
It makes no assertion identifying numerical class polynomials with CM objects.
"""
from pathlib import Path
import hashlib
import json
from math import comb

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT.parent / "bsd-localization/second_theta/certificate.json"
EXPECTED_INPUT_SHA256 = "5e533e6f0ea31a2c59293448a5f2f8077de512b9e3c50e7420f6eafd2a699898"


def lean(value):
    if isinstance(value, list):
        return "[" + ", ".join(lean(v) for v in value) + "]"
    if isinstance(value, tuple):
        return "(" + ", ".join(lean(v) for v in value) + ")"
    return str(value)


def main():
    raw = SOURCE.read_bytes()
    if hashlib.sha256(raw).hexdigest() != EXPECTED_INPUT_SHA256:
        raise ValueError("The E433 input certificate differs from its reviewed source")
    data = json.loads(raw)
    ss = data["supersingular"]
    cm7, cm140 = data["CM"]
    modulus = 433**4
    declarations = {
        "vertices433": ("List Pair", [tuple(v) for v in ss["supersingular_j"]]),
        "matrix433": ("List (List ℕ)", ss["T2_matrix"]),
        "eigenfunction433": ("List ℤ", ss["primitive_eigenfunction"]),
        "cm433Roots": ("List Pair", [tuple(a % modulus for a in r) for r in cm140["root_lifts"]]),
        "cm433Graph": ("List (List ℕ)", cm140["horizontal_T2_graph"]),
        "cm433Cycle": ("List ℕ", cm140["generator_cycle"]),
        "cm433Values": ("List ℤ", cm140["CM_values"]),
        "cm71Roots433": ("List Pair", [tuple(a % modulus for a in r) for r in cm7["root_lifts"]]),
        "cm71Cycle433": ("List ℕ", cm7["generator_cycle"]),
        "cm71Graph433": ("List (List ℕ)", cm7["horizontal_T2_graph"]),
        "cm71Values433": ("List ℤ", cm7["CM_values"]),
        "deuringRoots433": ("List Pair", [tuple(r) for r in ss["deuring_roots"]]),
        "deuringCoefficients433": ("List Pair", [(comb(216, k)**2 % 433, 0) for k in range(217)]),
    }
    header = r'''import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Perm.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.Choose.Basic

/-!+# Exact finite arithmetic in the E433 certificate

The assertions below concern the displayed integer data and congruences.
They do not identify these data with a Hilbert class polynomial, a quaternionic
automorphic form, a Selmer class, or an infinite arithmetic theta function.
Those identifications require separate arithmetic theorems.

Every computational proof uses kernel reduction; no native evaluator is used.
-/

namespace BSDFiniteWitness

set_option maxRecDepth 20000
set_option maxHeartbeats 0

abbrev Pair := ℕ × ℕ

/-- Multiplication of coordinates with `u^2 = 5`, reduced modulo `m`. -/
def mulMod (m : ℕ) (x y : Pair) : Pair :=
  ((x.1 * y.1 + 5 * x.2 * y.2) % m,
   (x.1 * y.2 + x.2 * y.1) % m)

def addMod (m : ℕ) (x y : Pair) : Pair :=
  ((x.1 + y.1) % m, (x.2 + y.2) % m)

def scaleMod (m : ℕ) (c : ℤ) (x : Pair) : Pair :=
  ((c * (x.1 : ℤ) % (m : ℤ)).toNat,
   (c * (x.2 : ℤ) % (m : ℤ)).toNat)

def linMod (m : ℕ) (ts : List (ℤ × Pair)) : Pair :=
  ts.foldl (fun acc t => addMod m acc (scaleMod m t.1 t.2)) (0, 0)

/-- Coefficients, in ascending order, of the classical Phi_2(x,Y). -/
def phi2Coefficients (m : ℕ) (x : Pair) : List Pair :=
  let x2 := mulMod m x x
  let x3 := mulMod m x2 x
  [linMod m [(1,x3),(-162000,x2),(8748000000,x),(-157464000000000,(1,0))],
   linMod m [(1488,x2),(40773375,x),(8748000000,(1,0))],
   linMod m [(-1,x2),(1488,x),(-162000,(1,0))], (1,0)]

def evaluateMod (m : ℕ) (cs : List Pair) (x : Pair) : Pair :=
  cs.foldr (fun c acc => addMod m (mulMod m acc x) c) (0, 0)

def phi2Mod (m : ℕ) (x y : Pair) : Pair :=
  evaluateMod m (phi2Coefficients m x) y

def reduce433 (x : Pair) : Pair := (x.1 % 433, x.2 % 433)

def productFromRoots (m : ℕ) (roots : List Pair) : List Pair :=
  roots.foldl (fun cs x =>
    List.zipWith (addMod m)
      (cs.map (fun c => mulMod m c (scaleMod m (-1) x)) ++ [(0,0)])
      ((0,0) :: cs)) [(1,0)]

def deuringJEquation (r j : Pair) : Bool :=
  let r2 := mulMod 433 r r
  let omr := addMod 433 (1,0) (scaleMod 433 (-1) r)
  let denominator := mulMod 433 r2 (mulMod 433 omr omr)
  let u := addMod 433 (addMod 433 r2 (scaleMod 433 (-1) r)) (1,0)
  let numerator := scaleMod 433 256 (mulMod 433 (mulMod 433 u u) u)
  denominator != (0,0) && mulMod 433 j denominator == numerator

'''
    text = header + "-- Input certificate SHA-256: " + hashlib.sha256(raw).hexdigest() + "\n\n"
    for name, (ty, val) in declarations.items():
        text += f"def {name} : {ty} :=\n  {lean(val)}\n\n"
    text += r'''
theorem prime433 : Nat.Prime 433 := by decide +kernel

theorem nonresidue5_at433 : ∀ a : Fin 433, a.val * a.val % 433 ≠ 5 := by
  decide +kernel

theorem vertex_table433 : vertices433.length = 36 ∧ vertices433.Nodup ∧
    (∀ x ∈ vertices433, x.1 < 433 ∧ x.2 < 433) := by
  decide +kernel

theorem matrix433_shape : matrix433.length = 36 ∧
    (∀ row ∈ matrix433, row.length = 36 ∧ row.sum = 3) := by
  decide +kernel

/-- An exact integral eigenvector identity, including every matrix row. -/
theorem eigenvector433_identity :
    matrix433.map (fun row =>
      (List.zipWith (fun (n : ℕ) (v : ℤ) => (n : ℤ) * v) row eigenfunction433).sum) =
    eigenfunction433.map Neg.neg := by
  decide +kernel

theorem eigenfunction433_primitive_witness :
    eigenfunction433.length = 36 ∧ (1 : ℤ) ∈ eigenfunction433 := by
  decide +kernel

/-- Each full cubic modular polynomial factors according to its matrix row. -/
theorem matrix433_phi2_factorization : ∀ i : Fin 36,
    productFromRoots 433
      ((vertices433.zip matrix433[i.val]!).flatMap (fun jn => List.replicate jn.2 jn.1)) =
    phi2Coefficients 433 vertices433[i.val]! := by
  decide +kernel

/-- The literal Deuring coefficients equal their defining binomial formula. -/
theorem deuringCoefficients433_correct :
    deuringCoefficients433 = (List.range 217).map (fun k => (((216 : ℕ).choose k)^2 % 433, 0)) := by
  rw [Nat.choose_eq_fast_choose]
  decide +kernel

theorem deuringRoots433_distinct :
    deuringRoots433.length = 216 ∧ deuringRoots433.Nodup ∧
    (∀ x ∈ deuringRoots433, x.1 < 433 ∧ x.2 < 433) := by
  decide +kernel

/-- All 216 distinct listed roots satisfy the degree-216 Deuring polynomial. -/
theorem deuringRoots433_verified :
    deuringRoots433.all (fun x => evaluateMod 433 deuringCoefficients433 x == (0,0)) = true := by
  decide +kernel

theorem deuringRoots433_map_to_vertices :
    deuringRoots433.all (fun x => vertices433.any (deuringJEquation x)) = true := by
  decide +kernel

theorem vertices433_covered_by_deuring :
    vertices433.all (fun j => deuringRoots433.any (fun x => deuringJEquation x j)) = true := by
  decide +kernel

def vertexValue433 (x : Pair) : ℤ :=
  ((vertices433.zip eigenfunction433).find? (fun t => t.1 == x)).map Prod.snd |>.getD 0

/-- The roots in the finite lift table are pairwise distinct modulo 433^4. -/
theorem cm433Roots_distinct : cm433Roots.length = 140 ∧ cm433Roots.Nodup ∧
    (∀ x ∈ cm433Roots, x.1 < 433^4 ∧ x.2 < 433^4) := by
  decide +kernel

theorem cm433Roots_reduce_to_vertices :
    ∀ x ∈ cm433Roots, reduce433 x ∈ vertices433 := by
  decide +kernel

theorem cm433Cycle_permutation : cm433Cycle.Perm (List.range 140) := by
  decide +kernel

theorem cm433Graph_degree_two : cm433Graph.length = 140 ∧
    (∀ row ∈ cm433Graph, row.length = 2 ∧ row.Nodup) := by
  decide +kernel

/-- Completeness as well as correctness of the displayed finite Phi_2 graph. -/
theorem cm433Graph_verified :
    (List.range 140).map (fun i =>
      (List.range 140).filter (fun j =>
        phi2Mod (433^4) cm433Roots[i]! cm433Roots[j]! == (0,0))) = cm433Graph := by
  decide +kernel

theorem cm433Cycle_edges : ∀ i : Fin 140,
    cm433Cycle[(i.val + 1) % 140]! ∈ cm433Graph[cm433Cycle[i.val]!]! := by
  decide +kernel

/-- All 140 weights are derived from the eigenfunction in cycle order. -/
theorem cm433Weights_match :
    cm433Cycle.map (fun i => vertexValue433 (reduce433 cm433Roots[i]!)) = cm433Values := by
  decide +kernel

theorem cm71Cycle_permutation433 : cm71Cycle433.Perm (List.range 7) := by
  decide +kernel

theorem cm71Roots433_distinct : cm71Roots433.length = 7 ∧ cm71Roots433.Nodup ∧
    (∀ x ∈ cm71Roots433, x.1 < 433^4 ∧ x.2 < 433^4) := by
  decide +kernel

theorem cm71Roots433_reduce_to_vertices :
    ∀ x ∈ cm71Roots433, reduce433 x ∈ vertices433 := by
  decide +kernel

theorem cm71Graph433_verified :
    (List.range 7).map (fun i =>
      (List.range 7).filter (fun j =>
        phi2Mod (433^4) cm71Roots433[i]! cm71Roots433[j]! == (0,0))) = cm71Graph433 := by
  decide +kernel

theorem cm71Graph433_degree_two : cm71Graph433.length = 7 ∧
    (∀ row ∈ cm71Graph433, row.length = 2 ∧ row.Nodup) := by
  decide +kernel

theorem cm71Cycle433_edges : ∀ i : Fin 7,
    cm71Cycle433[(i.val + 1) % 7]! ∈ cm71Graph433[cm71Cycle433[i.val]!]! := by
  decide +kernel

theorem cm71Weights_match433 :
    cm71Cycle433.map (fun i => vertexValue433 (reduce433 cm71Roots433[i]!)) =
      [1, 1, -1, 0, 0, 0, -1] := by
  decide +kernel

end BSDFiniteWitness
'''
    (ROOT / "BSDFiniteWitness.lean").write_text(text)
    print(json.dumps({"input_sha256": hashlib.sha256(raw).hexdigest(),
                      "output_sha256": hashlib.sha256(text.encode()).hexdigest(),
                      "output": "BSDFiniteWitness.lean"}, indent=2))


if __name__ == "__main__":
    main()
