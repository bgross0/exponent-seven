# Exclusion at the least split prime

27 November 2026. Native Lean 4.37.0-rc1.

Assume `GRHPrimeConductor`. Let `q` be a prime congruent to 3 modulo 4, with
`q >= QLOW = 310000000000000000000`, and let `p` be its least split prime.
For every odd `n <= 7`, Lean proves:

```text
There are no natural x,y with y >= 1 and 4*p^n = x^2 + q*y^2.
The ideal (p, omega-t)^n is not principal for any root t modulo p.
The class of (p, omega-t) raised to n is not 1.
```

In particular, that specific ideal class cannot have order seven. There is no
upper bound on `q`, no assumption that the whole class group has exponent seven,
and no unproved search assumption in the final applied statements.

This formalizes the small-odd-power exclusion underlying the paper's Corollary C.
It is a strengthening of the earlier formal classification statements in the
information it supplies about an individual ideal class, not a claim of a new
number-theoretic result beyond the paper.

## Exact final statements

The arithmetic exclusion is
`Exp7.LeastSplit.no_norm_odd_le_seven_GRH` in
[LeastSplitFull.lean](../../Exp7Lean/Exp7Lean/Arithmetic/LeastSplitFull.lean):

```lean
theorem LeastSplit.no_norm_odd_le_seven_GRH (hGRH : GRHPrimeConductor)
    {q p n : Nat} (h : LeastSplit q p) (hq : q.Prime) (h4 : q % 4 = 3)
    (hlo : QLOW <= q) (hn : Odd n) (hn7 : n <= 7) {x y : Nat} (hy : 1 <= y) :
    4 * p ^ n ≠ x ^ 2 + q * y ^ 2
```

`Exp7.exists_least_split_class_surviving_odd_powers_GRH` additionally proves
existence of `p` and a root `t`, and identifies the surviving element using the
existing `classOf` in Mathlib's `ClassGroup (OK q)`. Thus the exclusion is not
vacuous: the least split prime and its root ideal exist in the stated range.

`Exp7.LeastSplit.class_order_ne_seven_GRH` states the individual class-order
conclusion directly.

The native statements retain GRH as an explicit hypothesis. This addition does
not import or revalidate the external GRH proof.

## Proof chain

1. [PrincipalPower.lean](../../Exp7Lean/Exp7Lean/Arithmetic/PrincipalPower.lean)
   extracts a nonrational norm witness from principality of one ideal's odd
   power. The norm calculation follows the existing Step 1 proof, but works at
   an arbitrary odd exponent and does not need a class-group exponent assumption.
   Oddness rules out a rational generator using prime multiplicity.
2. [LeastSplit.lean](../../Exp7Lean/Exp7Lean/Arithmetic/LeastSplit.lean) uses the
   single inequality `q <= 4*p^7` at the least split prime through all six
   bootstrap rows. Minimality ensures that each row's split prime bounds `p`.
   This puts `p` between 701 and 4297 and gives exactly the Jacobi conditions and
   ladder bounds consumed by the existing `SearchHigh` theorem.
3. For powers 1, 3, and 5 in the bounded range, the first certificate row gives
   `p <= 6361`. Then `q <= 4*p^n <= 4*6361^5 < QLOW`, a contradiction.
4. Above `QTOP = 10^32`, the existing finite bridge and dyadic estimates supply
   a split prime `l` with `4*l^7 < q`. Minimality gives `p <= l`, contradicting
   any nonzero norm witness at an exponent at most seven.
5. [LeastSplitClass.lean](../../Exp7Lean/Exp7Lean/Arithmetic/LeastSplitClass.lean)
   joins the arithmetic exclusion to the individual ideal and class. The full
   module supplies `Exp7.searchHigh` from the 465 existing kernel certificates.
   Neither the low search nor the 33-field classification is used to deduce the
   new exclusions.

The new code does not change `Step1.lean`, the existing tail proofs, the search
checker, or any per-prime certificate.

## Remaining distinction from the full wording of Corollary C

To conclude that the class order is **at least nine**, one also needs that the
order is odd. The paper uses genus theory for this. The existing genus module
proves a different direction: odd exponent forces a prime discriminant.

`LeastSplit.nine_le_class_order_of_odd` proves the numeric lower bound with
oddness as an explicit input. This addition does not claim to have formalized
the converse genus-theory fact. The unconditional-in-oddness conclusions above
are the exclusions of powers 1, 3, 5, and 7, and of order seven.

## Validation and reproduction

The five new modules, the arithmetic umbrella, and both project root imports
were compiled with the pinned native toolchain. The final theorem's axiom
reports contain only `propext`, `Classical.choice`, and `Quot.sound`. These axiom
reports do not erase its explicit GRH hypothesis.

The kernel replay checks the four theorem modules against their compiled
imports. The existing search certificate objects are reused; this is not a
fresh evaluation of the 465 high certificates or the 401 low certificates.
[Commands, source hashes, and exit codes](kernel-replay.json) ·
[Replay log](kernel-replay.log)

From `Exp7Lean/`, when the existing high-search certificate objects have already
been checked and are available:

```sh
lake build Exp7Lean.Arithmetic.LeastSplitClass Exp7Lean.Arithmetic.LeastSplitExamples
lake env lean -o .lake/build/lib/lean/Exp7Lean/Arithmetic/LeastSplitFull.olean \
  Exp7Lean/Arithmetic/LeastSplitFull.lean
lake env leanchecker -v Exp7Lean.Arithmetic.PrincipalPower
lake env leanchecker -v Exp7Lean.Arithmetic.LeastSplit
lake env leanchecker -v Exp7Lean.Arithmetic.LeastSplitClass
lake env leanchecker -v Exp7Lean.Arithmetic.LeastSplitFull
```

A fresh checkout will also need to build the existing dependencies and high
certificates, using `lake build Exp7Lean.Arithmetic.LeastSplitFull` with resources
appropriate for the certificate run. The direct compile above reuses the
checked objects even when their Lake build traces are absent. A full-target
build in this checkout started rebuilding those old certificates and was stopped;
no successful fresh certificate run is claimed here.

The final applied module is imported by `Exp7Full`; the version
with the high-search input explicit is imported by the default `Exp7Lean`
target. No new Lean 4.35 integration result is claimed.

[LeastSplitExamples.lean](../../Exp7Lean/Exp7Lean/Arithmetic/LeastSplitExamples.lean)
checks the positive control `q=71, p=2, x=21, y=1`, which shows that the conductor
cutoff cannot be discarded. It also distinguishes a larger split prime from
the least split prime and checks the local ideal-power bridge at exponent one.
