"""Generator of the witness tables (SurvivorData.lean, Survivors.lean, DirectData.lean).

Usage:  python3 gen_tables.py LOWRANGE_DIR OUT_DIR
  LOWRANGE_DIR  directory containing low_survivors.txt and forms.py (read only)
  OUT_DIR       where the three Lean files are written

The functions below are an exact Python model of the Lean checkers in Checker.lean; every table
entry written is first verified against the model. The Lean kernel is the only thing trusted:
nothing in the Lean development depends on this script being correct. Requires sympy.
"""
import sys
sys.dont_write_bytecode = True  # LOWRANGE_DIR is read only: no __pycache__ there
LOW, OUT = sys.argv[1], sys.argv[2]
sys.path.insert(0, LOW)
from sympy import isprime, factorint
from forms import splits, seventh_power_principal

def mask(m):
    r = 0
    for x in range(m):
        r |= 1 << (x*x % m)
    return r
MODS = [3465, 4199, 20677, 64]
MASKS = [(mask(m), m) for m in MODS]

def newt(n, x):
    return (x + (n // x if x else 0)) // 2
def sqrtDown(n, fuel, x):
    while fuel > 0:
        y = newt(n, x)
        if y < x:
            x = y; fuel -= 1
        else:
            return x
    return x
def strictBetween(n, r):
    return r*r < n and n < (r+1)*(r+1)
STAT = {'newton': 0, 'y': 0}
def notSqB(x0, n):
    for mk, m in MASKS:
        if (mk >> (n % m)) & 1 == 0:
            return True
    STAT['newton'] += 1
    return strictBetween(n, sqrtDown(n, 200, x0))
def noSolUp(q, N, m, x0, fuel, y):
    while True:
        if fuel == 0: return False
        if N < q*y*y: return True
        STAT['y'] += 1
        if not (notSqB(x0, N - q*y*y) or (y % m if m else y) == 0):
            return False
        fuel -= 1; y += 1
def noSol(q, l):
    return noSolUp(q, 4*l**7, 0, 2*l**4, 4*l**7 + 1, 1)
def noSolPrim(q, l):
    return noSolUp(q, 4*l**7, l, 2*l**4, 4*l**7 + 1, 1)
def primeB(n):
    if n < 2: return False
    fuel, d = n, 2
    while True:
        if fuel == 0: return False
        if n < d*d: return True
        if n % d == 0: return False
        fuel -= 1; d += 1
def splitsB(q, l):
    if l == 2: return q % 8 == 7
    return pow(l - q % l, l // 2) % l == 1
def witB(q, l):
    return 1 <= q % l and primeB(l) and splitsB(q, l) and (noSol(q, l) if l == 2 else noSolPrim(q, l))
def entryOK(excl, n, e):
    if e == 0: return n in excl
    if n % e == 0: return 1 < e and e < n
    return witB(n, e)

def witness(q, nmax=80):
    """Smallest prime l with witB(q, l)."""
    cnt = 0; l = 2
    while cnt < nmax:
        if l != q and isprime(l) and splits(q, l):
            cnt += 1
            cand = True if l == 2 else not seventh_power_principal(q, l)
            if cand and witB(q, l):
                return l
        l += 1
    raise ValueError("no witness for %d" % q)

def entry(excl, n):
    if n in excl: return 0
    if not isprime(n): return min(factorint(n))
    return witness(n)

def fmt_list(xs, width=100, indent=2):
    lines = []; cur = " " * indent
    for i, x in enumerate(xs):
        t = str(x) + ("," if i + 1 < len(xs) else "")
        if len(cur) + len(t) + 1 > width and cur.strip():
            lines.append(cur.rstrip()); cur = " " * indent
        cur += t + " "
    if cur.strip(): lines.append(cur.rstrip())
    return "[\n" + "\n".join(lines) + "\n]"

# ---- survivors of the low-range search ----
lines = [l.split() for l in open(LOW + '/low_survivors.txt')]
assert all(t[0] == 'S' and len(t) == 5 for t in lines)
qs = [int(t[4]) for t in lines]
assert len(qs) == 6608 == len(set(qs))
excl = [118843]
aux = [entry(excl, q) for q in qs]
assert all(entryOK(excl, q, e) for q, e in zip(qs, aux))
primes = [q for q in qs if isprime(q) and q != 118843]
assert len(primes) == 1922
wit = [aux[qs.index(q)] for q in primes]
assert all(witB(q, l) for q, l in zip(primes, wit))
print("composite", sum(1 for q in qs if not isprime(q)), "primes", len(primes), "y", STAT, "max wit", max(wit), "max factor", max(aux))
d = {'qs': qs, 'aux': aux, 'primes': primes, 'wit': wit}
data = '''import Mathlib.Data.Nat.Notation

/-!
Exponent 7: the survivors of the low-range search (data only).

Generated from `lowrange/low_survivors.txt` (6608 lines `S p x y q`, all `q` distinct).

* `survivorQs`: the 6608 values `q`, in the order of the file.
* `survivorPrimes`: the 1922 prime values other than `118843`, in the same order.
-/

namespace Exp7

set_option maxRecDepth 1000000 in
/-- The 6608 values `q` of the survivors of the low-range search. -/
def survivorQs : List ℕ := %s

set_option maxRecDepth 1000000 in
/-- The 1922 primes among `survivorQs` other than `118843`. -/
def survivorPrimes : List ℕ := %s

end Exp7
''' % (fmt_list(d['qs']), fmt_list(d['primes']))
open(OUT + '/SurvivorData.lean', 'w').write(data)
thm = '''import Exp7Lean.Witness.Checker
import Exp7Lean.Witness.SurvivorData

/-!
Exponent 7: the survivors of the low-range search do not have exponent 7, except `118843`.

For every prime survivor `q ≠ 118843` the table gives a witness: a split prime `l` such that
`4 l^7 = x^2 + q y^2` has no solution with `y ≥ 1`, `l ∤ y`. For every composite survivor the
table gives its least prime factor. The tables are checked by the kernel (`decide +kernel`, no
`native_decide`).
-/

namespace Exp7

set_option maxRecDepth 1000000 in
/-- Witnesses for `survivorPrimes`, in the same order. -/
def survivorWit : List ℕ := %s

set_option maxRecDepth 1000000 in
/-- Entries for `survivorQs`, in the same order: `0` for `118843`, the least prime factor of a
composite `q`, a witness for a prime `q`. -/
def survivorAux : List ℕ := %s

theorem survivorWit_ok : checkZip [] survivorPrimes survivorWit = true := by decide +kernel

theorem survivorAux_ok : checkZip [118843] survivorQs survivorAux = true := by decide +kernel

/-- No prime survivor other than `118843` has class group of exponent 7. -/
theorem survivors_not_isExp7 : ∀ q ∈ survivorPrimes, ¬ IsExp7 q := by
  intro q hq hE
  have := mem_excl_of_checkZip _ _ survivorWit_ok q hq hE
  simp at this

/-- The only survivor with class group of exponent 7 is `118843`. (The hypothesis `q.Prime` is
not needed: `IsExp7 q` contains it.) -/
theorem survivorQs_isExp7 : ∀ q ∈ survivorQs, q.Prime → IsExp7 q → q = 118843 := by
  intro q hq _ hE
  have := mem_excl_of_checkZip _ _ survivorAux_ok q hq hE
  simpa using this

/-- The field `searchLow` of `ComputedLow`, from `survivorQs_isExp7` and the fact that is not
proved here: the completeness of the search, i.e. every `q` satisfying the conditions of the
search is in `survivorQs`. -/
theorem searchLow_of_mem
    (hmem : ∀ p, p.Prime → 3 ≤ p → p < 2760 → ∀ x y q : ℕ, 1 ≤ y → ¬ p ∣ y →
      4 * p ^ 7 = x ^ 2 + q * y ^ 2 → QloFull p ≤ q → q < QLOW → q %% 8 = 3 →
      (∀ l, l.Prime → 3 ≤ l → l < p → jacobiSym (-(q : ℤ)) l = -1) → q.Prime →
      q ∈ survivorQs) :
    ∀ p, p.Prime → 3 ≤ p → p < 2760 → ∀ x y q : ℕ, 1 ≤ y → ¬ p ∣ y →
      4 * p ^ 7 = x ^ 2 + q * y ^ 2 → QloFull p ≤ q → q < QLOW → q %% 8 = 3 →
      (∀ l, l.Prime → 3 ≤ l → l < p → jacobiSym (-(q : ℤ)) l = -1) →
      q.Prime → IsExp7 q → q = 118843 := by
  intro p hp hp3 hplt x y q hy hpy he hlo hhi h8 hin hq hE
  exact survivorQs_isExp7 q (hmem p hp hp3 hplt x y q hy hpy he hlo hhi h8 hin hq) hq hE

end Exp7
''' % (fmt_list(d['wit']), fmt_list(d['aux']))
open(OUT + '/Survivors.lean', 'w').write(thm)

# ---- direct range q < 10^5 ----
known=[71, 151, 223, 251, 463, 467, 487, 587, 811, 827, 859, 1163, 1171, 1483,
  1523, 1627, 1787, 1987, 2011, 2083, 2179, 2251, 2467, 2707, 3019, 3067, 3187, 3907, 4603, 5107,
  5923, 63499, 118843]
excl = known + [3, 7, 11, 19, 43, 67, 163]
ns = list(range(3, 10**5, 4))
assert len(ns) == 25000
tab = [entry(excl, n) for n in ns]
STAT['y'] = 0; STAT['newton'] = 0
assert all(entryOK(excl, n, e) for n, e in zip(ns, tab))
nw = sum(1 for n, e in zip(ns, tab) if e and n % e)
print("witness entries", nw, "zero entries", tab.count(0), "composite", 25000 - nw - tab.count(0), STAT, "max wit", max(e for n, e in zip(ns, tab) if e and n % e))
data = '''import Mathlib.Data.Nat.Notation

/-!
Exponent 7: the table for the direct range `q < 10^5` (data only).

`directTable` has 25000 entries; entry `k` belongs to `n = 3 + 4k`:
* `0` if `n` is one of the 32 primes below `10^5` of the list `known` or one of the seven primes
  `3, 7, 11, 19, 43, 67, 163` (class number one);
* the least prime factor of `n` if `n` is composite;
* otherwise (4769 primes) a witness: a prime `l` that splits in `ℚ(√-n)` such that
  `4 l^7 = x^2 + n y^2` has no solution with `y ≥ 1` (`l = 2`), resp. with `y ≥ 1`, `l ∤ y`
  (`l` odd).
-/

namespace Exp7

set_option maxRecDepth 1000000 in
/-- The table for `n = 3, 7, 11, …, 99999`. -/
def directTable : List ℕ := %s

end Exp7
''' % fmt_list(tab)
open(OUT + '/DirectData.lean', 'w').write(data)
