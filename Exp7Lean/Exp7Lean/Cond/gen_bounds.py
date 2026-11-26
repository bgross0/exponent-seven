"""Generate Exp7Lean/Cond/RobustBounds.lean: the bound `QloR`, the list `excludedPrimes` of the
primes `701 ≤ p ≤ 4297` with `4 p^7 < QloR p`, and the theorems using the 26 threshold rows.
The list is recomputed and compared in the Lean kernel (`mem_excludedPrimes`), so this script is
not trusted.

Usage (from the workspace root):  python3 Exp7Lean/Cond/gen_bounds.py
"""
import re

QLOW = 310000000000000000000
src = open("Exp7Lean/Basic.lean").read()
i = src.index("def bootstrapRows"); j = src.index("def allRows")
allrows = [(int(a), int(b)) for a, b in re.findall(r"⟨(\d+), (\d+)⟩", src[i:j])]
assert len(allrows) == 51
rob = []
for line in open("sieve-reduction/robust26.txt"):
    t = line.split()
    if t:
        rob.append((int(t[0]), int(t[2]), int(t[1])))


def Qlo(p): return max([QLOW] + [Q for Q, X in allrows if X <= p])
def QloRobust(p): return max([0] + [Q for T, Q, X in rob if T <= p])
def QloR(p): return max(Qlo(p), QloRobust(p))


primes = [n for n in range(2, 4298) if all(n % d for d in range(2, int(n**0.5) + 1))]
ex = [p for p in primes if 701 <= p and 4*p**7 < QloR(p)]
assert ex == [p for p in primes if 701 <= p and 4*p**7 < QloRobust(p)]
lines = []
for c in range(0, len(ex), 16):
    lines.append("  " + ", ".join(str(p) for p in ex[c:c+16]))
body = open("Exp7Lean/Cond/RobustBounds.template").read()
body = body.replace("EXLIST", ",\n".join(lines)).replace("NEX", str(len(ex)))
open("Exp7Lean/Cond/RobustBounds.lean", "w").write(body)
print("wrote RobustBounds.lean;", len(ex), "excluded primes:", ex[:6], "...", ex[-1])
