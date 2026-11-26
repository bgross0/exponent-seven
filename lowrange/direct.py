"""Direct computation below B = 10^5: every prime q = 3 mod 4, q < B, with class group of exponent
dividing 7.  Class numbers by counting reduced forms.

Usage:  python3 lowrange/direct.py        (about 3 minutes)
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from sympy import primerange
from forms import exponent_divides_7

B = 10**5
KNOWN = [71, 151, 223, 251, 463, 467, 487, 587, 811, 827, 859, 1163, 1171, 1483, 1523, 1627, 1787,
         1987, 2011, 2083, 2179, 2251, 2467, 2707, 3019, 3067, 3187, 3907, 4603, 5107, 5923, 63499,
         118843]

one, seven = [], []
n = 0
for q in primerange(3, B):
    if q % 4 != 3:
        continue
    n += 1
    ok, h = exponent_divides_7(q)
    if ok:
        (one if h == 1 else seven).append((q, h))
        print("q=%d h=%d" % (q, h), flush=True)
print("primes q = 3 mod 4 below %d examined: %d" % (B, n))
print("class number 1:", [q for q, _ in one])
print("exponent 7:", [q for q, _ in seven])
print("exponent 7 with h = 49:", [q for q, h in seven if h == 49])
assert [q for q, _ in one] == [3, 7, 11, 19, 43, 67, 163]
assert [q for q, _ in seven] == [q for q in KNOWN if q < B]
print("PASS: below %d the exponent-7 fields are exactly the %d known ones" % (B, len(seven)))
