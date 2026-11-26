"""Classify the survivors of lowsearch (q >= 10^5).

A survivor (p, x, y, q) satisfies the necessary conditions for: q prime, q = 3 mod 4, p the least
split prime of Q(sqrt(-q)), and P^7 principal.  For each distinct q:
  * discard q if it is not prime;
  * consistency: P^7 must be principal according to form reduction (independent of the search);
  * look for a witness: a split prime l with L^7 not principal.  A witness shows the exponent does
    not divide 7;
  * if the first 12 split primes give no witness, compute the class group (exponent_divides_7).

Usage:  python3 lowrange/classify.py lowrange/run/p*.log
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from sympy import isprime
from forms import splits, seventh_power_principal, split_primes, exponent_divides_7

NWIT = 12
surv = {}
nlines = 0; nprimes = 0
for path in sys.argv[1:]:
    for line in open(path):
        t = line.split()
        if not t:
            continue
        if t[0] == "S":
            nlines += 1
            p, x, y, q = map(int, t[1:])
            assert 4*p**7 == x*x + q*y*y and y % p != 0 and q % 8 == 3
            surv.setdefault(q, []).append((p, x, y))
        elif t[0] == "P":
            nprimes += 1
            assert t[-2] == "surv"

print("log files %d, primes %d, survivor lines %d, distinct q %d" % (len(sys.argv) - 1, nprimes, nlines, len(surv)))
composite = 0; rejected = 0; accepted = []; hist = {}
for q in sorted(surv):
    if not isprime(q):
        composite += 1
        continue
    for p, x, y in surv[q]:
        # the search claims: p splits, every smaller prime is inert, and P^7 is principal
        assert splits(q, p) and not any(splits(q, l) for l in split_primes(q, 1) if l < p)
        assert split_primes(q, 1)[0] == p, (q, p)
        assert seventh_power_principal(q, p), (q, p)
    wit = None
    for i, l in enumerate(split_primes(q, NWIT)):
        if not seventh_power_principal(q, l):
            wit = (i, l)
            break
    if wit is not None:
        rejected += 1
        hist[wit[0]] = hist.get(wit[0], 0) + 1
        continue
    ok, h = exponent_divides_7(q)
    print("no witness among %d split primes: q=%d  class number %d  exponent divides 7: %s" % (NWIT, q, h, ok))
    if ok:
        accepted.append((q, h))
    else:
        rejected += 1
print("composite q: %d   prime q rejected by a witness or by the class group: %d" % (composite, rejected))
print("index of the witness among the split primes (0 = least):", dict(sorted(hist.items())))
print("ACCEPTED (exponent divides 7):", accepted)
