"""Certificate generator for Exp7.Roots (Exp7Lean/Sieve/RootsCert.lean), an exact Python port
of rootsOf / rootsOf8, and a brute-force cross-check."""
from sympy import factorint
from sympy.ntheory import sqrt_mod

def crt(m1, m2, inv, r1, r2):
    return r1 + m1 * ((inv * (r2 + (m2 - r1 % m2))) % m2)

def two_roots_odd(u, m, s0):
    if m == 0: return [0]
    if m == 1: return [1]
    if m == 2: return [1, 3] if u % 4 == 1 else []
    if u % 8 != 1: return []
    M, H = 2**m, 2**(m-1)
    a = s0 % M
    return [a, M - a, (a + H) % M, (M - a + H) % M]

def two_list(S, e2, s0):
    if e2 == 0: return [0]
    e = e2 - 1
    out = []
    for s in two_roots_odd(S // 4, 2*e, s0):
        out += [2*s, 2*s + 2**(2*e+1)]
    return out

def roots_of(S, cert):
    e2, s0, odd = cert
    M, L = 2**(2*e2), two_list(S, e2, s0)
    for (l, e, r, inv) in odd:
        if r is None: return []
        q = l**(2*e)
        a, b = r % q, q - r % q
        L = [x for r1 in L for x in (crt(M, q, inv, r1, a), crt(M, q, inv, r1, b))]
        M *= q
    return L

def roots_of8(S, y, cert):
    N, T = y*y*8, (S + 5*y*y) % (y*y*8)
    return [r + y*y*t for r in roots_of(S, cert) for t in range(8) if (r + y*y*t)**2 % N == T]

def make_cert(S, y):
    f = factorint(y)
    e2 = f.pop(2, 0)
    s0 = 0
    if e2 >= 1:
        assert S % 8 == 4
        m, u = 2*e2 - 2, S // 4
        if m >= 3 and u % 8 == 1:
            s0 = sqrt_mod(u, 2**m)
            assert (s0*s0 - u) % 2**m == 0
    odd = []
    M = 2**(2*e2)
    for l in sorted(f):
        e = f[l]
        q = l**(2*e)
        if pow(S % l, (l-1)//2, l) == l-1:
            odd.append((l, e, None, 0))
        else:
            assert S % l != 0
            r = sqrt_mod(S, q)
            assert (r*r - S) % q == 0
            odd.append((l, e, r, pow(M, -1, q)))
        M *= q
    return (e2, s0, odd)

def lean_cert(cert):
    e2, s0, odd = cert
    ents = ", ".join("⟨%d, %d, %s, %d⟩" % (l, e, "none" if r is None else "some %d" % r, inv) for (l, e, r, inv) in odd)
    return "⟨%d, %d, [%s]⟩" % (e2, s0, ents)

def brute(S, y):
    m = y*y
    return [x for x in range(m) if (x*x - S) % m == 0]

def brute8(S, y):
    m = 8*y*y
    return [x for x in range(m) if (x*x + 3*y*y - S) % m == 0]

if __name__ == "__main__":
    S211, S73 = 4*211**7, 4*73**7
    small = [(S, y) for S in (S211, S73, 4*3**7, 4*5**7, 4*17**7, 4*7**7) for y in list(range(1, 200)) + [462, 1155, 1296, 1024, 2187]]
    n = 0
    for S, y in small:
        if any(S % l == 0 for l in factorint(y) if l != 2): continue   # p | y not supported
        c = make_cert(S, y)
        R = roots_of(S, c)
        assert sorted(R) == brute(S, y), (S, y)
        assert len(set(R)) == len(R)
        if y <= 60:
            R8 = roots_of8(S, y, c)
            assert sorted(R8) == brute8(S, y), (S, y)
        n += 1
    print("%d small cases agree with brute force" % n)
