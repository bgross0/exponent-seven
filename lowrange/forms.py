"""Binary quadratic forms of discriminant -q (q prime, q = 3 mod 4): the tools used by
direct.py and classify.py."""
from math import gcd, isqrt
from sympy import isprime, jacobi_symbol
from sympy.ntheory import sqrt_mod


def reduce_form(a, b, q):
    """Reduced form equivalent to (a, b, c), c = (b^2 + q)/(4a)."""
    c, r = divmod(b*b + q, 4*a)
    assert r == 0
    while True:
        if not (-a < b <= a):
            b = (b + a - 1) % (2*a) - a + 1
            c, r = divmod(b*b + q, 4*a)
            assert r == 0
        if a > c:
            a, b, c = c, -b, a
            continue
        if a == c and b < 0:
            b = -b
        return a, b, c


def class_number(q):
    """Number of reduced primitive forms of discriminant -q."""
    h = 0
    for a in range(1, isqrt(q//3) + 1):
        for b in range(-a + 1, a + 1):
            c, r = divmod(b*b + q, 4*a)
            if r or c < a or (a == c and b < 0) or gcd(gcd(a, abs(b)), c) != 1:
                continue
            h += 1
    return h


def splits(q, l):
    """Does the prime l != q split in Q(sqrt(-q))?  (q = 3 mod 4)"""
    if l == 2:
        return q % 8 == 7
    return jacobi_symbol(-q % l, l) == 1


def seventh_power_principal(q, l):
    """For a split prime l: is L^7 principal, L a prime ideal above l?
    L^7 is the primitive ideal of norm l^7 with form (l^7, b, c), b^2 = -q mod 4 l^7."""
    a = l**7
    if l == 2:
        m = 4*a
        b = next(t for t in sqrt_mod(-q % m, m, all_roots=True))
    else:
        b = sqrt_mod(-q % a, a)
        assert b is not None
        if b % 2 == 0:
            b += a
    assert (b*b + q) % (4*a) == 0
    return reduce_form(a, b, q) == (1, 1, (q + 1)//4)


def split_primes(q, count, start=2):
    out = []
    l = start
    while len(out) < count:
        if l != q and isprime(l) and splits(q, l):
            out.append(l)
        l += 1
    return out


def exponent_divides_7(q):
    """Decide whether the class group of Q(sqrt(-q)) has exponent dividing 7 (q < 10^7, say).
    Returns (bool, h).  The prime ideals of norm <= sqrt(q/3) generate the class group."""
    h = class_number(q)
    if h == 1:
        return True, h
    k = h
    while k % 7 == 0:
        k //= 7
    if k != 1:
        return False, h
    if h == 7:
        return True, h
    for l in range(2, isqrt(q//3) + 1):
        if isprime(l) and splits(q, l) and not seventh_power_principal(q, l):
            return False, h
    return True, h
