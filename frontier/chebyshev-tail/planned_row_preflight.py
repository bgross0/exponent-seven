#!/usr/bin/env python3
"""Exact integer preflight of the proposed X=30000 Rows evaluator extension.

Mirrors the source definitions in Numerics/{FixedLog,FixedSqrt,FixedExp,
FixedArith}.lean and Rows/{Corr,PrimePart,JPart,Check}.lean. The only intended
extensions are the prime table, context bound, and fuel 14. This is not a
Lean theorem. No floating-point or external numerical package is used.
"""

from collections import Counter
from math import isqrt
from pathlib import Path
import argparse
import json
import re

D, OFF, BASE = 10**20, 2**62, 2**64
P20 = (D, 12, 4, 69314718055994530941)
P20W = (D, 12, 8, 69314718055994530941)
P26 = (10**26, 16, 5, 69314718055994530941723212)
CONST = 223059076563587229937


def cdiv(a, b):
    return (a+b-1)//b if b else 0


def expo_search(bits, n):
    e = 0
    for i in range(bits-1, -1, -1):
        candidate = e + 2**i
        if 2**candidate <= n:
            e = candidate
    return e


def logs(n, params=P20):
    scale, terms, bits, l2lo = params
    k = expo_search(bits, n)
    e = k if n*n <= 2**(2*k+1) else k+1
    p = 2**e

    def ratio(a, b, upper):
        numerator, denominator = (a-b)**2*scale, (a+b)**2
        w = cdiv(numerator, denominator) if upper else numerator//denominator
        if upper and w+1 > scale:
            return scale*a
        value = cdiv(scale*scale, (2*terms+1)*(scale-w)) if upper else 0
        for j in range(terms-1, -1, -1):
            value = (cdiv(scale, 2*j+1) + cdiv(w*value, scale) if upper
                     else scale//(2*j+1) + w*value//scale)
        numerator = 2*(a-b)*value
        return cdiv(numerator, a+b) if upper else numerator//(a+b)

    if p <= n:
        return e*l2lo+ratio(n, p, False), e*(l2lo+1)+ratio(n, p, True)
    return (max(0, e*l2lo-ratio(p, n, True)),
            max(0, e*(l2lo+1)-ratio(p, n, False)))


def sqrts(n):
    candidate = D*2**(expo_search(4, n)//2+1)
    target = n*D*D
    for _ in range(7):
        candidate = (candidate + target//candidate)//2
    lower = candidate if candidate*candidate <= target else 0
    upper = candidate+1 if target <= (candidate+1)**2 else D*(n+1)
    return lower, upper


def primes_below(limit):
    sieve = bytearray(b'\x01')*limit
    sieve[:2] = b'\x00\x00'
    for p in range(2, isqrt(limit-1)+1):
        if sieve[p]:
            sieve[p*p:limit:p] = b'\x00'*((limit-1-p*p)//p+1)
    return [p for p in range(2, limit) if sieve[p]]


def preflight(existing_table=None):
    X, Q = 30000, 2**135
    primes = primes_below(X)
    vector = [1]*32 + [-1]*32
    cn = [sum(vector[k]*vector[k+j] for k in range(64-j)) for j in range(65)]
    if cn != [64-3*j if j <= 32 else j-64 for j in range(65)]:
        raise ArithmeticError('Haar correlation formula mismatch')
    sq = cn[0]
    pack = sum((c+OFF)*BASE**j for j, c in enumerate(cn))
    get = lambda j: (pack//BASE**j) % BASE
    LX, LXhi = logs(X)
    total, count, fallbacks, max_p26_gap = 0, 0, 0, 0
    widths = Counter()
    for p in primes:
        L, H = logs(p)
        S, SH = sqrts(p)
        h26 = logs(p, P26)[1]
        if h26 > (L+16)*10**6 or SH > S+1:
            raise ArithmeticError(f'table upper certificate failed at {p}')
        max_p26_gap = max(max_p26_gap, cdiv(h26, 10**6)-L)
        widths[H-L] += 1
        for k in range(1, 15):
            n = p**k
            if n >= X:
                break
            count += 1
            j = 64*k*L//LXhi
            if not (j <= 63 and X**j <= n**64 <= X**(j+1)):
                total -= 2*(L+16)
                fallbacks += 1
                continue
            hlo = max(0, 64*k*L*D//LXhi-j*D)
            hhi = min(D, max(0, cdiv(64*k*(L+16)*D, LX)-j*D))
            a, b = get(j), get(j+1)
            flo = a*D + (hlo*(b-a) if b >= a else hhi*(b-a))
            fhi = a*D + (hhi*(b-a) if b >= a else hlo*(b-a))
            wlo = L*(D if k % 2 == 0 else S)
            whi = (L+16)*(D if k % 2 == 0 else S+1)
            numerator = flo-OFF*D if k % 2 == 0 else OFF*D-fhi
            denominator = p**((k+1)//2)*sq*D*D
            total += 2*numerator*(wlo if numerator >= 0 else whi)//denominator

    # expNegHi D 10 0 (LX/2048), with all directed integer rounding.
    x, value = LX//2048, 0
    for k in range(10, -1, -1):
        value = D+x*value//(D*(k+1))
    rhi = cdiv(D*D, value)

    def fpow(r, k):
        value = D
        for _ in range(k):
            value = cdiv(value*r, D)
        return value

    r3, r4 = fpow(rhi, 3), fpow(rhi, 4)
    A, B = fpow(r3, 16), fpow(r4, 16)
    step = cdiv(LXhi, 1024)
    J = cdiv((sq+OFF-get(1))*D, sq)
    for m in range(16, 1024):
        if B >= D:
            J += 2*D
        else:
            i, j = m % 16, m//16
            om = max(0, 32*sq+32*OFF-((31-2*i)*get(j)+(2*i+1)*get(j+1)))
            J += cdiv(step*cdiv(2*A*D, D-B)*om, 32*D*sq)
        A, B = cdiv(A*r3, D), cdiv(B*r4, D)
    J += cdiv(4*X*D*D, 3*sqrts(X)[0]*(X*X-1))
    logq_hi = logs(Q, P20W)[1]
    margin = total-J-logq_hi+CONST
    if margin <= 0 or count != 3320 or len(primes) != 3245 or fallbacks:
        raise ArithmeticError('finite bridge preflight failed')

    old_count = None
    if existing_table:
        entries = [tuple(map(int, t)) for t in re.findall(
            r'\((\d+), (\d+), (\d+)\)', Path(existing_table).read_text())]
        if len(entries) != 834 or any(logs(p)[0] != L or sqrts(p)[0] != S
                                      for p, L, S in entries):
            raise ArithmeticError('mirror differs from existing certified table')
        old_count = len(entries)
    return {
        'status': 'exact integer preflight; not Lean checked',
        'X': X, 'Q': str(Q), 'scale': str(D),
        'vector': vector, 'sq': sq, 'pack': str(pack),
        'prime_count': len(primes), 'prime_power_terms': count,
        'fuel': 14, 'exclusive_exponent_cutoff': 15, 'cell_fallbacks': fallbacks,
        'log_X': [str(LX), str(LXhi)],
        'totalLo': str(total), 'jHi': str(J), 'logHi_Q': str(logq_hi),
        'constant_lower': str(CONST), 'margin_lower': str(margin),
        'P20_prime_log_width_counts': dict(sorted(widths.items())),
        'max_P26_rescaled_upper_minus_P20_lower': max_p26_gap,
        'P26_log_upper_and_sqrt_width_checks': 'all pass',
        'existing_table_entries_reproduced': old_count,
    }


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--existing-table', type=Path)
    args = parser.parse_args()
    print(json.dumps(preflight(args.existing_table), indent=2))
