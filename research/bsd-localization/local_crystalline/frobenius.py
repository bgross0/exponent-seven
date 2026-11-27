#!/usr/bin/env python3
"""Exact rational Kedlaya reduction for the local E389 pilot.

The infinite Frobenius tail is bounded by the argument in README.md.
This computes local crystalline data, not a global Kato-class localization.
"""

import argparse
from fractions import Fraction as Q
import json
from math import comb
from pathlib import Path


def trim(a):
    a = list(a)
    while a and a[-1] == 0:
        a.pop()
    return a


def add(a, b):
    return trim([(a[i] if i < len(a) else Q(0)) +
                 (b[i] if i < len(b) else Q(0)) for i in range(max(len(a), len(b)))])


def scale(a, c):
    return trim([x*c for x in a])


def mul(a, b):
    if not a or not b:
        return []
    c = [Q(0)] * (len(a)+len(b)-1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            c[i+j] += x*y
    return trim(c)


def shift(a, n):
    return [Q(0)]*n + list(a) if a else []


def derivative(a):
    return trim([i*a[i] for i in range(1, len(a))])


def divmod_poly(a, b):
    a, b = trim(a), trim(b)
    if not b:
        raise ZeroDivisionError
    quotient = [Q(0)] * max(0, len(a)-len(b)+1)
    while a and len(a) >= len(b):
        power = len(a)-len(b)
        c = a[-1]/b[-1]
        quotient[power] += c
        for i, value in enumerate(b):
            a[power+i] -= c*value
        a = trim(a)
    return trim(quotient), a


def inverse_mod(a, modulus):
    r0, r1 = list(modulus), list(a)
    t0, t1 = [], [Q(1)]
    while r1:
        quotient, remainder = divmod_poly(r0, r1)
        r0, r1 = r1, remainder
        t0, t1 = t1, add(t0, scale(mul(quotient, t1), -1))
    assert len(r0) == 1 and r0[0]
    answer = divmod_poly(scale(t0, 1/r0[0]), modulus)[1]
    assert divmod_poly(mul(a, answer), modulus)[1] == [Q(1)]
    return answer


def power(a, exponent):
    result = [Q(1)]
    while exponent:
        if exponent & 1:
            result = mul(result, a)
        a = mul(a, a)
        exponent //= 2
    return result


def floor_log(n, p):
    answer = 0
    while n >= p:
        n //= p
        answer += 1
    return answer


def rational_mod(x, modulus):
    assert x.denominator % 5 != 0
    return x.numerator * pow(x.denominator, -1, modulus) % modulus


def reduced_form(P, m, f, inv_derivative):
    """Cohomology coordinates of P(x) dx/Y^(2m+1), Y²=f(x)."""
    fp = derivative(f)
    P = list(P)
    for pole in range(m, 0, -1):
        remainder = divmod_poly(P, f)[1]
        B = divmod_poly(mul(remainder, inv_derivative), f)[1]
        A, zero = divmod_poly(add(P, scale(mul(B, fp), -1)), f)
        assert not zero
        P = add(A, scale(derivative(B), Q(2, 2*pole-1)))
    # Eliminate d(x^d Y), whose doubled numerator is 2d*x^(d-1)f+x^d f'.
    while len(P) > 2:
        d = len(P)-3
        exact = shift(fp, d)
        if d:
            exact = add(exact, scale(shift(f, d-1), 2*d))
        P = add(P, scale(exact, -P[-1]/exact[-1]))
    return P + [Q(0)]*(2-len(P))


def compute(digits=8, extra_terms=0, f_coefficients=(1, -8, 4, 4)):
    """Return matrix in the COLUMN convention on (dx/Y, x dx/Y)."""
    if digits < 2 or extra_terms < 0:
        raise ValueError("digits>=2 and extra_terms>=0 required")
    p = 5
    f = list(map(Q, f_coefficients))
    assert len(f) == 4 and f[-1] == 4
    inverse = inverse_mod(derivative(f), f)
    assert all(c.denominator % 5 for c in inverse), "good reduction at 5 required"
    fxp = [Q(0)]*(p*(len(f)-1)+1)
    for i, c in enumerate(f):
        fxp[p*i] = c
    delta = add(fxp, scale(power(f, p), -1))
    assert all(c.denominator == 1 and c.numerator % p == 0 for c in delta)
    # Every reduced kth term has valuation >= k+1-floor(log_5(10k+5)).
    first_omitted = 0
    while first_omitted+1-floor_log(10*first_omitted+5, 5) < digits:
        first_omitted += 1
    terms = first_omitted + extra_terms
    matrix = [[0, 0], [0, 0]]
    modulus = p**digits
    delta_power = [Q(1)]
    for k in range(terms):
        binomial = Q((-1)**k*comb(2*k, k), 4**k)
        m = 5*k+2
        for i in range(2):
            numerator = scale(shift(delta_power, 5*i+4), 5*binomial)
            reduced = reduced_form(numerator, m, f, inverse)
            column = [rational_mod(x, modulus) for x in reduced]
            for j in range(2):
                matrix[j][i] = (matrix[j][i]+column[j]) % modulus
        if k+1 < terms:
            delta_power = mul(delta_power, delta)
    finite_count = 1+sum((Y*Y-sum(int(c)*x**i for i,c in enumerate(f))) % 5 == 0
                         for x in range(5) for Y in range(5))
    trace = 6-finite_count
    determinant = (matrix[0][0]*matrix[1][1]-matrix[0][1]*matrix[1][0]) % modulus
    assert (matrix[0][0]+matrix[1][1]) % modulus == trace % modulus
    assert determinant == 5
    # Lift the ordinary root and find its eigenline (s,1).
    alpha = trace % 5
    assert alpha
    for n in range(2, digits+1):
        mod = 5**n
        alpha = (alpha-(alpha*alpha-trace*alpha+5)*pow(2*alpha-trace, -1, mod)) % mod
    s = matrix[0][1]*pow(alpha-matrix[0][0], -1, modulus) % modulus
    assert (matrix[0][0]*s+matrix[0][1]-alpha*s) % modulus == 0
    assert (matrix[1][0]*s+matrix[1][1]-alpha) % modulus == 0
    # On V=H^1_et(1), phi=F/5. The interpolation annihilator is
    # zeta=(1-F/5)(1-F^-1)^-1 omega
    #     =(20I-(10-trace)F)/(5*(6-trace)) omega.
    # This division by 5 costs one absolute digit.
    assert (6-trace) % 5 and all(matrix[j][0] % 5 == 0 for j in range(2))
    zeta_modulus = modulus//5
    zeta = [((4 if j == 0 else 0)-(10-trace)*(matrix[j][0]//5))
            *pow(6-trace, -1, zeta_modulus) % zeta_modulus for j in range(2)]
    for j in range(2):
        assert (5*(6-trace)*zeta[j]-(20 if j == 0 else 0)
                +(10-trace)*matrix[j][0]) % modulus == 0
    return {
        "status": "PASS", "prime": 5, "absolute_digits": digits, "modulus": modulus,
        "curve_Y_squared_polynomial_low_to_high": list(f_coefficients),
        "basis": ["omega=dx/Y", "eta=x dx/Y"], "matrix_convention": "columns are images of basis vectors",
        "frobenius_matrix": matrix, "finite_field_point_count": finite_count,
        "frobenius_trace": trace, "frobenius_determinant": determinant,
        "ordinary_unit_root": alpha,
        "unit_root_line": {"vector_in_omega_eta_basis": [s, 1], "differential": "eta+s*omega"},
        "interpolation_annihilator": {
            "vector_in_twisted_omega_eta_basis": zeta,
            "absolute_digits": digits-1, "modulus": zeta_modulus,
            "definition": "zeta=(1-F/5)*(1-F^-1)^-1*omega; phi=F/5 on V=H^1_et(1)",
            "purpose": "CH scalar pairing whose base value vanishes on every local class; divided-map log calibration remains to be proved",
        },
        "precision": {"first_omitted_k": terms,
                      "tail_coefficient_valuation_lower_bound": terms+1-floor_log(10*terms+5, 5),
                      "bound": "k+1-floor(log_5(10*k+5)); nondecreasing for k>=0",
                      "interpretation_reference": "README.md; Kedlaya Lemma 2 plus explicit reduction of Y dx"},
        "scope": "Local crystalline Frobenius and unit-root splitting; no global Kato jet or nonzero reflected logarithm"
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--digits", type=int, default=8)
    parser.add_argument("--extra-terms", type=int, default=0)
    parser.add_argument("--check", type=Path)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = compute(args.digits, args.extra_terms)
    if args.check:
        assert json.loads(args.check.read_text()) == result
    encoded = json.dumps(result, indent=2, sort_keys=True)+"\n"
    if args.output:
        args.output.write_text(encoded)
    print(encoded, end="")


if __name__ == "__main__":
    main()
