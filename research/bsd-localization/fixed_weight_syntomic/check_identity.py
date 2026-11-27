#!/usr/bin/env python3
"""Exact universal polynomial checks for the fixed-weight syntomic identity.

Only the Python standard library is used. Polynomials have rational
coefficients and integral (possibly negative) exponent vectors.
This checks algebra, not the geometric hypotheses or interpolation.
"""

from fractions import Fraction
import json


class Ring:
    def __init__(self, names):
        self.names = tuple(names.split())
        self.zero_exp = (0,) * len(self.names)

    def constant(self, value):
        return Poly(self, {self.zero_exp: Fraction(value)})

    def variable(self, name):
        exponent = list(self.zero_exp)
        exponent[self.names.index(name)] = 1
        return Poly(self, {tuple(exponent): Fraction(1)})


class Poly:
    def __init__(self, ring, terms):
        self.ring = ring
        self.terms = {e: c for e, c in terms.items() if c}

    def coerce(self, other):
        if isinstance(other, Poly):
            assert other.ring is self.ring
            return other
        return self.ring.constant(other)

    def __add__(self, other):
        other = self.coerce(other)
        terms = dict(self.terms)
        for e, c in other.terms.items():
            terms[e] = terms.get(e, Fraction(0)) + c
        return Poly(self.ring, terms)

    __radd__ = __add__

    def __neg__(self):
        return Poly(self.ring, {e: -c for e, c in self.terms.items()})

    def __sub__(self, other):
        return self + (-self.coerce(other))

    def __rsub__(self, other):
        return self.coerce(other) + (-self)

    def __mul__(self, other):
        other = self.coerce(other)
        terms = {}
        for e, c in self.terms.items():
            for f, d in other.terms.items():
                exponent = tuple(x + y for x, y in zip(e, f))
                terms[exponent] = terms.get(exponent, Fraction(0)) + c * d
        return Poly(self.ring, terms)

    __rmul__ = __mul__

    def __pow__(self, exponent):
        assert isinstance(exponent, int)
        if exponent < 0:
            assert len(self.terms) == 1, "Only Laurent monomials are inverted."
            e, c = next(iter(self.terms.items()))
            return Poly(self.ring, {tuple(exponent * n for n in e): c ** exponent})
        result = self.ring.constant(1)
        for _ in range(exponent):
            result = result * self
        return result

    def __eq__(self, other):
        return self.terms == self.coerce(other).terms


def product(ring, entries):
    result = ring.constant(1)
    for entry in entries:
        result = result * entry
    return result


def reduce_elliptic_frobenius(poly):
    """Reduce F-powers using F^2+3F+5=0, keeping all other variables."""
    position = poly.ring.names.index("F")
    largest = max((e[position] for e in poly.terms), default=0)
    powers = [(1, 0)]
    for _ in range(largest):
        constant, linear = powers[-1]
        powers.append((-5 * linear, constant - 3 * linear))
    terms = {}
    for exponent, coefficient in poly.terms.items():
        degree = exponent[position]
        assert degree >= 0
        for power, multiplier in enumerate(powers[degree]):
            target = list(exponent)
            target[position] = power
            target = tuple(target)
            terms[target] = terms.get(target, Fraction(0)) + coefficient * multiplier
    return Poly(poly.ring, terms)


def main():
    r = Ring("a b c d z")
    a, b, c, d, z = (r.variable(n) for n in r.names)
    roots = [a * c, a * d, b * c, b * d]
    signs = [1, -1, -1, 1]
    factors = [1 - uv * z for uv in roots]
    cleared_sum = sum(
        signs[i] * roots[i] * product(r, factors[:i] + factors[i + 1 :])
        for i in range(4)
    )
    numerator = (a - b) * (c - d) * (1 - a * b * c * d * z ** 2)
    assert cleared_sum == numerator
    assert cleared_sum != (a - b) * (c - d) * (1 + a * b * c * d * z ** 2)

    r = Ring("p t a c x y F")
    p, t, a, c, x, y, F = (r.variable(n) for n in r.names)
    b = x * t * a ** -1
    d = y * t * c ** -1
    z = F * p ** -1 * t ** -1
    N = 1 - x * y * F ** 2 * p ** -2
    assert 1 - a * b * c * d * z ** 2 == N
    assert 1 - a * b * c * d * (F * t ** -1) ** 2 != N

    D = product(r, [1 - u * v * z for u in (a, b) for v in (c, d)])
    C = (1 - a * y * c ** -1 * p ** -1 * F) * (
        1 - x * c * a ** -1 * p ** -1 * F
    )
    S = (1 - p * t * a ** -1 * c ** -1 * F ** -1) * (
        1 - x * y * t * p ** -1 * a ** -1 * c ** -1 * F
    )
    scalar = -a * c * p ** -1 * t ** -1
    assert D == scalar * F * S * C
    assert D != scalar * S * C

    # Clearing (10) against (8) reverses the known algebraic prefactor.
    # This does not determine the separate global syntomic sign epsilon_DR.
    assert D * (p * t * a ** -1 * c ** -1) == -F * S * C

    r = Ring("tau F")
    tau, F = (r.variable(n) for n in r.names)
    L = (5 * tau + 23) + (5 * tau + 11) * F
    R = 10 * (tau + 1) + (5 * tau + 11) * F
    delta = 5 * tau ** 2 + 18 * tau + 25
    cleared_matrix_identity = (
        -3 * F * (20 - (5 * tau + 3) * F) * L
        - 5 * delta * (30 + 3 * F)
    )
    assert reduce_elliptic_frobenius(cleared_matrix_identity) == 0
    assert reduce_elliptic_frobenius(L * R) == -15 * delta
    assert reduce_elliptic_frobenius((-3 * L) * R - 45 * delta) == 0
    wrong_L = (5 * tau + 23) + (5 * tau + 10) * F
    assert reduce_elliptic_frobenius(
        -3 * F * (20 - (5 * tau + 3) * F) * wrong_L
        - 5 * delta * (30 + 3 * F)
    ) != 0

    # Exact norm-five ideals in the project's class-character convention.
    # a_2=(2,omega), omega^2-omega+18=0; verify divisibility via
    # its selected roots modulo 2^j and the two p=5 embeddings.
    witnesses = [(5, -2, 3, 22), (2, -2, 1, 2)]
    selected_exponents = {}
    for j, u, v, omega_two_power in witnesses:
        assert u * u + u * v + 18 * v * v == 5 * 2 ** j
        assert (omega_two_power ** 2 - omega_two_power + 18) % (2 ** j) == 0
        assert (u + v * omega_two_power) % (2 ** j) == 0
    for omega_five in (2, 4):
        selected = [(-j) % 7 for j, u, v, _ in witnesses if (u + v * omega_five) % 5]
        assert len(selected) == 1
        selected_exponents[omega_five] = selected[0]
        ratio_exponent = (2 * selected[0]) % 7
        assert sorted((ratio_exponent, (-ratio_exponent) % 7)) == [3, 4]
    assert selected_exponents == {2: 2, 4: 5}

    print(json.dumps({
        "status": "passed",
        "method": "exact universal Laurent polynomial arithmetic over Q",
        "identities": [
            "four-contribution numerator after clearing denominators",
            "root and Tate normalization gives 1-chi_f^-1 F^2/p^2",
            "four-factor denominator equals -ac/(p*t) F S C",
            "relative algebraic sign and scalar in equation (10)",
            "conditional pilot matrix modulo F^2+3F+5",
            "projective inverse of the conditional pilot matrix",
            "exact inverse has scalar 1/9",
            "norm-five ideal witnesses and CM root-ratio trace zeta^3+zeta^4",
        ],
        "rejected_errors": [
            "wrong numerator sign",
            "missing Tate-induced factor p in z=F/(p*t)",
            "missing Frobenius F in denominator factorization",
            "incorrect linear coefficient of the conditional pilot matrix",
        ],
        "geometric_hypotheses_verified_by_this_script": False,
        "global_syntomic_sign_verified_by_this_script": False,
        "weight_one_interpolation_proved_by_this_script": False,
    }, indent=2))


if __name__ == "__main__":
    main()
