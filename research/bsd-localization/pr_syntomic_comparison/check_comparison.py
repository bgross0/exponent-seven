#!/usr/bin/env python3
"""Exact algebra for the conditional full PR/syntomic comparison.

No numerical fit, arithmetic-family comparison, or localization claim.
The shared utility only implements rational Laurent polynomials.
"""

from fractions import Fraction
import json
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "fixed_weight_syntomic"))
from check_identity import Poly, Ring, reduce_elliptic_frobenius


def elliptic_adjoint(poly):
    """Fix scalar variables and replace F by p/F in a Laurent polynomial."""
    ip = poly.ring.names.index("p")
    iF = poly.ring.names.index("F")
    terms = {}
    for exponent, coefficient in poly.terms.items():
        target = list(exponent)
        target[ip] += target[iF]
        target[iF] = -target[iF]
        target = tuple(target)
        terms[target] = terms.get(target, Fraction(0)) + coefficient
    return Poly(poly.ring, terms)


def quadratic_mul(x, y):
    """Q[omega]/(omega^2-omega+18), represented by (constant, linear)."""
    a, b = x
    c, d = y
    return (a*c - 18*b*d, a*d + b*c + b*d)


def quadratic_conjugate(x):
    a, b = x
    return (a+b, -b)


def quadratic_norm(x):
    return quadratic_mul(x, quadratic_conjugate(x))[0]


def quadratic_power(x, n):
    if n < 0:
        norm = quadratic_norm(x)
        x = tuple(Fraction(c, norm) for c in quadratic_conjugate(x))
        n = -n
    out = (Fraction(1), Fraction(0))
    for _ in range(n):
        out = quadratic_mul(out, x)
    return out


def main():
    r = Ring("p q a c F")
    p, q, a, c, F = (r.variable(n) for n in r.names)
    # q=p^s. On the test vector, CH's numerator and denominator are:
    test_num = 1 - q**-1 * F**-1
    test_den = 1 - q * p**-1 * F
    # Taking F-dagger=p/F gives these exact adjoints:
    adj_num = 1 - q**-1 * p**-1 * F
    adj_den = 1 - q * F**-1
    assert elliptic_adjoint(test_num) == adj_num
    assert elliptic_adjoint(test_den) == adj_den
    assert test_num != adj_num and test_den != adj_den
    # K_s = -F/(p*q) * R_s, after clearing the common denominator.
    assert adj_num == -p**-1 * q**-1 * F * (1 - p*q*F**-1)
    assert -p**-1*q**-1*F*(1 + p*q*F**-1) != adj_num
    # The reciprocal factorial/parity cancel separately; the remaining
    # monomial from (5), (3), and its F^-1 is precisely (a*c)^-1.
    assert (-p*q*a**-1*c**-1) * (-p**-1*q**-1*F) * F**-1 == a**-1*c**-1
    assert (-p*q*a**-1*c**-1) * F**-1 != a**-1*c**-1
    # R_s-1 = -(p-1)*q/F / (1-q/F), explaining its superflat estimate.
    assert (1-p*q*F**-1)-(1-q*F**-1) == -(p-1)*q*F**-1

    r = Ring("tau F")
    tau, F = (r.variable(n) for n in r.names)
    red = reduce_elliptic_frobenius
    D = 5*tau**2 + 18*tau + 25
    Cnum = 20 - (5*tau+3)*F
    Nnum = 30 + 3*F
    Mnum = 3*((5*tau+11) + 2*(tau+1)*F)
    Invnum = (5-tau) - 2*(tau+1)*F
    assert red(Cnum*Mnum - D*Nnum) == 0
    assert red(Mnum*Invnum - 9*D) == 0
    x, y = 3*(5*tau+11), 6*(tau+1)
    assert x*x - 3*x*y + 5*y*y == 27*D
    assert red(Mnum*((5-tau)-2*tau*F)-9*D) != 0
    # CH j=0 test annihilator pulled back through the conditional matrix.
    line_num = (10+50*tau) + (61+35*tau)*F
    assert red(Invnum*(20-13*F) + 3*line_num) == 0
    # Compare with the stated DL candidate using exact coefficient pairs.
    wedge = (10+50*tau)*(11+tau) - (61+35*tau)*(-2-10*tau)
    assert wedge == 8*(5*tau+1)*(10*tau+29)
    assert wedge != 0

    eta = (10, 1)
    theta = quadratic_mul(
        quadratic_power((-2, 3), 7),
        quadratic_power(eta, -5),
    )
    other = quadratic_mul(
        quadratic_power((-2, 1), 7),
        quadratic_power(eta, -2),
    )
    assert theta == (-281, 4)
    assert other == (277, 4)
    assert tuple(-x for x in quadratic_conjugate(theta)) == other
    assert quadratic_norm(theta) == 5**7
    assert (theta[0] + 2*theta[1]) % 5 == 2
    bar_theta = quadratic_conjugate(theta)
    assert (bar_theta[0] + 2*bar_theta[1]) % 5 == 0
    # theta^2 / 5^7 = theta/bar(theta), universally before the s-th power.
    ratio = quadratic_mul(theta, quadratic_power(bar_theta, -1))
    assert ratio == tuple(c / (5**7) for c in quadratic_power(theta, 2))

    print(json.dumps({
        "status": "passed",
        "method": "exact rational Laurent polynomial and quadratic-field arithmetic",
        "identities": [
            "CH adjoint factorization after clearing denominators",
            "nonanalytic p-power and Frobenius cancellation",
            "superflat regulator remainder",
            "conditional pilot PR comparison matrix",
            "exact inverse of the conditional pilot matrix",
            "unit determinant formula",
            "pullback of CH base annihilator",
            "nonzero wedge against the separate DL candidate",
            "ordinary norm-five ideal seventh-power generator",
            "conjugate norm-five generator and norm 5^7",
            "relative Lubin-Tate norm identity",
        ],
        "rejected_errors": [
            "using the test-vector operator without its adjoint",
            "wrong sign in the superflat regulator factor",
            "omitting the PR Frobenius correction",
            "wrong linear coefficient in the inverse matrix",
        ],
        "theta": [-281, 4],
        "bar_theta": [-277, -4],
        "norm_theta": 5**7,
        "actual_full_arithmetic_comparison_verified": False,
        "arithmetic_bad_line_identified": False,
        "nonzero_localization_proved": False,
    }, indent=2))


if __name__ == "__main__":
    main()
