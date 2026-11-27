#!/usr/bin/env python3
"""Exact checks of the linear-algebra claims in README.md.

This program does not certify cycle specialization, comparison theorems,
Selmer rank, or arithmetic nonzero localization. It uses rational matrices
to check the consequences of the fixed conventions in the accompanying
mathematical argument.
"""

from fractions import Fraction as Q
import json


def mat(rows):
    return tuple(tuple(Q(x) for x in row) for row in rows)


def eye(n):
    return mat([[int(i == j) for j in range(n)] for i in range(n)])


def transpose(a):
    return tuple(zip(*a))


def add(a, b):
    return mat([[x + y for x, y in zip(ar, br)] for ar, br in zip(a, b)])


def scale(c, a):
    return mat([[Q(c) * x for x in row] for row in a])


def sub(a, b):
    return add(a, scale(-1, b))


def mul(a, b):
    return mat([[sum(x * y for x, y in zip(row, col))
                 for col in transpose(b)] for row in a])


def apply(a, v):
    return tuple(sum(x * y for x, y in zip(row, v)) for row in a)


def determinant(a):
    assert len(a) == len(a[0]) == 2
    return a[0][0] * a[1][1] - a[0][1] * a[1][0]


def inverse(a):
    det = determinant(a)
    assert det != 0
    return scale(1 / det, mat([[a[1][1], -a[0][1]],
                              [-a[1][0], a[0][0]]]))


def kron(a, b):
    return mat([[x * y for x in ar for y in br] for ar in a for br in b])


def tensor(v, w):
    return tuple(x * y for x in v for y in w)


def pair(v, w, pairing):
    return sum(x * y for x, y in zip(v, apply(pairing, w)))


def adjoint(a, pairing):
    return mul(mul(inverse(pairing), transpose(a)), pairing)


def text_matrix(a):
    return [[str(x) for x in row] for row in a]


def main():
    checks = []

    def check(name, condition):
        if not condition:
            raise AssertionError(name)
        checks.append(name)

    identity = eye(2)
    j = mat([[0, 1], [-1, 0]])
    frob = mat([[0, -5], [1, -3]])
    phi = scale(Q(1, 5), frob)
    p = Q(5)
    check("elliptic Frobenius polynomial",
          add(add(mul(frob, frob), scale(3, frob)), scale(5, identity))
          == mat([[0, 0], [0, 0]]))
    check("untwisted Frobenius similitude",
          mul(mul(transpose(frob), j), frob) == scale(5, j))
    check("untwisted Frobenius adjoint",
          adjoint(frob, j) == scale(5, inverse(frob)))
    check("Tate-twisted Frobenius adjoint",
          adjoint(phi, j) == scale(Q(1, 5), inverse(phi)))

    # CH acts on the test vector. Reconstruct the output from both tests.
    v = (Q(2), Q(3))
    tests = ((Q(1), Q(2)), (Q(3), Q(5)))
    check("independent elliptic tests", determinant(mat(tests)) != 0)
    for s in (1, 4, 20, 100):
        weight_j = -s
        a = mul(sub(identity, scale(p ** (weight_j - 1), inverse(phi))),
                inverse(sub(identity, scale(p ** (-weight_j), phi))))
        k = mul(sub(identity, scale(p ** (-s - 1), frob)),
                inverse(sub(identity, scale(p ** s, inverse(frob)))))
        r = mul(sub(identity, scale(p ** (s + 1), inverse(frob))),
                inverse(sub(identity, scale(p ** s, inverse(frob)))))
        check(f"negative-twist adjoint s={s}", adjoint(a, j) == k)
        check(f"inverse-Frobenius cancellation s={s}",
              k == scale(-p ** (-s - 1), mul(frob, r)))
        check(f"two-coordinate reconstruction s={s}",
              all(pair(apply(k, v), eta, j) == pair(v, apply(a, eta), j)
                  for eta in tests))

    # The generic alternating adjoint is det(A) A^{-1}; it is not A^{-1}
    # without the determinant factor.
    a_generic = mat([[2, 1], [3, 4]])
    check("general alternating adjoint retains determinant",
          adjoint(a_generic, j)
          == scale(determinant(a_generic), inverse(a_generic)))
    check("inverse alone fails when determinant differs from one",
          adjoint(a_generic, j) != inverse(a_generic))

    # CM basis order is UU, UH, HU, HH. The HH dual tensor selects UU.
    cm_pairing = kron(j, j)
    cm_basis = tuple(tuple(Q(int(i == k)) for i in range(4)) for k in range(4))
    hh = cm_basis[3]
    selection = tuple(pair(basis, hh, cm_pairing) for basis in cm_basis)
    check("CM holomorphic tensor selects exactly UU",
          selection == (Q(1), Q(0), Q(0), Q(0)))
    e_basis = ((Q(1), Q(0)), (Q(0), Q(1)))
    full_pairing = kron(j, cm_pairing)
    for i, e in enumerate(e_basis):
        for m, cm in enumerate(cm_basis):
            for n, eta in enumerate(e_basis):
                measured = pair(tensor(e, cm), tensor(eta, hh), full_pairing)
                expected = pair(e, eta, j) if m == 0 else Q(0)
                check(f"full CM extraction E={i}, CM={m}, test={n}",
                      measured == expected)
    for eta in tests:
        check(f"rank-one period change is common scalar at test={eta}",
              pair(tensor(v, cm_basis[0]),
                   tensor(eta, tuple(Q(7, 3) * x for x in hh)), full_pairing)
              == Q(7, 3) * pair(v, eta, j))

    # Base dual-exponential image and the source-defined annihilator.
    a0 = mul(sub(identity, scale(Q(1, 5), inverse(phi))),
             inverse(sub(identity, phi)))
    a0_formula = scale(Q(1, 45), add(scale(59, identity), scale(13, frob)))
    a0_adjoint = scale(Q(1, 45), sub(scale(20, identity), scale(13, frob)))
    check("base interpolation operator", a0 == a0_formula)
    check("base determinant one", determinant(a0) == 1)
    check("base image operator", adjoint(a0, j) == a0_adjoint)
    zeta = apply(a0_adjoint, e_basis[0])
    check("base image annihilator", pair(zeta, zeta, j) == 0)
    check("base image vector coordinates",
          zeta == (Q(4, 9), Q(-13, 45)))

    # A separate exact semilinear counterexample: in Q(u), u^2=2,
    # v=(1,u), sigma(v)=(1,-u), Tr(v)=(2,0), v wedge Tr(v)=-2u.
    # Encode a+bu by (a,b); the nonzero wedge is explicit.
    trace_wedge = (Q(0), Q(-2))
    check("unweighted trace does not preserve a general coefficient line",
          trace_wedge != (Q(0), Q(0)))

    result = {
        "status": "pass",
        "checks_passed": len(checks),
        "checks": checks,
        "CM_selection_on_UU_UH_HU_HH": [str(x) for x in selection],
        "base_A0_matrix": text_matrix(a0),
        "base_A0_adjoint_matrix": text_matrix(a0_adjoint),
        "base_zeta_in_omega_Fomega": [str(x) for x in zeta],
        "trace_counterexample_wedge_in_1_u": [str(x) for x in trace_wedge],
        "not_checked": [
            "published geometric or p-adic comparison theorems",
            "projected DR22 edge specialization",
            "global class proportionality or Selmer hypotheses",
            "nonzero arithmetic localization",
        ],
    }
    # Emit the fresh witness without modifying the saved certificate.
    # verify_all.py compares this full result with check_result.json.
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
