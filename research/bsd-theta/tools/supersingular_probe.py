"""Exact exploratory Brandt-function calculation for characteristic 389.

The arithmetic is exact; interpretation as a toric period is a separate
mathematical obligation. Numpy only accelerates enumeration of a finite field.
"""

import json
from math import comb, gcd, lcm
from pathlib import Path

import numpy as np
import sympy as sp

P = 389
NONRESIDUE = 2


def add(x, y):
    return ((x[0] + y[0]) % P, (x[1] + y[1]) % P)


def neg(x):
    return (-x[0] % P, -x[1] % P)


def mul(x, y):
    a, b = x
    c, d = y
    return ((a * c + NONRESIDUE * b * d) % P, (a * d + b * c) % P)


def inv(x):
    a, b = x
    z = pow((a * a - NONRESIDUE * b * b) % P, -1, P)
    return (a * z % P, -b * z % P)


def scale(k, x):
    return (k * x[0] % P, k * x[1] % P)


def power(x, n):
    z = (1, 0)
    while n:
        if n % 2:
            z = mul(z, x)
        x = mul(x, x)
        n //= 2
    return z


def evaluate(coeffs, x):
    z = (0, 0)
    for c in reversed(coeffs):
        z = add(mul(z, x), c if isinstance(c, tuple) else (c % P, 0))
    return z


def deuring_roots():
    degree = (P - 1) // 2
    coeffs = [comb(degree, k) ** 2 % P for k in range(degree + 1)]
    a = np.repeat(np.arange(P, dtype=np.int64), P)
    b = np.tile(np.arange(P, dtype=np.int64), P)
    r, s = np.zeros(P * P, dtype=np.int64), np.zeros(P * P, dtype=np.int64)
    for c in reversed(coeffs):
        r, s = (r * a + NONRESIDUE * s * b + c) % P, (r * b + s * a) % P
    roots = [(int(a[i]), int(b[i])) for i in np.flatnonzero((r == 0) & (s == 0))]
    assert len(roots) == degree
    assert all(evaluate(coeffs, x) == (0, 0) for x in roots)
    return roots


def legendre_j(x):
    numerator = scale(256, power(add(add(power(x, 2), neg(x)), (1, 0)), 3))
    denominator = mul(power(x, 2), power(add(x, (-1, 0)), 2))
    return mul(numerator, inv(denominator))


def phi2_coeffs(x):
    x2 = power(x, 2)
    return [
        add(add(add(power(x, 3), scale(-162000, x2)), scale(8748000000, x)), (-157464000000000 % P, 0)),
        add(add(scale(1488, x2), scale(40773375, x)), (8748000000 % P, 0)),
        add(add(neg(x2), scale(1488, x)), (-162000 % P, 0)),
        (1, 0),
    ]


def divide_by_root(coeffs, x):
    q = [(0, 0)] * (len(coeffs) - 1)
    q[-1] = coeffs[-1]
    for k in range(len(q) - 2, -1, -1):
        q[k] = add(coeffs[k + 1], mul(x, q[k + 1]))
    assert add(coeffs[0], mul(x, q[0])) == (0, 0)
    return q


def adjacency(js):
    rows = []
    for x in js:
        polynomial = phi2_coeffs(x)
        row = []
        for y in js:
            mult = 0
            while len(polynomial) > 1 and evaluate(polynomial, y) == (0, 0):
                polynomial = divide_by_root(polynomial, y)
                mult += 1
            row.append(mult)
        assert polynomial == [(1, 0)] and sum(row) == 3
        rows.append(row)
    return rows


H_MINUS_71 = [
    737707086760731113357714241006081263,
    -425319473946139603274605151187659,
    5138800366453976780323726329446,
    -823534263439730779968091389,
    98394038810047812049302,
    -3091990138604570,
    313645809715,
    1,
]


def main():
    roots = deuring_roots()
    js = sorted(set(map(legendre_j, roots)))
    assert len(js) == 33
    rows = adjacency(js)
    matrix = sp.Matrix(rows)
    basis = (matrix + 2 * sp.eye(len(js))).nullspace()
    primitive = []
    for vec in basis:
        common = lcm(*(int(x.q) for x in vec))
        ints = [int(x * common) for x in vec]
        divisor = gcd(*ints)
        ints = [x // divisor for x in ints]
        if next(x for x in ints if x) < 0:
            ints = [-x for x in ints]
        primitive.append(ints)
    cm_indices = [i for i, j in enumerate(js) if evaluate(H_MINUS_71, j) == (0, 0)]
    data = {
        "status": "exact arithmetic; toric-period interpretation separately reviewed",
        "field": {"p": P, "basis": "1,u", "u_squared": NONRESIDUE},
        "deuring_roots": roots,
        "supersingular_j": js,
        "brandt_T2_function_matrix": rows,
        "T2_eigenvalue": -2,
        "eigenspace_dimension": len(basis),
        "primitive_eigenvectors": primitive,
        "hilbert_class_polynomial_D_minus71_ascending": H_MINUS_71,
        "CM_indices": cm_indices,
        "CM_values": [[vec[i] for i in cm_indices] for vec in primitive],
        "CM_induced_T2": [[rows[i][j] for j in cm_indices] for i in cm_indices],
    }
    target = Path(__file__).resolve().parents[1] / "data" / "supersingular-389.json"
    target.write_text(json.dumps(data, indent=2) + "\n")
    print(json.dumps({k: data[k] for k in ["eigenspace_dimension", "CM_indices", "CM_values", "CM_induced_T2"]}))


if __name__ == "__main__":
    main()
