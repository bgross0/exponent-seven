"""Explore a certified p-adic CM labeling before asserting theta compatibility.

CM reduction prime q=389 is distinct from the Iwasawa prime p=5.
Input lifts come from PARI; all finite precision inequalities are rechecked
with integer arithmetic here. Output is not itself a BSD proof.
"""

import json
from math import comb
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
Q = 389
K = 4
MOD = Q ** K


def add(x, y, modulus=MOD):
    return ((x[0] + y[0]) % modulus, (x[1] + y[1]) % modulus)


def mul(x, y, modulus=MOD):
    a, b = x
    c, d = y
    return ((a * c + 2 * b * d) % modulus, (a * d + b * c) % modulus)


def scale(c, x, modulus=MOD):
    return (c * x[0] % modulus, c * x[1] % modulus)


def ev(coeffs, x, modulus=MOD):
    z = (0, 0)
    for c in reversed(coeffs):
        z = add(mul(z, x, modulus), (c % modulus, 0), modulus)
    return z


def vp(x, bound=80):
    if x == 0:
        return bound
    z = 0
    while x % Q == 0:
        x //= Q
        z += 1
    return z


def pair_vp(x):
    return min(vp(x[0]), vp(x[1]))


def phi2(x, y, modulus=MOD):
    x2, y2 = mul(x, x, modulus), mul(y, y, modulus)
    z = add(mul(x2, x, modulus), mul(y2, y, modulus), modulus)
    z = add(z, scale(-1, mul(x2, y2, modulus), modulus), modulus)
    z = add(z, scale(1488, mul(mul(x, y, modulus), add(x, y, modulus), modulus), modulus), modulus)
    z = add(z, scale(-162000, add(x2, y2, modulus), modulus), modulus)
    z = add(z, scale(40773375, mul(x, y, modulus), modulus), modulus)
    z = add(z, scale(8748000000, add(x, y, modulus), modulus), modulus)
    return add(z, (-157464000000000 % modulus, 0), modulus)


def main():
    coeffs = json.loads((ROOT / "data/H-minus44375-coeffs.json").read_text())
    lifts = json.loads((ROOT / "data/CM-minus44375-lifts32.json").read_text())
    ss = json.loads((ROOT / "data/supersingular-389.json").read_text())
    assert len(coeffs) == 141 and coeffs[-1] == 1 and len(lifts) == 140
    derivative = [i * coeffs[i] for i in range(1, len(coeffs))]
    hensel = []
    for r in lifts:
        s = pair_vp(ev(derivative, r, Q ** 80))
        v = pair_vp(ev(coeffs, r, Q ** 80))
        assert v > 2 * s and v >= K + s, (s, v)
        hensel.append({"derivative_v": s, "value_v_lower_bound": v})
    lifts = [(r[0] % MOD, r[1] % MOD) for r in lifts]
    assert len(set(lifts)) == 140
    graph = [[j for j, y in enumerate(lifts) if phi2(x, y) == (0, 0)] for x in lifts]
    assert all(len(neighbors) == 2 for neighbors in graph), [len(x) for x in graph]
    assert all(i in graph[j] for i, nei in enumerate(graph) for j in nei)
    cycle = [0, min(graph[0])]
    while len(cycle) < len(lifts):
        candidates = [j for j in graph[cycle[-1]] if j != cycle[-2]]
        assert len(candidates) == 1
        assert candidates[0] not in cycle
        cycle.append(candidates[0])
    assert 0 in graph[cycle[-1]]
    values = dict(zip(map(tuple, ss["supersingular_j"]), ss["primitive_eigenvectors"][0]))
    weights = [values[(lifts[i][0] % Q, lifts[i][1] % Q)] for i in cycle]
    grouped = [sum(weights[i] for i in range(j, 140, 5)) for j in range(5)]
    jet = [sum(grouped[j] * comb(j, k) for j in range(5)) % 5 for k in range(3)]
    payload = {
        "status": "exact CM arithmetic; normalization and classical bridges audited in research/theta-certificate.md",
        "CM_discriminant": -44375,
        "CM_conductor": 25,
        "reduction_prime": Q,
        "root_precision_exponent": K,
        "root_extension": "u^2=2",
        "class_number": 140,
        "iwasawa_prime": 5,
        "hensel_checks": hensel,
        "CM_lifts_mod_q_to_k": lifts,
        "horizontal_2_isogeny_adjacency": graph,
        "class_generator_cycle": cycle,
        "CM_function_weights_in_cycle_order": weights,
        "raw_Gamma1_coefficients": grouped,
        "raw_quadratic_jet_mod5": jet,
    }
    (ROOT / "data/cm-jet-p5.json").write_text(json.dumps(payload, indent=2) + "\n")
    print(json.dumps({"root_count": len(lifts), "max_derivative_valuation": max(x["derivative_v"] for x in hensel), "grouped": grouped, "jet": jet}))


if __name__ == "__main__":
    main()
