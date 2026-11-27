#!/usr/bin/env python3
"""Independent exact Python replay of downloaded low-weight Sage artifacts.

The default mode checks the original level11 smoke core and level389 M2
checkpoint. --pilot-full independently verifies a subsequently completed
level389 core, including product/Serre provenance and saturation.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
import gzip
import hashlib
import json
from math import isqrt, gcd, lcm
from pathlib import Path

import sympy as sp


def load(path):
    return json.loads(gzip.decompress(path.read_bytes()))


def rows(data):
    return [[Fraction(x) for x in row] for row in data]


def rank_mod(data, p):
    a = [[int(x) % p for x in row] for row in data]
    rank = 0
    for j in range(len(a[0])):
        pivot = next((i for i in range(rank, len(a)) if a[i][j]), None)
        if pivot is None:
            continue
        a[rank], a[pivot] = a[pivot], a[rank]
        inv = pow(a[rank][j], -1, p)
        a[rank] = [x*inv % p for x in a[rank]]
        for i in range(rank+1, len(a)):
            c = a[i][j]
            if c:
                a[i] = [(x-c*y) % p for x, y in zip(a[i], a[rank])]
        rank += 1
        if rank == len(a):
            break
    return rank


def product(a, b, precision):
    """Exact signed Kronecker convolution, with a coefficient carry bound."""
    assert all(Fraction(x).denominator == 1 for x in a+b)
    a, b = list(map(int, a)), list(map(int, b))
    bound = min(len(a), len(b))*max(map(abs, a), default=0)*max(map(abs, b), default=0)
    bits = max(1, (2*bound).bit_length())
    radix = 1 << bits
    aa = sum(x << (bits*i) for i, x in enumerate(a))
    bb = sum(x << (bits*i) for i, x in enumerate(b))
    value, out = aa*bb, []
    for _ in range(precision):
        coefficient = value % radix
        if coefficient > radix//2:
            coefficient -= radix
        out.append(coefficient)
        value = (value-coefficient)//radix
    return out


def exact_matrix_product_equal(a, b, expected):
    """Check an integer matrix product by injective bounded radix encoding.

    This is one exact integer identity per output row, not a modular or
    probabilistic fingerprint. The chosen radix is larger than twice a
    proved bound on every possible coefficient of the difference.
    """
    assert len(a[0]) == len(b)
    columns = len(b[0])
    assert len(expected) == len(a) and all(len(row) == columns for row in expected)
    row_bounds = [max(map(abs, row), default=0) for row in b]
    bound = max(sum(abs(x)*s for x, s in zip(row, row_bounds))+max(map(abs, want), default=0)
                for row, want in zip(a, expected))
    bits = max(1, (2*bound).bit_length())
    def pack(row):
        answer = 0
        for x in reversed(row):
            answer = (answer << bits)+int(x)
        return answer
    packed = [pack(row) for row in b]
    for row, want in zip(a, expected):
        assert sum(int(x)*y for x, y in zip(row, packed) if x) == pack(want)
    return bits


def clear_row_denominators(matrix):
    denominators, integral = [], []
    for row in matrix:
        denominator = lcm(*(x.denominator for x in row))
        denominators.append(denominator)
        integral.append([int(x*denominator) for x in row])
    return integral, denominators


def clear_column_denominators(matrix):
    transposed = list(map(list, zip(*matrix)))
    cleared, denominators = clear_row_denominators(transposed)
    return list(map(list, zip(*cleared))), denominators


def sigma(n, k):
    return sum(d**k for d in range(1, n+1) if n % d == 0)


def eisenstein(weight, precision, level=1):
    factor = {4: 240, 6: -504, 10: -264}[weight]
    return [1]+[factor*sigma(n//level, weight-1) if n % level == 0 else 0
                for n in range(1, precision)]


def v5_integer(n):
    n = int(n)
    assert n != 0
    ans = 0
    while n % 5 == 0:
        ans += 1; n //= 5
    return ans


def replay_basis(record, previous):
    weight = record["weight"]
    precision = record["q_precision_exclusive"]
    raw = rows(record["raw_integer_q_basis"])
    basis = rows(record["q_basis"])
    assert len(raw) == len(basis) == record["dimension"]
    assert all(len(row) == precision for row in raw+basis)
    assert all(x.denominator == 1 for row in raw+basis for x in row)
    raw = [list(map(int, row)) for row in raw]
    basis = [list(map(int, row)) for row in basis]
    assert precision > record["metadata"]["sturm_bounds"][str(weight)]
    descriptions = record["provenance"].get("selected")
    serre_count = 0
    if descriptions is not None:
        assert len(descriptions) == len(raw)
        for row, desc in zip(raw, descriptions):
            if desc["kind"] == "product":
                a, b = desc["weights"]
                i, j = desc["basis_indices"]
                expected = product(previous[a][i], previous[b][j], precision)
            elif desc["kind"] == "Eisenstein_oldform":
                factor = Fraction(desc["scale"])
                expected = [factor*x for x in eisenstein(weight, precision, desc["V_level"])]
            elif desc["kind"] == "scaled_Serre_derivative":
                source_weight = desc["source_weight"]
                expected = previous[source_weight][desc["source_basis_index"]][:]
                e2 = [1]+[-24*sigma(n, 1) for n in range(1, precision)]
                current_weight = source_weight
                for step in desc["steps"]:
                    divisor = gcd(current_weight, 12)
                    assert step == {"input_weight": current_weight,
                                    "theta_multiplier": 12//divisor,
                                    "E2_multiplier": current_weight//divisor}
                    e2product = product(e2, expected, precision)
                    expected = [(12//divisor)*n*x-(current_weight//divisor)*y
                                for n, (x, y) in enumerate(zip(expected, e2product))]
                    current_weight += 2
                assert current_weight == weight
                serre_count += 1
            else:
                raise AssertionError("Unsupported provenance")
            assert row == expected
    work = raw
    index = 0
    for operation in record["saturation_at_5_operations"]:
        pivots = operation["replace_rows"]
        combination = operation["combination_rows"]
        assert operation["divisor"] == 5 and len(pivots) == len(combination)
        assert len(set(pivots)) == len(pivots)
        pivot_matrix = sp.Matrix([[row[j] for j in pivots] for row in combination])
        assert int(pivot_matrix.det()) % 5 != 0
        transformed = []
        for row in combination:
            nonzero = [(i, int(c)) for i, c in enumerate(row) if c]
            values = [sum(c*work[i][j] for i, c in nonzero) for j in range(precision)]
            assert all(x % 5 == 0 for x in values)
            transformed.append([x//5 for x in values])
        work = [row[:] for row in work]
        for i, replacement in zip(pivots, transformed):
            work[i] = replacement
        index += len(pivots)
    assert work == basis
    assert index == record["saturation_index_5_valuation"]
    rank_before, rank_after = rank_mod(raw, 5), rank_mod(basis, 5)
    assert rank_before == record["rank_mod5_before"]
    assert rank_after == record["rank_mod5_after"] == len(basis)
    pivots = record["pivot_columns"]
    minor = [[row[j] for j in pivots] for row in basis]
    assert rank_mod(minor, 5) == len(basis)
    report = {"weight": weight, "dimension": len(basis),
                   "rank_mod5_before": rank_before, "rank_mod5_after": rank_after,
                   "saturation_index_v5": index,
                   "selected_product_rows_replayed": 0 if descriptions is None else len(descriptions),
                   "unit_coefficient_minor_verified": True}
    if serre_count:
        report["scaled_Serre_derivatives_replayed"] = serre_count
    return basis, report


def independent_level11_weight2(basis):
    precision = len(basis[0])
    # eta(q)^2*eta(q^11)^2: q times the indicated integral Euler products.
    eta = [1]+[0]*(precision-1)
    for step in range(1, precision):
        exponent = 2+(2 if step % 11 == 0 else 0)
        for _ in range(exponent):
            for n in range(precision-1, step-1, -1):
                eta[n] -= eta[n-step]
    cusp = [0]+eta[:precision-1]
    # 11E2(q^11)-E2(q) is a genuine modular weight2 form at level11.
    eis = [10]+[24*sigma(n, 1)-(264*sigma(n//11, 1) if n % 11 == 0 else 0)
                 for n in range(1, precision)]
    known = sp.Matrix([cusp, eis])
    observed = sp.Matrix(basis)
    assert known.rank() == observed.rank() == 2
    assert known.col_join(observed).rank() == 2
    return {"eta_product": "eta(q)^2*eta(q^11)^2", "Eisenstein": "11*E2(q^11)-E2(q)",
            "exact_span_match": True, "coefficients_checked": 2*precision}


def independent_pilot_eigenform(basis, pivots):
    precision = len(basis[0])
    primes = [p for p in range(2, precision) if all(p % d for d in range(2, isqrt(p)+1))]
    ap = {}
    for p in primes:
        if p == 2:
            points = 1+sum((y*y+y-x**3-x*x+2*x) % p == 0 for x in range(p) for y in range(p))
            ap[p] = p+1-points
        else:
            squares = {y*y % p for y in range(1, p)}
            ap[p] = -sum(0 if (d := (1+4*(x**3+x*x-2*x)) % p) == 0
                         else (1 if d in squares else -1) for x in range(p))
    assert ap[5] == -3 and ap[389] == 1
    coeff = [0, 1]
    for n in range(2, precision):
        answer, remaining = 1, n
        for p in primes:
            if remaining % p:
                continue
            exponent = 0
            while remaining % p == 0:
                remaining //= p; exponent += 1
            if p == 389:
                value = ap[p]**exponent
            else:
                previous, value = 1, ap[p]
                for _ in range(2, exponent+1):
                    previous, value = value, ap[p]*value-p*previous
            answer *= value
            if remaining == 1:
                break
        assert remaining == 1
        coeff.append(answer)
    matrix = sp.Matrix(basis)
    square = matrix[:, pivots]
    coordinate_column = square.T.inv()*sp.Matrix([coeff[j] for j in pivots])
    assert coordinate_column.T*matrix == sp.Matrix([coeff])
    denominator_loss = max(v5_integer(Fraction(x).denominator) for x in coordinate_column)
    assert denominator_loss == 0
    return {"curve": "y^2+y=x^3+x^2-2x", "coefficients_checked": precision,
            "prime_point_counts": len(primes), "a5": ap[5], "a389": ap[389],
            "exact_q_span_match": True, "coordinate_denominator_v5": denominator_loss}


def compute(root):
    smoke = root/"pole-products-smoke"
    pilot = root/"pole-products-389"
    basis, reports = {}, []
    used = []
    for weight in (2, 4, 6, 10):
        path = smoke/f"M{weight}-basis.json.gz"
        record = load(path); used.append(path)
        assert record["metadata"]["level"] == 11
        basis[weight], report = replay_basis(record, basis)
        reports.append(report)
    independent = independent_level11_weight2(basis[2])
    path = smoke/"pole-core-capsule.json.gz"
    capsule = load(path); used.append(path)
    assert capsule["metadata"]["level"] == 11
    precision = capsule["q_precision_exclusive"]
    assert rows(capsule["M4_q_basis"]) == basis[4]
    assert rows(capsule["M10_q_basis"]) == basis[10]
    e4 = eisenstein(4, precision)
    theta_e4 = [n*x for n, x in enumerate(e4)]
    derivatives = []
    for row in basis[4]:
        first = product(e4, [n*x for n, x in enumerate(row)], precision)
        second = product(row, theta_e4, precision)
        derivatives.append([x-y for x, y in zip(first, second)])
    coordinates = sp.Matrix(rows(capsule["exact_numerator_relations"]))
    quotient = sp.Matrix(rows(capsule["numerator_to_195_quotient"]))
    assert coordinates*sp.Matrix(basis[10]) == sp.Matrix(derivatives)
    assert coordinates.rank() == 3 and quotient.rank() == 7
    assert coordinates*quotient == sp.zeros(4, 7)
    coordinate_loss = max(v5_integer(Fraction(x).denominator) for x in coordinates)
    quotient_loss = max(v5_integer(Fraction(x).denominator) for x in quotient)
    assert coordinate_loss == capsule["diagnostics"]["derivative_coordinate_denominator_v5"]
    assert quotient_loss == capsule["diagnostics"]["quotient_coordinate_denominator_v5"]
    path = pilot/"M2-basis.json.gz"
    pilot_record = load(path); used.append(path)
    assert pilot_record["metadata"]["level"] == 389 and pilot_record["dimension"] == 33
    pilot_basis, pilot_report = replay_basis(pilot_record, {})
    pilot_curve = independent_pilot_eigenform(pilot_basis, pilot_record["pivot_columns"])
    return {"status": "PASS", "smoke_level": 11, "smoke_q_precision_exclusive": precision,
            "smoke_basis_replays": reports, "independent_smoke_M2_identification": independent,
            "smoke_derivative_relation_rank": 3, "smoke_quotient_dimension": 7,
            "smoke_derivative_coefficients_replayed": 4*precision,
            "smoke_derivative_coordinate_denominator_v5": coordinate_loss,
            "smoke_quotient_coordinate_denominator_v5": quotient_loss,
            "pilot_level": 389, "pilot_M2_replay": pilot_report,
            "independent_pilot_eigenform": pilot_curve,
            "source_sha256": {str(path.relative_to(root)): hashlib.sha256(path.read_bytes()).hexdigest()
                              for path in used},
            "scope": "Independent exact Python replay of the actual level11 Sage smoke core and level389 M2 checkpoint. Level389 M4/full core and any CM input projection remain unclaimed."}


def compute_full_pilot(directory):
    """Replay the full pilot without a large rational RREF or inverse."""
    bases, records, reports, used = {}, {}, [], []
    for weight in (2, 4, 6, 10):
        path = directory/f"M{weight}-basis.json.gz"
        record = load(path); used.append(path)
        assert record["metadata"]["level"] == 389
        assert record["dimension"] == 31*(weight-1)+weight+2*(weight//4)
        bases[weight], report = replay_basis(record, bases)
        records[weight] = record
        reports.append(report)
    independent = independent_pilot_eigenform(bases[2], records[2]["pivot_columns"])
    path = directory/"pole-core-capsule.json.gz"
    capsule = load(path); used.append(path)
    assert capsule["metadata"]["level"] == 389
    precision = capsule["q_precision_exclusive"]
    assert len(bases[4][0]) == len(bases[10][0]) == precision
    assert rows(capsule["M4_q_basis"]) == bases[4]
    assert rows(capsule["M10_q_basis"]) == bases[10]
    e4 = eisenstein(4, precision)
    theta_e4 = [n*x for n, x in enumerate(e4)]
    derivatives = []
    for row in bases[4]:
        first = product(e4, [n*x for n, x in enumerate(row)], precision)
        second = product(row, theta_e4, precision)
        derivatives.append([x-y for x, y in zip(first, second)])
    coordinates = rows(capsule["exact_numerator_relations"])
    quotient = rows(capsule["numerator_to_195_quotient"])
    assert len(coordinates) == 99 and all(len(row) == 293 for row in coordinates)
    assert len(quotient) == 293 and all(len(row) == 195 for row in quotient)
    integral_coordinates, row_denominators = clear_row_denominators(coordinates)
    scaled_derivatives = [[d*x for x in row] for d, row in zip(row_denominators, derivatives)]
    derivative_radix_bits = exact_matrix_product_equal(integral_coordinates, bases[10], scaled_derivatives)

    # The stored quotient explicitly contains a 195-by-195 identity submatrix.
    # This certifies its rational rank without an expensive rational RREF.
    identity_rows = {}
    for i, row in enumerate(quotient):
        nonzero = [(j, x) for j, x in enumerate(row) if x]
        if len(nonzero) == 1 and nonzero[0][1] == 1:
            identity_rows.setdefault(nonzero[0][0], i)
    assert set(identity_rows) == set(range(195))
    assert len(set(identity_rows.values())) == 195
    integral_quotient, _ = clear_column_denominators(quotient)
    relation_radix_bits = exact_matrix_product_equal(integral_coordinates, integral_quotient,
                                                     [[0]*195 for _ in range(99)])
    # CQ=0 and rank(Q)=195 give rank(C)<=98. A modular minor of rank98
    # gives the matching lower bound over Q. No asserted Sage rank is trusted.
    rank_prime = None
    for prime in (5, 65537, 65539, 65543, 65551, 65557, 65563, 1000003):
        assert sp.isprime(prime)
        rank = rank_mod(integral_coordinates, prime)
        assert rank <= 98
        if rank == 98:
            rank_prime = prime
            break
    assert rank_prime is not None, "Need another exact relation-rank witness"
    coordinate_loss = max(v5_integer(x.denominator) for row in coordinates for x in row)
    quotient_loss = max(v5_integer(x.denominator) for row in quotient for x in row)
    assert coordinate_loss == capsule["diagnostics"]["derivative_coordinate_denominator_v5"]
    assert quotient_loss == capsule["diagnostics"]["quotient_coordinate_denominator_v5"]
    assert coordinate_loss == 0
    return {"status": "PASS", "level": 389, "q_precision_exclusive": precision,
            "classical_basis_replays": reports,
            "independent_pilot_eigenform": independent,
            "exact_derivative_coefficients_replayed": 99*precision,
            "relation_rank": 98, "relation_rank_lower_bound_prime": rank_prime,
            "relation_rank_upper_bound": "CQ=0 with a rank195 quotient in a293-dimensional numerator space",
            "quotient_dimension": 195, "quotient_identity_minor_rows": [identity_rows[j] for j in range(195)],
            "derivative_coordinate_denominator_v5": coordinate_loss,
            "quotient_coordinate_denominator_v5": quotient_loss,
            "exact_product_method": "Signed Kronecker encoding with a proved coefficient-difference bound; no probabilistic evaluation",
            "derivative_product_radix_bits": derivative_radix_bits,
            "relation_product_radix_bits": relation_radix_bits,
            "source_sha256": {path.name: hashlib.sha256(path.read_bytes()).hexdigest() for path in used},
            "scope": "Independent exact Python replay of completed level389 classical bases, saturation, derivative relations, and195-dimensional quotient. No CM input projection, analytic-tail/backend-lattice identification, cup functional, or regulator comparison is inferred."}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument("--artifact-root", type=Path, help="Original directory containing pole-products-smoke and pole-products-389")
    group.add_argument("--pilot-full", type=Path, help="Completed pilot directory containing all four M-weight checkpoints and the core capsule")
    parser.add_argument("--output", type=Path)
    parser.add_argument("--check", type=Path)
    args = parser.parse_args()
    result = compute_full_pilot(args.pilot_full) if args.pilot_full else compute(args.artifact_root)
    if args.check:
        assert result == json.loads(args.check.read_text())
    text = json.dumps(result, indent=2, sort_keys=True)+"\n"
    if args.output:
        args.output.write_text(text)
    print(text, end="")


if __name__ == "__main__":
    main()
