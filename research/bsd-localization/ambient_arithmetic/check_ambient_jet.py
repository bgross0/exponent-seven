#!/usr/bin/env python3
"""Exact tests for the conditional ambient-H2 / reflected-class reduction.

These are algebraic fixtures, not computed arithmetic Galois cohomology.
Requires SymPy. Default: print stable JSON, without writing any file.
Use --check PATH to compare a saved result, or --output PATH to save one.
"""
import argparse
from itertools import combinations
import json
from pathlib import Path

import sympy as s

t = s.symbols("t")


def at_zero(A):
    return A.applyfunc(lambda a: s.expand(a).subs(t, 0))


def valuation(f):
    f = s.cancel(f)
    if f == 0:
        return None
    num, den = s.fraction(f)
    vp = min(m[0] for m, _ in s.Poly(num, t).terms())
    vq = min(m[0] for m, _ in s.Poly(den, t).terms())
    return int(vp - vq)


def smith_orders(A):
    """t-valuations of nonzero Smith factors via determinantal ideals."""
    delta = [0]
    for k in range(1, min(A.rows, A.cols) + 1):
        vals = []
        for rr in combinations(range(A.rows), k):
            for cc in combinations(range(A.cols), k):
                v = valuation(A.extract(rr, cc).det())
                if v is not None:
                    vals.append(v)
        if not vals:
            break
        delta.append(min(vals))
    return [delta[j] - delta[j - 1] for j in range(1, len(delta))]


def first_bockstein(D):
    """Rank of ker(D0) --D1--> coker(D0), invariant under base changes."""
    D0 = at_zero(D)
    D1 = at_zero(D.diff(t))
    basis = D0.nullspace()
    K0 = s.Matrix.hstack(*basis) if basis else s.zeros(D.cols, 0)
    image = D1 * K0
    beta_rank = D0.row_join(image).rank() - D0.rank()
    return {
        "H1_base_dimension": len(basis),
        "H2_base_dimension": D.rows - D0.rank(),
        "first_bockstein_rank": int(beta_rank),
    }


def conj(v, signs):
    return s.diag(*signs) * v.subs(t, -t)


def vector_json(v):
    return [str(a) for a in v]


def analyze(name, n, signs, Fp, Fb, kappa, ell):
    D = s.Matrix([[0, 0, t**n]])
    F = Fp.col_join(Fb)
    A = D.col_join(F)
    ck = conj(kappa, signs)
    reflected = ((kappa - ck) / t).applyfunc(s.cancel)
    k0, x0 = at_zero(kappa), at_zero(reflected)
    M_basis = s.Matrix([[1, 0], [0, 1], [0, 0]])
    N = s.Matrix.hstack(kappa, ck)[:2, :]
    Phi = F * M_basis

    assert D * kappa == s.zeros(1, 1)
    assert Fp * kappa == s.zeros(1, 1)
    assert valuation((Fb * kappa)[0]) == 2
    assert Fp * ck != s.zeros(1, 1)
    assert Fb * ck == s.zeros(1, 1)
    assert conj(reflected, signs) == reflected
    assert at_zero(A) * x0 == s.zeros(3, 1)
    assert at_zero(A) * k0 == s.zeros(3, 1)
    assert N.det() != 0

    h = sum(smith_orders(D))
    index = valuation(N.det())
    local_index = valuation(Phi.det())
    ordinary_length = sum(smith_orders(A))
    assert ordinary_length == 4
    assert smith_orders(A) == [0, 2, 2]
    assert index == h
    assert local_index + h == ordinary_length
    assert valuation((Phi * N).det()) == 4
    assert valuation(s.Matrix.hstack(kappa, reflected)[:2, :].det()) == h - 1

    log_value = (ell * x0)[0]
    assert bool(log_value != 0) == (h == 1)
    global_beta = first_bockstein(D)
    ordinary_beta = first_bockstein(A)
    assert global_beta["first_bockstein_rank"] == (1 if h == 1 else 0)
    assert ordinary_beta["first_bockstein_rank"] == 0
    assert at_zero(D.diff(t)) * k0 == s.zeros(1, 1)

    # A nonconstant change of cochain basis must not create a Bockstein.
    P = s.Matrix([[1, t, 0], [0, 1, t + t**2], [0, 0, 1]])
    Q = s.Matrix([[1, 0, t], [t, 1, t**2], [0, 0, 1]])
    assert P.det() == 1 and Q.det() == 1
    assert first_bockstein(D * P) == global_beta
    assert first_bockstein(Q * A * P) == ordinary_beta
    assert smith_orders(Q * A * P) == [0, 2, 2]

    # Normalization changes only the original strict line at the base.
    u = 1 + 3*t + 5*t**2
    knew = u * kappa
    xnew = ((knew - conj(knew, signs)) / t).applyfunc(s.cancel)
    assert at_zero(xnew) == x0 + 6*k0
    assert ell * at_zero(xnew) == ell * x0

    # The cochain sign is (-1)^n, not (-1)^(n-1): t is anti-invariant.
    C1 = s.diag(*signs)
    assert D * C1 == D.subs(t, -t)
    assert signs[2] == (-1)**n

    return {
        "name": name,
        "ambient_H2_length": h,
        "reflected_family_index": index,
        "local_quotient_index": local_index,
        "ordinary_smith_t_orders": smith_orders(A),
        "ambient_smith_t_orders": smith_orders(D),
        "global_first_jet": global_beta,
        "ordinary_first_jet": ordinary_beta,
        "ambient_beta_on_strict_kappa0": 0,
        "kappa0": vector_json(k0),
        "reflected_x0": vector_json(x0),
        "model_logarithm": str(log_value),
        "obstructed_base_direction_c_sign": signs[2],
        "basis_change_checks_passed": True,
        "normalization_check_passed": True,
        "scope": "Algebraic fixture; no arithmetic realization asserted.",
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", type=Path,
                        help="Compare the computed result with this JSON file.")
    parser.add_argument("--output", type=Path,
                        help="Write the computed result to this JSON file.")
    args = parser.parse_args()
    models = [
        analyze(
            "even_global_H2_length_two",
            2,
            [1, -1, 1],
            s.Matrix([[t**2, 1, 0]]),
            s.Matrix([[t**2, -1, 0]]),
            s.Matrix([1, -t**2, 0]),
            s.Matrix([[0, 0, 1]]),
        ),
        analyze(
            "odd_global_H2_length_one",
            1,
            [1, 1, -1],
            s.Matrix([[t**2, t, 1]]),
            s.Matrix([[t**2, -t, -1]]),
            s.Matrix([1, -t, 0]),
            s.Matrix([[0, 1, 0]]),
        ),
    ]
    # Explicit warning against replacing 'one-dimensional H2' by 'beta nonzero'.
    mixed = s.diag(t, t**2)
    mixed_jet = first_bockstein(mixed)
    assert mixed_jet["H2_base_dimension"] == 2
    assert mixed_jet["first_bockstein_rank"] == 1
    assert sum(smith_orders(mixed)) == 3

    # Generalized Bockstein theorem: coker beta = tB/t²B in these models.
    for n in range(1, 6):
        D = s.Matrix([[t**n]])
        b = first_bockstein(D)
        assert 1 - b["first_bockstein_rank"] == (0 if n == 1 else 1)

    result = {
        "format": "ambient-arithmetic-jet-check-v1",
        "all_checks_passed": True,
        "models": models,
        "higher_dimensional_H2_guard": mixed_jet,
        "claims_not_verified": [
            "A global Galois-cohomology presentation for the pilot.",
            "The arithmetic value of the anticyclotomic cup product.",
            "The main-conjecture and local-regulator comparison hypotheses.",
            "Arithmetic realization or full Poitou-Tate self-duality of fixtures.",
        ],
    }
    if args.check is not None:
        saved = json.loads(args.check.read_text())
        if saved != result:
            raise SystemExit(f"Result mismatch: {args.check}")
    encoded = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.output is not None:
        args.output.write_text(encoded)
    print(encoded, end="")


if __name__ == "__main__":
    main()
