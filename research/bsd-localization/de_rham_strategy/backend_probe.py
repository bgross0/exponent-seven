#!/usr/bin/env python3
"""Bounded Sage backend gates. No automatic installation or network access.

Use ordinary Python for --mode plan. Use `sage -python` for the other modes.
The backend is NOT executed or certified by this source file existing.
"""
from __future__ import annotations

import argparse
import gzip
import hashlib
import inspect
import json
from pathlib import Path
import platform
import time


def progress(message):
    print(message, flush=True)


def write_json(path, value, compressed=False):
    data = (json.dumps(value, sort_keys=True, separators=(",", ":")) + "\n").encode()
    path.parent.mkdir(parents=True, exist_ok=True)
    if compressed:
        path.write_bytes(gzip.compress(data, mtime=0))
    else:
        path.write_bytes(data)
    return hashlib.sha256(data).hexdigest()


def plan(digits):
    n = 6 * (digits + 1) // 4
    k = 2 + 4*n
    sturm = k * 390 // 12
    return {"scope": "Backend plan, not a computation of the elliptic CM jet",
            "prime": 5, "level": 389, "weight": 2,
            "matrix_digits": digits, "katz_n": n,
            "top_classical_weight": k,
            "expected_matrix_dimension": 31*(k-1)+k+2*(k//4),
            "expected_sturm_bound": sturm,
            "expected_basis_digits": digits + (n+5)//6,
            "q_precision_exclusive": 5*sturm,
            "safe_trace_largest_coefficient": 5*sturm,
            "integral_input_growth_proved": False,
            "proper_projection_computed": False}


def metadata(sage_version):
    return {"sage_version": sage_version, "python_version": platform.python_version(),
            "backend_source_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            "operator_convention": "Rows: U(e_i)=sum_j A[i,j]e_j; form rows act by c -> cA."}


def katz(args, sa, meta):
    import sage.modular.overconvergent.hecke_series as hs
    job = plan(args.digits)
    source = Path(inspect.getfile(hs))
    meta["sage_hecke_series_source_sha256"] = hashlib.sha256(source.read_bytes()).hexdigest()
    sa.set_random_seed(args.seed)
    progress("Building the Katz basis and finite U5 block; no ordinary projector is applied.")
    start = time.monotonic()
    alist, e, elldash, mdash = hs.higher_level_UpGj(
        sa.ZZ(5), sa.ZZ(389), [sa.ZZ(2)], sa.ZZ(args.digits),
        True, sa.ZZ(6), extra_data=True)
    a = alist[0]
    assert int(elldash) == job["expected_sturm_bound"]
    assert int(mdash) == job["expected_basis_digits"]
    assert a.nrows() == a.ncols() == job["expected_matrix_dimension"]
    assert e.ncols() == 5*elldash
    # The current Sage routine assumes an integral solution of T=A E.
    # Check that finite identity, instead of merely accepting the charpoly.
    r = sa.Zmod(5**args.digits)
    em = e.change_ring(r)
    eshort = em.matrix_from_columns(list(range(int(elldash))))
    up_e = em.matrix_from_columns([5*j for j in range(int(elldash))])
    progress("Checking every coefficient of U5(E)=A E at the matrix precision.")
    residual = a * eshort - up_e
    if not residual.is_zero():
        raise ArithmeticError("Finite U(E)=A E identity failed; do not use this matrix.")
    progress("Preparing both classical stabilization fixtures.")
    qprec = int(5*elldash)
    curve = sa.EllipticCurve([0, 1, 1, -2, 0])
    coeff = list(map(int, curve.anlist(qprec-1)))
    # Hensel lift the unit root of X^2+3X+5 from alpha=2 mod 5.
    modulus = 5**int(mdash)
    alpha = 2
    for d in range(1, int(mdash)):
        old = 5**d
        alpha = next(alpha+t*old for t in range(5)
                     if ((alpha+t*old)**2+3*(alpha+t*old)+5) % (5*old) == 0)
    beta = (-3-alpha) % modulus
    f_alpha = [(coeff[j] - (beta*coeff[j//5] if j % 5 == 0 else 0)) % modulus
               for j in range(qprec)]
    f_beta = [(coeff[j] - (alpha*coeff[j//5] if j % 5 == 0 else 0)) % modulus
              for j in range(qprec)]
    for lam, series in [(alpha, f_alpha), (beta, f_beta)]:
        assert all((series[5*j]-lam*series[j]) % modulus == 0
                   for j in range(int(elldash)))
    capsule = {"schema": "katz-matrix-gate-v1", "metadata": meta,
               "parameters": job, "elldash": int(elldash), "mdash": int(mdash),
               "row_operator_A_mod_5m": [[int(x) for x in row] for row in a.rows()],
               "Katz_E_mod_5mdash": [[int(x) for x in row] for row in e.rows()],
               "classical_fixtures": {"alpha": alpha, "beta": beta,
                                      "f_alpha": f_alpha, "f_beta": f_beta},
               "checks": {"full_finite_U_E_equals_A_E": True,
                          "both_classical_U_eigenidentities": True},
               "scope": "Finite backend geometry; tail and input norm contracts still required."}
    checksum = write_json(args.output / "katz-capsule.json.gz", capsule, True)
    report = {"status": "finite_matrix_gate_passed", "metadata": meta, "parameters": job,
              "uncompressed_capsule_sha256": checksum,
              "elapsed_seconds": time.monotonic()-start,
              "proper_de_Rham_input_projection_computed": False,
              "next_gate": "Katz coordinates of U5(input), measured dual-kernel Smith guard, and input tail bound"}
    write_json(args.output / "backend-result.json", report)
    progress(json.dumps(report, indent=2))


def pole_core(args, sa, meta):
    progress("Constructing the exact M10/E4^2 modulo d(M4/E4) core.")
    start = time.monotonic()
    m4 = sa.ModularForms(389, 4)
    m10 = sa.ModularForms(389, 10)
    precision = max(390, int(m10.sturm_bound())+1)
    m4.set_precision(precision)
    m10.set_precision(precision)
    b4 = [f.q_expansion(precision) for f in m4.integral_basis()]
    b10 = [f.q_expansion(precision) for f in m10.integral_basis()]
    assert len(b4) == 99 and len(b10) == 293
    ps = sa.PowerSeriesRing(sa.QQ, "q", default_prec=precision)
    q = ps.gen()
    e4 = ps([1]+[240*sa.sigma(j, 3) for j in range(1, precision)])
    de4 = q*e4.derivative()
    bmat = sa.matrix(sa.QQ, [[f[j] for j in range(precision)] for f in b10])
    derivatives = []
    for b in b4:
        numerator = e4*(q*b.derivative()) - b*de4
        derivatives.append([numerator[j] for j in range(precision)])
    dmat_q = sa.matrix(sa.QQ, derivatives)
    # Rows of dcoords express E4 theta(b)-b theta(E4) in the M10 basis.
    dcoords = bmat.solve_left(dmat_q)
    assert dcoords*bmat == dmat_q
    assert dcoords.rank() == 98
    echelon = dcoords.row_space().basis_matrix()
    pivots = list(echelon.pivots())
    free = [j for j in range(293) if j not in pivots]
    assert len(free) == 195
    # Q is a right matrix: a row of numerator coordinates v maps to v*Q.
    quotient = sa.matrix(sa.QQ, 293, 195)
    for j, fcol in enumerate(free):
        quotient[fcol, j] = 1
        for i, pcol in enumerate(pivots):
            quotient[pcol, j] = -echelon[i, fcol]
    assert (dcoords*quotient).is_zero() and quotient.rank() == 195
    rational_rows = lambda m: [[str(x) for x in row] for row in m.rows()]
    capsule = {"schema": "pole-core-gate-v1", "metadata": meta,
               "q_precision_exclusive": precision,
               "M4_q_basis": [[str(f[j]) for j in range(precision)] for f in b4],
               "M10_q_basis": rational_rows(bmat),
               "exact_numerator_relations": rational_rows(dcoords),
               "numerator_to_195_quotient": rational_rows(quotient),
               "checks": {"derivative_identity": True, "relation_rank_98": True,
                          "quotient_dimension_195": True},
               "scope": "Open de Rham core; no CM input, residue projection, or cup functional yet."}
    checksum = write_json(args.output / "pole-core-capsule.json.gz", capsule, True)
    report = {"status": "exact_pole_core_gate_passed", "metadata": meta,
              "uncompressed_capsule_sha256": checksum,
              "elapsed_seconds": time.monotonic()-start,
              "proper_de_Rham_input_projection_computed": False}
    write_json(args.output / "backend-result.json", report)
    progress(json.dumps(report, indent=2))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--mode", choices=["plan", "katz", "pole-core"], default="plan")
    parser.add_argument("--digits", type=int, default=6)
    parser.add_argument("--seed", type=int, default=38971)
    parser.add_argument("--output", type=Path, default=Path("de-rham-backend-output"))
    args = parser.parse_args()
    if not 1 <= args.digits <= 12:
        parser.error("This bounded handoff accepts 1 through 12 matrix digits.")
    if args.mode == "plan":
        progress(json.dumps(plan(args.digits), indent=2))
        return
    try:
        import sage.all as sa
        from sage.env import SAGE_VERSION
    except ImportError as exc:
        raise SystemExit("Sage is not available in this Python. Run `sage -python backend_probe.py ...`; no installation was attempted.") from exc
    meta = metadata(SAGE_VERSION)
    if args.mode == "katz":
        katz(args, sa, meta)
    else:
        pole_core(args, sa, meta)


if __name__ == "__main__":
    main()
