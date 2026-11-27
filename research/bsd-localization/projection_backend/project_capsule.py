#!/usr/bin/env python3
"""Project the existing Sage Katz capsule with a checkable finite certificate.

Usage needs NumPy, not Sage. The output is conditional finite linear algebra:
the CM input-tail estimate and identification with the infinite operator
must be supplied separately before these are certified de Rham coordinates.
"""
from __future__ import annotations

import argparse
import gzip
import hashlib
import json
import itertools
from pathlib import Path
import time

import numpy as np

from finite_projection import (array, matmul_mod, require, solve_integral,
    verify_integral_solution, dual_kernel, verify_dual_kernel,
    normalize_projection, combine_balls, ball_contains_integer)


ROOT = Path(__file__).resolve().parent


def load_json(path):
    data = path.read_bytes()
    return json.loads(gzip.decompress(data) if path.suffix == ".gz" else data)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def write_json(path, obj):
    data = (json.dumps(obj, separators=(",", ":"), sort_keys=True)+"\n").encode()
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(gzip.compress(data, mtime=0) if path.suffix == ".gz" else data)


def prepare_inputs(capsule, trace, scale, input_kind="depleted"):
    require(capsule["schema"] == "katz-matrix-gate-v1", "Unexpected Katz capsule schema")
    schemas = {"depleted": "E389-Kminus71-cubic-averaged-trace-v1",
               "undepleted-product": "E389-Kminus71-undepleted-cubic-trace-v1"}
    require(input_kind in schemas and trace["schema"] == schemas[input_kind], "Unexpected trace schema for the requested input kind")
    p = capsule["parameters"]["prime"]
    require(p == 5 and capsule["parameters"]["level"] == 389 and capsule["parameters"]["weight"] == 2,
            "This adapter is only for the stated pilot")
    m, md = capsule["parameters"]["matrix_digits"], capsule["mdash"]
    ell = capsule["elldash"]
    require(isinstance(scale, int) and 0 <= scale < md, "Scale must leave input precision")
    require(trace["coefficient_ring"]["digits"] >= md, "Trace input has too few digits")
    require(trace["q_precision"]["largest_coefficient"] >= 5*(ell-1), "Trace input is too short")
    e = array(capsule["Katz_E_mod_5mdash"], p**md)
    a = array(capsule["row_operator_A_mod_5m"], p**m)
    require(e.ndim == 2 and e.shape[0] == a.shape[0] == a.shape[1], "Incompatible basis/operator dimensions")
    require(e.shape[1] >= 5*ell, "Katz basis is too short")
    require(np.array_equal(matmul_mod(a, e[:, :ell], p**m), e[:, 5*np.arange(ell)] % p**m),
            "Saved finite U(E)=A E identity fails")
    columns, labels = [], []
    for order in range(3):
        for scalar in range(3):
            columns.append([trace["averaged_trace_orders_0_1_2"][order][5*j][scalar] for j in range(ell)])
            labels.append(f"W{order}_xi{scalar}")
    fixtures = capsule["classical_fixtures"]
    for name in ("alpha", "beta"):
        series = fixtures["f_"+name]
        require(len(series) >= 5*ell, "Classical fixture is too short")
        columns.append([series[5*j] for j in range(ell)])
        labels.append("U_f_"+name)
    rhs = (array(columns, p**md).T * p**scale) % p**md
    return {"p": p, "matrix_digits": m, "fit_digits": md, "operator": a,
            "fit_matrix": e[:, :ell].T, "rhs": rhs, "labels": labels,
            "roots": {name: fixtures[name] for name in ("alpha", "beta")}, "input_kind": input_kind,
            "scope": "Coordinates of the scaled U(input) and equally scaled U(f_lambda) in the finite q-basis"}


def cubic_mul(a, b, modulus):
    coefficients = [0]*5
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            coefficients[i+j] += x*y
    v = coefficients
    return [(v[0]+v[3]-v[4]) % modulus,
            (v[1]+2*v[3]-v[4]) % modulus,
            (v[2]-v[3]+3*v[4]) % modulus]


def transfer_eigenvalues(inputs):
    """Recompute the fixed 5R eigenvalues; compare to the separate witness."""
    p, digits = 5, 8
    modulus = p**digits
    tau = [1, -1, -1]
    tau2 = cubic_mul(tau, tau, modulus)
    denominator = [(tau2[i]+6*tau[i]+(20 if i == 0 else 0)) % modulus for i in range(3)]
    inverse = next(list(x) for x in itertools.product(range(5), repeat=3)
                   if cubic_mul(denominator, x, 5) == [1, 0, 0])
    current = 5
    while current < modulus:
        current = min(current*current, modulus)
        error = cubic_mul(denominator, inverse, current)
        inverse = cubic_mul(inverse, [(2-error[0]) % current, -error[1] % current, -error[2] % current], current)
    require(cubic_mul(denominator, inverse, modulus) == [1, 0, 0], "Euler denominator inverse failed")
    alpha = 2
    for d in range(1, digits):
        alpha = next(alpha+t*5**d for t in range(5)
                     if ((alpha+t*5**d)**2+3*(alpha+t*5**d)+5) % 5**(d+1) == 0)
    beta = (-3-alpha) % modulus
    values = {}
    for name, eigenvalue in (("alpha", alpha), ("beta", beta)):
        require((eigenvalue-inputs["roots"][name]) % 5**min(digits, inputs["fit_digits"]) == 0,
                "Capsule root does not match the fixed elliptic Euler transfer")
        numerator = [2*(6*eigenvalue*(tau[i]+(1 if i == 0 else 0))
                         +5*tau2[i]+33*tau[i]+(58 if i == 0 else 0)) % modulus for i in range(3)]
        values[name] = cubic_mul(numerator, inverse, modulus)
    saved = load_json(ROOT.parent/"cm_product_transfer/transfer-result.json")
    require(saved["matrix_modulus"] == modulus and
            [values["alpha"], values["beta"]] == saved["five_times_R_eigenvalues_U_alpha_beta"],
            "Fixed Euler eigenvalue witness differs")
    return values, digits


def transfer_to_depleted(inputs, coefficients):
    if inputs["input_kind"] == "depleted":
        return {name: {key: coefficients[name][key] for key in inputs["labels"][:9]}
                for name in ("alpha", "beta")}
    values, digits = transfer_eigenvalues(inputs)
    target = {}
    for name in ("alpha", "beta"):
        # Columns of this matrix are multiplication by 5R(lambda) in the
        # integral cubic basis. Divide by5 only after ball propagation.
        columns = [cubic_mul(values[name], [int(i == j) for i in range(3)], 5**digits)
                   for j in range(3)]
        multiplier = list(map(list, zip(*columns)))
        target[name] = {}
        for order in range(3):
            vector = [coefficients[name][f"W{order}_xi{i}"] for i in range(3)]
            for i in range(3):
                ball = combine_balls(vector, multiplier[i], digits, 5)
                ball["denominator_exponent"] += 1
                ball["absolute_digits"] -= 1
                target[name][f"W{order}_xi{i}"] = ball
    return target


def projections(inputs, fit, duals):
    p = inputs["p"]
    coordinates = np.asarray(fit["coordinates"], dtype=np.int64)
    precision = fit["coordinate_digits"]
    result = {}
    for name, fixture_index in (("alpha", 9), ("beta", 10)):
        normalization = coordinates[:, fixture_index]
        result[name] = {}
        for index, label in enumerate(inputs["labels"]):
            result[name][label] = normalize_projection(coordinates[:, index], normalization,
                duals[name], precision, precision, p)
    calibration = load_json(ROOT.parent/"de_rham_strategy/result.json")
    c = calibration["stabilizations_to_omega_eta_columns"]
    cd = calibration["calibration_digits"]
    target = transfer_to_depleted(inputs, result)
    vectors = {}
    target_vectors = {}
    old_vectors = {}
    for label in inputs["labels"][:9]:
        pair = [result[name][label] for name in ("alpha", "beta")]
        vectors[label] = [combine_balls(pair, c[i], cd, p) for i in range(2)]
        target_pair = [target[name][label] for name in ("alpha", "beta")]
        target_vectors[label] = [combine_balls(target_pair, c[i], cd, p) for i in range(2)]
        # Recover the symmetric oldspace coordinate from the tame trace.
        # The eventual global test vector has its own prescribed combination.
        old_vectors[label] = [combine_balls([b], [pow(62, -1, p**cd)], cd, p)
                              for b in target_vectors[label]]
    fixture_checks = {}
    for name in ("alpha", "beta"):
        for other in ("alpha", "beta"):
            b = result[name]["U_f_"+other]
            expected = int(name == other)
            fixture_checks[name+"_on_"+other] = {
                "contains_expected": ball_contains_integer(b, expected),
                "absolute_digits": b["absolute_digits"]}
            require(fixture_checks[name+"_on_"+other]["contains_expected"], "Classical projection fixture failed")
    zero_checks = {label: [ball_contains_integer(b, 0) for b in target_vectors[label]]
                   for label in inputs["labels"][:6]}
    return {"input_kind": inputs["input_kind"], "stabilization_coefficients": result,
            "elliptic_trace_in_omega_eta": vectors,
            "target_depleted_stabilization_coefficients": target,
            "target_depleted_elliptic_trace_in_omega_eta": target_vectors,
            "symmetric_oldspace_coordinate_divided_by_62": old_vectors,
            "classical_fixture_checks": fixture_checks,
            "predicted_lower_zero_diagnostics": zero_checks,
            "interpretation": "The first two coordinate fields describe the selected input. Target-depleted fields apply R(U) when the input is Qplus; they are never identified as raw q-series. All are conditional finite projection balls until the infinite-tail comparison is established."}


def verify_certificate(inputs, certificate):
    p = inputs["p"]
    precision = verify_integral_solution(inputs["fit_matrix"], inputs["rhs"], certificate["fit"], p)
    m = min(inputs["matrix_digits"], precision)
    require(m > 0 and certificate["effective_matrix_digits"] == m, "Wrong effective operator precision")
    coords = array(certificate["fit"]["coordinates"], p**m)
    a = array(inputs["operator"], p**m)
    for name, idx in (("alpha", 9), ("beta", 10)):
        dual = certificate["dual_functionals"][name]
        require(dual["matrix_digits"] == m, "Incorrect dual matrix precision")
        require(dual["eigenvalue"] == inputs["roots"][name] % p**m, "Wrong target root")
        verify_dual_kernel(a, dual, p)
        r = coords[:, idx][None, :]
        require(np.array_equal(matmul_mod(r, a, p**m), (r*dual["eigenvalue"]) % p**m),
                "Fitted classical fixture is not a finite left eigenrow")
    expected = projections(inputs, certificate["fit"], certificate["dual_functionals"])
    require(expected == certificate["projection"], "Projection output differs from its witnesses")
    return expected


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--katz", type=Path, required=True)
    parser.add_argument("--trace", type=Path)
    parser.add_argument("--input-kind", choices=("depleted", "undepleted-product"), default="depleted")
    parser.add_argument("--output", type=Path, default=Path("finite-projection-output"))
    parser.add_argument("--verify", type=Path, help="Verify a saved finite-projection-certificate.json.gz")
    parser.add_argument("--scale", type=int, default=0, help="Multiply all input and normalization rows by 5^scale before fitting")
    args = parser.parse_args()
    if args.trace is None:
        args.trace = (ROOT.parent/"trace_scaling/cubic-trace-6825-12.json.gz" if args.input_kind == "depleted"
                      else ROOT.parent/"cm_product_transfer/cubic-product-6825-12.json.gz")
    start = time.monotonic()
    print("Reading capsule and checking its finite U(E)=A E identity", flush=True)
    inputs = prepare_inputs(load_json(args.katz), load_json(args.trace), args.scale, args.input_kind)
    sources = {"katz_sha256": sha(args.katz), "trace_sha256": sha(args.trace),
               "calibration_sha256": sha(ROOT.parent/"de_rham_strategy/result.json")}
    if args.input_kind == "undepleted-product":
        sources["Euler_transfer_sha256"] = sha(ROOT.parent/"cm_product_transfer/transfer-result.json")
    if args.verify:
        cert = load_json(args.verify)
        require(cert["sources"] == sources and cert["input_scale"] == args.scale
                and cert["input_kind"] == args.input_kind, "Source/scale/input-kind mismatch")
        verify_certificate(inputs, cert)
        print(json.dumps({"status": "finite_certificate_verified", "scope": cert["scope"]}, indent=2))
        return
    print("Fitting eleven scaled U-input columns and constructing the inverse-minor witness", flush=True)
    fit = solve_integral(inputs["fit_matrix"], inputs["rhs"], inputs["p"], inputs["fit_digits"])
    m = min(inputs["matrix_digits"], fit["coordinate_digits"])
    require(m > 0, "No matrix precision remains after the coordinate solve")
    duals = {}
    for name in ("alpha", "beta"):
        print(f"Constructing the {name} dual kernel with a measured inverse-minor guard", flush=True)
        duals[name] = dual_kernel(inputs["operator"], inputs["roots"][name], inputs["p"], m)
    cert = {"schema": "finite-elliptic-projection-v1", "sources": sources,
            "input_scale": args.scale, "input_kind": args.input_kind,
            "fit": fit, "dual_functionals": duals,
            "effective_matrix_digits": m, "projection": projections(inputs, fit, duals),
            "scope": "Finite exact modular linear algebra only. A compatible integral Katz expansion, an infinite-operator comparison, and exact eigenline existence are additional mathematical inputs. No certified CM de Rham value or nonzero reflected logarithm is asserted."}
    print("Verifying the completed certificate independently of the elimination path", flush=True)
    verify_certificate(inputs, cert)
    write_json(args.output/"finite-projection-certificate.json.gz", cert)
    report = {"status": "finite_algebra_certificate_passed", "sources": sources,
              "fit_guard": fit["inverse_minor"]["guard"],
              "coordinate_digits": fit["coordinate_digits"],
              "effective_matrix_digits": m,
              "dual_guards": {name: duals[name]["inverse_minor"]["guard"] for name in duals},
              "projection": cert["projection"], "elapsed_seconds": time.monotonic()-start,
              "scope": cert["scope"]}
    write_json(args.output/"projection-result.json", report)
    print(json.dumps(report, indent=2), flush=True)


if __name__ == "__main__":
    main()
