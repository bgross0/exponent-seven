#!/usr/bin/env python3
"""Exact low-weight-product fallback for the finite de Rham pole core.

Run with sage -python. No installation, network use, or elliptic projection.
Each basis is checkpointed before the following weight is attempted.
"""
from __future__ import annotations

import argparse
import gzip
import hashlib
import json
from pathlib import Path
import platform
import time


def save(path, obj):
    path.parent.mkdir(parents=True, exist_ok=True)
    raw = (json.dumps(obj, sort_keys=True, separators=(",", ":"))+"\n").encode()
    payload = gzip.compress(raw, mtime=0) if path.suffix == ".gz" else raw
    temporary = path.with_name(path.name+".tmp")
    temporary.write_bytes(payload)
    temporary.replace(path)
    return hashlib.sha256(raw).hexdigest()


def load(path):
    raw = path.read_bytes()
    return json.loads(gzip.decompress(raw) if path.suffix == ".gz" else raw)


def rows_json(mat):
    return [[str(x) for x in row] for row in mat.rows()]


class Progress:
    def __init__(self, output):
        self.output = output
        self.start = time.monotonic()
        self.events = []

    def __call__(self, stage, **data):
        event = {"stage": stage, "elapsed_seconds": time.monotonic()-self.start, **data}
        self.events.append(event)
        print(json.dumps(event, sort_keys=True), flush=True)
        save(self.output/"progress.json", self.events)


class Selector:
    """Incremental row selection over a finite field; never asserts Q-span."""
    def __init__(self, sa, prime, length):
        self.sa = sa
        self.field = sa.GF(prime)
        self.length = length
        self.pivots = {}

    def add(self, coefficients):
        row = self.sa.vector(self.field, coefficients)
        if len(row) != self.length:
            raise ValueError("Wrong coefficient vector length")
        for pivot in sorted(self.pivots):
            if row[pivot]:
                row -= row[pivot]*self.pivots[pivot]
        nonzero = row.nonzero_positions()
        if not nonzero:
            return False
        pivot = nonzero[0]
        row *= row[pivot]**(-1)
        self.pivots[pivot] = row
        return True

    def rank(self):
        return len(self.pivots)


def integer_rows(sa, series, precision):
    """Clear bounded q-denominators; preserve exact Q-spans and record scales."""
    rows, scalars = [], []
    for f in series:
        raw = [sa.QQ(f[i]) for i in range(precision)]
        denominator = sa.lcm([x.denominator() for x in raw])
        integral = [sa.ZZ(denominator*x) for x in raw]
        content = sa.gcd(integral)
        if not content:
            raise ArithmeticError("Zero basis element")
        rows.append([x//content for x in integral])
        scalars.append(str(sa.QQ(denominator)/content))
    return sa.matrix(sa.ZZ, rows), scalars


def saturate_five(sa, basis, maximum_rounds, progress, weight):
    """Exact local saturation with an auditable sequence of row operations.

    The supplied coefficient precision must exceed the weight's Sturm bound.
    Each kernel combination is divisible by5 in every saved coefficient.
    Sturm then ensures global q-integrality of the corresponding modular form.
    """
    b = basis
    operations = []
    for round_index in range(maximum_rounds+1):
        reduced = b.change_ring(sa.GF(5))
        kernel = reduced.left_kernel().basis_matrix()
        if kernel.nrows() == 0:
            return b, operations
        if round_index == maximum_rounds:
            raise ArithmeticError("5-saturation round cap reached")
        kernel = kernel.echelon_form()
        pivots = list(kernel.pivots())
        lifted = sa.matrix(sa.ZZ, [[int(x) for x in row] for row in kernel.rows()])
        combinations = lifted*b
        if any(x % 5 for x in combinations.list()):
            raise ArithmeticError("Nonintegral saturation replacement")
        replacements = sa.matrix(sa.ZZ, [[x//5 for x in row]
                                         for row in combinations.rows()])
        replacement_by_row = {pivot: replacements.row(index)
                              for index,pivot in enumerate(pivots)}
        updated = sa.matrix(sa.ZZ, [replacement_by_row.get(index,b.row(index))
                                    for index in range(b.nrows())])
        operations.append({"replace_rows": pivots,
                           "combination_rows": [[int(x) for x in row]
                                                for row in lifted.rows()],
                           "divisor": 5})
        b = updated
        progress("saturating_at_5", weight=weight, round=round_index+1,
                 replaced_rows=len(pivots))
    raise AssertionError("Unreachable saturation state")


def certify_basis(sa, args, meta, weight, matrix, provenance, progress):
    expected = meta["dimensions"][str(weight)]
    if matrix.nrows() != expected:
        raise ArithmeticError(f"M{weight}: obtained {matrix.nrows()}, need {expected}")
    progress("certifying_exact_rank_by_modular_minor", weight=weight,
             dimension=expected,prime=args.selection_prime)
    rank_matrix = matrix.change_ring(sa.GF(args.selection_prime))
    rank_columns = list(rank_matrix.pivots())
    if len(rank_columns) != expected:
        raise ArithmeticError(f"M{weight}: auxiliary-prime rank certificate failed")
    determinant_residue = int(rank_matrix.matrix_from_columns(rank_columns).det())
    if determinant_residue == 0:
        raise ArithmeticError("The alleged rank-certificate minor is zero")
    # An integer minor nonzero modulo a prime is nonzero over Q. With exactly
    # expected rows this is an exact rank proof, without costly QQ elimination.
    exact_rank = expected
    rank_certificate = {"method":"full_size_integer_minor_nonzero_mod_prime",
                        "prime":args.selection_prime,"pivot_columns":rank_columns,
                        "determinant_residue":determinant_residue,
                        "QQ_rank_elimination_performed":False}
    raw = matrix
    saturation = []
    rank_five_before = int(matrix.change_ring(sa.GF(5)).rank())
    if not args.no_saturate_5:
        matrix, saturation = saturate_five(
            sa, matrix, args.max_saturation_rounds, progress, weight)
    rank_five_after = int(matrix.change_ring(sa.GF(5)).rank())
    if not args.no_saturate_5 and rank_five_after != expected:
        raise ArithmeticError("Saturation did not reach full mod5 rank")
    # These columns give a certified unit determinant when 5-saturation succeeds.
    pivot_prime = 5 if rank_five_after == expected else args.selection_prime
    pivot_columns = list(matrix.change_ring(sa.GF(pivot_prime)).pivots())
    if len(pivot_columns) != expected:
        raise ArithmeticError("No full-rank modular pivot minor found")
    checkpoint = {"schema": "product-modular-basis-v1", "metadata": meta,
                  "weight": weight, "dimension": expected,
                  "q_precision_exclusive": args.q_precision,
                  "raw_integer_q_basis": rows_json(raw),
                  "q_basis": rows_json(matrix), "provenance": provenance,
                  "saturation_at_5_operations": saturation,
                  "saturation_index_5_valuation": sum(len(x["replace_rows"])
                                                       for x in saturation),
                  "exact_rank": exact_rank,
                  "exact_rank_certificate": rank_certificate,
                  "rank_mod5_before": rank_five_before,
                  "rank_mod5_after": rank_five_after,
                  "pivot_columns": pivot_columns,
                  "pivot_selection_prime": pivot_prime,
                  "five_saturated_q_lattice": rank_five_after == expected,
                  "sturm_integrality_argument": "q-precision exceeds the full Sturm bound; each rational product is a modular form and each saturation division is checked through this precision.",
                  "elapsed_seconds": time.monotonic()-progress.start}
    checksum = save(args.output/f"M{weight}-basis.json.gz", checkpoint)
    progress("basis_checkpointed", weight=weight, dimension=expected,
             rank_mod5=rank_five_after, saturation_index_5_valuation=
             checkpoint["saturation_index_5_valuation"], sha256=checksum)
    return matrix, checkpoint


def eisenstein(sa, weight, precision, level=1):
    factor = -sa.QQ(2*weight)/sa.bernoulli(weight)
    values = [sa.QQ(1)]+[sa.QQ(0)]*(precision-1)
    for n in range(1, (precision-1)//level+1):
        values[level*n] = factor*sa.sigma(n, weight-1)
    return values


def product_basis(sa, args, meta, weight, left, right, left_weight,
                  right_weight, supplement, supplement_weight, progress):
    target = meta["dimensions"][str(weight)]
    field = sa.GF(args.selection_prime)
    mod_ps = sa.PowerSeriesRing(field, "q", default_prec=args.q_precision)
    exact_ps = sa.PowerSeriesRing(sa.ZZ, "q", default_prec=args.q_precision)
    left_mod = [mod_ps(row.list()).add_bigoh(args.q_precision) for row in left.rows()]
    right_mod = [mod_ps(row.list()).add_bigoh(args.q_precision) for row in right.rows()]
    left_exact = [exact_ps(row.list()).add_bigoh(args.q_precision) for row in left.rows()]
    right_exact = [exact_ps(row.list()).add_bigoh(args.q_precision) for row in right.rows()]
    select = Selector(sa, args.selection_prime, args.q_precision)
    accepted, descriptions = [], []
    attempted = 0
    progress("selecting_products", weight=weight, target_dimension=target,
             factors=[left_weight, right_weight])
    for i in range(len(left_mod)):
        first_j = i if left_weight == right_weight else 0
        for j in range(first_j, len(right_mod)):
            if attempted >= args.max_candidates:
                raise ArithmeticError(f"M{weight}: product candidate cap reached at rank{select.rank()}")
            attempted += 1
            product = left_mod[i]*right_mod[j]
            if select.add([product[n] for n in range(args.q_precision)]):
                exact = left_exact[i]*right_exact[j]
                accepted.append([exact[n] for n in range(args.q_precision)])
                descriptions.append({"kind": "product", "weights": [left_weight,right_weight],
                                     "basis_indices": [i,j]})
            if select.rank() == target:
                break
        if attempted % 128 < len(right_mod):
            progress("product_selection_progress", weight=weight,
                     attempted=attempted, rank=select.rank())
        if select.rank() == target:
            break
    product_rank = select.rank()
    # Explicit level-one Eisenstein oldforms supplement missing low-weight generators.
    if select.rank() < target:
        for old_level in (1, args.level):
            rational = eisenstein(sa, weight, args.q_precision, old_level)
            integral, scales = integer_rows(sa, [rational], args.q_precision)
            row = integral.row(0)
            if select.add(row):
                accepted.append(row.list())
                descriptions.append({"kind": "Eisenstein_oldform", "weight": weight,
                                     "V_level": old_level, "scale": scales[0]})
    eisenstein_rank = select.rank()
    serre_attempted = 0
    # The Serre derivative D_k(f)=theta(f)-(k/12)E2*f is classical of weight k+2.
    # Use the integer multiple (12/gcd(k,12))*D_k to avoid introducing fractions.
    # Iteration supplies a bounded supplement even when weight-2 was not built.
    if select.rank() < target:
        if supplement_weight >= weight or (weight-supplement_weight) % 2:
            raise ArithmeticError("Invalid Serre derivative source weight")
        e2_values = [1]+[-24*sa.sigma(n,1) for n in range(1,args.q_precision)]
        e2_mod = mod_ps(e2_values).add_bigoh(args.q_precision)
        e2_exact = exact_ps(e2_values).add_bigoh(args.q_precision)
        steps = []
        for k in range(supplement_weight,weight,2):
            divisor = int(sa.gcd(k,12))
            steps.append({"input_weight":k, "theta_multiplier":12//divisor,
                          "E2_multiplier":k//divisor})
        for index,source_row in enumerate(supplement.rows()):
            serre_attempted += 1
            candidate = mod_ps(source_row.list()).add_bigoh(args.q_precision)
            for step in steps:
                candidate = (step["theta_multiplier"]*mod_ps.gen()*candidate.derivative()
                             -step["E2_multiplier"]*e2_mod*candidate)
            if select.add([candidate[n] for n in range(args.q_precision)]):
                exact = exact_ps(source_row.list()).add_bigoh(args.q_precision)
                for step in steps:
                    exact = (step["theta_multiplier"]*exact_ps.gen()*exact.derivative()
                             -step["E2_multiplier"]*e2_exact*exact)
                accepted.append([exact[n] for n in range(args.q_precision)])
                descriptions.append({"kind":"scaled_Serre_derivative",
                                     "source_weight":supplement_weight,
                                     "source_basis_index":index, "steps":steps})
            if select.rank() == target:
                break
    progress("product_selection_finished", weight=weight, attempted=attempted,
             product_rank=product_rank, rank_after_explicit_Eisenstein=eisenstein_rank,
             Serre_candidates_tested=serre_attempted,
             rank_after_Serre_derivatives=select.rank())
    if select.rank() != target:
        save(args.output/f"M{weight}-partial.json.gz",
             {"weight": weight, "rank": select.rank(), "target_dimension": target,
              "q_basis": [[str(x) for x in row] for row in accepted],
              "provenance": descriptions, "selection_prime":args.selection_prime,
              "scope": "Partial modular rank; a bad selection prime can lower this rank"})
        raise ArithmeticError(f"M{weight}: candidate rank modulo{args.selection_prime} is{select.rank()} of{target}")
    return certify_basis(sa, args, meta, weight, sa.matrix(sa.ZZ, accepted),
                         {"construction": "low_weight_products", "selected": descriptions,
                          "candidates_tested": attempted,
                          "product_rank_before_Eisenstein": product_rank,
                          "rank_after_Eisenstein":eisenstein_rank,
                          "Serre_candidates_tested":serre_attempted,
                          "selection_prime": args.selection_prime}, progress)


def denominator_valuation(sa, matrix, prime=5):
    return max([int(sa.QQ(x).denominator().valuation(prime))
                for x in matrix.list()] or [0])


def build_quotient(sa, args, meta, b4, b10, c10, progress):
    ps = sa.PowerSeriesRing(sa.QQ, "q", default_prec=args.q_precision)
    q = ps.gen()
    e4 = ps(eisenstein(sa, 4, args.q_precision)).add_bigoh(args.q_precision)
    theta_e4 = q*e4.derivative()
    derivatives = []
    for row in b4.rows():
        b = ps(row.list()).add_bigoh(args.q_precision)
        numerator = e4*(q*b.derivative())-b*theta_e4
        derivatives.append([numerator[j] for j in range(args.q_precision)])
    dseries = sa.matrix(sa.QQ, derivatives)
    basis = b10.change_ring(sa.QQ)
    pivots = c10["pivot_columns"]
    progress("solving_exact_derivative_coordinates", relations=b4.nrows(),
             numerator_dimension=b10.nrows())
    square = basis.matrix_from_columns(pivots)
    coordinates = square.solve_left(dseries.matrix_from_columns(pivots))
    if coordinates*basis != dseries:
        raise ArithmeticError("Derivative q-identity failed")
    relation_rank = int(coordinates.rank())
    if relation_rank != b4.nrows()-1:
        raise ArithmeticError("Derivative kernel is not the expected constant line")
    echelon = coordinates.row_space().basis_matrix()
    relation_pivots = list(echelon.pivots())
    free = [i for i in range(b10.nrows()) if i not in relation_pivots]
    quotient = sa.matrix(sa.QQ, b10.nrows(), len(free))
    for j, column in enumerate(free):
        quotient[column,j] = 1
        for i, pivot in enumerate(relation_pivots):
            quotient[pivot,j] = -echelon[i,column]
    if not (coordinates*quotient).is_zero() or quotient.rank() != len(free):
        raise ArithmeticError("Exact quotient identity failed")
    if args.level == 389 and (relation_rank,len(free)) != (98,195):
        raise ArithmeticError("Pilot dimensions failed")
    coordinate_loss = denominator_valuation(sa, coordinates)
    if c10["five_saturated_q_lattice"] and coordinate_loss:
        raise ArithmeticError("Unexpected 5-denominator despite unit coefficient minor")
    report = {"status": "exact_pole_core_gate_passed", "metadata": meta,
              "M4_dimension": b4.nrows(), "M10_dimension": b10.nrows(),
              "exact_relation_rank": relation_rank, "quotient_dimension": len(free),
              "five_saturated_M10_q_lattice": c10["five_saturated_q_lattice"],
              "derivative_coordinate_denominator_v5": coordinate_loss,
              "quotient_coordinate_denominator_v5": denominator_valuation(sa, quotient),
              "elapsed_seconds": time.monotonic()-progress.start,
              "proper_de_Rham_input_projection_computed": False,
              "geometric_pole_lattice_comparison_proved": False,
              "scope": "Exact finite open de Rham quotient. No CM input projection, residue filter, cup functional, or arithmetic regulator comparison."}
    capsule = {"schema": "pole-core-gate-v1", "metadata": meta,
               "q_precision_exclusive": args.q_precision,
               "M4_q_basis": rows_json(b4), "M10_q_basis": rows_json(b10),
               "exact_numerator_relations": rows_json(coordinates),
               "numerator_to_195_quotient": rows_json(quotient),
               "checks": {"derivative_identity": True,
                          "relation_rank_98": relation_rank == 98,
                          "quotient_dimension_195": len(free) == 195},
               "diagnostics": report,
               "scope": report["scope"]}
    checksum = save(args.output/"pole-core-capsule.json.gz", capsule)
    report["uncompressed_capsule_sha256"] = checksum
    save(args.output/"backend-result.json", report)
    progress("exact_pole_core_passed", relation_rank=relation_rank,
             quotient_dimension=len(free),
             quotient_coordinate_denominator_v5=report["quotient_coordinate_denominator_v5"])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--level", type=int, choices=(11,389), default=389)
    parser.add_argument("--q-precision", type=int, default=390)
    parser.add_argument("--selection-prime", type=int, default=65537)
    parser.add_argument("--max-candidates", type=int, default=20000)
    parser.add_argument("--max-saturation-rounds", type=int, default=30)
    parser.add_argument("--no-saturate-5", action="store_true")
    parser.add_argument("--input-m2", type=Path)
    parser.add_argument("--method", choices=("products","ring"), default="products")
    parser.add_argument("--stop-weight", type=int, choices=(2,4,6,10), default=10)
    parser.add_argument("--output", type=Path, default=Path("pole-core-fast-output"))
    parser.add_argument("--plan", action="store_true")
    args = parser.parse_args()
    if args.plan:
        print(json.dumps({"level": args.level, "method": args.method,
                          "q_precision_exclusive": args.q_precision,
                          "weights": [k for k in (2,4,6,10) if k <= args.stop_weight],
                          "stop_weight": args.stop_weight,"local_saturation_prime": 5,
                          "pilot_expected_dimensions": [33,99,163,293],
                          "pilot_expected_relation_rank": 98,
                          "pilot_expected_quotient_dimension": 195,
                          "measured_runtime": None,
                          "scope": "Execution plan only"}, indent=2))
        return
    try:
        import sage.all as sa
        from sage.env import SAGE_VERSION
    except ImportError as exc:
        raise SystemExit("Run with sage -python; no Sage installation was attempted.") from exc
    if args.q_precision < 2 or args.q_precision > 5000:
        parser.error("q-precision must be between2 and5000")
    if not sa.is_prime(args.selection_prime) or args.selection_prime == 5:
        parser.error("selection-prime must be a prime other than5")
    progress = Progress(args.output)
    spaces = {k: sa.ModularForms(args.level,k) for k in (2,4,6,10)}
    dimensions = {str(k): int(m.dimension()) for k,m in spaces.items()}
    bounds = {str(k): int(m.sturm_bound()) for k,m in spaces.items()}
    if args.q_precision <= max(bounds[str(k)] for k in (2,4,6,10) if k <= args.stop_weight):
        raise SystemExit("q-precision must be strictly greater than every requested weight's Sturm bound")
    meta = {"sage_version": SAGE_VERSION, "python_version": platform.python_version(),
            "source_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            "level": args.level, "dimensions": dimensions, "sturm_bounds": bounds,
            "method": args.method,
            "operator_convention": "Rows; numerator coordinate row v maps to v*Q."}
    if args.level == 389 and dimensions != {"2":33,"4":99,"6":163,"10":293}:
        raise ArithmeticError("Unexpected pilot dimensions")
    progress("starting", metadata=meta, q_precision_exclusive=args.q_precision)
    if args.input_m2:
        checkpoint = load(args.input_m2)
        if checkpoint["weight"] != 2 or checkpoint["metadata"]["level"] != args.level:
            raise ArithmeticError("Wrong M2 checkpoint level or weight")
        if checkpoint["q_precision_exclusive"] < args.q_precision:
            raise ArithmeticError("M2 checkpoint precision is insufficient")
        raw2 = sa.matrix(sa.ZZ, [[sa.ZZ(x) for x in row[:args.q_precision]]
                                 for row in checkpoint["q_basis"]])
        source2 = {"construction": "checkpoint", "path": str(args.input_m2),
                   "sha256": hashlib.sha256(args.input_m2.read_bytes()).hexdigest()}
    else:
        progress("computing_M2_directly", dimension=dimensions["2"])
        start2 = time.monotonic()
        series2 = spaces[2].q_expansion_basis(prec=args.q_precision)
        raw2, scales2 = integer_rows(sa, series2, args.q_precision)
        source2 = {"construction": "Sage_ModularForms_q_expansion_basis",
                   "weight": 2, "rational_row_scales": scales2,
                   "M2_q_expansion_seconds": time.monotonic()-start2}
        # Preserve this expensive result even if a later certification is interrupted.
        save(args.output/"M2-raw.json.gz",
             {"schema": "product-modular-basis-v1", "metadata": meta, "weight": 2,
              "q_precision_exclusive": args.q_precision,
              "q_basis": rows_json(raw2), "provenance": source2})
        progress("M2_raw_checkpointed", **source2)
    bases = {}
    records = {}
    bases[2], records[2] = certify_basis(sa,args,meta,2,raw2,source2,progress)
    if args.method == "products":
        for weight,a,b in ((4,2,2),(6,2,4),(10,4,6)):
            if weight > args.stop_weight:
                break
            supplement_weight = max(k for k in bases if k < weight)
            bases[weight], records[weight] = product_basis(
                sa,args,meta,weight,bases[a],bases[b],a,b,
                bases[supplement_weight],supplement_weight,progress)
    else:
        ring = sa.ModularFormsRing(args.level)
        for weight in (4,6,10):
            if weight > args.stop_weight:
                break
            progress("building_via_Sage_ring", weight=weight)
            series = ring.q_expansion_basis(weight,prec=args.q_precision,use_random=False)
            raw, scales = integer_rows(sa,series,args.q_precision)
            bases[weight], records[weight] = certify_basis(
                sa,args,meta,weight,raw,
                {"construction": "Sage_ModularFormsRing_q_expansion_basis",
                 "rational_row_scales": scales},progress)
    if args.stop_weight < 10:
        report = {"status":"exact_low_weight_bases_passed","metadata":meta,
                  "stop_weight":args.stop_weight,
                  "completed_dimensions":{str(k):b.nrows() for k,b in bases.items()},
                  "elapsed_seconds":time.monotonic()-progress.start,
                  "pole_quotient_computed":False,
                  "scope":"Certified low-weight basis checkpoints only; the quotient stage was not requested."}
        save(args.output/"basis-result.json",report)
        progress("requested_low_weights_passed",stop_weight=args.stop_weight,
                 completed_dimensions=report["completed_dimensions"])
        return
    build_quotient(sa,args,meta,bases[4],bases[10],records[10],progress)


if __name__ == "__main__":
    main()
