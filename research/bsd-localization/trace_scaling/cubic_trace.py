#!/usr/bin/env python3
"""One both-depleted CM trace, averaged to the unramified cubic field.

This computes (1+sigma)/2 of the omega=2, both-depleted A input.  It is
an averaged representative with the same E-projected cohomology class under
the separate analytic-target audit.  It is not the identical raw CM family,
and no nonvanishing or final cohomological precision is asserted.
"""

from __future__ import annotations

import argparse
import gzip
import hashlib
import json
from pathlib import Path
import resource
import sys
import time

sys.dont_write_bytecode = True
import selected_trace as st

HERE = Path(__file__).resolve().parent
REFERENCE = HERE / "traces-2048-12.json.gz"
REFERENCE_SHA256 = "fbbe08f468a1d83dc86848f4e40dd352ee8ea230341fc5acf868899a3e05a4cf"


def to_cubic(a, modulus):
    """(a+sigma(a))/2 in 1,xi,xi^2, xi=zeta+zeta^-1."""
    a0, a1, a2, a3, a4, a5 = a
    inv2 = pow(2, -1, modulus)
    return ((2*a0-2*(a2+a5)+a3+a4)*inv2 % modulus,
            (a1-a3-a4)*inv2 % modulus,
            (a2+a5-a3-a4)*inv2 % modulus)


def from_cubic(b, modulus):
    b0, b1, b2 = b
    return ((b0-b1+2*b2) % modulus, 0, (-b1+b2) % modulus,
            -b1 % modulus, -b1 % modulus, (-b1+b2) % modulus)


class PackedCubic(st.PackedRing):
    def average(self, product):
        """Direct sigma-average of a packed product, with only three remainders."""
        w, mask, modulus = self.width, self.mask, self.modulus
        inv2 = (modulus+1)//2
        c0 = (product & mask)+((product >> (7*w)) & mask)
        c1 = ((product >> w) & mask)+((product >> (8*w)) & mask)
        c2 = ((product >> (2*w)) & mask)+((product >> (9*w)) & mask)
        c3 = ((product >> (3*w)) & mask)+((product >> (10*w)) & mask)
        c4 = (product >> (4*w)) & mask
        c5 = (product >> (5*w)) & mask
        c6 = (product >> (6*w)) & mask
        return ((2*c0-2*(c2+c5)+c3+c4)*inv2 % modulus,
                (c1+c6-c3-c4)*inv2 % modulus,
                (c2+c5-c3-c4)*inv2 % modulus)

    def averaged_jet_product(self, a, b):
        a0, a1, a2 = a
        b0, b1, b2 = b
        return (self.average(a0*b0), self.average(a1*b0+a0*b1),
                self.average(a2*b0+a1*b1+a0*b2))


def certify_cubic(modulus):
    ring = PackedCubic(modulus)
    vectors = [tuple(int(i == j) for i in range(6)) for j in range(6)]
    vectors += [(modulus-1,)*6, tuple((7*i*i+3*i+2) % modulus for i in range(6)), (0,)*6]
    checks = 0
    for a in vectors:
        avg = st.cm.scale(st.cm.add(a, st.conjugate(a, modulus), modulus), pow(2, -1, modulus), modulus)
        assert from_cubic(to_cubic(a, modulus), modulus) == avg
        assert st.conjugate(avg, modulus) == avg
        checks += 2
        for b in vectors:
            pa, pb = ring.pack(a), ring.pack(b)
            for multiplier in (1, 2, 3):
                product = multiplier*pa*pb
                assert ring.average(product) == to_cubic(ring.reduce(product), modulus)
                checks += 1
    xi = st.cm.add(st.cm.zeta(1), st.cm.zeta(-1), modulus)
    xi2 = st.cm.mul(xi, xi, modulus)
    xi3 = st.cm.mul(xi2, xi, modulus)
    polynomial = st.cm.add(st.cm.add(xi3, xi2, modulus),
                           st.cm.add(st.cm.scale(xi, -2, modulus), (-1, 0, 0, 0, 0, 0), modulus), modulus)
    assert polynomial == (0,)*6
    assert all((r**3+r*r-2*r-1) % 5 for r in range(5))
    return checks+2


def build(bound=6825, digits=12):
    assert bound >= 1 and 1 <= digits <= 27
    started = time.perf_counter()
    modulus, raw_bound = 5**digits, 71*bound
    ring, logs = PackedCubic(modulus), st.UnitLogs(digits)
    checks = certify_cubic(modulus)
    g, counts = st.cm_table(max(0, raw_bound-389), 2, digits, ring, logs, only_prime_to_5=True)
    generated = time.perf_counter()
    small = []
    for j in range(1, (raw_bound-1)//389+1):
        if j % 5 == 0:
            continue
        gj = (g[0][j], g[1][j], g[2][j])
        if any(gj):
            small.append((389*j, tuple(ring.pack(st.conjugate(ring.unpack(c), modulus)) for c in gj)))
    targets = sorted(set(range(1, bound+1)) | {71*n for n in range(1, bound+1)})
    output = [[[0]*3 for _ in range(bound+1)] for _ in range(3)]
    digest = hashlib.sha256()
    pairs = 0
    for m in targets:
        raw = [[0]*3 for _ in range(3)]
        for shift, hj in small:
            if shift >= m:
                break
            i = m-shift
            if i % 5 == 0:
                continue
            gi = (g[0][i], g[1][i], g[2][i])
            if not any(gi):
                continue
            P0, P1, P2 = ring.averaged_jet_product(gi, hj)
            exponent = -logs(i)
            choose2 = (exponent*(exponent-1)//2) % modulus
            for r in range(3):
                raw[0][r] += P0[r]
                raw[1][r] += P1[r]+exponent*P0[r]
                raw[2][r] += P2[r]+exponent*P1[r]+choose2*P0[r]
            pairs += 1
        raw = [[c % modulus for c in row] for row in raw]
        digest.update(st.canonical_bytes([m, raw]))
        destinations = []
        if m <= bound:
            destinations.append(m)
        if m % 71 == 0:
            destinations.append(m//71)
        for n in destinations:
            for order in range(3):
                for r in range(3):
                    output[order][n][r] = (output[order][n][r]+raw[order][r]) % modulus
    contracted = time.perf_counter()

    reference_bytes = REFERENCE.read_bytes()
    assert hashlib.sha256(reference_bytes).hexdigest() == REFERENCE_SHA256, "pinned q2048 reference differs"
    reference = json.loads(gzip.decompress(reference_bytes))
    prior = reference["common_traces_orders_0_1_2"]["2"]["both_depleted_g_times_V389_h"]
    comparison_modulus = min(modulus, reference["coefficient_ring"]["modulus"])
    comparison_bound = min(bound, reference["q_precision"]["largest_coefficient"])
    comparisons = 0
    for order in range(3):
        for n in range(comparison_bound+1):
            assert tuple(c % comparison_modulus for c in output[order][n]) == to_cubic(
                prior[order][n], comparison_modulus), ("full precision cubic overlap", order, n)
            comparisons += 1
    counts.update({
        "embedding_omega_mod5": 2,
        "raw_product_q_bound": raw_bound,
        "cm_table_q_bound": max(0, raw_bound-389),
        "selected_raw_product_indices": len(targets),
        "shared_cyclotomic_jet_products_evaluated": pairs,
        "packed_radix_bits": ring.width,
        "unit_log_cache_entries": len(logs.cache),
        "selected_raw_averaged_product_sha256": digest.hexdigest(),
    })
    result = {
        "schema": "E389-Kminus71-cubic-averaged-trace-v1",
        "scope": "one averaged representative of an E-projected class; no nonvanishing or final error-bound claim",
        "source_case": "omega=2; both_depleted_g_times_V389_h",
        "averaging": "(1+sigma)/2, sigma(zeta)=zeta^-1; applied to the entire traced q-series",
        "cohomological_justification": "../analytic_target_audit/README.md; averaging preserves the E-projected class, not the raw family",
        "coefficient_ring": {"p": 5, "digits": digits, "modulus": modulus,
                             "basis": ["1", "xi", "xi^2"],
                             "xi": "zeta+zeta^-1", "polynomial_ascending": [-1, -2, 1, 1],
                             "unramified_extension_degree": 3},
        "q_precision": {"largest_coefficient": bound, "remainder": f"O(q^{bound+1})"},
        "weight_coordinate": "W=6^(kappa-1)-1",
        "orders": ["constant", "coefficient of W", "coefficient of W^2 (half of second derivative)"],
        "averaged_trace_orders_0_1_2": output,
        "counts": counts,
        "verification": {
            "exact_cubic_arithmetic_checks": checks,
            "reference": "traces-2048-12.json.gz",
            "reference_gzip_sha256": hashlib.sha256(reference_bytes).hexdigest(),
            "overlap_q_bound": comparison_bound, "overlap_modulus": comparison_modulus,
            "overlap_cubic_vector_coefficients_checked": comparisons,
        },
        "intended_backend_parameters": {
            "matrix_precision_m": 6, "Katz_depth_n": 10,
            "top_classical_weight": 42, "Sturm_ell_prime": 1365,
            "basis_working_precision_m_prime": 8,
            "safe_basis_q_cutoff": 6825, "actual_U5_input_largest_index": 6820,
            "qualification": "parameter sizing only; input-growth norms and critical-slope conditioning still need certified bounds",
        },
    }
    performance = {"CM_table_seconds": round(generated-started, 6),
                   "contraction_seconds": round(contracted-generated, 6),
                   "generation_and_overlap_seconds": round(time.perf_counter()-started, 6)}
    return result, performance


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--bound", type=int, default=6825)
    parser.add_argument("--digits", type=int, default=12)
    parser.add_argument("--output", type=Path, default=HERE / "cubic-trace-6825-12.json.gz")
    parser.add_argument("--receipt", type=Path, default=HERE / "cubic-result.json")
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    started = time.perf_counter()
    result, performance = build(args.bound, args.digits)
    encoded = st.canonical_bytes(result)
    compressed = st.deterministic_gzip(encoded)
    if args.check:
        assert args.output.read_bytes() == compressed, "saved averaged trace differs"
    else:
        args.output.write_bytes(compressed)
    receipt = {"status": "all checks passed", "bound": args.bound, "digits": args.digits,
               "wall_seconds": round(time.perf_counter()-started, 6),
               "process_peak_RSS_KiB": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
               "gzip_bytes": len(compressed), "uncompressed_bytes": len(encoded),
               "gzip_sha256": hashlib.sha256(compressed).hexdigest(),
               "uncompressed_sha256": hashlib.sha256(encoded).hexdigest(),
               "performance": performance, "counts": result["counts"],
               "verification": result["verification"], "scope": result["scope"]}
    if not args.check:
        args.receipt.write_text(json.dumps(receipt, indent=2, sort_keys=True)+"\n")
    print(json.dumps(receipt, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
