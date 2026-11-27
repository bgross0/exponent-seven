#!/usr/bin/env python3
"""Selected-index contraction for the E389/K(-71) CM tame-trace jets.

Only raw q coefficients at n and 71*n are formed.  A single cyclotomic
three-term jet product serves both V389 placements and both depletion
conventions.  This is an arithmetic input generator, not a nonvanishing test
for a projected analytic class or global regulator.
"""

from __future__ import annotations

import argparse
from array import array
from concurrent.futures import ProcessPoolExecutor
import gzip
import hashlib
import importlib.util
import io
import json
from pathlib import Path
import resource
import sys
import time


HERE = Path(__file__).resolve().parent
BASE = HERE.parent
CM_PATH = BASE / "reflected_pilot" / "cm_weight_jets.py"
REFERENCE_PATH = BASE / "tame_trace_compute" / "traces.json"
REFERENCE_SHA256 = "4117034c9ef61b5cc09d81e4c42f3449624e82216b12e5e639cc25107541148a"
sys.dont_write_bytecode = True
spec = importlib.util.spec_from_file_location("cm_weight_jets", CM_PATH)
cm = importlib.util.module_from_spec(spec)
assert spec.loader is not None
spec.loader.exec_module(cm)

CASE_NAMES = (
    "g_depleted_times_V389_h",
    "V389_g_depleted_times_h",
    "both_depleted_g_times_V389_h",
    "both_depleted_V389_g_times_h",
)


def canonical_bytes(value):
    return (json.dumps(value, sort_keys=True, separators=(",", ":")) + "\n").encode()


def deterministic_gzip(value):
    stream = io.BytesIO()
    with gzip.GzipFile(filename="", mode="wb", fileobj=stream,
                      compresslevel=9, mtime=0) as f:
        f.write(value)
    return stream.getvalue()


def conjugate(a, modulus):
    """zeta -> zeta^-1 in the six-coordinate Phi_7 basis."""
    a0, a1, a2, a3, a4, a5 = a
    return ((a0-a1) % modulus, -a1 % modulus, (a5-a1) % modulus,
            (a4-a1) % modulus, (a3-a1) % modulus, (a2-a1) % modulus)


class PackedRing:
    """Carry-free multiplication of three-term jets in (Z/M)[zeta_7]."""

    def __init__(self, modulus):
        self.modulus = modulus
        # A polynomial coefficient of a product is a sum of at most six
        # terms.  The W^2 jet coefficient sums three such products.
        self.width = (18*(modulus-1)**2).bit_length()
        self.mask = (1 << self.width)-1
        assert (1 << self.width) > 18*(modulus-1)**2

    def pack(self, a):
        return sum(int(c) << (self.width*i) for i, c in enumerate(a))

    def unpack(self, a):
        return tuple((a >> (self.width*i)) & self.mask for i in range(6))

    def reduce(self, product):
        """Degree<=10 product, first modulo X^7-1, then modulo Phi_7."""
        w, mask, modulus = self.width, self.mask, self.modulus
        c6 = (product >> (6*w)) & mask
        return (
            ((product & mask)+((product >> (7*w)) & mask)-c6) % modulus,
            (((product >> w) & mask)+((product >> (8*w)) & mask)-c6) % modulus,
            (((product >> (2*w)) & mask)+((product >> (9*w)) & mask)-c6) % modulus,
            (((product >> (3*w)) & mask)+((product >> (10*w)) & mask)-c6) % modulus,
            (((product >> (4*w)) & mask)-c6) % modulus,
            (((product >> (5*w)) & mask)-c6) % modulus,
        )

    def jet_product(self, a, b):
        a0, a1, a2 = a
        b0, b1, b2 = b
        return (self.reduce(a0*b0),
                self.reduce(a1*b0+a0*b1),
                self.reduce(a2*b0+a1*b1+a0*b2))


class UnitLogs:
    def __init__(self, digits):
        self.digits, self.modulus, self.logmod = digits, 5**digits, 5**(digits+1)
        log6 = cm.log5_unit(6, digits+1)
        assert log6 % 5 == 0 and log6 % 25 != 0
        self.inverse = pow(log6//5, -1, self.modulus)
        self.cache = {}

    def __call__(self, u):
        u %= self.logmod
        assert u % 5
        if u not in self.cache:
            value = cm.log5_unit(u, self.digits+1)
            assert value % 5 == 0
            self.cache[u] = value//5*self.inverse % self.modulus
        return self.cache[u]


def cm_table(bound, residue, digits, ring, logs, only_prime_to_5=False):
    """Compact CM tables, then packed ring elements; no product q-series."""
    modulus = 5**digits
    kind = "H" if modulus <= 2**16 else "I" if modulus <= 2**32 else "Q"
    assert modulus <= 2**64
    columns = [array(kind, [0])*(6*(bound+1)) for _ in range(3)]
    root = cm.lift_root(residue, 5, digits+1)
    eta_log = logs(10+root)*pow(7, -1, modulus) % modulus
    counts = {"enumerated_ideals": 0, "ideals_prime_to_selected_p": 0}
    for n, k, u, v in cm.ideal_elements(bound):
        counts["enumerated_ideals"] += 1
        if only_prime_to_5 and n % 5 == 0:
            continue
        image = (u+v*root) % logs.logmod
        if image % 5 == 0:
            continue
        counts["ideals_prime_to_selected_p"] += 1
        lam = (logs(image)-k*eta_log) % modulus
        weights = (1, lam, (lam*(lam-1)//2) % modulus)
        character_power = (-k) % 7
        offset = 6*n
        if character_power < 6:
            for col, value in zip(columns, weights):
                j = offset+character_power
                col[j] = (col[j]+value) % modulus
        else:
            for col, value in zip(columns, weights):
                for j in range(offset, offset+6):
                    col[j] = (col[j]-value) % modulus
    packed = [[ring.pack(col[6*n:6*n+6]) for n in range(bound+1)] for col in columns]
    counts["compact_table_storage_bytes"] = sum(len(c)*c.itemsize for c in columns)
    counts["packed_table_storage_upper_bound_bytes"] = sum(sys.getsizeof(c)+sum(map(sys.getsizeof, c)) for c in packed)
    return packed, counts


def add_weighted(target, product, exponent, modulus):
    """Add (1+W)^exponent * product through W^2, with delayed reduction."""
    p0, p1, p2 = product
    c2 = (exponent*(exponent-1)//2) % modulus
    for r in range(6):
        target[0][r] += p0[r]
        target[1][r] += p1[r]+exponent*p0[r]
        target[2][r] += p2[r]+exponent*p1[r]+c2*p0[r]


def branch_trace(bound, digits, residue):
    started = time.perf_counter()
    modulus, raw_bound = 5**digits, 71*bound
    # Both factors are cuspidal and the raised one starts at q^389.
    table_bound = max(0, raw_bound-389)
    ring, logs = PackedRing(modulus), UnitLogs(digits)
    g, counts = cm_table(table_bound, residue, digits, ring, logs)
    generated = time.perf_counter()
    small = []
    for j in range(1, min(table_bound, (raw_bound-1)//389)+1):
        gj = tuple(col[j] for col in g)
        if not any(gj):
            continue
        hj = tuple(ring.pack(conjugate(ring.unpack(x), modulus)) for x in gj)
        small.append((389*j, hj, j % 5 != 0, logs(389*j) if j % 5 else None))
    targets = sorted(set(range(1, bound+1)) | {71*n for n in range(1, bound+1)})
    output = {name: [[[0]*6 for _ in range(bound+1)] for _ in range(3)] for name in CASE_NAMES}
    digest = hashlib.sha256()
    pairs_possible = sum(max(0, (m-1)//389) for m in targets)
    full_blocks, full_remainder = divmod(raw_bound-1, 389)
    full_pairs = 389*full_blocks*(full_blocks-1)//2 + full_blocks*(full_remainder+1)
    pairs_nonzero = 0
    pairs_products = 0
    for m in targets:
        # A/B: both indices prime to 5.  Extra A/B: only the differentiated
        # factor is prime to 5.  Conjugate B only after summing all pairs.
        A, B, extra_A, extra_B = ([[0]*6 for _ in range(3)] for _ in range(4))
        for shift, hj, j_unit, log_389j in small:
            if shift >= m:
                break
            i = m-shift
            gi = (g[0][i], g[1][i], g[2][i])
            if not any(gi):
                continue
            pairs_nonzero += 1
            i_unit = i % 5 != 0
            if not i_unit and not j_unit:
                continue
            P = ring.jet_product(gi, hj)
            pairs_products += 1
            if i_unit:
                add_weighted(A if j_unit else extra_A, P, -logs(i), modulus)
            if j_unit:
                add_weighted(B if i_unit else extra_B, P, -log_389j, modulus)
        raw = (
            [[(A[o][r]+extra_A[o][r]) % modulus for r in range(6)] for o in range(3)],
            [conjugate([B[o][r]+extra_B[o][r] for r in range(6)], modulus) for o in range(3)],
            [[c % modulus for c in row] for row in A],
            [conjugate(row, modulus) for row in B],
        )
        digest.update(canonical_bytes([m, raw]))
        destinations = []
        if m <= bound:
            destinations.append(m)
        if m % 71 == 0:
            destinations.append(m//71)
        for name, jet in zip(CASE_NAMES, raw):
            for n in destinations:
                for o in range(3):
                    row = output[name][o][n]
                    for r in range(6):
                        row[r] = (row[r]+jet[o][r]) % modulus
    ended = time.perf_counter()
    counts.update({
        "cm_table_q_bound": table_bound,
        "raw_product_q_bound": raw_bound,
        "selected_raw_product_indices": len(targets),
        "all_possible_selected_convolution_pairs": pairs_possible,
        "all_possible_full_convolution_pairs_for_one_placement": full_pairs,
        "pairs_with_nonzero_CM_jets": pairs_nonzero,
        "cyclotomic_jet_products_evaluated": pairs_products,
        "ordinary_integer_multiplications_per_jet_product": 6,
        "packed_radix_bits": ring.width,
        "unit_log_cache_entries": len(logs.cache),
        "selected_raw_product_sha256": digest.hexdigest(),
    })
    performance = {
        "CM_table_seconds": round(generated-started, 6),
        "contraction_seconds": round(ended-generated, 6),
        "total_seconds": round(ended-started, 6),
        "process_peak_RSS_KiB": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
    }
    return residue, output, counts, performance


def certify_ring(digits):
    """Exact adversarial packing checks, including the maximum carry bound."""
    modulus, checks = 5**digits, 0
    ring = PackedRing(modulus)
    vectors = [tuple(int(i == j) for i in range(6)) for j in range(6)]
    vectors += [(modulus-1,)*6, tuple((17*i*i+9*i+1) % modulus for i in range(6)),
                (0,)*6]
    for a in vectors:
        for b in vectors:
            pa, pb = ring.pack(a), ring.pack(b)
            assert ring.reduce(pa*pb) == cm.mul(a, b, modulus)
            triple = ring.jet_product((pa, pa, pa), (pb, pb, pb))
            expected = cm.mul(a, b, modulus)
            assert triple == (expected, cm.scale(expected, 2, modulus), cm.scale(expected, 3, modulus))
            checks += 4
    a, b = (vectors[0], vectors[3], vectors[6]), (vectors[5], vectors[1], vectors[7])
    result = ring.jet_product(tuple(map(ring.pack, a)), tuple(map(ring.pack, b)))
    for order in range(3):
        expected = (0,)*6
        for j in range(order+1):
            expected = cm.add(expected, cm.mul(a[j], b[order-j], modulus), modulus)
        assert result[order] == expected
        checks += 1
    return checks


def build(bound=128, digits=5, embeddings=(2, 4), workers=1):
    assert bound >= 1 and 1 <= digits <= 27
    assert embeddings and set(embeddings) <= {2, 4}
    assert workers in (1, 2)
    reference_bytes = REFERENCE_PATH.read_bytes()
    assert hashlib.sha256(reference_bytes).hexdigest() == REFERENCE_SHA256
    reference = json.loads(reference_bytes)
    modulus = 5**digits
    ring_checks = certify_ring(digits)
    if workers == 2 and len(embeddings) > 1:
        with ProcessPoolExecutor(max_workers=2) as executor:
            futures = [executor.submit(branch_trace, bound, digits, r) for r in embeddings]
            results = [f.result() for f in futures]
    else:
        results = [branch_trace(bound, digits, r) for r in embeddings]
    traces, counts, performance = {}, {}, {}
    overlap_checks = 0
    depletion_U5_zero_checks = 0
    overlap_modulus = min(modulus, reference["coefficient_ring"]["modulus"])
    overlap_bound = min(bound, reference["q_precision"]["largest_coefficient"])
    for residue, branch, stats, timing in results:
        key = str(residue)
        traces[key], counts[key], performance[key] = branch, stats, timing
        for name, jet in branch.items():
            old = reference["common_traces_orders_0_1_2"][key][name]
            for order in range(3):
                for n in range(overlap_bound+1):
                    assert tuple(c % overlap_modulus for c in jet[order][n]) == tuple(
                        c % overlap_modulus for c in old[order][n]), ("pinned overlap", key, name, order, n)
                    overlap_checks += 1
        # U5(F*V5(H))=(U5 F)*H, and the differentiated factor is
        # 5-depleted.  Tame trace commutes with U5.  Thus each difference
        # between one- and both-depleted inputs is killed by U5.
        for one, both in ((CASE_NAMES[0], CASE_NAMES[2]), (CASE_NAMES[1], CASE_NAMES[3])):
            for order in range(3):
                for n in range(0, bound+1, 5):
                    assert branch[one][order][n] == branch[both][order][n], (
                        "U5 of depletion difference", key, one, order, n)
                    depletion_U5_zero_checks += 1
    result = {
        "schema": "E389-Kminus71-selected-tame-traces-v1",
        "scope": "arithmetic CM trace inputs only; no nonvanishing claim for an analytic projection or global class",
        "coefficient_ring": {"p": 5, "digits": digits, "modulus": modulus,
                             "polynomial": [1]*7,
                             "basis": ["1", "zeta", "zeta^2", "zeta^3", "zeta^4", "zeta^5"]},
        "q_precision": {"largest_coefficient": bound, "remainder": f"O(q^{bound+1})"},
        "weight_coordinate": "W=6^(kappa-1)-1",
        "orders": ["constant", "coefficient of W", "coefficient of W^2 (half of second derivative)"],
        "character_convention": "psi((2,omega))=zeta; h inverts only the finite class character",
        "trace_formula": "Tr1(Xi)=Tr2(Xi)=Xi+U71(Xi); same theorem and conventions as tame_trace_compute",
        "common_traces_orders_0_1_2": traces,
        "counts_by_embedding": counts,
        "verification": {
            "pinned_reference": "../tame_trace_compute/traces.json",
            "pinned_reference_sha256": REFERENCE_SHA256,
            "overlap_q_bound": overlap_bound,
            "overlap_modulus": overlap_modulus,
            "overlap_vector_coefficients_checked": overlap_checks,
            "exact_packed_ring_identities_checked": ring_checks,
            "depletion_difference_U5_zero_vector_coefficients_checked": depletion_U5_zero_checks,
            "CM_arithmetic_module_sha256": hashlib.sha256(CM_PATH.read_bytes()).hexdigest(),
        },
    }
    return result, performance


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--bound", type=int, default=128)
    parser.add_argument("--digits", type=int, default=5)
    parser.add_argument("--embedding", choices=("both", "2", "4"), default="both")
    parser.add_argument("--workers", type=int, choices=(1, 2), default=1)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--receipt", type=Path)
    args = parser.parse_args()
    embeddings = (2, 4) if args.embedding == "both" else (int(args.embedding),)
    started = time.perf_counter()
    result, performance = build(args.bound, args.digits, embeddings, args.workers)
    encoded = canonical_bytes(result)
    compressed = deterministic_gzip(encoded)
    if args.output:
        payload = compressed if args.output.suffix == ".gz" else encoded
        if args.check:
            assert args.output.read_bytes() == payload, "saved artifact differs"
        else:
            args.output.write_bytes(payload)
    else:
        assert not args.check, "--check requires --output"
    receipt = {
        "status": "all checks passed", "bound": args.bound, "digits": args.digits,
        "embeddings": list(embeddings), "workers": args.workers,
        "uncompressed_sha256": hashlib.sha256(encoded).hexdigest(),
        "gzip_sha256": hashlib.sha256(compressed).hexdigest(),
        "uncompressed_bytes": len(encoded), "gzip_bytes": len(compressed),
        "wall_seconds": round(time.perf_counter()-started, 6),
        "parent_process_peak_RSS_KiB": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
        "performance_by_embedding": performance,
        "counts_by_embedding": result["counts_by_embedding"],
        "verification": result["verification"],
        "scope": result["scope"],
    }
    if args.receipt:
        args.receipt.write_text(json.dumps(receipt, indent=2, sort_keys=True)+"\n")
    print(json.dumps(receipt, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
