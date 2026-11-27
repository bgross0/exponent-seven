#!/usr/bin/env python3
"""Compare the backend-size cubic input to the independent q128 reducer."""

import argparse
import gzip
import hashlib
import json
from pathlib import Path


HERE = Path(__file__).resolve().parent


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    large_bytes = (HERE / "cubic-trace-6825-12.json.gz").read_bytes()
    small_bytes = (HERE.parent / "weight_reflection" / "reduced_trace_inputs.json").read_bytes()
    large = json.loads(gzip.decompress(large_bytes))
    small = json.loads(small_bytes)
    assert large["schema"] == "E389-Kminus71-cubic-averaged-trace-v1"
    assert small["schema"] == "E389-CM-single-cubic-trace-v1"
    assert large["coefficient_ring"]["basis"] == small["coefficient_ring"]["basis"]
    modulus = small["coefficient_ring"]["modulus"]
    assert modulus == 3125 and small["q_bound"] == 128
    checks = 0
    for order in range(3):
        for n in range(small["q_bound"]+1):
            assert [c % modulus for c in large["averaged_trace_orders_0_1_2"][order][n]] == small["coefficients"][order][n], (order, n)
            checks += 1
    result = {
        "status": "all checks passed",
        "comparison_q_bound": small["q_bound"], "comparison_modulus": modulus,
        "cubic_vector_coefficients_checked": checks,
        "scalar_coefficients_checked": 3*checks,
        "large_gzip_sha256": hashlib.sha256(large_bytes).hexdigest(),
        "independent_q128_reducer": "../weight_reflection/reduced_trace_inputs.json",
        "independent_q128_reducer_sha256": hashlib.sha256(small_bytes).hexdigest(),
    }
    encoded = json.dumps(result, indent=2, sort_keys=True)+"\n"
    path = HERE / "cubic-overlap.json"
    if args.check:
        assert path.read_text() == encoded
    else:
        path.write_text(encoded)
    print(encoded, end="")


if __name__ == "__main__":
    main()
