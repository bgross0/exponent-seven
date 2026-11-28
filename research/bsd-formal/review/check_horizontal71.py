"""Independent integer-only review of the proposed degree-seven correspondence.

This checks the literal algebraic certificates and residue assertions. It does
not identify either polynomial with arithmetic CM/isogeny objects, and is not
a replacement for the Lean kernel proof.
"""
from hashlib import sha256
from math import gcd
from pathlib import Path
import ast
import json
import re
import sys


def clean(poly):
    return {ij: value for ij, value in poly.items() if value}


def add(*polys):
    out = {}
    for poly in polys:
        for ij, value in poly.items():
            out[ij] = out.get(ij, 0) + value
    return clean(out)


def mul(left, right):
    out = {}
    for (i, j), a in left.items():
        for (k, ell), b in right.items():
            key = (i + k, j + ell)
            out[key] = out.get(key, 0) + a * b
    return clean(out)


def scale(a, poly):
    return clean({ij: a * value for ij, value in poly.items()})


def rows_poly(rows):
    return clean({(i, j): value for j, row in enumerate(rows)
                  for i, value in enumerate(row)})


def derivative_y(poly):
    return {(i, j - 1): j * value for (i, j), value in poly.items() if j}


def literal_list(path, name):
    text = path.read_text()
    start_def = re.search(rf"^def {re.escape(name)}\s*:.*?:=\s*", text, re.M)
    assert start_def is not None, (path, name)
    start = text.index("[", start_def.end())
    depth = 0
    for end in range(start, len(text)):
        depth += (text[end] == "[") - (text[end] == "]")
        if depth == 0:
            return ast.literal_eval(text[start:end + 1])
    raise ValueError((path, name, "unterminated list"))


def run(path):
    source_hashes = {}
    if path.is_dir():
        source = path / "BSDHorizontal71.lean"
        hsource = path / "BSDHenselWitness.lean"
        tables = path / "BSDFiniteWitness.lean"
        denominator = re.search(r"^def commonDenominator : ℕ := (\d+)$", source.read_text(), re.M)
        assert denominator is not None
        data = {"denominator": int(denominator.group(1)),
                "H": literal_list(hsource, "candidate71Coefficients")}
        for key, name in [("q", "horizontalCoefficients"),
                          ("s", "cofactorCoefficients"),
                          ("ell", "verticalCoefficients"),
                          ("rphi", "modularRemainderCoefficients"),
                          ("rh", "classRemainderCoefficients")]:
            data[key] = literal_list(source, name)
        roots = literal_list(tables, "cm71Roots433")
        graph = literal_list(tables, "cm71Graph433")
        raw = (json.dumps(data, sort_keys=True) + "\n").encode()
        source_hashes = {p.name: sha256(p.read_bytes()).hexdigest()
                         for p in [source, hsource, tables]}
    else:
        raw = path.read_bytes()
        data = json.loads(raw)
        roots = [(28588000027, 10435564403), (28588000027, 24716560718),
                 (33616723189, 25864771405), (33616723189, 9287353716),
                 (3764567456, 0), (7578901485, 6948732840),
                 (7578901485, 28203392281)]
        graph = [[1, 3], [0, 2], [1, 5], [0, 6], [5, 6], [2, 4], [3, 4]]
    D = data["denominator"]
    hx = clean({(i, 0): value for i, value in enumerate(data["H"])})
    hy = clean({(0, i): value for i, value in enumerate(data["H"])})
    phi = {(3, 0): 1, (0, 3): 1, (2, 2): -1,
           (2, 1): 1488, (1, 2): 1488, (2, 0): -162000,
           (0, 2): -162000, (1, 1): 40773375,
           (1, 0): 8748000000, (0, 1): 8748000000,
           (0, 0): -157464000000000}
    q, ell, s, rphi, rh = [rows_poly(data[name])
                           for name in ["q", "ell", "s", "rphi", "rh"]]
    assert not add(scale(D * D, phi), scale(-1, mul(q, ell)),
                   scale(-1, mul(hx, rphi)))
    assert not add(scale(D * D, hy), scale(-1, mul(q, s)),
                   scale(-1, mul(hx, rh)))

    modulus = 433 ** 4
    assert len(roots) == len(graph) == 7

    def pair_add(a, b):
        return ((a[0] + b[0]) % modulus, (a[1] + b[1]) % modulus)

    def pair_mul(a, b):
        return ((a[0] * b[0] + 5 * a[1] * b[1]) % modulus,
                (a[0] * b[1] + a[1] * b[0]) % modulus)

    def pair_pow(a, n):
        result = (1, 0)
        for _ in range(n):
            result = pair_mul(result, a)
        return result

    def evaluate(poly, a, b):
        result = (0, 0)
        for (i, j), value in poly.items():
            term = pair_mul(pair_pow(a, i), pair_pow(b, j))
            result = pair_add(result, (value * term[0], value * term[1]))
        return result

    def is_unit(a):
        return gcd(a[0] * a[0] - 5 * a[1] * a[1], modulus) == 1

    assert gcd(D, modulus) == 1
    for j, root in enumerate(roots):
        assert evaluate(hy, (0, 0), root) == (0, 0)
        assert is_unit(evaluate(derivative_y(hy), (0, 0), root))
    for i, a in enumerate(roots):
        for j, b in enumerate(roots):
            is_edge = j in graph[i]
            assert (evaluate(q, a, b) == (0, 0)) == is_edge
            if is_edge:
                assert is_unit(evaluate(derivative_y(q), a, b))
                assert evaluate(phi, a, b) == (0, 0)
            else:
                assert is_unit(evaluate(phi, a, b))

    return {
        "certificate_sha256": sha256(raw).hexdigest(),
        "independent_checker_sha256": sha256(Path(__file__).read_bytes()).hexdigest(),
        "source_sha256": source_hashes,
        "source_mode": "direct Lean literals" if source_hashes else "generator JSON",
        "arithmetic": "Python integers only; sparse bivariate coefficient dictionaries",
        "exact_bivariate_identities": 2,
        "denominator_coprime_to_modulus": True,
        "denominator_mod_433": D % 433,
        "candidate_root_residues": 7,
        "candidate_derivative_unit_checks": 7,
        "directed_horizontal_edges": 14,
        "horizontal_derivative_unit_checks": 14,
        "nonedge_phi_unit_checks": 35,
        "status": "PASS",
        "arithmetic_CM_identification_claimed": False,
        "Lean_kernel_verification_claimed": False,
    }


if __name__ == "__main__":
    print(json.dumps(run(Path(sys.argv[1])), indent=2))
