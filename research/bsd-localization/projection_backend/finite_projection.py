#!/usr/bin/env python3
"""Checked finite p-adic linear algebra, independent of Sage.

The input-lattice and infinite-operator comparisons are separate hypotheses.
NumPy is used only for bounded signed-integer arithmetic, never floating point.
"""
from __future__ import annotations

import numpy as np


class CertificateError(ValueError):
    pass


def require(condition, message):
    if not condition:
        raise CertificateError(message)


def valuation(value, p, cap):
    value = int(value)
    if value == 0:
        return cap
    answer = 0
    while answer < cap and value % p == 0:
        value //= p
        answer += 1
    return answer


def minimum_valuation(values, p, cap):
    return min((valuation(x, p, cap) for x in np.asarray(values).flat), default=cap)


def array(values, modulus):
    require(modulus * modulus < 2**62, "Modulus exceeds the exact int64 scalar-product contract")
    return np.asarray(values, dtype=np.int64) % modulus


def matmul_mod(a, b, modulus):
    """Integer multiplication with a proved per-accumulator overflow bound."""
    a, b = array(a, modulus), array(b, modulus)
    require(a.ndim == b.ndim == 2 and a.shape[1] == b.shape[0], "Matrix dimensions differ")
    out = np.zeros((a.shape[0], b.shape[1]), dtype=np.int64)
    # Each chunk contributes <= chunk*(modulus-1)^2; the old accumulator
    # is < modulus. Taking half of INT64_MAX leaves a strict safety margin.
    block = max(1, (2**62) // max(1, (modulus - 1)**2))
    for start in range(0, a.shape[1], block):
        stop = min(a.shape[1], start + block)
        out = (out + a[:, start:stop] @ b[start:stop, :]) % modulus
    return out


def dot_exact(a, b):
    return sum(int(x)*int(y) for x, y in zip(a, b))


def echelon_local(values, p, digits):
    """Minimum-valuation Gaussian elimination over Z/p^digits.

    Return S, U, permutations with S*A[:,columns] = U. Only unimodular
    row operations and column swaps are used. A nonzero trailing pivot
    of valuation d divides every remaining entry. The visible pivots
    are therefore nondecreasing local elementary-divisor valuations.
    """
    modulus = p**digits
    u = array(values, modulus).copy()
    rows, cols = u.shape
    s = np.eye(rows, dtype=np.int64)
    row_labels, column_labels = list(range(rows)), list(range(cols))
    exponents = []
    previous = 0
    for k in range(min(rows, cols)):
        trailing = u[k:, k:]
        pivot = None
        for d in range(previous, digits):
            mask = (trailing // p**d) % p != 0
            flat = int(np.argmax(mask))
            if bool(mask.flat[flat]):
                i, j = np.unravel_index(flat, trailing.shape)
                pivot = (k+int(i), k+int(j), d)
                break
        if pivot is None:
            break
        i, j, d = pivot
        if i != k:
            u[[k, i], :] = u[[i, k], :]
            s[[k, i], :] = s[[i, k], :]
            row_labels[k], row_labels[i] = row_labels[i], row_labels[k]
        if j != k:
            u[:, [k, j]] = u[:, [j, k]]
            column_labels[k], column_labels[j] = column_labels[j], column_labels[k]
        power = p**d
        inverse_unit = pow(int(u[k, k]) // power, -1, modulus)
        u[k, :] = u[k, :] * inverse_unit % modulus
        s[k, :] = s[k, :] * inverse_unit % modulus
        require(int(u[k, k]) == power, "Pivot normalization failed")
        if k + 1 < rows:
            factors = u[k+1:, k] // power
            u[k+1:, :] = (u[k+1:, :] - factors[:, None]*u[k, :]) % modulus
            s[k+1:, :] = (s[k+1:, :] - factors[:, None]*s[k, :]) % modulus
        exponents.append(d)
        previous = d
    return {"U": u, "S": s, "rows": row_labels, "columns": column_labels,
            "exponents": exponents, "rank_visible": len(exponents)}


def inverse_minor_witness(values, decomposition, p, digits):
    """Extract a scaled inverse of a full-rank visible pivot minor."""
    modulus = p**digits
    a = array(values, modulus)
    r = decomposition["rank_visible"]
    require(r > 0, "Empty minors are not used by this implementation")
    ii = decomposition["rows"][:r]
    jj = decomposition["columns"][:r]
    exponents = decomposition["exponents"]
    guard = max(exponents)
    upper = decomposition["U"][:r, :r]
    powers = np.asarray([p**d for d in exponents], dtype=np.int64)
    require(np.all(upper % powers[:, None] == 0), "Nonintegral row division")
    v = upper // powers[:, None]
    require(np.all(np.diag(v) == 1), "Normalized upper matrix is not unipotent")
    left = decomposition["S"][:r, ii]
    outside = [i for i in range(a.shape[0]) if i not in set(ii)]
    require(not outside or np.all(decomposition["S"][:r, outside] == 0),
            "Pivot rows involve an unselected original row")
    rhs = (np.asarray([p**(guard-d) for d in exponents], dtype=np.int64)[:, None]*left) % modulus
    x = np.zeros_like(rhs)
    for i in range(r-1, -1, -1):
        correction = matmul_mod(v[i:i+1, i+1:], x[i+1:, :], modulus)[0]
        x[i, :] = (rhs[i, :] - correction) % modulus
    witness = {"rows": ii, "columns": jj, "guard": guard,
               "scaled_inverse": x.tolist()}
    verify_inverse_minor(a, witness, p, digits)
    return witness


def verify_inverse_minor(values, witness, p, digits):
    modulus = p**digits
    a = array(values, modulus)
    ii, jj = witness["rows"], witness["columns"]
    require(len(ii) == len(jj) > 0, "Minor must be nonempty and square")
    require(len(set(ii)) == len(ii) and len(set(jj)) == len(jj), "Repeated minor index")
    require(all(isinstance(i, int) and 0 <= i < a.shape[0] for i in ii), "Invalid row index")
    require(all(isinstance(j, int) and 0 <= j < a.shape[1] for j in jj), "Invalid column index")
    c = witness["guard"]
    require(isinstance(c, int) and 0 <= c < digits, "No positive inverse precision remains")
    d = a[np.ix_(ii, jj)]
    x = array(witness["scaled_inverse"], modulus)
    require(x.shape == d.shape, "Wrong inverse shape")
    target = p**c * np.eye(len(ii), dtype=np.int64)
    require(np.array_equal(matmul_mod(d, x, modulus), target), "D*X is not p^c I")
    require(np.array_equal(matmul_mod(x, d, modulus), target), "X*D is not p^c I")
    require(minimum_valuation(x, p, digits) == 0, "Guard is not sharp for this minor")
    return c


def solve_integral(values, rhs, p, digits):
    """Construct and certify a finite integral solution A*x=rhs.

    No claim of an infinite modular-form expansion is made. Any compatible
    exact integral solution is determined modulo p^(digits-guard).
    """
    modulus = p**digits
    a, b = array(values, modulus), array(rhs, modulus)
    require(a.shape[0] == b.shape[0], "Right side has wrong row count")
    e = echelon_local(a, p, digits)
    rank = e["rank_visible"]
    require(rank == a.shape[1], "Coordinate fit has unresolved kernel")
    transformed = matmul_mod(e["S"], b, modulus)
    require(np.all(transformed[rank:, :] == 0), "No finite integral coordinate fit exists")
    z = np.zeros((rank, b.shape[1]), dtype=np.int64)
    for i in range(rank-1, -1, -1):
        power = p**e["exponents"][i]
        delta = (transformed[i, :] - matmul_mod(e["U"][i:i+1, i+1:rank], z[i+1:, :], modulus)[0]) % modulus
        require(np.all(delta % power == 0), "Coordinate fit needs a nonintegral coordinate")
        z[i, :] = delta // power
    x = np.zeros_like(z)
    for i, j in enumerate(e["columns"]):
        x[j, :] = z[i, :]
    inverse = inverse_minor_witness(a, e, p, digits)
    answer = {"coordinates": x.tolist(), "inverse_minor": inverse,
              "input_digits": digits, "coordinate_digits": digits-inverse["guard"]}
    verify_integral_solution(a, b, answer, p)
    return answer


def verify_integral_solution(values, rhs, answer, p):
    digits = answer["input_digits"]
    modulus = p**digits
    a, b = array(values, modulus), array(rhs, modulus)
    x = array(answer["coordinates"], modulus)
    require(x.shape == (a.shape[1], b.shape[1]), "Coordinate shape differs")
    require(np.array_equal(matmul_mod(a, x, modulus), b), "Coordinate residual is nonzero")
    witness = answer["inverse_minor"]
    require(len(witness["columns"]) == a.shape[1], "Fit minor omits coordinate columns")
    c = verify_inverse_minor(a, witness, p, digits)
    require(answer["coordinate_digits"] == digits-c, "Incorrect coordinate precision")
    return digits-c


def dual_kernel(operator, eigenvalue, p, digits):
    modulus = p**digits
    a = array(operator, modulus)
    require(a.ndim == 2 and a.shape[0] == a.shape[1] >= 2, "Operator must be square, dimension >=2")
    b = (a - int(eigenvalue)*np.eye(a.shape[0], dtype=np.int64)) % modulus
    e = echelon_local(b, p, digits)
    require(e["rank_visible"] == a.shape[0]-1,
            "Target packet is not isolated to one visible kernel direction; add Hecke conditions or precision")
    n = a.shape[0]
    z = np.zeros(n, dtype=np.int64)
    z[-1] = 1
    for i in range(n-2, -1, -1):
        power = p**e["exponents"][i]
        delta = (-dot_exact(e["U"][i, i+1:], z[i+1:])) % modulus
        require(delta % power == 0, "Kernel has no integral chosen normalization")
        z[i] = delta // power
    w = np.zeros(n, dtype=np.int64)
    for i, j in enumerate(e["columns"]):
        w[j] = z[i]
    inverse = inverse_minor_witness(b, e, p, digits)
    certificate = {"eigenvalue": int(eigenvalue) % modulus, "matrix_digits": digits,
                   "fixed_coordinate": e["columns"][-1], "primitive_vector": w.tolist(),
                   "inverse_minor": inverse, "direction_digits": digits-inverse["guard"],
                   "scope": "Finite modular kernel; exact eigenline existence and infinite operator comparison are additional hypotheses"}
    verify_dual_kernel(a, certificate, p)
    return certificate


def verify_dual_kernel(operator, certificate, p):
    digits = certificate["matrix_digits"]
    modulus = p**digits
    a = array(operator, modulus)
    b = (a-int(certificate["eigenvalue"])*np.eye(a.shape[0], dtype=np.int64)) % modulus
    w = array(certificate["primitive_vector"], modulus)
    require(w.shape == (a.shape[0],), "Kernel vector shape differs")
    j = certificate["fixed_coordinate"]
    require(isinstance(j, int) and 0 <= j < len(w) and int(w[j]) == 1, "Kernel normalization is not one")
    require(np.all(matmul_mod(b, w[:, None], modulus) == 0), "Kernel residual is nonzero")
    minor = certificate["inverse_minor"]
    require(set(minor["columns"]) == set(range(a.shape[0]))-{j}, "Minor does not complement fixed coordinate")
    c = verify_inverse_minor(b, minor, p, digits)
    require(certificate["direction_digits"] == digits-c, "Incorrect kernel precision")
    return digits-c


def quotient_ball(numerator, denominator, numerator_digits, denominator_digits, p):
    """A/B with independently certified absolute precisions.

    If v=v_p(B), t=min(v_p(A), numerator_digits), the absolute precision
    is min(numerator_digits-v, denominator_digits+t-2v).
    """
    numerator %= p**numerator_digits
    denominator %= p**denominator_digits
    v = valuation(denominator, p, denominator_digits)
    require(v < denominator_digits, "Normalization is not certified nonzero")
    t = valuation(numerator, p, numerator_digits)
    absolute = min(numerator_digits-v, denominator_digits+t-2*v)
    relative = absolute+v
    require(relative > 0, "No quotient precision remains")
    modulus = p**relative
    residue = numerator*pow(denominator//p**v, -1, modulus) % modulus
    return {"p": p, "residue": residue, "denominator_exponent": v,
            "absolute_digits": absolute,
            "meaning": "p^(-denominator_exponent)*residue + O(p^absolute_digits)"}


def normalize_projection(row, normalization_row, dual, row_digits, normalization_digits, p):
    w = dual["primitive_vector"]
    k = dual["direction_digits"]
    eta = minimum_valuation(row, p, row_digits)
    rho = minimum_valuation(normalization_row, p, normalization_digits)
    numerator_digits = min(row_digits, k+eta)
    denominator_digits = min(normalization_digits, k+rho)
    require(numerator_digits > 0 and denominator_digits > 0, "Insufficient pairing precision")
    numerator = dot_exact(row, w)
    denominator = dot_exact(normalization_row, w)
    result = quotient_ball(numerator, denominator, numerator_digits, denominator_digits, p)
    result["precision"] = {"kernel_digits": k, "row_digits": row_digits,
                           "normalization_row_digits": normalization_digits,
                           "row_valuation_lower_bound": eta,
                           "normalization_row_valuation_lower_bound": rho,
                           "numerator_digits": numerator_digits,
                           "denominator_digits": denominator_digits}
    return result


def ball_valuation_lower_bound(ball):
    return valuation(ball["residue"], ball["p"], ball["absolute_digits"]+ball["denominator_exponent"])-ball["denominator_exponent"]


def ball_contains_integer(ball, integer):
    modulus = ball["p"]**(ball["absolute_digits"]+ball["denominator_exponent"])
    return (ball["residue"]-int(integer)*ball["p"]**ball["denominator_exponent"]) % modulus == 0


def combine_balls(balls, scalars, scalar_digits, p):
    """Sum of balls times integral scalars known to scalar_digits."""
    exponent = max(b["denominator_exponent"] for b in balls)
    absolute = min(min(b["absolute_digits"]+valuation(s, p, scalar_digits),
                       scalar_digits+ball_valuation_lower_bound(b))
                   for b, s in zip(balls, scalars))
    require(absolute+exponent > 0, "No precision in coordinate conversion")
    modulus = p**(absolute+exponent)
    residue = sum(int(s)*b["residue"]*p**(exponent-b["denominator_exponent"])
                  for b, s in zip(balls, scalars)) % modulus
    return {"p": p, "residue": residue, "denominator_exponent": exponent,
            "absolute_digits": absolute,
            "meaning": "p^(-denominator_exponent)*residue + O(p^absolute_digits)"}
