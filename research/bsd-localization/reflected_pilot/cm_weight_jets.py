#!/usr/bin/env python3
"""Exact CM weight-one q-expansions and second weight jets for Q(sqrt(-71)).

No CM j-invariants, diagonal-cycle classes, or p-adic L-values are computed.
The output is input to a future overconvergent modular-form computation.
Only Python's standard library is used.
"""

from __future__ import annotations

import argparse
import gzip
import hashlib
import io
import json
from math import gcd, isqrt
from pathlib import Path
import time


HERE = Path(__file__).resolve().parent
ZERO = (0,) * 6
ONE = (1, 0, 0, 0, 0, 0)
SOURCE_ARCHIVE_SHA256 = "f4d0332acbe087da2dda53a9a380f41c75d3ec63c5ad59441f2a5785ef21531a"


def vp(n: int, p: int = 5) -> int:
    assert n != 0
    v = 0
    while n % p == 0:
        n //= p
        v += 1
    return v


def lift_root(residue: int, p: int, digits: int) -> int:
    """Lift a simple root of X^2-X+18 digit by digit."""
    r, modulus = residue, p
    assert (r * r - r + 18) % p == 0
    assert gcd(2 * r - 1, p) == 1
    for _ in range(1, digits):
        digit = (-(r * r - r + 18) // modulus) * pow(2 * r - 1, -1, p) % p
        r += digit * modulus
        modulus *= p
        assert (r * r - r + 18) % modulus == 0
    return r


def log5_unit(u: int, digits: int) -> int:
    """Iwasawa log(u) mod 5^digits, with log of a root of unity zero.

    Compute log(u^4)/4.  For z=u^4-1, v5(z)>=1; omitted terms
    n>=2*digits have valuation n-v5(n)>=n/2>=digits.  Guard digits
    make every division by the 5-part of n exact before unit inversion.
    A unit residue mod 5^digits suffices because log is 1-Lipschitz.
    """
    assert u % 5
    cutoff = 2 * digits
    guard = max(vp(n) for n in range(1, cutoff))
    bigmod, modulus = 5 ** (digits + guard), 5**digits
    z = (pow(u, 4, bigmod) - 1) % bigmod
    power, out = 1, 0
    for n in range(1, cutoff):
        power = power * z % bigmod
        a = vp(n)
        assert power % (5**a) == 0
        term = power // (5**a) * pow(n // (5**a), -1, modulus)
        out += term if n % 2 else -term
    return out * pow(4, -1, modulus) % modulus


def zeta(exponent: int, modulus: int | None = None) -> tuple[int, ...]:
    exponent %= 7
    out = tuple(int(i == exponent) for i in range(6)) if exponent < 6 else (-1,) * 6
    return tuple(x % modulus for x in out) if modulus else out


def add(a, b, modulus):
    return tuple((x + y) % modulus for x, y in zip(a, b))


def scale(a, c, modulus):
    return tuple(x * c % modulus for x in a)


def mul(a, b, modulus):
    # First reduce modulo X^7-1, then use X^6=-(1+...+X^5).
    c = [0] * 7
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                c[(i + j) % 7] += x * y
    return tuple((c[i] - c[6]) % modulus for i in range(6))


def conjugate(a, modulus):
    out = ZERO
    for i, c in enumerate(a):
        out = add(out, scale(zeta(-i), c, modulus), modulus)
    return out


def reduced_forms():
    forms = []
    for a in range(1, isqrt(71 // 3) + 1):
        for b in range(-a, a + 1):
            if (b * b + 71) % (4 * a):
                continue
            c = (b * b + 71) // (4 * a)
            if a > c or (abs(b) == a or a == c) and b < 0:
                continue
            if gcd(gcd(a, b), c) == 1:
                forms.append((a, b, c))
    return forms


def ideal_elements(bound):
    """Enumerate each integral ideal b once, as b=(alpha)/a^k.

    a=(2,omega), a^7=(10+omega), and a^k=(2^k,omega-r_k).
    alpha=2^k*x+(omega-r_k)*y.  Quotienting alpha by units +/-1
    is implemented by y>0, or y=0 and x>0.  The exact identity
    4*2^k*N(b)=(2*2^k*x+(1-2*r_k)*y)^2+71*y^2 bounds the search.
    """
    for k in range(7):
        a = 2**k
        r = lift_root(0, 2, k) if k else 0
        b = 1 - 2 * r
        c = (r * r - r + 18) // a
        for y in range(isqrt(4 * a * bound // 71) + 1):
            radius = isqrt(4 * a * bound - 71 * y * y)
            # ceil((-b*y-radius)/(2*a)), written without floating point.
            lo = (-b * y - radius + 2 * a - 1) // (2 * a)
            hi = (-b * y + radius) // (2 * a)
            for x in range(lo, hi + 1):
                if y == 0 and x <= 0:
                    continue
                n = a * x * x + b * x * y + c * y * y
                assert 1 <= n <= bound
                u, v = a * x - r * y, y
                assert u * u + u * v + 18 * v * v == a * n
                yield n, k, u, v


def primes_to(bound):
    small = list(range(bound + 1))
    primes = []
    for ell in range(2, bound + 1):
        if small[ell] == ell:
            primes.append(ell)
            for n in range(ell * ell, bound + 1, ell):
                if small[n] == n:
                    small[n] = ell
    return primes, small


def legendre(n, ell):
    r = pow(n % ell, (ell - 1) // 2, ell)
    return -1 if r == ell - 1 else r


def epsilon71(n):
    # The quadratic character of discriminant -71 is (n/71).
    return legendre(n, 71)


def curve_coefficients(bound):
    primes, small = primes_to(bound)
    ap = {}
    for ell in primes:
        if ell == 2:
            ap[ell] = -2
        elif ell == 389:
            ap[ell] = 1  # split multiplicative reduction, audited previously
        else:
            # 1+Legendre(4*x^3+4*x^2-8*x+1,ell) values of y for fixed x.
            ap[ell] = -sum(legendre(4*x*x*x + 4*x*x - 8*x + 1, ell)
                           for x in range(ell))
            assert ap[ell] * ap[ell] <= 4 * ell
    out = [0] * (bound + 1)
    out[1] = 1
    for n in range(2, bound + 1):
        ell, m = small[n], n // small[n]
        out[n] = ap[ell] * out[m]
        if m % ell == 0 and ell != 389:
            out[n] -= ell * out[m // ell]
    assert out[5] == -3
    return out


def unit_root(digits):
    r, modulus = 2, 5
    for _ in range(1, digits):
        digit = (-(r*r + 3*r + 5) // modulus) * pow(2*r + 3, -1, 5) % 5
        r += digit * modulus
        modulus *= 5
        assert (r*r + 3*r + 5) % modulus == 0
    return r


def convolve_mod(a, b, modulus, degree):
    """Exact integer convolution by carry-free binary packing."""
    width = (len(a) * (modulus - 1)**2).bit_length() + 1
    mask = (1 << width) - 1
    aa = sum((x % modulus) << (width*i) for i, x in enumerate(a))
    bb = sum((x % modulus) << (width*i) for i, x in enumerate(b))
    cc = aa * bb
    return [(cc >> (width*i) & mask) % modulus for i in range(degree + 1)]


def choose2(n, modulus):
    return n * (n - 1) * pow(2, -1, modulus) % modulus


def verify_hecke(base, tangent, second, modulus, log_coordinate):
    bound = len(base) - 1
    primes, _ = primes_to(bound)
    checks = 0
    for ell in primes:
        for n in range(1, bound // ell + 1):
            rhs = mul(base[ell], base[n], modulus)
            rhs1 = add(mul(tangent[ell], base[n], modulus),
                       mul(base[ell], tangent[n], modulus), modulus)
            rhs2 = add(add(mul(second[ell], base[n], modulus),
                           mul(tangent[ell], tangent[n], modulus), modulus),
                       mul(base[ell], second[n], modulus), modulus)
            if n % ell == 0 and ell not in (5, 71):
                eps = epsilon71(ell)
                rhs = add(rhs, scale(base[n // ell], -eps, modulus), modulus)
                lower = add(tangent[n // ell],
                            scale(base[n // ell], log_coordinate(ell), modulus), modulus)
                rhs1 = add(rhs1, scale(lower, -eps, modulus), modulus)
                L = log_coordinate(ell)
                lower2 = add(add(second[n // ell], scale(tangent[n // ell], L, modulus), modulus),
                             scale(base[n // ell], choose2(L, modulus), modulus), modulus)
                rhs2 = add(rhs2, scale(lower2, -eps, modulus), modulus)
            assert base[ell*n] == rhs, ("Hecke constant", ell, n)
            assert tangent[ell*n] == rhs1, ("Hecke derivative", ell, n)
            assert second[ell*n] == rhs2, ("Hecke second coefficient", ell, n)
            checks += 1
    return checks


def shift_series(series, shift):
    out = [ZERO] * len(series)
    for n in range(1, (len(series)-1)//shift + 1):
        out[shift*n] = series[n]
    return out


def multiply_series(a, b, modulus):
    """Cyclotomic convolution optimized for a sparse degeneracy oldform."""
    out = [ZERO] * len(a)
    aa = [(i, c) for i, c in enumerate(a) if c != ZERO]
    bb = [(j, c) for j, c in enumerate(b) if c != ZERO]
    if len(aa) < len(bb):
        aa, bb = bb, aa
    for j, y in bb:
        for i, x in aa:
            if i + j >= len(out):
                break
            out[i+j] = add(out[i+j], mul(x, y, modulus), modulus)
    return out


def de_rham_input_jets(g, h, shifts, modulus, log_coordinate, deplete_h=False):
    """Coefficients W^0,W^1,W^2 of (d^-s(Va*g)^[5])*(Vb*h).

    Here W=6^s-1; the multiplier at q^n is (1+W)^(-log5(n)/log5(6)).
    The output is a raw weight-two overconvergent q-series.  It has NOT
    been reduced modulo exact differentials or projected to the E factor.
    """
    gg = [shift_series(s, shifts[0]) for s in g]
    hh = [shift_series(s, shifts[1]) for s in h]
    if deplete_h:
        for n in range(0, len(hh[0]), 5):
            for j in range(3):
                hh[j][n] = ZERO
    for n in range(len(gg[0])):
        if n % 5 == 0:
            for j in range(3):
                gg[j][n] = ZERO
        else:
            L = log_coordinate(n)
            c0, c1, c2 = [gg[j][n] for j in range(3)]
            gg[1][n] = add(c1, scale(c0, -L, modulus), modulus)
            gg[2][n] = add(add(c2, scale(c1, -L, modulus), modulus),
                          scale(c0, choose2(-L, modulus), modulus), modulus)
    output = []
    for order in range(3):
        acc = [ZERO] * len(g[0])
        for a in range(order+1):
            term = multiply_series(gg[a], hh[order-a], modulus)
            acc = [add(x, y, modulus) for x, y in zip(acc, term)]
        output.append(acc)
    return output


def seventh_root_unit(u, modulus):
    """Unique seventh root of a 5-adic unit, computed without logarithms."""
    r = next(a for a in range(1, 5) if pow(a, 7, 5) == u % 5)
    mod = 5
    while mod < modulus:
        digit = (-(r**7-u) // mod) * pow(7*r**6, -1, 5) % 5
        r += digit * mod
        mod *= 5
        assert (r**7-u) % mod == 0
    return r


def check_weight_five(branch, residue, bound, modulus):
    """Independently compare the jet with algebraic weight 5 mod 5^3.

    No logarithm is used in the algebraic coefficient calculation.
    W=6^4-1 has valuation 1, so discarded integral W^3 terms vanish mod125.
    """
    checkmod = min(125, modulus)
    root = lift_root(residue, 5, 3)
    eta_root = seventh_root_unit(10 + root, 125)
    exact = [ZERO] * (bound + 1)
    for n, k, u, v in ideal_elements(bound):
        image = (u + v*root) % 125
        if image % 5 == 0:
            continue
        coefficient = pow(image, 4, checkmod) * pow(eta_root, -4*k, checkmod) % checkmod
        exact[n] = add(exact[n], scale(zeta(-k), coefficient, checkmod), checkmod)
    W = (6**4-1) % checkmod
    for n in range(1, bound+1):
        expected = add(add(branch["base"][n], scale(branch["tangent"][n], W, checkmod), checkmod),
                       scale(branch["second"][n], W*W, checkmod), checkmod)
        assert tuple(c % checkmod for c in expected) == exact[n], ("weight-five specialization", residue, n)
    return bound


def build(bound=4096, digits=12):
    assert bound >= 25 and digits >= 1
    assert next(d for d in range(1, 7) if pow(5, d, 7) == 1) == 6
    modulus, logmod = 5**digits, 5 ** (digits + 1)
    log6 = log5_unit(6, digits + 1)
    assert log6 % 5 == 0 and log6 % 25 != 0
    inv_log6_over5 = pow(log6 // 5, -1, modulus)
    inv7 = pow(7, -1, logmod)

    def normalized_log(u):
        value = log5_unit(u, digits + 1)
        assert value % 5 == 0
        return value // 5 * inv_log6_over5 % modulus

    forms = reduced_forms()
    assert len(forms) == 7
    r128 = lift_root(0, 2, 7)
    assert (10 + r128) % 128 == 0 and 10*10 + 10 + 18 == 128
    # a is not principal: no algebraic integer has norm 2; its order is 7.
    assert all(u*u != 2 for u in range(-2, 3)) and 71 > 4*2

    classical = [ZERO] * (bound + 1)
    branches = {}
    for residue in (2, 4):
        root = lift_root(residue, 5, digits + 1)
        log_eta_seventh = log5_unit(10 + root, digits + 1) * inv7 % logmod
        branches[residue] = {
            "root": root,
            "log_eta_seventh": log_eta_seventh,
            "base": [ZERO] * (bound + 1),
            "tangent": [ZERO] * (bound + 1),
            "second": [ZERO] * (bound + 1),
            "ideal_count": 0,
        }

    ideals = 0
    for n, k, u, v in ideal_elements(bound):
        ideals += 1
        character = zeta(-k, modulus)
        classical[n] = add(classical[n], character, modulus)
        for branch in branches.values():
            image = (u + v * branch["root"]) % logmod
            if image % 5 == 0:
                continue
            lam = (log5_unit(image, digits + 1) - k * branch["log_eta_seventh"]) % logmod
            assert lam % 5 == 0
            exponent = lam // 5 * inv_log6_over5 % modulus
            branch["base"][n] = add(branch["base"][n], character, modulus)
            branch["tangent"][n] = add(branch["tangent"][n], scale(character, exponent, modulus), modulus)
            branch["second"][n] = add(branch["second"][n],
                                      scale(character, choose2(exponent, modulus), modulus), modulus)
            branch["ideal_count"] += 1

    assert classical[1] == ONE
    assert all(conjugate(c, modulus) == c for c in classical)
    verification = {}
    for residue, branch in branches.items():
        base, tangent, second = branch["base"], branch["tangent"], branch["second"]
        alpha_exp = 2 if residue == 2 else 5
        alpha, beta = zeta(alpha_exp, modulus), zeta(-alpha_exp, modulus)
        assert base[1] == ONE and tangent[1] == ZERO and base[5] == alpha
        for n in range(1, bound + 1):
            expected = classical[n]
            if n % 5 == 0:
                expected = add(expected, scale(mul(beta, classical[n//5], modulus), -1, modulus), modulus)
            assert base[n] == expected, ("p-stabilization", residue, n)
        checks = verify_hecke(base, tangent, second, modulus, normalized_log)
        # First derivative of U5*g_W=alpha(W)*g_W is included in Hecke checks.
        alpha_log_coordinate = mul(tangent[5], zeta(-alpha_exp, modulus), modulus)
        assert alpha_log_coordinate[1:] == (0,) * 5
        verification[str(residue)] = {
            "hecke_relations_at_each_of_orders_0_1_2": checks,
            "ordinary_Up_eigenvalue_zeta_exponent": alpha_exp,
            "ordinary_Up_logarithmic_derivative": alpha_log_coordinate[0],
            "integral_ideals_prime_to_selected_p": branch["ideal_count"],
            "algebraic_weight5_specialization_coefficients_checked_mod125_or_available_precision":
                check_weight_five(branch, residue, bound, modulus),
        }

    # The two CM types satisfy lambda_p(b)+lambda_pbar(b)=log(Nb).
    # This identity on ideals prime to 5 checks the weight normalization.
    for n in range(1, bound + 1):
        if n % 5:
            lhs = add(branches[2]["tangent"][n], branches[4]["tangent"][n], modulus)
            assert lhs == scale(classical[n], normalized_log(n), modulus)
            L = normalized_log(n)
            rhs2 = add(add(branches[2]["second"][n],
                           scale(branches[2]["tangent"][n], 1-L, modulus), modulus),
                       scale(classical[n], choose2(L, modulus), modulus), modulus)
            assert branches[4]["second"][n] == rhs2

    f = curve_coefficients(bound)
    trace_reduction = None
    if bound >= 71:
        a71, degree = f[71], 72
        determinant = degree*degree-a71*a71
        matrix = [[degree, a71], [a71, degree]]
        inverse = [[degree * pow(determinant, -1, modulus) % modulus,
                    -a71 * pow(determinant, -1, modulus) % modulus],
                   [-a71 * pow(determinant, -1, modulus) % modulus,
                    degree * pow(determinant, -1, modulus) % modulus]]
        assert determinant % 5 != 0
        for i in range(2):
            for j in range(2):
                assert sum(matrix[i][r]*inverse[r][j] for r in range(2)) % modulus == int(i == j)
        trace_reduction = {
            "source_level": 27619, "target_level": 389,
            "a71": a71, "degeneracy_degree": degree,
            "pullback_trace_Gram_matrix_on_E_factor": matrix,
            "determinant": determinant,
            "inverse_matrix_modulus": inverse,
            "five_adic_precision_loss_from_this_matrix_inversion": 0,
            "scope": "finite Gram-matrix certificate; the two tame traces of the input overconvergent form have not been computed",
        }
    alpha_f = unit_root(digits)
    beta_f = 5 * pow(alpha_f, -1, modulus) % modulus
    f_ordinary = [(a - (beta_f * f[n//5] if n and n % 5 == 0 else 0)) % modulus
                  for n, a in enumerate(f)]
    f_critical = [(a - (alpha_f * f[n//5] if n and n % 5 == 0 else 0)) % modulus
                  for n, a in enumerate(f)]
    for n in range(1, bound // 5 + 1):
        assert f_ordinary[5*n] == alpha_f * f_ordinary[n] % modulus
        assert f_critical[5*n] == beta_f * f_critical[n] % modulus
    primitive = [(a * pow(n, -1, modulus) % modulus) if n and n % 5 else 0
                 for n, a in enumerate(f)]

    # Raw overconvergent input H_W=d^-1(f^[5])*h_W, h has character psi^-1.
    # This is NOT its ordinary projection, its period-normalized integral,
    # or a regulator on a diagonal class. Its diagonal g/h projections may
    # vanish identically for structural reasons explained in the README.
    payload_branches = {}
    for residue, branch in branches.items():
        h0 = [conjugate(c, modulus) for c in branch["base"]]
        h1 = [conjugate(c, modulus) for c in branch["tangent"]]
        h2 = [conjugate(c, modulus) for c in branch["second"]]
        prod0_cols = [convolve_mod(primitive, [c[j] for c in h0], modulus, bound) for j in range(6)]
        prod1_cols = [convolve_mod(primitive, [c[j] for c in h1], modulus, bound) for j in range(6)]
        H0 = [tuple(col[n] for col in prod0_cols) for n in range(bound+1)]
        H1 = [tuple(col[n] for col in prod1_cols) for n in range(bound+1)]
        # Independently inspect early convolution terms directly.
        for n in range(1, min(bound, 40) + 1):
            for h, H in ((h0, H0), (h1, H1)):
                direct = ZERO
                for i in range(1, n):
                    direct = add(direct, scale(h[n-i], primitive[i], modulus), modulus)
                assert direct == H[n]
        payload_branches[str(residue)] = {
            "omega_mod_5_power_digits_plus_one": branch["root"],
            "g_base": branch["base"],
            "g_weight_derivative": branch["tangent"],
            "g_weight_coefficient_2": branch["second"],
            "raw_iterated_input_base": H0,
            "raw_iterated_input_weight_derivative": H1,
            "raw_de_rham_input_cross_oldforms": {
                "g_depleted_times_V389_h": de_rham_input_jets(
                    [branch["base"], branch["tangent"], branch["second"]],
                    [h0, h1, h2], (1, 389), modulus, normalized_log),
                "V389_g_depleted_times_h": de_rham_input_jets(
                    [branch["base"], branch["tangent"], branch["second"]],
                    [h0, h1, h2], (389, 1), modulus, normalized_log),
                "both_depleted_g_times_V389_h": de_rham_input_jets(
                    [branch["base"], branch["tangent"], branch["second"]],
                    [h0, h1, h2], (1, 389), modulus, normalized_log, deplete_h=True),
                "both_depleted_V389_g_times_h": de_rham_input_jets(
                    [branch["base"], branch["tangent"], branch["second"]],
                    [h0, h1, h2], (389, 1), modulus, normalized_log, deplete_h=True),
            },
        }

    return {
        "schema": "E389-Kminus71-CM-weight-jet-v2",
        "scope": "modular-form input data only; no diagonal class, complementary regulator, or finite logarithm computed",
        "upstream_archive_sha256": SOURCE_ARCHIVE_SHA256,
        "curve": [0, 1, 1, -2, 0],
        "quadratic_field": {"omega_polynomial": [18, -1, 1], "reduced_forms": forms,
                            "class_generator": "a=(2,omega)", "a_seventh_generator": [10, 1],
                            "a_seventh_norm": 128},
        "coefficient_ring": {"p": 5, "digits": digits, "modulus": modulus,
                             "polynomial": [1]*7, "basis": ["1", "zeta", "zeta^2", "zeta^3", "zeta^4", "zeta^5"]},
        "q_precision": {"largest_coefficient": bound, "remainder": f"O(q^{bound+1})"},
        "weight_coordinate": "W=6^s-1, s=kappa-1; derivatives are d/dW at W=0",
        "second_jet_convention": "stored order2 entries are W^2 coefficients, i.e. one half of the second W derivative",
        "de_rham_input_formula": "(d^(-s)(V_a*g_W)^[5])*(V_b*h_W), h_W obtained by zeta->zeta^-1; a,b=(1,389) or (389,1)",
        "depletion_warning": "g-depleted and both-depleted variants are distinct raw inputs; no equality of their projected periods or Euler corrections is claimed",
        "tangent_formula": "[log5(iota(alpha))-(k/7)log5(iota(10+omega))]/log5(6), b=(alpha)/a^k",
        "character_convention": "psi(a)=zeta; psi(b)=zeta^(-k); psi^-1 obtained by zeta->zeta^-1",
        "all_integral_ideal_count": ideals,
        "classical_theta": classical,
        "f_q_coefficients_exact": f,
        "two_degeneracy_trace_reduction": trace_reduction,
        "f_alpha_modulus": alpha_f,
        "f_beta_modulus": beta_f,
        "f_ordinary_q_coefficients": f_ordinary,
        "f_critical_slope_q_coefficients": f_critical,
        "d_inverse_f_p_depleted": primitive,
        "branches": payload_branches,
        "verification": verification,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--bound", type=int, default=4096)
    parser.add_argument("--digits", type=int, default=12)
    parser.add_argument("--output", type=Path, default=HERE / "cm-weight-jets.json.gz")
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    started = time.perf_counter()
    result = build(args.bound, args.digits)
    encoded = (json.dumps(result, separators=(",", ":"), sort_keys=True) + "\n").encode()
    if args.check:
        saved = args.output.read_bytes()
        if args.output.suffix == ".gz":
            saved = gzip.decompress(saved)
        assert saved == encoded, "saved data differ"
    else:
        if args.output.suffix == ".gz":
            stream = io.BytesIO()
            # No filename or timestamp in the header; deterministic across reruns.
            with gzip.GzipFile(filename="", mode="wb", fileobj=stream,
                               compresslevel=9, mtime=0) as compressed:
                compressed.write(encoded)
            args.output.write_bytes(stream.getvalue())
        else:
            args.output.write_bytes(encoded)
    receipt = {
        "file": str(args.output),
        "uncompressed_sha256": hashlib.sha256(encoded).hexdigest(),
        "file_sha256": hashlib.sha256(args.output.read_bytes()).hexdigest(),
        "file_bytes": args.output.stat().st_size,
        "seconds": round(time.perf_counter() - started, 3),
        "bound": args.bound, "digits": args.digits,
        "verification": result["verification"],
        "scope": result["scope"],
    }
    print(json.dumps(receipt, indent=2))


if __name__ == "__main__":
    main()
