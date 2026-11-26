"""Audit verifier for the smoothed-Haar local zero obstruction.

This reuses the original finite prime sum and independently implements the
shifted-logarithmic-derivative high-tail estimate. It is an external mpmath.iv
interval check, not a Lean theorem or an independent interval-arithmetic engine.
Run from any directory: python verify_shifted_tail.py > shifted-tail-result.json
"""

from fractions import Fraction
import importlib.util
import json
from pathlib import Path


source = Path(__file__).resolve().parents[1] / "zero_rectangle.py"
spec = importlib.util.spec_from_file_location("original_zero_rectangle", source)
base = importlib.util.module_from_spec(spec)
spec.loader.exec_module(base)
iv, I, enclose = base.iv, base.I, base.enclose

GAMMA = I([
    "0.577215664901532860606512090082",
    "0.577215664901532860606512090083",
])
ROWS = [
    (19000, 39 * 10**29, 10**32),
    (30000, 10**32, 10**40),
    (100000, 10**40, 10**60),
    (1000000, 10**60, 10**162),
]


def rational(x):
    return I(x.numerator) / I(x.denominator)


def shifted_tail(C, Qmax, T):
    """T positive and even; evaluate the identity at sigma=T+1."""
    assert T >= 2 and T % 2 == 0
    harmonic = sum((Fraction(1, k) for k in range(1, T // 2 + 1)), Fraction(0))
    mass = (iv.log(I(Qmax)) - iv.log(iv.pi) + rational(harmonic) - GAMMA + 4) / (2 * T)
    factor = I((T + 1)**2 + T**2) / I(T)**4
    return C * factor * mass, mass, harmonic


def check(row):
    X, Qmin, Qmax = row
    # The original check recomputes every prime-power term with 45-digit iv
    # arithmetic, not the saved result JSON. Recovering its enclosing endpoints
    # loses at most one micro-unit of margin and remains conservative.
    original = base.check(X, Qmin, Qmax)
    scale = original["scale"]
    margin = I(original["margin"]) / scale
    L = iv.log(I(X))
    a, b, N = 99 * L / 200, L / 200, 98 * L / 100
    delta = I(1) / 100
    A = (2 * a * base.sinh(delta * L / 2))**2 / N
    B = (4 * base.sinh(delta * L / 2) + 2 * a * delta * base.cosh(delta * L / 2))**2 / N
    C = 4 * (1 + base.cosh(a / 2))**2 * base.cosh(b / 2)**2 / (N * b**2)

    # On t>=0, -g(t) is t/b, then 1, then (a+b-t)/(2b).
    # This sign and the monotonic taper give exact L1 and variation bounds
    # for g(t)*sinh(eta*t), uniformly over |eta|<=delta. See AUDIT.md.
    A_exact = 4 * (base.cosh(a * delta) - 1)**2 * base.sinh(b * delta)**2 / (N * b**2 * delta**4)
    B_exact = 16 * base.sinh(delta * (a - b))**2 / N
    taper_test = base.sinh(delta * (a - b)) - 2 * b * delta * base.cosh(delta * (a - b))
    assert taper_test.a > 0

    # The elementary n^-2 bound proves Z <= log(q)+kappa, and kappa<1.
    kappa = 3 - GAMMA - iv.log(I(2)) / 2 - iv.log(iv.pi)
    assert kappa.b < 1
    results = []
    for T, low_addend, low_kind in ((100, 4, "original"), (100, 1, "original"), (80, 1, "original"), (60, 1, "exact_haar")):
        high, shifted_mass, harmonic = shifted_tail(C, Qmax, T)
        low_mass = iv.log(I(Qmax)) + low_addend
        ab = A_exact + B_exact if low_kind == "exact_haar" else A + B
        low = ab * low_mass
        residual = margin - low - high
        assert residual.a > 0
        results.append({
            "height": T,
            "low_zero_kernel_bound": low_kind,
            "low_zero_mass_bound": f"log(Qmax)+{low_addend}",
            "harmonic_numerator": str(harmonic.numerator),
            "harmonic_denominator": str(harmonic.denominator),
            "shifted_zero_mass_upper_enclosure": enclose(shifted_mass),
            "low_zero_loss_upper_enclosure": enclose(low),
            "high_zero_loss_upper_enclosure": enclose(high),
            "residual": enclose(residual),
        })

    # This reports the first passing even height for these fixed kernels and
    # this specific inequality, not an optimal possible zero obstruction.
    low = (A + B) * (iv.log(I(Qmax)) + 1)
    first_even = None
    for T in range(2, 1002, 2):
        high, _, _ = shifted_tail(C, Qmax, T)
        if (margin - low - high).a > 0:
            first_even = T
            break
    return {
        "X": X,
        "Qmin": str(Qmin),
        "Qmax": str(Qmax),
        "scale": scale,
        "delta": "1/100",
        "original_verifier": original,
        "elementary_kappa_enclosure": enclose(kappa),
        "exact_haar_A_enclosure": enclose(A_exact),
        "exact_haar_B_enclosure": enclose(B_exact),
        "monotone_taper_test_enclosure": enclose(taper_test),
        "shifted_tail_profiles": results,
        "first_passing_even_height_for_logq_plus_1": first_even,
        "status": "External interval inequalities; analytic proof audit only; no Lean theorem",
    }


if __name__ == "__main__":
    print(json.dumps([check(row) for row in ROWS], indent=2))
