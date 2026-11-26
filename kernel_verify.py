"""Rigorous check of the least-split-prime certificates (interval arithmetic, mpmath.iv).

Statement checked for each row (Q, X, v):

    Let q <= Q be a prime, q = 3 mod 4, chi = (-q/.) the odd real primitive character mod q,
    and assume GRH for L(s, chi).  Then some prime p < X splits in Q(sqrt(-q)).

Proof.  If not, every prime p < X is inert (the only ramified prime is q, and q >= X is forced
because q < X would make q itself a ramified prime below X -- that case is excluded separately:
all rows are applied only to q > X).  With f the normalised autocorrelation of the step
function with values v on m equal cells of [0, log X], the explicit formula and GRH give

    sum_{p<X} A_p  <=  log(q/pi) + psi(3/4) + J_f .

The row is valid when   sum_{p<X} A_p - J_up - log Q + (log pi - psi(3/4))  > 0   with every
quantity enclosed by outward-rounded intervals.

Usage:  python3 kernel_verify.py build   (search rows with floats, then verify, write JSON)
        python3 kernel_verify.py check   (re-verify the stored JSON only)
"""
import sys, json, math
from fractions import Fraction
from mpmath import iv, mp

iv.dps = 40
QLOW = 31 * 10**19          # 3.1e20, end of the Elsenhans-Klueners-Nicolae table
QTOP = 10**32               # start of the bootstrap; above this the Bach-Sorenson (ERH) bound applies with room to spare
M_STEPS = 64
CERT = "certificate.json"


def primes_below(x):
    sieve = bytearray([1]) * x
    sieve[:2] = b"\0\0"
    for p in range(2, math.isqrt(x - 1) + 1):
        if sieve[p]:
            sieve[p*p:x:p] = bytes((x - 1 - p*p)//p + 1)
    return [p for p in range(2, x) if sieve[p]]


def prev_prime(x):
    """largest prime < x"""
    return primes_below(x)[-1]


def frac(fr):
    return iv.mpf(fr.numerator) / iv.mpf(fr.denominator)


def rigorous_margin(Q, X, v):
    """Lower bound for  sum A_p - J_up - log Q + log(pi) - psi(3/4)."""
    m = len(v)
    sq = sum(t*t for t in v)
    corr = [frac(Fraction(sum(v[k]*v[k+j] for k in range(m - j)), sq)) for j in range(m + 1)]
    one = iv.mpf(1)
    logX = iv.log(iv.mpf(X))
    width = logX / m

    def f_at(n):
        coord = iv.log(iv.mpf(n)) / width
        lo = max(0, int(math.floor(float(coord.a))) - 0)
        hi = min(m - 1, int(math.floor(float(coord.b))))
        # float() of an endpoint may be off by one ulp: widen by one cell on each side if close
        if float(coord.a) - lo < 1e-9:
            lo = max(0, lo - 1)
        if hi + 1 - float(coord.b) < 1e-9:
            hi = min(m - 1, hi + 1)
        vals = []
        for k in range(lo, hi + 1):
            h = coord - k
            vals.append(corr[k] + h*(corr[k+1] - corr[k]))
        a = min(t.a for t in vals); b = max(t.b for t in vals)
        return iv.mpf([a, b])

    total = iv.mpf(0)
    for p in primes_below(X):
        logp = iv.log(iv.mpf(p))
        n = p; sign = -1
        while n < X:
            total += 2*sign*logp*f_at(n)/iv.sqrt(iv.mpf(n))
            n *= p; sign = -sign

    # J_up >= int_0^oo a(u)(1-f(u)) du,  a(u) = 2 e^{-3u/2}/(1-e^{-2u}) = e^{-u/2}/sinh u  (decreasing, <= 1/u)
    J = one - corr[1]                                    # first cell
    pieces = 16
    step = width / pieces
    for j in range(1, m):
        slope = corr[j+1] - corr[j]
        for i in range(pieces):
            u = step*(j*pieces + i)
            a = 2*iv.exp(-iv.mpf(3)/2*u)/(one - iv.exp(-2*u))
            mean = corr[j] + slope*frac(Fraction(2*i + 1, 2*pieces))
            J += step*a*(one - mean)                     # 1 - f >= 0, a decreasing
    Xi = iv.mpf(X)
    J += 4/(3*Xi*iv.sqrt(Xi)*(one - 1/(Xi*Xi)))          # tail u > log X

    # log(pi) - psi(3/4) = log(pi) + gamma - pi/2 + 3 log 2 ; enclose gamma by 30-digit bounds
    gamma = iv.mpf(["0.577215664901532860606512090082", "0.577215664901532860606512090083"])
    const = iv.log(iv.pi) + gamma - iv.pi/2 + 3*iv.log(iv.mpf(2))
    margin = total - J - iv.log(iv.mpf(Q)) + const
    return margin.a, total, J


def float_row(Q, m=M_STEPS, slack=0.02):
    """smallest X (by bisection on the float margin) and an integer vector v"""
    import kernel_opt
    lo, hi = 200, 20000
    while hi - lo > 1:
        mid = (lo + hi)//2
        mg, _ = kernel_opt.margin(mid, m, float(Q))
        if mg >= slack:
            hi = mid
        else:
            lo = mid
    mg, vec = kernel_opt.margin(hi, m, float(Q))
    scale = 100000/max(abs(t) for t in vec)
    v = [int(round(t*scale)) for t in vec]
    return hi, v


def certified_row(Q):
    X, v = float_row(Q)
    while True:
        lo, _, _ = rigorous_margin(Q, X, v)
        if lo > 0:
            return {"Q": Q, "X": X, "v": v, "margin_lower": float(mp.mpf(lo))}
        X += 1                                           # float optimum was too optimistic
        _, v = float_row(Q) if False else (X, v)


def build():
    import warnings; warnings.simplefilter("ignore")
    rows = []
    # Stage A: bootstrap from the published cap.  q <= Q and E | 7  =>  split p < X  =>  q <= 4 p^7.
    Q = QTOP
    chain = []
    while True:
        row = certified_row(Q)
        P = prev_prime(row["X"])
        newQ = 4*P**7
        row["stage"] = "bootstrap"; row["P"] = P; row["newQ"] = newQ
        chain.append(row)
        print("bootstrap  Q=%.4e  X=%d  P=%d  margin>%.5f  ->  4P^7=%.4e" % (Q, row["X"], P, row["margin_lower"], newQ), flush=True)
        if newQ >= Q:
            break
        Q = newQ
    Qstar = Q; Pstar = chain[-1]["P"]
    # Stage B: ladder below Q*, used to shorten the search (q <= Q_i => split prime < X_i).
    ladder = []
    k = 1
    while True:
        Qi = int(Qstar / 10**(k/8))
        if Qi <= QLOW:
            break
        row = certified_row(Qi); row["stage"] = "ladder"
        ladder.append(row)
        print("ladder     Q=%.4e  X=%d  margin>%.5f" % (Qi, row["X"], row["margin_lower"]), flush=True)
        k += 1
    row = certified_row(QLOW); row["stage"] = "ladder"; ladder.append(row)
    print("ladder     Q=%.4e  X=%d  margin>%.5f" % (QLOW, row["X"], row["margin_lower"]), flush=True)
    out = {"QLOW": QLOW, "QTOP": QTOP, "Qstar": Qstar, "Pstar": Pstar, "m": M_STEPS,
           "bootstrap": chain, "ladder": ladder}
    json.dump(out, open(CERT, "w"))
    print("Q* = %d   P* = %d" % (Qstar, Pstar))


def check():
    c = json.load(open(CERT))
    ok = True
    Q = c["QTOP"]
    for row in c["bootstrap"]:
        assert row["Q"] == Q
        lo, _, _ = rigorous_margin(row["Q"], row["X"], row["v"])
        P = prev_prime(row["X"])
        assert lo > 0 and P == row["P"] and row["newQ"] == 4*P**7
        print("bootstrap  Q=%d  X=%d  P=%d  margin>%s" % (row["Q"], row["X"], P, mp.nstr(mp.mpf(lo), 8)))
        if row["newQ"] < Q:
            Q = row["newQ"]
    assert Q == c["Qstar"] and c["Pstar"] == c["bootstrap"][-1]["P"]
    for row in c["ladder"]:
        lo, _, _ = rigorous_margin(row["Q"], row["X"], row["v"])
        assert lo > 0
        print("ladder     Q=%d  X=%d  margin>%s" % (row["Q"], row["X"], mp.nstr(mp.mpf(lo), 8)))
    print("ALL ROWS VERIFIED.  Q* = %d, P* = %d" % (c["Qstar"], c["Pstar"]))


def write_ladder(path="ladder.txt"):
    """rows 'X Q' meaning: q <= Q forces a split prime < X.  Read by sieve7."""
    c = json.load(open(CERT))
    with open(path, "w") as f:
        f.write("%d\n" % c["QLOW"])
        for row in c["ladder"] + c["bootstrap"]:
            f.write("%d %d\n" % (row["X"], row["Q"]))


if __name__ == "__main__":
    {"build": build, "check": check}[sys.argv[1]]()
    write_ladder()
