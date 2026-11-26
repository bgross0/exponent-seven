"""Integer mirror of the verified row evaluator (Exp7Lean/Rows/*.lean), used to pre-validate
the 175 rows.  log / sqrt / exp enclosures are approximated with mpmath (the Lean evaluator
uses the verified fixed-point routines; differences are a few units of 1e-20)."""
import json, re, sys
from mpmath import mp, mpf, log, sqrt, exp, floor
mp.dps = 60
D = 10**20
OFF = 2**62
B = 2**64
CERT = "/home/zlab/GitHub/exponent-seven/lowrange/certificate_full.json"

def cdiv(a, b): return (a + b - 1)//b
def flo(x): return int(floor(x))

def table():
    src = open("Exp7Lean/Numerics/PrimeTable.lean").read()
    return [(int(a), int(b), int(c)) for a, b, c in re.findall(r"\((\d+), (\d+), (\d+)\)", src)]

def pack_of(v):
    m = len(v)
    cn = [sum(v[k]*v[k+j] for k in range(m-j)) for j in range(m+1)]
    return sum((cn[j] + OFF) * B**j for j in range(m+1)), cn

def getN(pack, j): return (pack // B**j) % B

def term(X, LX, LXhi, sq, pack, p, L, S, k):
    n = p**k
    j = (64*k*L)//LXhi
    if not (X**j <= n**64 and n**64 <= X**(j+1)):
        return -2*(L+16), False
    Hlo = max(0, (64*k*L*D)//LXhi - j*D)
    x = max(0, cdiv(64*k*(L+16)*D, LX) - j*D)
    Hhi = min(D, x)
    a = getN(pack, j); b = getN(pack, j+1)
    if a <= b:
        Flo = a*D + Hlo*(b-a); Fhi = a*D + Hhi*(b-a)
    else:
        Flo = a*D - Hhi*(a-b); Fhi = a*D - Hlo*(a-b)
    Z = OFF*D
    if k % 2 == 0:
        wlo = L*D; whi = (L+16)*D
    else:
        wlo = L*S; whi = (L+16)*(S+1)
    den = p**((k+1)//2)*sq*D*D
    if k % 2 == 0:
        if Z <= Flo: return (2*(Flo-Z)*wlo)//den, True
        return -cdiv(2*(Z-Flo)*whi, den), True
    else:
        if Fhi <= Z: return (2*(Z-Fhi)*wlo)//den, True
        return -cdiv(2*(Fhi-Z)*whi, den), True

def total(X, LX, LXhi, sq, pack, T):
    tot = 0; ok = True; cnt = 0
    for (p, L, S) in T:
        if p < X:
            k = 1
            while p**k < X:
                t, o = term(X, LX, LXhi, sq, pack, p, L, S, k)
                tot += t; ok = ok and o; cnt += 1
                k += 1
            assert k <= 13
    return tot, ok, cnt

def jhi(X, LX, LXhi, sq, pack):
    rhi = flo(D*exp(-mpf(LX//2048)/D)) + 2
    def fmulHi(a, b): return cdiv(a*b, D)
    def fpowHi(r, k):
        x = D
        for _ in range(k): x = cdiv(x*r, D)
        return x
    r3 = fpowHi(rhi, 3); r4 = fpowHi(rhi, 4)
    stepHi = cdiv(LXhi, 1024)
    first = cdiv((sq + OFF - getN(pack, 1))*D, sq)
    tail = cdiv(4*X*D*D, 3*(flo(D*sqrt(X)) - 1)*(X*X-1))
    A = fpowHi(r3, 16); Bq = fpowHi(r4, 16); acc = 0
    for m in range(16, 1024):
        j = m//16; i = m % 16
        a = getN(pack, j); b = getN(pack, j+1)
        om = 32*sq + 32*OFF - ((31-2*i)*a + (2*i+1)*b)
        assert om >= 0
        assert Bq < D
        aHi = cdiv(2*A*D, D - Bq)
        acc += cdiv(stepHi*aHi*om, 32*D*sq)
        A = fmulHi(A, r3); Bq = fmulHi(Bq, r4)
    return first + acc + tail

CONST = 223059076563587229937

def margin(Q, X, v, T):
    pack, cn = pack_of(v)
    sq = cn[0]
    LX = flo(D*log(X)) - 8; LXhi = flo(D*log(X)) + 9
    tot, ok, cnt = total(X, LX, LXhi, sq, pack, T)
    J = jhi(X, LX, LXhi, sq, pack)
    LQ = flo(D*log(Q)) + 40
    return tot - J - LQ + CONST, ok, cnt

if __name__ == "__main__":
    c = json.load(open(CERT))
    T = table()
    assert len(T) == 834
    rows = c["bootstrap"] + c["ladder"]
    worst = None
    for idx, r in enumerate(rows):
        mg, ok, cnt = margin(r["Q"], r["X"], r["v"], T)
        d = mg/D - r["margin_lower"]
        if not ok or mg <= 0 or abs(d) > 1e-12:
            print("ROW", idx, r["X"], "margin", mg/D, "ref", r["margin_lower"], "ok", ok)
        worst = d if worst is None else min(worst, d)
    print("done; worst diff", worst, "rows", len(rows))
