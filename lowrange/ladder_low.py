"""Extend the certificate ladder below 3.1e20, down to B = 10^5.

Each row (Q, X, v) is checked by kernel_verify.rigorous_margin and certifies, under GRH:
    every prime q = 3 mod 4 with X <= q <= Q has a split prime below X.
Output: certificate_full.json (the original certificate with the extra ladder rows appended, in
the same format, so that both verifiers read it) and ladder_full.txt (rows "X Q", first line B).

Usage:  python3 lowrange/ladder_low.py        (run from the repository root)
"""
import sys, json, warnings
sys.path.insert(0, ".")
warnings.simplefilter("ignore")
import kernel_opt
import kernel_verify as kv
from mpmath import mp

B = 10**5            # below B the class groups are computed directly (lowrange/direct.py)
M = 64


def float_row(Q, slack=0.02):
    lo, hi = 3, 20000
    while hi - lo > 1:
        mid = (lo + hi)//2
        mg, _ = kernel_opt.margin(mid, M, float(Q))
        if mg >= slack:
            hi = mid
        else:
            lo = mid
    _, vec = kernel_opt.margin(hi, M, float(Q))
    scale = 100000/max(abs(t) for t in vec)
    return hi, [int(round(t*scale)) for t in vec]


def certified_row(Q):
    X, v = float_row(Q)
    while True:
        lo, _, _ = kv.rigorous_margin(Q, X, v)
        if lo > 0:
            return {"Q": Q, "X": X, "v": v, "margin_lower": float(mp.mpf(lo)), "stage": "ladder-low"}
        X += 1
        _, v2 = kernel_opt.margin(X, M, float(Q))
        scale = 100000/max(abs(t) for t in v2)
        v = [int(round(t*scale)) for t in v2]


def main():
    c = json.load(open("certificate.json"))
    rows = []
    k = 1
    while True:
        Q = int(c["QLOW"] / 10**(k/8))
        if Q <= B:
            break
        row = certified_row(Q)
        rows.append(row)
        print("low  Q=%.4e  X=%d  margin>%.5f" % (Q, row["X"], row["margin_lower"]), flush=True)
        k += 1
    row = certified_row(B)
    rows.append(row)
    print("low  Q=%.4e  X=%d  margin>%.5f" % (B, row["X"], row["margin_lower"]), flush=True)
    assert all(r["X"] < B for r in c["bootstrap"] + c["ladder"] + rows)   # every row applies to all q >= B
    full = dict(c)
    full["ladder"] = c["ladder"] + rows
    full["B"] = B
    json.dump(full, open("lowrange/certificate_full.json", "w"))
    with open("lowrange/ladder_full.txt", "w") as f:
        f.write("%d\n" % B)
        for r in full["ladder"] + full["bootstrap"]:
            f.write("%d %d\n" % (r["X"], r["Q"]))
    print("rows added:", len(rows), " total ladder rows:", len(full["ladder"]))


if __name__ == "__main__":
    main()
