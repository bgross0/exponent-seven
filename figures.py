"""Figures for the note (paper/fig_*.pdf).  Reads certificate.json and logs/prod_*.log only.

Usage:  python3 figures.py
"""
import json, math, glob
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

BLUE, ORANGE = "#257de0", "#f47230"
INK, INK2, GRID = "#191919", "#666666", "#e6e6e6"

plt.rcParams.update({
    "font.family": "STIXGeneral", "mathtext.fontset": "stix", "font.size": 9, "axes.titlesize": 9, "axes.labelsize": 9,
    "axes.edgecolor": INK2, "axes.labelcolor": INK, "xtick.color": INK2, "ytick.color": INK2,
    "axes.grid": True, "grid.color": GRID, "grid.linewidth": 0.6, "axes.axisbelow": True,
    "axes.spines.top": False, "axes.spines.right": False, "legend.frameon": False,
    "savefig.bbox": "tight", "savefig.pad_inches": 0.03,
})
W, H = 5.6, 2.5

cert = json.load(open("certificate.json"))


def autocorr(v):
    m, sq = len(v), sum(t*t for t in v)
    return [sum(v[k]*v[k+j] for k in range(m - j))/sq for j in range(m + 1)]


def f_of(u, corr, logX):
    m = len(corr) - 1
    c = u/(logX/m)
    if c >= m:
        return 0.0
    k = int(c)
    return corr[k] + (c - k)*(corr[k+1] - corr[k])


# Figure 1: the kernel of the first bootstrap row, with the primes it is evaluated at.
row = cert["bootstrap"][0]
X, corr = row["X"], autocorr(row["v"])
logX = math.log(X)
us = [logX*i/2000 for i in range(2001)]
primes = [p for p in range(2, X) if all(p % d for d in range(2, int(p**0.5) + 1))]
fig, ax = plt.subplots(figsize=(W, H))
ax.axhline(0, color=INK2, lw=0.8)
ax.plot(us, [f_of(u, corr, logX) for u in us], color=BLUE, lw=2)
ymin = -0.5
ax.vlines([math.log(p) for p in primes], ymin, ymin + 0.06, color=INK2, lw=0.4)
ax.set_ylim(ymin, 1.05)
ax.set_xlabel(r"$u$   (ticks at $u=\log p$ for the primes $p<X$)")
ax.set_ylabel(r"$f(u)$")
ax.set_xlim(0, logX*1.02)
fig.savefig("paper/fig_kernel.pdf")
plt.close(fig)

# Figure 2: every certificate row, q <= Q forces a split prime below X.
fig, ax = plt.subplots(figsize=(W, H))
lad, boot = cert["ladder"], cert["bootstrap"]
ax.plot([r["Q"] for r in lad], [r["X"] for r in lad], "o", ms=4, color=BLUE, mec="white", mew=0.8,
        label="ladder rows (shorten the search)")
ax.plot([r["Q"] for r in boot], [r["X"] for r in boot], "s", ms=4.5, color=ORANGE, mec="white", mew=0.8,
        label=r"bootstrap rows ($Q\to 4P^7$)")
ax.axhline(4297, color=INK2, lw=0.8, ls="--")
ax.text(3.5e20, 4297*1.03, r"$P^*=4297$", color=INK2, va="bottom")
ax.set_xscale("log")
ax.set_xlabel(r"$Q$   (certified: every admissible $q\leq Q$ has a split prime $p<X$)")
ax.set_ylabel(r"$X$")
ax.legend(loc="upper left")
fig.savefig("paper/fig_certificate.pdf")
plt.close(fig)

# Figure 3: search work per prime p (positions surviving the wheel), all with 0 survivors.
rows = []
for path in sorted(glob.glob("logs/prod_*.log")):
    for line in open(path):
        t = line.split()
        if t and t[0] == "P":
            d = dict(zip(t[0::2], t[1::2]))
            rows.append((int(d["P"]), int(d["wheel"]), int(d["surv"])))
rows.sort()
assert len(rows) == 465 and all(s == 0 for _, _, s in rows)
fig, ax = plt.subplots(figsize=(W, H))
ax.plot([p for p, _, _ in rows], [w for _, w, _ in rows], "o", ms=2.6, color=BLUE, mec="none")
ax.set_yscale("log")
ax.set_xlabel(r"least split prime candidate $p$")
ax.set_ylabel("positions after the wheel")
fig.savefig("paper/fig_search.pdf")
plt.close(fig)
print("wrote paper/fig_kernel.pdf, paper/fig_certificate.pdf, paper/fig_search.pdf")
