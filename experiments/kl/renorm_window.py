"""Local window analysis around -1: oscillation field, H-field statistics,
per-shell high-osc counts (local dimension), and the exact fiber-min identity.

Fibers are indexed by level-(k-1) bases; the base at local offset q=t/3^j
(v3(t)=0) is r = -1 + t*3^(k-1-j) mod 3^(k-1); its fiber values are
c(r + i*3^(k-1)).  osc = (max-min)/mean.

Outputs renorm_window.csv (per k, per shell j: counts of osc>t) and prints:
  - exact identity residual at -1:  c(-1) - [lam^-2 c(-4) + lam^(a-1)*minfib]
  - per-shell osc counts and multipliers, t = 0.1..0.4
  - H-field sibling-spread stats
"""
import csv, math, os, sys
import numpy as np
from renorm_common import ALPHA, HERE, load_C, lam_of, c_at

KS = [int(x) for x in sys.argv[1:]] or [15, 16, 17, 18, 19]
JMAX = 9          # deepest shell of fiber bases
rows = []

for k in KS:
    C = load_C(k)
    lam, _ = lam_of(k)
    M, M1 = 3 ** k, 3 ** (k - 1)
    c1 = c_at(C, k, -1)

    # ---- exact identity at -1 ----
    minfib = min(c_at(C, k, -1 + i * M1) for i in range(3))
    lhs = c1
    rhs = lam ** -2 * c_at(C, k, -4) + lam ** (ALPHA - 1) * minfib
    print(f"k={k}: identity rel residual (c-F(c))/c at -1: {(lhs-rhs)/lhs:.3e}"
          f"   min/c(-1)={minfib/c1:.6f}"
          f"   lam^(1-a)-lam^(-1-a)*c(-4)/c(-1)="
          f"{lam**(1-ALPHA) - lam**(-1-ALPHA)*c_at(C,k,-4)/c1:.6f}")

    # ---- osc field over window bases, shell by shell ----
    for j in range(1, JMAX + 1):
        oscs = []
        for t in range(3 ** j):
            if t % 3 == 0 and j > 1:
                continue
            r = (-1 + t * 3 ** (k - 1 - j)) % M1
            fib = [c_at(C, k, r + i * M1) for i in range(3)]
            mn, mx, me = min(fib), max(fib), sum(fib) / 3
            oscs.append((mx - mn) / me)
        oscs = np.array(oscs)
        row = dict(k=k, j=j, n=len(oscs), mean_osc=round(float(oscs.mean()), 5),
                   max_osc=round(float(oscs.max()), 5))
        for t in (0.1, 0.2, 0.3, 0.4):
            row[f"n_gt_{t}"] = int((oscs > t).sum())
        rows.append(row)

with open(os.path.join(HERE, "renorm_window.csv"), "w", newline="") as f:
    w = csv.DictWriter(f, fieldnames=list(rows[0])); w.writeheader(); w.writerows(rows)

print("\nper-shell counts of osc>t among bases at 3-adic distance 3^-j from -1")
print("(within level k; shells j=1..%d; multiplier = ratio to previous shell)" % JMAX)
for k in KS:
    print(f"k={k}:  j : n    mean  " + "  ".join(f">{t}" for t in (0.1, 0.2, 0.3, 0.4)))
    prev = None
    for r in [r for r in rows if r["k"] == k]:
        mult = ""
        if prev:
            mult = "  mult(0.2)=%.2f" % (r["n_gt_0.2"] / prev["n_gt_0.2"]) \
                if prev["n_gt_0.2"] else ""
        print(f"   {r['j']:2d}: {r['n']:5d} {r['mean_osc']:.3f} "
              f"{r['n_gt_0.1']:5d} {r['n_gt_0.2']:5d} {r['n_gt_0.3']:5d} "
              f"{r['n_gt_0.4']:5d}{mult}")
        prev = r
