"""Trace argmin chains of the local system at -1 and the min-harmonic residual.

Local coordinates: offset q = u/3^nu in Z(3^infty) <-> level-k state
-1 + u*3^(k-nu).  Children of q are (2q+i)/3, i = 0,1,2 (the lifts of
R8(state)).  H(q) := (c(state)/c(-1)) * lam^((alpha-1)*nu(q)) is constant
along exact-argmin chains (pure-branch); spine chain from 0 has H ~ 1,
co-spine chain from the non-argmin fiber lift has H ~ C.

Outputs renorm_chains.csv and prints chain tables.
"""
import csv, math, os, sys
from fractions import Fraction
import numpy as np
from renorm_common import ALPHA, HERE, load_C, lam_of, cval

KS = [int(x) for x in sys.argv[1:]] or [15, 16, 17, 18, 19]
rows = []

def chain(C, k, lam, u0, nu0, steps, label):
    """Follow argmin children from offset u0/3^nu0; return list of dicts."""
    c1 = cval(C, k, 0, 1)
    w8 = lam ** (ALPHA - 1)
    out = []
    u, nu = u0, nu0
    for s in range(steps):
        val = cval(C, k, u, nu)
        # children: offsets 2u + i*3^nu at depth nu+1
        kids = [((2 * u + i * 3 ** nu) % 3 ** (nu + 1)) for i in range(3)]
        kvals = [cval(C, k, w, nu + 1) for w in kids]
        imin = int(np.argmin(kvals))
        ksort = sorted(kvals)
        margin = (ksort[1] - ksort[0]) / ksort[0]
        H = (val / c1) * lam ** ((ALPHA - 1) * nu)
        out.append(dict(k=k, label=label, step=s, nu=nu, u=u,
                        val_over_c1=val / c1, H=H, argmin_digit=imin,
                        margin=margin))
        u, nu = kids[imin], nu + 1
    return out

for k in KS:
    C = load_C(k)
    lam, _ = lam_of(k)
    # spine: from q=0 (which fiber lift is argmin of the top fiber?)
    fib = [cval(C, k, j, 1) for j in range(3)]
    jmin = int(np.argmin(fib))           # spine's first offset (1 or 2)
    jco = 3 - jmin                       # the other nontrivial lift
    rows += chain(C, k, lam, 0, 1, min(k - 4, 12), "spine")   # 0's chain
    rows += chain(C, k, lam, jco, 1, min(k - 4, 12), "cospine")

with open(os.path.join(HERE, "renorm_chains.csv"), "w", newline="") as f:
    w = csv.DictWriter(f, fieldnames=list(rows[0])); w.writeheader(); w.writerows(rows)

for k in KS:
    for lab in ["spine", "cospine"]:
        rs = [r for r in rows if r["k"] == k and r["label"] == lab]
        print(f"k={k} {lab}: digits=" +
              "".join(str(r["argmin_digit"]) for r in rs))
        print("   H: " + " ".join(f"{r['H']:.4f}" for r in rs))
        print("   u: " + " ".join(str(r["u"]) for r in rs))
        print("   margin: " + " ".join(f"{r['margin']:.3f}" for r in rs))
