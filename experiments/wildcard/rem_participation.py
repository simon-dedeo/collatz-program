#!/usr/bin/env python3
"""REM / replica reading of the KL extremal eigenvector.

The adversarial (min) KL operator selects, per chord fiber {r, r+3^{k-1}, r+2*3^{k-1}},
the WORST lift. The 'disorder' it optimizes over is the fiber-oscillation
    D_r = (fiber average of c_k) - (fiber min of c_k)  >= 0.
Derrida's Random Energy Model order parameter is the participation ratio (overlap)
    Y = sum_r D_r^2 / (sum_r D_r)^2   in (0,1],
    1/Y = effective # of fibers carrying the adversary's action.
Delocalized / replica-symmetric  <=> (1/Y)/N_fibers -> const  (mass spread over ~all fibers).
Condensed / frozen (RSB, glassy)  <=> (1/Y)/N_fibers -> 0     (mass on rare fibers).
Y itself = P(two independent fibers drawn prop. to D coincide) = the REM overlap q.
"""
import numpy as np, math, sys, os

OUT = os.path.join(os.path.dirname(__file__), "rem_results.csv")
rows = [("k","N_fibers","sumD","Y_overlap","invY_eff","invY_over_N",
         "top1pct_share","top01pct_share","gini")]

def gini_sorted(x):  # x nonneg, ascending sort inside
    x = np.sort(x); n = x.size; cx = np.cumsum(x); s = cx[-1]
    if s == 0: return 0.0
    return (n + 1 - 2*np.sum(cx)/s)/n

for k in range(14, 19):
    v = np.load(f"experiments/kl/eigvec_k{k}.npy")           # length 3^{k-1}
    Nf = 3**(k-2)
    A = v.reshape(3, Nf)                                     # rows j=0,1,2 are the 3 lifts
    avg = A.mean(axis=0)
    mn  = A.min(axis=0)
    D = avg - mn                                            # >=0 per fiber
    del v, A
    s = D.sum()
    p = D / s
    Y = float(np.sum(p*p))
    invY = 1.0/Y
    # tail shares
    Ds = np.sort(D)[::-1]
    c = np.cumsum(Ds)/s
    t1  = float(c[max(0,int(0.01*Nf))-1]) if Nf>=100 else float(c[-1])
    t01 = float(c[max(0,int(0.001*Nf))-1]) if Nf>=1000 else float(c[-1])
    g = gini_sorted(D)
    rows.append((k, Nf, f"{s:.6e}", f"{Y:.6e}", f"{invY:.6e}",
                 f"{invY/Nf:.6e}", f"{t1:.5f}", f"{t01:.5f}", f"{g:.5f}"))
    print(f"k={k} Nf={Nf} Y={Y:.4e} 1/Y={invY:.4e} (1/Y)/Nf={invY/Nf:.5f} "
          f"top1%={t1:.4f} top0.1%={t01:.4f} gini={g:.4f}", flush=True)

with open(OUT,"w") as f:
    for r in rows: f.write(",".join(str(x) for x in r)+"\n")
print("wrote", OUT)
