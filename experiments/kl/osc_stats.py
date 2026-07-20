#!/usr/bin/env python3
"""Fiber-oscillation statistics of the GPU candidate eigenvectors (k = 14..18).

Reproduces the table in docs/notes/adversarial-operator.md §5.
Indexing: c is indexed by i = (m-2)/3 for m in [3^k] ascending (m ≡ 2 mod 3).
The level-(k-1) fiber of r ∈ [3^{k-1}] is {r + j*3^{k-1} : j=0,1,2}, whose
indices are (r-2)/3 + j*3^{k-2}; hence reshape(3, 3^{k-2}) puts fibers in columns.
Class of the fiber label r = 3*i+2 mod 9 is determined by i mod 3: 0->2, 1->5, 2->8.
"""
import numpy as np, math, os

HERE = os.path.dirname(os.path.abspath(__file__))
ALPHA = math.log2(3)

def s(lam):  # annealed Perron value (kl-limit-object.md Lemma 1.3)
    return lam**-2 + (lam**(ALPHA-2) + lam**(ALPHA-1))/3

LAM_FLOAT = {14: 1.8307723, 15: 1.8419684, 16: 1.8522348, 17: 1.8616888, 18: 1.8703250}

def stats(k):
    c = np.load(os.path.join(HERE, f"eigvec_k{k}.npy"), mmap_mode='r')
    n = c.shape[0]; assert n == 3**(k-1)
    C = np.asarray(c).reshape(3, n//3)
    mn, mx, av = C.min(0), C.max(0), C.mean(0)
    D = av - mn
    delta = float(D.sum()/C.sum())                       # mean relative fiber oscillation
    eps_sup = float((1 - mn/mx).max())                   # sup relative oscillation
    eps_med = float(np.median(1 - mn/mx))
    am = C.argmin(0); argmin_frac = [float((am == j).mean()) for j in range(3)]
    Ds = np.sort(D)[::-1]; tot = Ds.sum()
    top1 = float(Ds[:max(1, len(Ds)//100)].sum()/tot); top10 = float(Ds[:len(Ds)//10].sum()/tot)
    rel = D/av; cls = np.arange(len(D)) % 3
    bycls = [float(rel[cls == j].mean()) for j in range(3)]  # r ≡ 2, 5, 8 (mod 9)
    lam = LAM_FLOAT[k]
    ident = (s(lam) - 1)/(lam**(ALPHA-2) + lam**(ALPHA-1))   # oscillation-law prediction
    return dict(k=k, delta=delta, identity=ident, eps_sup=eps_sup, eps_med=eps_med,
                argmin=argmin_frac, top1=top1, top10=top10, bycls=bycls,
                spread=float(mx.max()/mn.min()))

if __name__ == "__main__":
    for k in sorted(LAM_FLOAT):
        r = stats(k)
        print(f"k={r['k']}  delta={r['delta']:.6f} (identity {r['identity']:.6f})  "
              f"eps_sup={r['eps_sup']:.4f}  eps_med={r['eps_med']:.4f}  "
              f"argmin={np.round(r['argmin'],4)}  top1%={r['top1']:.3f}  top10%={r['top10']:.3f}  "
              f"relD by class 2/5/8: {np.round(r['bycls'],4)}  Cmax/Cmin={r['spread']:.1f}")
