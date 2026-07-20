"""Perron value rho_k(lambda=2) of the KL operator, warm-started from the
saved eigenvector at lambda_k. Collatz-Wielandt gives rigorous brackets:
for any positive c: min F(c)/c <= rho <= max F(c)/c.
Vectorized build() from kl_gpu.py (numpy)."""
import numpy as np, math, sys, time, json

ALPHA = math.log(3, 2)
EDIR = "/Users/simon/Desktop/COLLATZ/experiments/kl/eigvecs"
CACHE = "/Users/simon/Desktop/COLLATZ/experiments/kl/analysis_cache"


def build(k):
    M = 3 ** k
    ms = np.arange(2, M, 3, dtype=np.int64)
    n = len(ms)
    itype = np.int32 if n < 2 ** 31 else np.int64
    idx_of = np.full(M, -1, dtype=itype)
    idx_of[ms] = np.arange(n, dtype=itype)
    i4m = idx_of[(4 * ms) % M]
    mod9 = ms % 9
    mask2 = mod9 == 2
    mask8 = mod9 == 8
    Mk1 = 3 ** (k - 1)
    ref2 = np.zeros((n, 3), dtype=itype)
    ref8 = np.zeros((n, 3), dtype=itype)
    r2 = ((4 * ms[mask2] - 2) // 3) % Mk1
    r8 = ((2 * ms[mask8] - 1) // 3) % Mk1
    for j in range(3):
        ref2[mask2, j] = idx_of[(r2 + j * Mk1) % M]
        ref8[mask8, j] = idx_of[(r8 + j * Mk1) % M]
    del idx_of, ms, mod9
    return i4m, mask2, mask8, ref2, ref8, n


def F(c, S, lam):
    i4m, mask2, mask8, ref2, ref8, n = S
    w2, w8, w4 = lam ** (ALPHA - 2), lam ** (ALPHA - 1), lam ** -2.0
    m2 = np.minimum(np.minimum(c[ref2[:, 0]], c[ref2[:, 1]]), c[ref2[:, 2]])
    m8 = np.minimum(np.minimum(c[ref8[:, 0]], c[ref8[:, 1]]), c[ref8[:, 2]])
    return w4 * c[i4m] + np.where(mask2, w2 * m2, 0.0) \
        + np.where(mask8, w8 * m8, 0.0)


out = {}
for k in [int(x) for x in sys.argv[1:]] or range(12, 18):
    t0 = time.time()
    S = build(k)
    c = np.load(f"{EDIR}/eigvec_k{k}.npy")
    lam = 2.0
    ev = None
    for t in range(600):
        f = F(c, S, lam)
        ev_new = f.max()
        f /= ev_new
        if t > 50 and ev is not None and abs(ev_new - ev) < 1e-14 * ev:
            c = f; ev = ev_new; break
        c = f; ev = ev_new
    q = F(c, S, lam) / c
    lo, hi = float(q.min()), float(q.max())
    out[k] = dict(ev=float(ev), cw_lo=lo, cw_hi=hi, iters=t + 1)
    print(f"k={k}: rho_k(2) ~ {ev:.9f}  CW=[{lo:.9f},{hi:.9f}]  "
          f"1-rho={1-ev:.6e}  [{time.time()-t0:.0f}s, {t+1} iters]", flush=True)
    del S, c, f, q

json.dump(out, open(f"{CACHE}/rho_at_2.json", "w"), indent=1)
gaps = [1 - out[k]["ev"] for k in sorted(out)]
print("1-rho ratios:", [round(gaps[i+1]/gaps[i], 4) for i in range(len(gaps)-1)])
