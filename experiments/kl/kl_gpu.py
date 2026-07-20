"""KL nonlinear Perron solver, GPU (cupy) with numpy fallback.
Usage: python kl_gpu.py K_MIN K_MAX [OUTDIR]
Saves per-k: eigenvector eigvec_k{k}.npy (float64, host order) + one summary line.
Same system as kl_perron_solver.py (validated against KL 2003 table k=2..11
and exact-rational certification at k=12..14)."""
import sys, math, time

try:
    import cupy as xp
    GPU = True
except ImportError:
    import numpy as xp
    GPU = False
import numpy as np

ALPHA = math.log(3, 2)


def build(k):
    """Build index arrays on host (numpy), return device copies."""
    M = 3**k
    ms = np.arange(2, M, 3, dtype=np.int64)
    n = len(ms)
    itype = np.int32 if n < 2**31 else np.int64
    idx_of = np.full(M, -1, dtype=itype)
    idx_of[ms] = np.arange(n, dtype=itype)
    i4m = idx_of[(4 * ms) % M]
    mod9 = ms % 9
    idx2 = np.nonzero(mod9 == 2)[0].astype(itype)
    idx8 = np.nonzero(mod9 == 8)[0].astype(itype)
    Mk1 = 3**(k - 1)
    m2 = ms[idx2]
    r2 = ((4 * m2 - 2) // 3) % Mk1
    m8 = ms[idx8]
    r8 = ((2 * m8 - 1) // 3) % Mk1
    ref2c = np.empty((len(m2), 3), dtype=itype)
    ref8c = np.empty((len(m8), 3), dtype=itype)
    for j in range(3):
        ref2c[:, j] = idx_of[(r2 + j * Mk1) % M]
        ref8c[:, j] = idx_of[(r8 + j * Mk1) % M]
    dev = lambda a: xp.asarray(a)
    return (dev(i4m), dev(idx2), dev(idx8), dev(ref2c), dev(ref8c), n)


def eigval(lam, S, iters=4000, tol=1e-13):
    i4m, idx2, idx8, ref2c, ref8c, n = S
    c = xp.ones(n, dtype=xp.float64)
    w2 = lam**(ALPHA - 2)
    w8 = lam**(ALPHA - 1)
    w4 = lam**-2.0
    ev = 1.0
    for t in range(iters):
        f = w4 * c[i4m]
        m2v = xp.minimum(xp.minimum(c[ref2c[:, 0]], c[ref2c[:, 1]]), c[ref2c[:, 2]])
        f[idx2] = f[idx2] + w2 * m2v
        del m2v
        m8v = xp.minimum(xp.minimum(c[ref8c[:, 0]], c[ref8c[:, 1]]), c[ref8c[:, 2]])
        f[idx8] = f[idx8] + w8 * m8v
        del m8v
        ev_new = float(f.max())
        f /= ev_new
        if t > 100 and abs(ev_new - ev) < tol * ev:
            c = f
            ev = ev_new
            break
        c = f
        ev = ev_new
    return ev, c


def solve(k, outdir):
    t0 = time.time()
    S = build(k)
    l0, l1 = 1.80, 1.85
    g0 = math.log(eigval(l0, S)[0])
    g1 = math.log(eigval(l1, S)[0])
    for _ in range(60):
        if abs(g1 - g0) < 1e-16:
            break
        l2 = min(max(l1 - g1 * (l1 - l0) / (g1 - g0), 1.05), 2.5)
        if abs(l2 - l1) < 1e-9:
            l1 = l2
            break
        l0, g0 = l1, g1
        l1 = l2
        g1 = math.log(eigval(l1, S)[0])
    ev, c = eigval(l1, S)
    chost = xp.asnumpy(c) if GPU else c
    np.save(f"{outdir}/eigvec_k{k}.npy", chost)
    print(f"k={k:2d} states={len(chost):>10d} lambda={l1:.7f} "
          f"gamma={math.log(l1, 2):.7f} ev={ev:.12f} "
          f"[{time.time()-t0:.0f}s, {'GPU' if GPU else 'CPU'}]", flush=True)


if __name__ == "__main__":
    kmin, kmax = int(sys.argv[1]), int(sys.argv[2])
    outdir = sys.argv[3] if len(sys.argv) > 3 else "."
    print(f"backend: {'cupy/GPU' if GPU else 'numpy/CPU'}", flush=True)
    for k in range(kmin, kmax + 1):
        solve(k, outdir)
