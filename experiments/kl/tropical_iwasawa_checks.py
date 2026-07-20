#!/usr/bin/env python3
"""Numerical companion to docs/notes/tropical-iwasawa.md.

A. Extract lambda_k from converged eigenvectors (class-5 fixed-point ratios).
B. Fiber-oscillation data delta_k, eps_k; verify the oscillation identity
   s(lambda_k) - 1 = (w2+w8) * delta_k at k = 12..17.
C. Growth-law fits: geometric-gap (Model A), free-limit (Model B),
   increment-geometric, and the Iwasawa-ansatz e_k = mu*3^k + lam*k + nu.
D. Spectral tower experiment k=2..6: augmentation triangularity (exact),
   failure of Gamma-equivariance and of tower intertwining, eigenvalue nesting.
Run from repo root:  python3 experiments/kl/tropical_iwasawa_checks.py
"""
import numpy as np

ALPHA = np.log2(3.0)
EIGDIR = "experiments/kl/eigvecs"

# ---------- shared constructors ----------

def system(k):
    """Index arrays for the level-k KL system (same conventions as kl_perron_solver)."""
    mod = 3 ** k
    ms = np.arange(2, mod, 3, dtype=np.int64)          # [3^k], ascending, n = 3^(k-1)
    idx = {int(m): i for i, m in enumerate(ms)}
    i4m = np.array([idx[int((4 * m) % mod)] for m in ms], dtype=np.int64)
    mask2 = (ms % 9 == 2)
    mask8 = (ms % 9 == 8)
    sub = 3 ** (k - 1)
    ref2 = np.zeros((mask2.sum(), 3), dtype=np.int64)
    ref8 = np.zeros((mask8.sum(), 3), dtype=np.int64)
    for a, (mask, ref, num, den) in enumerate([(mask2, ref2, 4, 2), (mask8, ref8, 2, 1)]):
        rows = ms[mask]
        r = ((num * rows - den) // 3) % sub
        for j in range(3):
            ref[:, j] = [idx[int(x)] for x in (r + j * sub) % mod]
    return ms, i4m, mask2, mask8, ref2, ref8

def s_of_lambda(lam):
    return lam ** -2.0 + (lam ** (ALPHA - 2) + lam ** (ALPHA - 1)) / 3.0

def weights(lam):
    return lam ** (ALPHA - 2), lam ** (ALPHA - 1)

def annealed_matrix(k, lam):
    ms, i4m, mask2, mask8, ref2, ref8 = system(k)
    n = len(ms)
    w2, w8 = weights(lam)
    A = np.zeros((n, n))
    A[np.arange(n), i4m] += lam ** -2.0
    for i, row in zip(np.where(mask2)[0], ref2):
        for j in row:
            A[i, j] += w2 / 3.0
    for i, row in zip(np.where(mask8)[0], ref8):
        for j in row:
            A[i, j] += w8 / 3.0
    return A

# ---------- A/B: eigenvector-derived data ----------

def extract(k):
    v = np.load(f"{EIGDIR}/eigvec_k{k}.npy")
    n = 3 ** (k - 1)
    assert v.shape[0] == n, (k, v.shape)
    mod = 3 ** k
    ms = np.arange(2, mod, 3, dtype=np.int64)
    # lambda from class-5 rows: c^m = lam^-2 c^{4m}
    m5 = ms[ms % 9 == 5]
    lam_arr = np.sqrt(v[((4 * m5) % mod - 2) // 3] / v[(m5 - 2) // 3])
    lam = float(np.median(lam_arr))
    iqr = float(np.percentile(lam_arr, 75) - np.percentile(lam_arr, 25))
    # fiber oscillation: fibers over Y_{k-1} are {r + j*3^{k-1}} -> indices i, i+n/3, i+2n/3?
    # index of m = (m-2)/3; m = r + j*3^{k-1} -> i = (r-2)/3 + j*3^{k-2}*... careful:
    # (r + j*3^{k-1} - 2)/3 = (r-2)/3 + j*3^{k-2}. r ranges over [3^{k-1}] -> (r-2)/3 in [0, 3^{k-2}).
    nsub = 3 ** (k - 2)
    fib = v.reshape(3, nsub)  # row j = values at r + j*3^{k-1}, col = (r-2)/3
    fmin = fib.min(axis=0); favg = fib.mean(axis=0); fmax = fib.max(axis=0)
    delta = float((favg - fmin).sum() / v.sum())
    eps = float((1.0 - fmin / fmax).max())
    med_osc = float(np.median(1.0 - fmin / fmax))
    # oscillation identity residual (assumes rho = 1 at lam):
    w2, w8 = weights(lam)
    resid = (s_of_lambda(lam) - 1.0) - (w2 + w8) * delta
    return dict(k=k, lam=lam, iqr=iqr, gamma=float(np.log2(lam)), delta=delta,
                eps=eps, med_osc=med_osc, resid=float(resid))

# ---------- C: fits ----------

def fits(ks, gammas):
    ks = np.asarray(ks, float); g = np.asarray(gammas, float)
    inc = np.diff(g); kk = ks[:-1]
    out = {}
    # Model A: 1-gamma = C q^k
    X = np.vstack([np.ones_like(ks), ks]).T
    coef, *_ = np.linalg.lstsq(X, np.log(1 - g), rcond=None)
    qA = float(np.exp(coef[1]))
    pred = 1 - np.exp(X @ coef)
    out["A"] = dict(q=qA, C=float(np.exp(coef[0])), rms=float(np.sqrt(np.mean((pred - g) ** 2))))
    # increments geometric: inc = D r^k
    coef, *_ = np.linalg.lstsq(np.vstack([np.ones_like(kk), kk]).T, np.log(inc), rcond=None)
    r = float(np.exp(coef[1])); D = float(np.exp(coef[0]))
    ginf = g[-1] + D * r ** ks[-1] * r / (1 - r)   # sum of remaining increments
    out["inc"] = dict(r=r, D=D, gamma_inf=float(ginf),
                      rms=float(np.sqrt(np.mean((D * r ** kk - inc) ** 2))))
    # Model B: gamma = ginf - C q^k, profile over ginf
    prof = []
    for gi in np.arange(g[-1] + 1e-4, 1.0001, 1e-4):
        y = np.log(gi - g)
        coef, *_ = np.linalg.lstsq(X, y, rcond=None)
        pred = gi - np.exp(X @ coef)
        prof.append((gi, float(np.sqrt(np.mean((pred - g) ** 2))), float(np.exp(coef[1]))))
    prof = np.array(prof)
    i = int(prof[:, 1].argmin())
    out["B"] = dict(gamma_inf=float(prof[i, 0]), rms=float(prof[i, 1]), q=float(prof[i, 2]),
                    rms_at_1=float(prof[-1, 1]))
    # Iwasawa ansatz on e_k = -log3(1-gamma_k) = mu*3^k + lam*k + nu
    e = -np.log(1 - g) / np.log(3)
    Xi = np.vstack([3.0 ** ks, ks, np.ones_like(ks)]).T
    coef, *_ = np.linalg.lstsq(Xi, e, rcond=None)
    out["iwasawa_gap"] = dict(mu=float(coef[0]), lam=float(coef[1]), nu=float(coef[2]),
                              rms=float(np.sqrt(np.mean((Xi @ coef - e) ** 2))))
    # Iwasawa ansatz on increments e'_k = -log3(inc)
    ei = -np.log(inc) / np.log(3)
    Xi2 = np.vstack([3.0 ** kk, kk, np.ones_like(kk)]).T
    coef, *_ = np.linalg.lstsq(Xi2, ei, rcond=None)
    out["iwasawa_inc"] = dict(mu=float(coef[0]), lam=float(coef[1]), nu=float(coef[2]),
                              rms=float(np.sqrt(np.mean((Xi2 @ coef - ei) ** 2))))
    return out

# ---------- D: spectral tower experiment ----------

def spectral(kmax=6, lam=2.0):
    print(f"\n=== D. spectral tower at lambda = {lam} (s = {s_of_lambda(lam):.10f}) ===")
    prev_eigs = None
    for k in range(2, kmax + 1):
        A = annealed_matrix(k, lam)
        n = A.shape[0]
        # augmentation triangularity: column sums all equal s(lambda)
        cs = A.sum(axis=0)
        print(f"k={k} n={n}: colsum spread = {cs.max()-cs.min():.2e} (s = {cs.mean():.10f})")
        eigs = np.sort_complex(np.linalg.eigvals(A))
        # Perron gap
        mods = np.sort(np.abs(eigs))[::-1]
        print(f"   |eig|: top3 = {mods[:3].round(6)}, perron gap = {mods[0]-mods[1]:.6f}")
        if prev_eigs is not None:
            d = np.array([np.min(np.abs(eigs - e)) for e in prev_eigs])
            print(f"   nesting: max dist(spec_k-1 -> spec_k) = {d.max():.6f}, "
                  f"median = {np.median(d):.6f}")
        prev_eigs = eigs
        # Gamma-equivariance: commutator with U_a, a=4 (generator) and a=10 (in Gamma_1)
        if k <= 5:
            mod = 3 ** k
            ms = np.arange(2, mod, 3, dtype=np.int64)
            idx = {int(m): i for i, m in enumerate(ms)}
            for a in (4, 10):
                P = np.zeros((n, n))
                for i, m in enumerate(ms):
                    P[i, idx[int((a * m) % mod)]] = 1.0
                comm = np.abs(A @ P - P @ A).max()
                print(f"   ||[A, U_{a}]||_max = {comm:.6f}")
            # tower intertwining: pi_* A^(k) vs A^(k-1) pi_* on pullbacks
            if k >= 3:
                Am1 = annealed_matrix(k - 1, lam)
                nm1 = Am1.shape[0]
                # pullback matrix P*: C(Y_{k-1}) -> C(Y_k), (P*c)(m) = c(m mod 3^{k-1})
                Pb = np.zeros((n, nm1))
                msm1 = np.arange(2, 3 ** (k - 1), 3, dtype=np.int64)
                idxm1 = {int(m): i for i, m in enumerate(msm1)}
                for i, m in enumerate(ms):
                    Pb[i, idxm1[int(m % 3 ** (k - 1))]] = 1.0
                diff = np.abs(A @ Pb - Pb @ Am1).max()
                print(f"   ||A^(k) pi* - pi* A^(k-1)||_max = {diff:.6f}  (0 would mean tower map)")

def spectrum_theorem_check(kmax=6, lams=(2.0, 1.83, 1.5)):
    """Verify spec(A_lam^(k)) = {s(lam)} u {lam^-2 zeta : zeta^n = 1, zeta != 1}, n = 3^(k-1),
    as multisets (optimal assignment), and the trace intertwining pi_! A = A' pi_!."""
    from scipy.optimize import linear_sum_assignment
    print("\n=== spectrum theorem check ===")
    for lam in lams:
        for k in range(2, kmax + 1):
            A = annealed_matrix(k, lam)
            n = A.shape[0]
            eigs = np.linalg.eigvals(A)
            pred = np.array([s_of_lambda(lam)] +
                            [lam ** -2 * np.exp(2j * np.pi * t / n) for t in range(1, n)])
            D = np.abs(eigs[:, None] - pred[None, :])
            r, c = linear_sum_assignment(D)
            line = f"lam={lam} k={k}: spec-vs-predicted (matched) max err = {D[r, c].max():.2e}"
            if k >= 3:
                Am1 = annealed_matrix(k - 1, lam)
                mod, sub = 3 ** k, 3 ** (k - 1)
                ms = np.arange(2, mod, 3, dtype=np.int64)
                msm1 = np.arange(2, sub, 3, dtype=np.int64)
                idxm1 = {int(m): i for i, m in enumerate(msm1)}
                S = np.zeros((Am1.shape[0], n))
                for i, m in enumerate(ms):
                    S[idxm1[int(m % sub)], i] = 1.0
                line += f"   ||pi_! A - A' pi_!|| = {np.abs(S @ A - Am1 @ S).max():.2e}"
            print(line)

# ---------- main ----------

if __name__ == "__main__":
    print("=== A/B. eigenvector-derived lambda_k, delta_k (k = 12..17) ===")
    rows = []
    for k in range(12, 18):
        try:
            rows.append(extract(k))
        except Exception as e:
            print(f"k={k}: skipped ({e})")
    print(f"{'k':>3} {'lambda_k':>11} {'gamma_k':>10} {'IQR':>8} {'delta_k':>10} "
          f"{'eps_k':>7} {'med_osc':>8} {'ident.resid':>11}")
    for r in rows:
        print(f"{r['k']:>3} {r['lam']:>11.7f} {r['gamma']:>10.7f} {r['iqr']:>8.1e} "
              f"{r['delta']:>10.6f} {r['eps']:>7.4f} {r['med_osc']:>8.4f} {r['resid']:>11.2e}")

    print("\n=== C. growth-law fits ===")
    gam = {2:0.4365884,3:0.6112622,4:0.6891089,5:0.7335799,6:0.7608188,7:0.7825687,
           8:0.8031969,9:0.8168311,10:0.8295463,11:0.8417566,12:0.8531363,13:0.8630058,
           14:0.8724524}
    for r in rows:
        gam[r["k"]] = r["gamma"]
    gam[18] = 0.9033          # PRELIMINARY (reported by the k=18 run; file incomplete)
    ks_all = sorted(gam)
    g_all = [gam[k] for k in ks_all]
    print("increments:", {k2: round(gam[k2] - gam[k2 - 1], 7) for k2 in ks_all if k2 - 1 in gam and k2 >= 11})
    incs = [gam[k2] - gam[k2 - 1] for k2 in ks_all if k2 - 1 in gam]
    kk = [k2 for k2 in ks_all if k2 - 1 in gam]
    print("increment ratios:", {kk[i]: round(incs[i] / incs[i - 1], 4) for i in range(1, len(kk)) if kk[i] == kk[i-1] + 1})
    print("gap ratios (1-g_k+1)/(1-g_k):",
          {k2: round((1 - gam[k2]) / (1 - gam[k2 - 1]), 4) for k2 in ks_all if k2 - 1 in gam and k2 >= 11})
    for window in [(8, 14), (11, 17), (11, 18), (12, 18), (14, 18)]:
        ks = [k for k in ks_all if window[0] <= k <= window[1]]
        f = fits(ks, [gam[k] for k in ks])
        print(f"\n-- window k = {window[0]}..{window[1]} --")
        print(f"  A (ginf=1):  q = {f['A']['q']:.5f}  rms = {f['A']['rms']:.2e}"
              f"   -> lam_Iw = {-np.log(f['A']['q'])/np.log(3):.4f}")
        print(f"  increments:  r = {f['inc']['r']:.5f}  rms = {f['inc']['rms']:.2e}"
              f"   -> ginf = {f['inc']['gamma_inf']:.4f}, lam_Iw = {-np.log(f['inc']['r'])/np.log(3):.4f}")
        print(f"  B (free):    ginf = {f['B']['gamma_inf']:.4f}  q = {f['B']['q']:.5f}"
              f"  rms = {f['B']['rms']:.2e}  (rms at ginf->1: {f['B']['rms_at_1']:.2e})")
        print(f"  Iwasawa gap: mu = {f['iwasawa_gap']['mu']:.2e}  lam = {f['iwasawa_gap']['lam']:.4f}"
              f"  nu = {f['iwasawa_gap']['nu']:.3f}  rms = {f['iwasawa_gap']['rms']:.2e}")
        print(f"  Iwasawa inc: mu = {f['iwasawa_inc']['mu']:.2e}  lam = {f['iwasawa_inc']['lam']:.4f}"
              f"  nu = {f['iwasawa_inc']['nu']:.3f}  rms = {f['iwasawa_inc']['rms']:.2e}")

    spectral(kmax=6, lam=2.0)
    spectral(kmax=5, lam=1.83)
    spectrum_theorem_check(kmax=6)
