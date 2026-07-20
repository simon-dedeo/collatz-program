# limit_object_checks.py — reproduces every numerical claim in docs/notes/kl-limit-object.md
#
# Sections (run all: `python3 limit_object_checks.py [KMAX=12]`):
#   [1] thresholds lambda_k, extremal eigenvectors, oscillation identity (Thm 3.2(i)),
#       KL Table-2 quantities (cbar_kk, cbar_{k-1,k}, Cmax), fiber-oscillation stats
#       (delta_k mean / eps sup / median)  — note §3.2
#   [2] annealed operator: all column sums = s(lambda), rho(A) = s(lambda), s(2)=s(4)=1
#       — note Lemma 1.3, Prop 1.4
#   [3] quenched value at lambda = 2 (k up to 14) and lambda in (2,12] — note §1.4 remark,
#       §4 secondary observable
#   [4] rho_k(lambda) monotone decreasing on [1,2] (empirical) — note §2.3
#   [5] fits and pre-registered predictions for gamma_15..gamma_18 and rho_k(2), k=15..18
#       — note §4
#
# Same operator as kl_perron_solver.py (float power iteration); certified values come
# from certify.py, not from this script.

import numpy as np, math, sys

ALPHA = math.log(3, 2)  # log2(3)

def build(k):
    M = 3**k
    ms = np.arange(2, M, 3, dtype=np.int64)
    n = len(ms)
    i4m = ((4*ms) % M - 2)//3                      # idx[m] = (m-2)//3
    mod9 = ms % 9
    mask2 = mod9 == 2
    mask8 = mod9 == 8
    Mk1 = 3**(k-1)
    ref2 = np.zeros((n,3), dtype=np.int64); ref8 = np.zeros((n,3), dtype=np.int64)
    m2 = ms[mask2]; m8 = ms[mask8]
    r2 = ((4*m2-2)//3) % Mk1
    r8 = ((2*m8-1)//3) % Mk1
    for j in range(3):
        ref2[mask2, j] = ((r2 + j*Mk1) % M - 2)//3
        ref8[mask8, j] = ((r8 + j*Mk1) % M - 2)//3
    return i4m, mask2, mask8, ref2, ref8, n

def eigval(lam, S, iters=8000, tol=1e-14, want_vec=False):
    i4m, mask2, mask8, ref2, ref8, n = S
    c = np.ones(n)
    w2 = lam**(ALPHA-2); w8 = lam**(ALPHA-1); w4 = lam**-2.0
    ev = 1.0
    for t in range(iters):
        f = w4 * c[i4m]
        m2 = np.minimum(np.minimum(c[ref2[:,0]], c[ref2[:,1]]), c[ref2[:,2]])
        m8 = np.minimum(np.minimum(c[ref8[:,0]], c[ref8[:,1]]), c[ref8[:,2]])
        f = f + np.where(mask2, w2*m2, 0.0) + np.where(mask8, w8*m8, 0.0)
        ev_new = f.max()
        f /= ev_new
        if t > 100 and abs(ev_new-ev) < tol*ev:
            c = f; ev = ev_new; break
        c = f; ev = ev_new
    m2 = np.minimum(np.minimum(c[ref2[:,0]], c[ref2[:,1]]), c[ref2[:,2]])
    m8 = np.minimum(np.minimum(c[ref8[:,0]], c[ref8[:,1]]), c[ref8[:,2]])
    fpc = (w4*c[i4m] + np.where(mask2, w2*m2, 0.0) + np.where(mask8, w8*m8, 0.0)) / c
    if want_vec:
        return ev, fpc.min(), fpc.max(), c
    return ev, fpc.min(), fpc.max()

def solve_threshold(k, S, iters=8000):
    l0, l1 = 1.6, 1.8
    g0 = math.log(eigval(l0,S,iters)[0]); g1 = math.log(eigval(l1,S,iters)[0])
    for _ in range(60):
        if abs(g1-g0) < 1e-16: break
        l2 = min(max(l1 - g1*(l1-l0)/(g1-g0), 1.05), 2.5)
        if abs(l2-l1) < 1e-10: l1 = l2; break
        l0,g0 = l1,g1; l1 = l2; g1 = math.log(eigval(l1,S,iters)[0])
    return l1

def s_of(lam):
    return lam**-2.0 + (lam**(ALPHA-2) + lam**(ALPHA-1))/3.0

def fibers(k, c):
    Mk1 = 3**(k-1); M = 3**k
    rs = np.arange(2, Mk1, 3, dtype=np.int64)
    trip = np.stack([((rs + j*Mk1) % M - 2)//3 for j in range(3)], axis=1)
    vals = c[trip]
    return vals.min(axis=1), vals.mean(axis=1), vals.max(axis=1)

KMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 12

print("s(2) =", s_of(2.0), "  s(4) =", s_of(4.0), "  s'(2) = 3(alpha-2)/8 =", 3*(ALPHA-2)/8)

# ---------- [1] thresholds, oscillation identity, Table-2 quantities ----------
print("\n[1] thresholds / oscillation identity (Thm 3.2(i)) / KL Table-2 quantities")
print(f"{'k':>2} {'lam_k':>10} {'gam_k':>10} {'CWpinch':>8} {'delta_k':>9} {'(s-ev)/(w2+w8)':>14} "
      f"{'1-3delta':>9} {'cbar_kk':>8} {'cb_k1k':>8} {'Cmax':>9} {'eps_sup':>8} {'eps_med':>8}")
for k in range(2, KMAX+1):
    S = build(k)
    lam = solve_threshold(k, S)
    ev, cwlo, cwhi, c = eigval(lam, S, want_vec=True)
    c = c / c.min()                                # LP normalization min c = 1
    fmin, favg, fmax = fibers(k, c)
    delta = (favg - fmin).sum() / c.sum()
    w2 = lam**(ALPHA-2); w8 = lam**(ALPHA-1)
    eps = 1 - fmin/fmax
    print(f"{k:>2} {lam:>10.7f} {math.log2(lam):>10.7f} {cwhi-cwlo:>8.1e} {delta:>9.6f} "
          f"{(s_of(lam)-ev)/(w2+w8):>14.6f} {1-3*delta:>9.5f} {c.mean():>8.4f} {fmin.mean():>8.4f} "
          f"{c.max():>9.3f} {eps.max():>8.5f} {np.median(eps):>8.5f}", flush=True)

# ---------- [2] annealed operator ----------
print("\n[2] annealed operator: column sums and rho(A) vs s(lambda)")
for k in (3,4,5):
    S = build(k); i4m, mask2, mask8, ref2, ref8, n = S
    for lam in (1.5, 1.7922310, 2.0, 3.0):
        w2 = lam**(ALPHA-2); w8 = lam**(ALPHA-1); w4 = lam**-2.0
        A = np.zeros((n,n))
        for i in range(n):
            A[i, i4m[i]] += w4
            if mask2[i]:
                for j in range(3): A[i, ref2[i,j]] += w2/3
            if mask8[i]:
                for j in range(3): A[i, ref8[i,j]] += w8/3
        cs = A.sum(axis=0)
        rho = max(abs(np.linalg.eigvals(A)))
        print(f"  k={k} lam={lam:.4f}: colsums equal? {np.allclose(cs, s_of(lam))} "
              f"rho(A)={rho:.10f} s={s_of(lam):.10f}")

# ---------- [3] quenched values at lambda = 2 and lambda > 2 ----------
print("\n[3] rho_k(F_2) (secondary observable) and rho(F_lam), lam in (2,12]")
for k in range(2, min(KMAX+2, 15)):
    S = build(k)
    ev, lo, hi = eigval(2.0, S)
    print(f"  k={k:>2} rho(F_2) = {ev:.7f}", flush=True)
for k in (4,5,6):
    S = build(k)
    vals = "  ".join(f"{lam}:{eigval(lam,S)[0]:.4f}" for lam in (2.2,2.5,3.0,3.9,4.0,4.5,5.0,6.0,8.0,12.0))
    print(f"  k={k}: {vals}")

# ---------- [4] monotonicity in lambda (empirical) ----------
print("\n[4] rho_6(lambda) on [1.05, 2]: strictly decreasing?")
S = build(6); prev = None; ok = True
for lam in np.arange(1.05, 2.001, 0.05):
    ev = eigval(float(lam), S)[0]
    if prev is not None and ev >= prev: ok = False
    prev = ev
print("  strictly decreasing on grid:", ok)

# ---------- [5] fits and pre-registered predictions ----------
print("\n[5] fits (window k=8..14) and predictions for k=15..18")
lam_paper = {2:1.3534010,3:1.5275960,4:1.6122870,5:1.6627590,6:1.6944520,
             7:1.7201900,8:1.7449630,9:1.7615320,10:1.7771270}
gam = {k: math.log2(v) for k,v in lam_paper.items()}
gam.update({11:0.8417566, 12:0.8531358, 13:0.8630053, 14:0.8724520})   # certified
ks = list(range(8,15)); js = range(15,19)

def geom_fit(g, ks):
    x = np.array(ks, float); y = np.array([math.log(g-gam[k]) for k in ks])
    b, a = np.polyfit(x, y, 1)
    C, q = math.exp(a), math.exp(b)
    sse = sum((g - C*q**k - gam[k])**2 for k in ks)
    return C, q, sse, {j: g - C*q**j for j in js}

for g, name in [(1.0, "A  (gamma_inf = 1)"), (0.95, "B  (0.95)"), (0.92, "B  (0.92)"), (0.90, "B  (0.90)")]:
    C, q, sse, pred = geom_fit(g, ks)
    print(f"  {name}: q={q:.5f} C={C:.6f} rms={math.sqrt(sse/len(ks)):.2e}  "
          + "  ".join(f"g{j}={pred[j]:.7f}" for j in js))
print("  free-g SSE profile:", ["g=%.2f:%.1e" % (g, geom_fit(g, ks)[2]) for g in (0.90,0.92,0.96,0.9999)])
inc = {k: gam[k]-gam[k-1] for k in range(10,15)}
qbar = np.mean([inc[k+1]/inc[k] for k in (10,11,12,13)])   # last four ratios, as in the note
print(f"  nonparametric: mean inc-ratio {qbar:.5f} -> implied gamma_inf "
      f"{gam[14] + inc[14]*qbar/(1-qbar):.4f}; ratio for exactly 1: "
      f"{(1-gam[14])/((1-gam[14])+inc[14]):.5f}")
rho2 = {8:0.9103342,9:0.9193913,10:0.9267254,11:0.9334900,12:0.9398400,13:0.9450493,14:0.9499767}
x = np.array(sorted(rho2), float); y = np.array([math.log(1-rho2[k]) for k in sorted(rho2)])
b, a = np.polyfit(x, y, 1)
print(f"  secondary 1-rho_k(2)=Cq^k: q={math.exp(b):.5f} C={math.exp(a):.5f}  preds:",
      {j: round(1-math.exp(a+b*j),5) for j in js})
