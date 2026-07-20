import numpy as np, math, sys

ALPHA = math.log(3,2)

def build(k):
    M = 3**k
    ms = np.arange(2, M, 3, dtype=np.int64)      # classes m ≡ 2 mod 3, mod 3^k
    idx = {m:i for i,m in enumerate(ms)}
    n = len(ms)
    i4m = np.array([idx[(4*m) % M] for m in ms], dtype=np.int64)
    mod9 = ms % 9
    mask2 = mod9 == 2
    mask8 = mod9 == 8
    Mk1 = 3**(k-1)
    ref2 = np.zeros((n,3), dtype=np.int64); ref8 = np.zeros((n,3), dtype=np.int64)
    for i,m in enumerate(ms):
        if mod9[i]==2:
            r = ((4*m-2)//3) % Mk1
            ref2[i] = [idx[(r + j*Mk1) % M] for j in range(3)]
        elif mod9[i]==8:
            r = ((2*m-1)//3) % Mk1
            ref8[i] = [idx[(r + j*Mk1) % M] for j in range(3)]
    return i4m, mask2, mask8, ref2, ref8, n

def eigval(lam, S, iters=4000, tol=1e-13):
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
    # Collatz-Wielandt bounds
    fpc = (w4*c[i4m] + np.where(mask2, w2*np.minimum(np.minimum(c[ref2[:,0]],c[ref2[:,1]]),c[ref2[:,2]]),0.0)
                     + np.where(mask8, w8*np.minimum(np.minimum(c[ref8[:,0]],c[ref8[:,1]]),c[ref8[:,2]]),0.0)) / c
    return ev, fpc.min(), fpc.max()

def solve(k, iters=4000):
    S = build(k)
    lo, hi = 1.2, 2.0
    # secant on g(lam)=log ev(lam)
    l0, l1 = 1.6, 1.8
    g0 = math.log(eigval(l0,S,iters)[0]); g1 = math.log(eigval(l1,S,iters)[0])
    for _ in range(60):
        if abs(g1-g0) < 1e-16: break
        l2 = l1 - g1*(l1-l0)/(g1-g0)
        l2 = min(max(l2, 1.05), 2.5)
        if abs(l2-l1) < 1e-9: l1 = l2; break
        l0,g0 = l1,g1; l1 = l2; g1 = math.log(eigval(l1,S,iters)[0])
    ev, cwlo, cwhi = eigval(l1,S,iters)
    return l1, ev, cwlo, cwhi

kl_table = {2:1.3534010,3:1.5275960,4:1.6122870,5:1.6627590,6:1.6944520,7:1.7201900,8:1.7449630,9:1.7615320,10:1.7771270,11:1.7922310}
for k in range(2, int(sys.argv[1])+1):
    lam, ev, cwlo, cwhi = solve(k)
    ref = kl_table.get(k)
    print(f"k={k:2d} states={len(build(k)[0]):>8d} lambda={lam:.7f} gamma={math.log(lam,2):.7f}"
          + (f"  KL: {ref:.7f} diff={lam-ref:+.7f}" if ref else "  ** NEW **"), flush=True)
