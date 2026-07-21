import numpy as np, math
np.set_printoptions(suppress=True, precision=6)
ALPHA = math.log(3,2)

def build_annealed(k, lam):
    """Annealed (linear) KL transfer operator L on [3^k]={m mod 3^k: m=2 mod3}.
    Same branch maps as kl_perron_solver.build, but min_j -> (1/3) sum_j (pushforward).
    Returns L (n x n) and the pure odometer part A0 and chord part A1 (L=A0+A1)."""
    M = 3**k
    ms = np.arange(2, M, 3, dtype=np.int64)
    idx = {int(m):i for i,m in enumerate(ms)}
    n = len(ms)
    Mk1 = 3**(k-1)
    w4 = lam**-2.0; w2 = lam**(ALPHA-2); w8 = lam**(ALPHA-1)
    A0 = np.zeros((n,n)); A1 = np.zeros((n,n))
    for i,m in enumerate(ms):
        m=int(m)
        A0[i, idx[(4*m)%M]] += w4                       # odometer term (all classes)
        if m%9==2:
            r=((4*m-2)//3)%Mk1
            for j in range(3):
                A1[i, idx[(r+j*Mk1)%M]] += w2/3.0
        elif m%9==8:
            r=((2*m-1)//3)%Mk1
            for j in range(3):
                A1[i, idx[(r+j*Mk1)%M]] += w8/3.0
    return A0+A1, A0, A1, ms

def perron(L):
    w,V = np.linalg.eig(L)
    i = np.argmax(w.real); rho=w[i].real
    c = np.abs(V[:,i].real); c/=c.max()
    wl,Vl = np.linalg.eig(L.T)
    il = np.argmax(wl.real); l = np.abs(Vl[:,il].real)
    return rho, c, l

def doob(L, rho, c):
    D=np.diag(c); Di=np.diag(1.0/c)
    return (Di@L@D)/rho

print("=== BRIDGE 1: transfer operator as a QUANTUM CHANNEL (peripheral spectrum) ===")
print("lambda=2 (Perron eigenvalue should be s(2)=1). Doob-normalized P is column/row-stochastic.")
rows=[]
for k in [3,4,5,6]:
    L,A0,A1,ms = build_annealed(k, 2.0)
    rho,c,l = perron(L)
    P = doob(L, rho, c)
    rs = P.sum(axis=1)
    ev = np.linalg.eigvals(P)
    mag = np.abs(ev)
    peri = ev[mag>1-1e-7]
    # period = number of peripheral eigenvalues (they form a cyclic group)
    phases = np.sort(np.angle(peri))
    per = len(peri)
    # subdominant: largest |mu|<1
    sub = np.sort(mag[mag<1-1e-7])[::-1]
    gap = 1-sub[0] if len(sub) else float('nan')
    print(f"k={k} n={L.shape[0]:4d} rho(Perron)={rho:.6f} rowsum(P) in [{rs.min():.4f},{rs.max():.4f}] "
          f"#peripheral(|mu|=1)={per} spectral_gap(1-|mu2|)={gap:.5f}")
    rows.append((k,L.shape[0],rho,per,gap))
    if k==4:
        print("   peripheral eigenvalue phases/2pi:", np.round(np.sort(np.angle(peri))/(2*math.pi),4))

# odometer-only peripheral group (before chords): pure cyclic permutation m->4m, period 3^{k-1}
print("\n  odometer-only (A0 doob-normalized) peripheral group = full cyclic 3^{k-1}-th roots:")
for k in [3,4]:
    L,A0,A1,ms=build_annealed(k,2.0)
    # A0 alone is w4*permutation; doob w.r.t its Perron (const vector, rho=w4)
    P0 = A0/(2.0**-2.0)  # = pure permutation matrix
    ev0=np.linalg.eigvals(P0)
    print(f"   k={k}: #|mu|=1 for pure odometer = {np.sum(np.abs(ev0)>1-1e-7)}  (= n = 3^(k-1)={3**(k-1)})")

print("\n=== BRIDGE 2: Dolan-Grady free-fermion INTEGRABILITY test of the transfer matrix ===")
print("Split L = A0 (odometer/kinetic) + A1 (chord/field). Onsager-integrable iff")
print("[A0,[A0,[A0,A1]]] = beta^2 [A0,A1]  (and symmetric).  Test proportionality.")
def comm(X,Y): return X@Y-Y@X
for k in [3,4,5]:
    L,A0,A1,ms=build_annealed(k,2.0)
    C01=comm(A0,A1)
    T=comm(A0,comm(A0,comm(A0,A1)))         # [A0,[A0,[A0,A1]]]
    # best-fit beta^2 minimizing ||T - b*C01||: b = <T,C01>/<C01,C01>
    num=np.vdot(C01,T).real; den=np.vdot(C01,C01).real
    b=num/den if den>0 else float('nan')
    resid=np.linalg.norm(T-b*C01)/ (np.linalg.norm(T)+1e-30)
    # symmetric one
    C10=comm(A1,A0)
    T2=comm(A1,comm(A1,comm(A1,A0)))
    num2=np.vdot(C10,T2).real; den2=np.vdot(C10,C10).real
    b2=num2/den2 if den2>0 else float('nan')
    resid2=np.linalg.norm(T2-b2*C10)/(np.linalg.norm(T2)+1e-30)
    print(f"k={k}: DG relation 1 best beta^2={b:.4f} rel.residual={resid:.4f} | "
          f"relation 2 beta^2={b2:.4f} residual={resid2:.4f}  (0=integrable, ~1=NOT)")
