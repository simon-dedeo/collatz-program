import numpy as np, math
from fractions import Fraction as Fr

print("=== Bridge 1b: the -1 charge as a -1 PERIPHERAL eigenvalue of the argmin-selection channel ===")
# Prufer offsets around -1: q = u/3^nu in Z(3^oo)/Z, with x2 relabeling q->2q mod 1.
# depth<=D offsets; build permutation matrix of q->2q; -1 charge = antisymmetric (-1) eigenmode.
def offsets(D):
    S=set()
    for nu in range(1,D+1):
        for u in range(0,3**nu):
            S.add(Fr(u,3**nu))
    return sorted(S)
for D in [1,2,3]:
    offs=offsets(D); idx={q:i for i,q in enumerate(offs)}; n=len(offs)
    P=np.zeros((n,n))
    for q in offs:
        P[idx[(2*q)%1], idx[q]]=1.0   # relabeling permutation
    ev=np.linalg.eigvals(P)
    n_m1=np.sum(np.abs(ev+1)<1e-9); n_p1=np.sum(np.abs(ev-1)<1e-9)
    # order of the element / cycle lengths present
    print(f"  depth<= {D}: #offsets={n}  #eigval(+1)={n_p1} #eigval(-1)={n_m1}  "
          f"(-1 present => Z/2 sign-rep 'charge' is a peripheral mode)")
print("  => the swap {1/3<->2/3} (ord(2 mod 3)=2) gives eigenvalues {+1 (sym=a+b), -1 (antisym=b-a=CHARGE)}")

print("\n=== Bridge 3: geometry-of-numbers reality check (covolume / equidistribution of W mod Lambda) ===")
def words_W_mod(K,L,m):
    # count words 0<=b0<...<b_{L-1}<K with W=sum 3^{L-1-i} 2^{b_i} == r mod m, all r
    from itertools import combinations
    cnt=[0]*m
    p3=[pow(3,e,m) for e in range(L)]
    p2=[pow(2,b,m) for b in range(K)]
    for comb in combinations(range(K),L):
        w=0
        for i,b in enumerate(comb):
            w=(w+p3[L-1-i]*p2[b])%m
        cnt[w]+=1
    return cnt
import math as _m
for (K,L) in [(11,7),(21,13)]:
    Lam=2**K-3**L
    C=_m.comb(K,L)
    if Lam>0 and Lam< 6000:
        cnt=words_W_mod(K,L,Lam)
        N0=cnt[0]
        arr=np.array(cnt)
        print(f"  (K,L)=({K},{L}) Lambda=2^{K}-3^{L}={Lam}  C=binom={C}  C/Lambda={C/Lam:.3f}  "
              f"N_Lambda(cycles cand.)={N0}  mean/res={arr.mean():.3f} std={arr.std():.3f}")
# small-L obstruction: (7,1): Lambda=125=5^3, W=2^{b0} power of 2 -> N_5=0
K,L=7,1; Lam=2**K-3**L
c5=words_W_mod(K,L,5)
print(f"  (7,1): Lambda={Lam}=5^3 ; W is a power of two -> N_5={c5[0]} (residue class 0 empty => obstruction; "
      f"powers of 2 mod 5 hit {sorted(set(pow(2,b,5) for b in range(K)))})")
print("  covolume view: ker(W mod Lambda) has index=|image| in (Z/Lambda); when W surjective, covol=Lambda,")
print("  Gaussian/Minkowski heuristic #points ~ vol/covol = C/Lambda. BUT W is EXPONENTIAL in b_i, so the")
print("  simplex-of-b_i is NOT a linear congruence => Ehrhart/Barvinok do NOT apply (honest negative).")
