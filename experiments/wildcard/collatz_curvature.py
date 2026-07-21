#!/usr/bin/env python3
"""Discrete Ricci curvature of the undirected Collatz graph.

Graph G on V=[1,N]: edge {n, T(n)}, T(n)=n/2 (even) or 3n+1 (odd).
Neighbors of n:  successor T(n);  predecessors 2n (always) and (n-1)/3 iff n=4 mod 6.
=> deg(n)=2 on 'chain' vertices, deg(n)=3 at BRANCH vertices, which are EXACTLY n=4 mod 6
   (the +1-then-/3 odd predecessor = the x3 branch). Girth: only the 1-2-4 triangle.

Forman-Ricci (Sreejith/Samal et al., unweighted): F(u,v)=4-deg(u)-deg(v)  [+3*#triangles].
Ollivier-Ricci (Ollivier 2009; idleness 0): kappa(u,v)=1-W1(mu_u,mu_v), mu uniform on nbrs,
   ground cost = graph distance; solved exactly by LP (scipy).
Real theorem tie-in: Ollivier kappa>=k>0 => spectral gap>=k & exp. concentration (Ollivier'09);
   Forman F controls the graph-Laplacian via a discrete Bochner-Weitzenbock (Forman 2003).
"""
import numpy as np, math
from collections import defaultdict
from scipy.optimize import linprog
import networkx as nx

def T(n): return n//2 if n%2==0 else 3*n+1

# ---------- Forman over large N, stratified by residue mod 6 ----------
def forman(N):
    deg = np.zeros(N+2, dtype=np.int32)
    edges = []
    for n in range(1,N+1):
        t = T(n)
        if 1 <= t <= N:
            edges.append((n,t)); deg[n]+=1; deg[t]+=1
    edges = list({tuple(sorted(e)) for e in edges})  # simple undirected
    deg = np.zeros(N+2, dtype=np.int32)
    for u,v in edges: deg[u]+=1; deg[v]+=1
    # branch vertices
    branch = [n for n in range(1,N+1) if deg[n]>=3]
    frac4mod6 = np.mean([ (n%6==4) for n in branch]) if branch else float('nan')
    F = np.array([4-deg[u]-deg[v] for (u,v) in edges])
    return deg, edges, F, branch, frac4mod6

# ---------- Ollivier exact on a core window ----------
def ollivier(N, core_hi):
    G = nx.Graph()
    for n in range(1,N+1):
        t=T(n)
        if 1<=t<=N: G.add_edge(n,t)
    kap = {}
    for u in range(1, core_hi+1):
        if u not in G: continue
        for v in G.neighbors(u):
            if v<=u: continue
            Nu=list(G.neighbors(u)); Nv=list(G.neighbors(v))
            # ground distances between Nu and Nv (small, use BFS cutoff)
            C=np.zeros((len(Nu),len(Nv)))
            for i,a in enumerate(Nu):
                d=nx.single_source_shortest_path_length(G,a,cutoff=6)
                for j,b in enumerate(Nv):
                    C[i,j]=d.get(b, 7)
            # W1 transport LP: min sum C*x, row sums=1/|Nu|, col sums=1/|Nv|
            nu,nv=len(Nu),len(Nv)
            Aeq=[]; beq=[]
            for i in range(nu):
                r=np.zeros(nu*nv); r[i*nv:(i+1)*nv]=1; Aeq.append(r); beq.append(1/nu)
            for j in range(nv):
                r=np.zeros(nu*nv); r[j::nv]=1; Aeq.append(r); beq.append(1/nv)
            res=linprog(C.ravel(), A_eq=np.array(Aeq), b_eq=np.array(beq),
                        bounds=[(0,None)]*(nu*nv), method="highs")
            W1=res.fun
            kap[(u,v)]=1.0-W1
    return kap, G

if __name__=="__main__":
    N=200000
    deg,edges,F,branch,frac=forman(N)
    print(f"[Forman] N={N}  #edges={len(edges)}  #branch(deg>=3)={len(branch)} "
          f"frac branch with n=4 mod6 = {frac:.6f}")
    vals,counts=np.unique(F,return_counts=True)
    print("  Forman value : count :", dict(zip(vals.tolist(),counts.tolist())))
    print(f"  mean Forman = {F.mean():.5f}")
    # density of branch vertices among all vertices
    print(f"  branch-vertex density = {len(branch)/N:.5f}  (1/6={1/6:.5f})")

    kap,G=ollivier(N=6000, core_hi=1500)
    ks=np.array(list(kap.values()))
    print(f"[Ollivier] core edges={len(kap)}  mean kappa={ks.mean():.5f}  "
          f"min={ks.min():.5f} max={ks.max():.5f}")
    # stratify by whether the edge touches a branch vertex
    by=defaultdict(list)
    for (u,v),k in kap.items():
        du,dv=G.degree(u),G.degree(v)
        by[(min(du,dv),max(du,dv))].append(k)
    for key in sorted(by):
        a=np.array(by[key]); print(f"  deg-pair {key}: n={len(a)} meanK={a.mean():.4f}")
    # correlation: negative curvature concentrated at branch (n=4 mod6) vertices
    touch4=[k for (u,v),k in kap.items() if u%6==4 or v%6==4]
    notouch=[k for (u,v),k in kap.items() if u%6!=4 and v%6!=4]
    print(f"  edges touching n=4mod6: n={len(touch4)} meanK={np.mean(touch4):.4f}")
    print(f"  edges NOT touching    : n={len(notouch)} meanK={np.mean(notouch):.4f}")
