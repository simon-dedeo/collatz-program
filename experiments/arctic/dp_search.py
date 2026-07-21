#!/usr/bin/env python3
"""
Faithful DP / top-termination arctic search (tests Theorem A directly).

YAH Theorem 3.10 setting: alphabet {1, B, B#, h, s, t} where B# is the marked
(root) blank of the dependency-pair problem.  I = { B# s -> B# h , B# t -> B# h }.
We prove SN(I_top / Z): weakly-monotone AZ algebra, ALL of Z weak, ALL of I weak,
and ONE chosen I-rule strict (it only ever fires at the root, so no left context).

SAT  => that I-rule is removable by an arctic-integer interpretation => Theorem A FALSE.
UNSAT (all dims/bounds) => consistent with the arctic DP no-go.
"""
import argparse, time
from z3 import *
NINF = -10**6
LETTERS = ['1','B','M','h','s','t']   # M := B# (marked blank)
# base system Z (unmarked blank B), all WEAK
Z = [
    ("R1", ['h','1','1'],     ['1','h']),
    ("R2", ['1','1','h','B'], ['1','1','s','B']),
    ("R3", ['1','s'],         ['s','1']),
    ("R4", ['B','s'],         ['B','h']),
    ("R5", ['h','1','B'],     ['t','1','1','B']),
    ("R6", ['1','t'],         ['t','1','1','1']),
    ("R7", ['B','t'],         ['B','h']),
]
# dependency-pair rules I (marked blank M = B#)
I = [
    ("I_s", ['M','s'], ['M','h']),
    ("I_t", ['M','t'], ['M','h']),
]
def aplus(a,b): return If(Or(a==NINF,b==NINF), NINF, a+b)
def amax(a,b):  return If(a>=b, a, b)
def rmax(xs):
    r=xs[0]
    for x in xs[1:]: r=amax(r,x)
    return r
def mmul(A,B,d): return [[rmax([aplus(A[i][k],B[k][j]) for k in range(d)]) for j in range(d)] for i in range(d)]
def mvec(A,v,d): return [rmax([aplus(A[i][k],v[k]) for k in range(d)]) for i in range(d)]
def vmax(u,v,d): return [amax(u[i],v[i]) for i in range(d)]
def waffine(w,Ms,vs,d):
    M=Ms[w[0]]; v=vs[w[0]]
    for a in w[1:]:
        v=vmax(mvec(M,vs[a],d),v,d); M=mmul(M,Ms[a],d)
    return M,v
def gt(a,b): return Or(a>b, And(a==NINF,b==NINF))   # strict |>
def build(d,K,strict):
    s=Solver(); Ms={}; vs={}
    for a in LETTERS:
        M=[[Int(f"M_{a}_{i}_{j}") for j in range(d)] for i in range(d)]
        v=[Int(f"v_{a}_{i}") for i in range(d)]
        Ms[a]=M; vs[a]=v
        for i in range(d):
            for j in range(d): s.add(Or(M[i][j]==NINF, And(M[i][j]>=-K, M[i][j]<=K)))
            s.add(Or(v[i]==NINF, And(v[i]>=-K, v[i]<=K)))
        s.add(Or(M[0][0]>=0, v[0]>=0))   # weak-monotone well-def (line 1034)
    for (name,L,R) in Z+I:              # every Z and I rule at least weak
        ML,vL=waffine(L,Ms,vs,d); MR,vR=waffine(R,Ms,vs,d)
        s.add(And([ML[i][j]>=MR[i][j] for i in range(d) for j in range(d)]+[vL[i]>=vR[i] for i in range(d)]))
    name,L,R=[r for r in I if r[0]==strict][0]  # chosen I rule strict
    ML,vL=waffine(L,Ms,vs,d); MR,vR=waffine(R,Ms,vs,d)
    s.add(And([gt(ML[i][j],MR[i][j]) for i in range(d) for j in range(d)]+[gt(vL[i],vR[i]) for i in range(d)]))
    return s,Ms,vs
def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--dmax',type=int,default=6)
    ap.add_argument('--K',type=int,default=3); ap.add_argument('--timeout',type=int,default=120000)
    a=ap.parse_args()
    print(f"# DP arctic search (Theorem A): dmax={a.dmax} K={a.K}")
    print("setting,dim,K,strict_I_rule,result,time_ms")
    for d in range(1,a.dmax+1):
        for tgt in ['I_s','I_t']:
            s,Ms,vs=build(d,a.K,tgt); s.set("timeout",a.timeout)
            t0=time.time(); res=s.check(); dt=int((time.time()-t0)*1000)
            print(f"DP,{d},{a.K},{tgt},{res},{dt}",flush=True)
            if res==sat:
                m=s.model()
                with open(f"/Users/simon/Desktop/COLLATZ/experiments/arctic/FOUND_DP_d{d}_K{a.K}_{tgt}.txt",'w') as f:
                    for x in LETTERS:
                        M=[[m.evaluate(Ms[x][i][j]).as_long() for j in range(d)] for i in range(d)]
                        v=[m.evaluate(vs[x][i]).as_long() for i in range(d)]
                        f.write(f"M_{x}={M}\n v_{x}={v}\n")
                print(f"### FOUND DP d={d} {tgt} -> THEOREM A FALSE",flush=True)
if __name__=='__main__': main()
