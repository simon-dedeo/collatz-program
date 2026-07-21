#!/usr/bin/env python3
"""Independent (no-z3) verification of arctic models AND rewrite-derivation rule counts."""
import glob, re, os
NINF = float('-inf')

# ---------- pure-python max-plus ----------
def mmul(A,B):
    n,m,p=len(A),len(B),len(B[0])
    return [[max((A[i][k]+B[k][j]) for k in range(m)) for j in range(p)] for i in range(n)]
def mvec(A,v):
    return [max(A[i][k]+v[k] for k in range(len(v))) for i in range(len(A))]
def vmax(u,w): return [max(u[i],w[i]) for i in range(len(u))]
def waffine(word,Ms,vs):
    M=[row[:] for row in Ms[word[0]]]; v=vs[word[0]][:]
    for a in word[1:]:
        v=vmax(mvec(M,vs[a]),v); M=mmul(M,Ms[a])
    return M,v
def ge(a,b): return a>=b  # -inf handled by float
def gt(a,b): return (a>b) or (a==NINF and b==NINF)  # arctic |>

RULES=[("R1",['h','1','1'],['1','h']),("R2",['1','1','h','B'],['1','1','s','B']),
       ("R3",['1','s'],['s','1']),("R4",['B','s'],['B','h']),
       ("R5",['h','1','B'],['t','1','1','B']),("R6",['1','t'],['t','1','1','1']),
       ("R7",['B','t'],['B','h'])]

def parse_found(path):
    Ms,vs={},{}
    for line in open(path):
        m=re.match(r'\s*M_(\w+)\s*=\s*(\[\[.*\]\])',line)
        if m:
            a=m.group(1); mat=eval(m.group(2))
            Ms[a]=[[(NINF if x<=-999999 else x) for x in row] for row in mat]
        m=re.match(r'\s*v_(\w+)\s*=\s*(\[.*\])',line)
        if m:
            a=m.group(1); vv=eval(m.group(2))
            vs[a]=[(NINF if x<=-999999 else x) for x in vv]
    return Ms,vs

def check_model(path):
    Ms,vs=parse_found(path)
    target=re.search(r'_(R\d)\.txt$',path)
    target=target.group(1) if target else '?'
    d=len(Ms['1'])
    report=[]
    ok_strict=None
    for (name,L,R) in RULES:
        ML,vL=waffine(L,Ms,vs); MR,vR=waffine(R,Ms,vs)
        weak=all(ge(ML[i][j],MR[i][j]) for i in range(d) for j in range(d)) and all(ge(vL[i],vR[i]) for i in range(d))
        strict=all(gt(ML[i][j],MR[i][j]) for i in range(d) for j in range(d)) and all(gt(vL[i],vR[i]) for i in range(d))
        report.append((name,weak,strict))
        if name==target: ok_strict=strict
    # well-def: (M)_00>=0 OR v_0>=0
    welldef=all((Ms[a][0][0]>=0) or (vs[a][0]>=0) for a in Ms)
    allweak=all(w for(_,w,_) in report)
    return target,d,allweak,ok_strict,welldef,report

# ---------- rewrite simulator: confirm rule usage counts ----------
def apply_once(s):
    """One leftmost-ish rewrite; returns (new_string, rule_name) or None. Deterministic-ish
       following the intended Turing simulation (search each rule left to right)."""
    # order matters for a faithful simulation of the machine; we search all, prefer the
    # unique applicable machine step. Represent string as list of chars over {1,B,h,s,t}.
    for (name,L,R) in RULES:
        Ls,Rs=''.join(L),''.join(R)
        i=s.find(Ls)
        if i>=0:
            return s[:i]+Rs+s[i+len(Ls):], name
    return None

def simulate(n, maxsteps=10**7):
    """Run Z from B h 1^n B; count rule uses; return (final,counts,steps)."""
    from collections import Counter
    s='B'+'h'+'1'*n+'B'
    cnt=Counter(); steps=0
    while steps<maxsteps:
        r=apply_once(s)
        if r is None: break
        s,name=r; cnt[name]+=1; steps+=1
    return s,cnt,steps

if __name__=='__main__':
    print("=== MODEL VERIFICATION (independent of z3) ===")
    for p in sorted(glob.glob('/Users/simon/Desktop/COLLATZ/experiments/arctic/FOUND_AZ_d1_*.txt')):
        tgt,d,allweak,strict,welldef,rep=check_model(p)
        print(f"{os.path.basename(p)}: dim={d} all_weak={allweak} target_strict={strict} welldef={welldef}  VALID={allweak and strict and welldef}")
    print("\n=== DERIVATION RULE COUNTS (B h 1^n B ->* ...) ===")
    for n in [1,2,3,4,5,7,8,9,16,17]:
        fin,cnt,steps=simulate(n)
        print(f"n={n:3d} steps={steps:5d} final={fin[:40]} counts={dict(sorted(cnt.items()))}")
