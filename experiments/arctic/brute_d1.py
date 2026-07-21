#!/usr/bin/env python3
"""
Independent (NO z3) brute-force feasibility check at dimension 1 for EXACT Z.
Cross-validates the z3 UNSAT results. Pure max-plus arithmetic in Python.
d=1: each symbol is [s](x)=max(a_s+x, b_s), a_s,b_s in {-inf} U [-K,K].
"""
import itertools, sys
NINF = float('-inf')
LETTERS = ['1','B','h','s','t']
RULES = [("R1",['h','1','1'],['1','h']),("R2",['1','1','h'],['1','1','s']),
         ("R3",['1','s'],['s','1']),("R4",['s'],['h']),("R5",['h','1'],['t','1','1']),
         ("R6",['1','t'],['t','1','1','1']),("R7",['t'],['h'])]

def word_av(word, A, Bv):
    """composite [w](x)=max(M+x, V): return (M, V). a1 outermost."""
    M = A[word[0]]; V = Bv[word[0]]
    for c in word[1:]:
        a, b = A[c], Bv[c]
        # compose max(M + max(a+x,b), V) = max(M+a+x, M+b, V)
        newM = (NINF if (M==NINF or a==NINF) else M+a)
        Mb   = (NINF if (M==NINF or b==NINF) else M+b)
        V = max(Mb, V)
        M = newM
    return M, V

def ge(x,y): return x>=y
def gt(x,y): return (x>y) or (x==NINF and y==NINF)

def search(K, semiring):
    vals = [NINF] + list(range(-K, K+1)) if semiring=='AZ' else [NINF] + list(range(0, K+1))
    # per-symbol (a,b) candidates satisfying well-def
    persym = []
    for a in vals:
        for b in vals:
            if semiring=='AN':
                if b!=NINF: continue          # extended monotone: v=-inf
                if not (a!=NINF and a>=0): continue
            else:
                ok = (a!=NINF and a>=0) or (b!=NINF and b>=0)
                if not ok: continue
            persym.append((a,b))
    found = {name:None for (name,_,_) in RULES}
    # iterate over choices for each of 5 letters
    for combo in itertools.product(persym, repeat=len(LETTERS)):
        A = {LETTERS[i]:combo[i][0] for i in range(len(LETTERS))}
        Bv = {LETTERS[i]:combo[i][1] for i in range(len(LETTERS))}
        # check all rules weak
        wav = {}
        weak_ok = True
        for (name,L,R) in RULES:
            ML,VL = word_av(L,A,Bv); MR,VR = word_av(R,A,Bv)
            wav[name] = (ML,VL,MR,VR)
            if not (ge(ML,MR) and ge(VL,VR)): weak_ok=False; break
        if not weak_ok: continue
        for (name,_,_) in RULES:
            if found[name] is not None: continue
            ML,VL,MR,VR = wav[name]
            if gt(ML,MR) and gt(VL,VR):
                found[name] = (dict(A),dict(Bv))
    return found

if __name__=='__main__':
    for semiring in ['AN','AZ']:
        for K in [1,2,3]:
            found = search(K, semiring)
            line = ",".join(f"{n}={'SAT' if found[n] else 'unsat'}" for (n,_,_) in RULES)
            print(f"{semiring} d=1 K={K}: {line}")
