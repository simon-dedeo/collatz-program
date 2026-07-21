#!/usr/bin/env python3
"""
Arctic (max-plus) matrix-interpretation feasibility search for Zantema's Collatz SRS Z.

EXACT rules of Z (Yolcu-Aaronson-Heule 2021, arXiv:2105.14697v3, Example 3.1, p.13).
Alphabet Sigma = {1, B, h, s, t}  (B = blank).  The blank B is in the alphabet but
DOES NOT appear in any rule; states are  h 1^k B.  The 7 rules are BLANK-FREE:

  R1: h 1 1  -> 1 h
  R2: 1 1 h  -> 1 1 s
  R3: 1 s    -> s 1
  R4: s      -> h
  R5: h 1    -> t 1 1
  R6: 1 t    -> t 1 1 1
  R7: t      -> h

Arctic semiring (YAH 2.3.2 / Koprowski-Waldmann [KW09]):
  A = Z u {-inf} (AZ) or N u {-inf} (AN); x (+) y = max(x,y); x (x) y = x + y.
  Symbol interpretation affine:  [s](x) = M_s (x) x (+) v_s.
  well-def / WEAK monotone (AZ, top-termination only): (M_s)_{1,1}>=0 OR (v_s)_1>=0.
  EXTENDED monotone (AN, direct removal):  v_s = -inf vector, (M_s)_{1,1}>=0.
  Compatibility (KW Lemma 6.5):
     weak    l->r :  M_l >= M_r  and  v_l >= v_r            (elementwise >=)
     strict  l->r :  M_l |> M_r  and  v_l |> v_r            (elementwise |>)
     where  a |> b  <=>  a >_Z b  or  a = b = -inf.

Query: ALL 7 rules weak, ONE chosen rule additionally strict.
  SAT   => that rule is orientable (a candidate falsification / relative-orientation).
  UNSAT (all rules, all d, all K) => consistent with the no-go.
"""
import argparse, time
from z3 import *

NINF = -10**6  # sentinel for -infinity; finite entries in [-K,K], K << 10^6

LETTERS = ['1', 'B', 'h', 's', 't']
RULES = [
    ("R1", ['h','1','1'], ['1','h']),
    ("R2", ['1','1','h'], ['1','1','s']),
    ("R3", ['1','s'],     ['s','1']),
    ("R4", ['s'],         ['h']),
    ("R5", ['h','1'],     ['t','1','1']),
    ("R6", ['1','t'],     ['t','1','1','1']),
    ("R7", ['t'],         ['h']),
]

def aplus(a, b):   # arctic (x) = + ; -inf absorbs
    return If(Or(a == NINF, b == NINF), NINF, a + b)
def amax(a, b):    # arctic (+) = max
    return If(a >= b, a, b)
def reduce_max(xs):
    r = xs[0]
    for x in xs[1:]:
        r = amax(r, x)
    return r
def mat_mul(A, B, d):
    return [[reduce_max([aplus(A[i][k], B[k][j]) for k in range(d)]) for j in range(d)] for i in range(d)]
def mat_vec(A, v, d):
    return [reduce_max([aplus(A[i][k], v[k]) for k in range(d)]) for i in range(d)]
def vec_max(u, v, d):
    return [amax(u[i], v[i]) for i in range(d)]

def word_affine(word, Ms, vs, d):
    """[a1..ak](x) = M (x) x (+) v, with a1 applied outermost (YAH convention)."""
    M = [row[:] for row in Ms[word[0]]]; v = vs[word[0]][:]
    for a in word[1:]:
        v = vec_max(mat_vec(M, vs[a], d), v, d)
        M = mat_mul(M, Ms[a], d)
    return M, v

def gt_arctic(a, b):  # strict |>
    return Or(a > b, And(a == NINF, b == NINF))

def build(d, K, semiring, strict_rule):
    s = Solver()
    Ms, vs = {}, {}
    for a in LETTERS:
        M = [[Int(f"M_{a}_{i}_{j}") for j in range(d)] for i in range(d)]
        v = [Int(f"v_{a}_{i}") for i in range(d)]
        Ms[a] = M; vs[a] = v
        for i in range(d):
            for j in range(d):
                e = M[i][j]
                if semiring == 'AN':
                    s.add(Or(e == NINF, And(e >= 0, e <= K)))
                else:
                    s.add(Or(e == NINF, And(e >= -K, e <= K)))
        for i in range(d):
            e = v[i]
            if semiring == 'AN':
                s.add(e == NINF)                 # extended monotone: v = -inf
            else:
                s.add(Or(e == NINF, And(e >= -K, e <= K)))
        if semiring == 'AN':
            s.add(M[0][0] >= 0)
        else:
            s.add(Or(M[0][0] >= 0, v[0] >= 0))
    for (name, L, R) in RULES:
        ML, vL = word_affine(L, Ms, vs, d)
        MR, vR = word_affine(R, Ms, vs, d)
        weak = And([ML[i][j] >= MR[i][j] for i in range(d) for j in range(d)] +
                   [vL[i] >= vR[i] for i in range(d)])
        s.add(weak)
        if strict_rule == name:
            strict = And([gt_arctic(ML[i][j], MR[i][j]) for i in range(d) for j in range(d)] +
                         [gt_arctic(vL[i], vR[i]) for i in range(d)])
            s.add(strict)
    return s, Ms, vs

def extract(model, Ms, vs, d):
    out = {}
    for a in LETTERS:
        M = [[model.evaluate(Ms[a][i][j]).as_long() for j in range(d)] for i in range(d)]
        v = [model.evaluate(vs[a][i]).as_long() for i in range(d)]
        out[a] = (M, v)
    return out

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--dmax', type=int, default=6)
    ap.add_argument('--K', type=int, default=3)
    ap.add_argument('--timeout', type=int, default=60000)
    ap.add_argument('--semirings', default='AN,AZ')
    args = ap.parse_args()
    print(f"# arctic search on EXACT Z: dmax={args.dmax} K={args.K} timeout={args.timeout}ms")
    print("semiring,dim,K,strict_rule,result,time_ms")
    for semiring in args.semirings.split(','):
        for d in range(1, args.dmax+1):
            for (name,_,_) in RULES:
                s, Ms, vs = build(d, args.K, semiring, name)
                s.set("timeout", args.timeout)
                t0 = time.time()
                res = s.check()
                dt = int((time.time()-t0)*1000)
                print(f"{semiring},{d},{args.K},{name},{res},{dt}", flush=True)
                if res == sat:
                    sol = extract(s.model(), Ms, vs, d)
                    with open(f"/Users/simon/Desktop/COLLATZ/experiments/arctic/FOUNDZ_{semiring}_d{d}_K{args.K}_{name}.txt",'w') as f:
                        f.write(f"ORIENTS {name} strict, rest weak: {semiring} d={d} K={args.K}\n")
                        for a in LETTERS:
                            M,v = sol[a]
                            f.write(f"M_{a} = {M}\n  v_{a} = {v}\n")

if __name__ == '__main__':
    main()
