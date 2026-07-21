#!/usr/bin/env python3
"""
Arctic (max-plus) matrix-interpretation feasibility search for Zantema's Collatz SRS Z.

TRUE rules of Z (YAH 2021, arXiv:2105.14697, Example 3.1), 5 symbols {1, B, h, s, t}
where B is the blank; the pre-think used a blank-free simplification, we use the real system:
  R1: h 1 1      -> 1 h
  R2: 1 1 h B    -> 1 1 s B
  R3: 1 s        -> s 1
  R4: B s        -> B h
  R5: h 1 B      -> t 1 1 B
  R6: 1 t        -> t 1 1 1
  R7: B t        -> B h

Arctic semiring (YAH 2.3.2 / Koprowski-Waldmann [KW09]):
  A = Z u {-inf} (AZ) or N u {-inf} (AN); x (+) y = max(x,y); x (x) y = x + y.
  Symbol interpretation affine:  [s](x) = M_s (x) x (+) v_s.
  Well-def / weak monotonicity (line 1034): (M_s)_{1,1} >= 0  OR  (v_s)_1 >= 0.
  Extended monotone (direct rule removal): A=AN, v_s = -inf vector, (M_s)_{1,1} >= 0.
  Compatibility (KW Lemma 6.5, YAH lines 1044-1046):
     weak   l->r :  M_l >= M_r  and  v_l >= v_r          (elementwise >=)
     strict l->r :  M_l |> M_r  and  v_l |> v_r          (elementwise |>)
  where  a |> b  <=>  a >_Z b  or  a = b = -inf   ;   a >= b is the ordinary >=.

Rule removal (Theorem 2.15): ALL rules weak, the removed rule strict.  SAT => rule removable
=> no-go FALSE.  UNSAT for all rules/dims/bounds => consistent with the no-go.
"""
import sys, itertools, argparse
from z3 import *

NINF = -10**6  # sentinel for -infinity; finite entries bounded to [-K,K] with K << 10^6

# ---- alphabet & rules (words are left-to-right letter lists) ----
LETTERS = ['1', 'B', 'h', 's', 't']
RULES = [
    ("R1", ['h','1','1'],            ['1','h']),
    ("R2", ['1','1','h','B'],        ['1','1','s','B']),
    ("R3", ['1','s'],                ['s','1']),
    ("R4", ['B','s'],                ['B','h']),
    ("R5", ['h','1','B'],            ['t','1','1','B']),
    ("R6", ['1','t'],                ['t','1','1','1']),
    ("R7", ['B','t'],                ['B','h']),
]

def aplus(a, b):   # (x) = +   ; -inf absorbs
    return If(Or(a == NINF, b == NINF), NINF, a + b)

def amax(a, b):    # (+) = max ; correct for sentinel since NINF < every finite entry
    return If(a >= b, a, b)

def mat_mul(A, B, d):
    return [[ reduce_max([aplus(A[i][k], B[k][j]) for k in range(d)])
              for j in range(d)] for i in range(d)]

def mat_vec(A, v, d):
    return [ reduce_max([aplus(A[i][k], v[k]) for k in range(d)]) for i in range(d)]

def vec_max(u, v, d):
    return [ amax(u[i], v[i]) for i in range(d)]

def reduce_max(xs):
    r = xs[0]
    for x in xs[1:]:
        r = amax(r, x)
    return r

def word_affine(word, Ms, vs, d):
    """Composite affine map of a word:  [a1..ak](x) = M (x) x (+) v.
       [ab](x) = Ma(Mb x (+) vb)(+)va = (Ma Mb) x (+) (Ma vb (+) va)."""
    M = Ms[word[0]]; v = vs[word[0]]
    for a in word[1:]:
        v = vec_max(mat_vec(M, vs[a], d), v, d)     # v <- M (x) v_a (+) v
        M = mat_mul(M, Ms[a], d)                     # M <- M (x) M_a
    return M, v

def ge(a, b):      # weak >=  (sentinel handles -inf)
    return a >= b

def gt_arctic(a, b):  # strict |> :  a>_Z b  or  a=b=-inf
    return Or(a > b, And(a == NINF, b == NINF))

def build(d, K, semiring, strict_rule):
    """Return (solver, Ms, vs).  strict_rule in RULE names or 'ANY'."""
    s = Solver()
    Ms, vs = {}, {}
    for a in LETTERS:
        M = [[Int(f"M_{a}_{i}_{j}") for j in range(d)] for i in range(d)]
        v = [Int(f"v_{a}_{i}") for i in range(d)]
        Ms[a] = M; vs[a] = v
        # entry domains
        for i in range(d):
            for j in range(d):
                e = M[i][j]
                if semiring == 'AN':
                    s.add(Or(e == NINF, And(e >= 0, e <= K)))
                else:  # AZ
                    s.add(Or(e == NINF, And(e >= -K, e <= K)))
        for i in range(d):
            e = v[i]
            if semiring == 'AN':
                # extended monotone: v = -inf vector
                s.add(e == NINF)
            else:
                s.add(Or(e == NINF, And(e >= -K, e <= K)))
        # well-def / monotonicity: (M)_{1,1}>=0 OR (v)_1>=0  (0-based [0][0], [0])
        if semiring == 'AN':
            s.add(M[0][0] >= 0)   # v is -inf so need top-left >=0
        else:
            s.add(Or(M[0][0] >= 0, v[0] >= 0))
    # rule constraints
    strict_flags = []
    for (name, L, R) in RULES:
        ML, vL = word_affine(L, Ms, vs, d)
        MR, vR = word_affine(R, Ms, vs, d)
        weak = And([ge(ML[i][j], MR[i][j]) for i in range(d) for j in range(d)] +
                   [ge(vL[i], vR[i]) for i in range(d)])
        strict = And([gt_arctic(ML[i][j], MR[i][j]) for i in range(d) for j in range(d)] +
                     [gt_arctic(vL[i], vR[i]) for i in range(d)])
        s.add(weak)  # every rule must be at least weakly decreasing
        if strict_rule == 'ANY':
            f = Bool(f"strict_{name}")
            s.add(f == strict)
            strict_flags.append(f)
        elif strict_rule == name:
            s.add(strict)
    if strict_rule == 'ANY':
        s.add(Or(strict_flags))
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
    ap.add_argument('--timeout', type=int, default=60000)  # ms per query
    ap.add_argument('--semirings', default='AN,AZ')
    args = ap.parse_args()
    print(f"# arctic search: dmax={args.dmax} K={args.K} timeout={args.timeout}ms")
    print("semiring,dim,K,strict_rule,result,time_ms")
    for semiring in args.semirings.split(','):
        for d in range(1, args.dmax+1):
            # test each rule individually as the removed (strict) one, plus 'ANY'
            targets = [name for (name,_,_) in RULES]
            for tgt in targets:
                s, Ms, vs = build(d, args.K, semiring, tgt)
                s.set("timeout", args.timeout)
                import time; t0=time.time()
                res = s.check()
                dt = int((time.time()-t0)*1000)
                print(f"{semiring},{d},{args.K},{tgt},{res},{dt}", flush=True)
                if res == sat:
                    m = s.model()
                    sol = extract(m, Ms, vs, d)
                    with open(f"/Users/simon/Desktop/COLLATZ/experiments/arctic/FOUND_{semiring}_d{d}_K{args.K}_{tgt}.txt",'w') as f:
                        f.write(f"FALSIFICATION: arctic interpretation removes {tgt} in {semiring} d={d} K={args.K}\n")
                        for a in LETTERS:
                            M,v = sol[a]
                            f.write(f"M_{a} = {M}\n  v_{a} = {v}\n")
                    print(f"### FOUND: {semiring} d={d} rule {tgt} -> NO-GO FALSE", flush=True)

if __name__ == '__main__':
    main()
