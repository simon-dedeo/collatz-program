"""Build known_cycles.csv and candidates.csv.

candidates.csv: for L=1..18 and the two nearest K (K+ = ceil(L log2 3), giving
smallest positive Lambda; K- = K+ - 1, giving smallest |Lambda| with Lambda<0),
report Lambda, Phi=K-L, whether (K,L) is an exact CF convergent of log2 3, and
N0 = #parity words of shape (K,L) with delta=0 (Lambda | W), computed by the
exact transfer-matrix DP (mod-Lambda restriction of the S_{K,L} exp-sum).
Also mean/spread of the Dedekind sum over a word sample, to show it is O(1)-O(K)
scale (linear in CF digits) and cannot resolve W ~ 2^K mod Lambda.
"""
import csv, math, itertools, random
from fractions import Fraction
from modknots import analyze_word, bs_weight, lam, LOG2_3

def cf_convergents(x, n):
    a = []
    xi = x
    for _ in range(n):
        ai = math.floor(xi)
        a.append(ai)
        frac = xi - ai
        if frac < 1e-12:
            break
        xi = 1/frac
    # convergents
    h0, h1 = 1, a[0]
    k0, k1 = 0, 1
    conv = [(a[0], 1)]
    for ai in a[1:]:
        h0, h1 = h1, ai*h1 + h0
        k0, k1 = k1, ai*k1 + k0
        conv.append((h1, k1))
    return conv  # list of (K,L) = (numerator, denominator)

def count_delta0(K, L, Lambda):
    """Exact # words of shape (K,L) with W ≡ 0 mod |Lambda|, via DP.
    State = (#ones placed so far). We build W = sum_i v_i 2^i 3^{c_i} left->right
    is awkward; instead process positions right->left tracking (ones_after, w mod m)."""
    m = abs(Lambda)
    if m == 1:
        return math.comb(K, L)  # everything ≡ 0
    # dp over positions i=K-1..0; state: number of ones chosen so far among
    # processed suffix -> dict {(ones, wmod): count}. Add position i: if we set
    # v_i=1, contributes 2^i * 3^{ones_after_i}. ones_after_i = current ones count.
    from collections import defaultdict
    dp = defaultdict(int)
    dp[(0, 0)] = 1
    pow2 = [pow(2, i, m) for i in range(K)]
    pow3 = [pow(3, j, m) for j in range(L+1)]
    for i in range(K-1, -1, -1):
        ndp = defaultdict(int)
        for (ones, wmod), cnt in dp.items():
            # v_i = 0
            ndp[(ones, wmod)] += cnt
            # v_i = 1  (only if ones < L)
            if ones < L:
                add = (pow2[i] * pow3[ones]) % m
                ndp[(ones+1, (wmod+add) % m)] += cnt
        dp = ndp
    return dp[(L, 0)]

def ded_stats(K, L, sample=400):
    """mean/min/max Dedekind sum and trace-bit-length over a random word sample
    (reservoir-free: draw random L-subsets directly)."""
    random.seed(1)
    deds = []; trbits = []
    seen = set()
    tries = 0
    while len(deds) < sample and tries < sample*20:
        tries += 1
        pos = tuple(sorted(random.sample(range(K), L)))
        if pos in seen:
            continue
        seen.add(pos)
        v = [0]*K
        for p in pos: v[p] = 1
        d = analyze_word(tuple(v))
        deds.append(d['ded'])
        trbits.append(d['trace'].bit_length())
    return (min(deds), sum(deds)/len(deds), max(deds), min(trbits), max(trbits))

def main():
    conv = set(cf_convergents(LOG2_3, 30))
    with open("candidates.csv", "w", newline="") as f:
        w = csv.writer(f)
        w.writerow(["L","K","sign","Lambda","Phi_eq_KminusL","is_CF_convergent",
                    "num_words_CKL","N_delta0","ded_min","ded_mean","ded_max",
                    "tracebits_min","tracebits_max"])
        for L in range(1, 19):
            Kp = math.ceil(L*LOG2_3)          # smallest K with 2^K > 3^L
            for K, sign in [(Kp, "+"), (Kp-1, "-")]:
                if K < L or K < 1:
                    continue
                Lambda = lam(K, L)
                nCKL = math.comb(K, L)
                N0 = count_delta0(K, L, Lambda) if abs(Lambda) <= 3_000_000 else -1
                dmin, dmean, dmax, tbmin, tbmax = ded_stats(K, L)
                N0s = str(N0) if N0 >= 0 else "skip(|Lam|>3e6)"
                w.writerow([L, K, sign, Lambda, "K-L="+str(K-L),
                            "yes" if (K, L) in conv else "no",
                            nCKL, N0s, f"{dmin:.4f}", f"{dmean:.4f}", f"{dmax:.4f}",
                            tbmin, tbmax])
                print(f"L={L:2d} K={K:2d} {sign} Lam={Lambda:>12d} CF={'Y' if (K,L) in conv else '.'} "
                      f"CKL={nCKL:>9d} N0={N0s:>14s} ded[{dmin:.3f},{dmax:.3f}] trbits[{tbmin},{tbmax}]")

    # known cycles table
    known = [("0",(0,)),("m1",(1,)),("1_2",(1,0)),("m5",(1,1,0)),
             ("m17",(1,1,1,1,0,1,1,1,0,0,0))]
    with open("known_cycles.csv","w",newline="") as f:
        w=csv.writer(f)
        w.writerow(["name","K","L","Lambda","W","x_v","Phi","trace","ded","hyp_len","runvector"])
        for name,v in known:
            if sum(v)==0:
                w.writerow([name,1,0,1,0,0,"-","-","-","-","()"]); continue
            d=analyze_word(v)
            x=d['W']//d['Lambda']
            w.writerow([name,d['K'],d['L'],d['Lambda'],d['W'],x,d['Phi'],
                        d['trace'],f"{d['ded']:.4f}",f"{d['hyp_len']:.4f}",str(d['a'])])
    print("wrote candidates.csv, known_cycles.csv")

if __name__=="__main__":
    main()
