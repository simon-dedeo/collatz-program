"""Exact local densities N_p(K,L)/(C/p) at the small prime factors p | Lambda.

This is the rigorous backbone of the "no local obstruction at small primes"
finding.  For each near-convergent (K,L) [L = floor(K log2/log3), Lambda>0] and
each small prime factor p | Lambda (p <= PMAX), compute the EXACT count
    N_p(K,L) = #{words shape (K,L) : W(v) == 0 mod p}
and the normalized density  N_p * p / C(K,L)  (== 1 under equidistribution).
If N_p > 0 for every such p, there is no single-small-prime finite-place
obstruction at (K,L): the necklace congruence W==0 mod p is locally solvable.

Theory (docs/notes/cycle-finite-places.md, Lemma "small primes never obstruct"):
the word-slide graph on shape (K,L) is connected and single slides change W by
+-3^c 2^j, whose additive span mod p is all of Z/p (it contains 2^0-... = 1);
so for K large enough vs p the map v |-> W(v) mod p is surjective and N_p>0.
"""
import sys, csv
from math import comb, log
from local_count import count_mod

LOG2, LOG3 = log(2.0), log(3.0)
PMAX = 300

def small_prime_factors(n, pmax):
    fs = {}
    d = 2
    while d <= pmax and d * d <= n:
        while n % d == 0:
            fs[d] = fs.get(d, 0) + 1
            n //= d
        d += 1 if d == 2 else 2
    # catch a prime cofactor <= pmax
    if 1 < n <= pmax:
        fs[n] = fs.get(n, 0) + 1
    return fs

def main():
    kmin = int(sys.argv[1]) if len(sys.argv) > 1 else 20
    kmax = int(sys.argv[2]) if len(sys.argv) > 2 else 160
    out = sys.argv[3] if len(sys.argv) > 3 else "local_density.csv"
    rows = []
    min_ratio = 1e9
    worst = None
    for K in range(kmin, kmax + 1):
        L = int(K * LOG2 / LOG3)
        Lam = 2**K - 3**L
        if Lam <= 1:
            continue
        C = comb(K, L)
        for p, e in sorted(small_prime_factors(Lam, PMAX).items()):
            N = count_mod(K, L, p)
            ratio = N * p / C
            rows.append((K, L, p, e, N, f"{ratio:.4f}", int(N > 0)))
            if ratio < min_ratio:
                min_ratio = ratio; worst = (K, L, p, N)
    with open(out, "w", newline="") as f:
        w = csv.writer(f)
        w.writerow(["K", "L", "p", "p_exp_in_Lambda", "N_p", "N_p*p/C", "N_p_positive"])
        w.writerows(rows)
    npos = sum(r[6] for r in rows)
    print(f"rows={len(rows)}  all N_p>0: {npos == len(rows)}  "
          f"min(N_p*p/C)={min_ratio:.4f} at (K,L,p,N)={worst}")
    print(f"wrote {out}")

if __name__ == "__main__":
    main()
