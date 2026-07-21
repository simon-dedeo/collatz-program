"""Prime-power lifting test (the valuation loophole raised by gpt-5.6-sol).

N_p(K,L)>0 does NOT a priori imply N_{p^e}(K,L)>0: a structural failure to lift
solutions of W==0 mod p to mod p^e would be a CHEAP finite-place obstruction at
a MODEST prime power p^e || Lambda (no giant prime needed).  This script hunts
for it: over near-convergent (K,L) it finds prime powers p^e || Lambda with
e>=2 (and p^e small enough for the DP), and compares N_p, N_{p^2}, ..., N_{p^e}.
A drop to 0 at some level would be a genuine new obstruction; monotone
nonvanishing supports the collapse verdict.
"""
import csv
from math import log, comb
from local_count import count_mod

LOG2, LOG3 = log(2.0), log(3.0)
PMAX_PE = 200000  # cap on p^e for the exact DP

def prime_power_factors(n, pe_cap):
    """small p^e || n with p^e <= pe_cap and e>=2, returned as (p,e)."""
    out = []
    d = 2
    m = n
    while d * d <= m and d < 5000:
        if m % d == 0:
            e = 0
            while m % d == 0:
                m //= d; e += 1
            if e >= 2 and d**e <= pe_cap:
                out.append((d, e))
        d += 1 if d == 2 else 2
    return out

def main():
    rows = []
    any_drop = False
    for K in range(3, 400):
        L = int(K * LOG2 / LOG3)
        Lam = 2**K - 3**L
        if Lam <= 1:
            continue
        C = comb(K, L)
        for (p, e) in prime_power_factors(Lam, PMAX_PE):
            counts = []
            for k in range(1, e + 1):
                counts.append(count_mod(K, L, p**k))
            liftok = all(c > 0 for c in counts)
            if not liftok:
                any_drop = True
            rows.append((K, L, p, e, "|".join(map(str, counts)),
                         f"{counts[0]*p/C:.3f}", f"{counts[-1]*p**e/C:.3f}",
                         int(liftok)))
    with open("lifting_test.csv", "w", newline="") as f:
        w = csv.writer(f)
        w.writerow(["K", "L", "p", "e", "N_p|N_p2|...|N_pe",
                    "N_p*p/C", "N_pe*pe/C", "all_levels_positive"])
        w.writerows(rows)
    print(f"prime powers p^e||Lambda (e>=2, p^e<={PMAX_PE}) at near-convergents K<400:")
    print(f"  cases tested: {len(rows)}")
    print(f"  any N_{{p^k}}==0 (a cheap lifting obstruction)? {any_drop}")
    print(f"  wrote lifting_test.csv")

if __name__ == "__main__":
    main()
