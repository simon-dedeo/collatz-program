"""Threshold k*(p) = min k with linf_ratio<=tol, m=k/2, vs log p.
Determines the empirical constant C in 'k >= C log p'."""
import csv, math
import numpy as np
from math import lcm, comb
from sympy import primerange
from exact_dp import dp_counts
from exceptional import order_capped


def linf_ratio_series(p, kmax):
    """For each k up to kmax, linf_ratio at m=k//2 (single DP run to kmax)."""
    cnt = dp_counts(p, kmax)   # gives all layers, but 2^j uses full length; need per-k
    # NOTE: dp_counts(p,kmax)[m] is for length kmax, not length k. Recompute per k.
    res = {}
    for k in range(4, kmax + 1):
        c = dp_counts(p, k)
        m = k // 2
        Ckm = comb(k, m)
        pr = c[m].astype(np.float64) / Ckm
        res[k] = float(pr.max()) * p
    return res


def main():
    # sample primes across a log range; include some small-subgroup ones
    sample = [11, 23, 31, 47, 73, 101, 131, 191, 251, 307, 431, 499, 601,
              997, 1201, 2003, 4057, 6553]
    tol = 1.10
    rows = []
    with open("threshold.csv", "w", newline="") as f:
        w = csv.writer(f)
        w.writerow(["p", "logp", "sg", "sg_exp", "kstar_1.10", "kstar_1.02",
                    "kstar/logp", "sg_over_pm1"])
        for p in sample:
            o2 = order_capped(2, p, p); o3 = order_capped(3, p, p)
            sg = lcm(o2, o3)
            logp = math.log(p)
            kmax = min(60, max(30, int(6 * logp) + 2))
            ser = linf_ratio_series(p, kmax)
            def kstar(t):
                for k in sorted(ser):
                    if ser[k] <= t:
                        return k
                return None
            k110 = kstar(1.10); k102 = kstar(1.02)
            rows.append((p, logp, sg, k110))
            w.writerow([p, f"{logp:.3f}", sg, f"{math.log(sg)/logp:.3f}",
                        k110, k102,
                        f"{k110/logp:.2f}" if k110 else "NA",
                        f"{sg/(p-1):.3f}"])
    print("p      logp   sg    kstar(1.10)  kstar/logp")
    for p, logp, sg, k110 in rows:
        print(f"{p:6d} {logp:5.2f} {sg:5d}   {k110}         "
              f"{k110/logp:.2f}" if k110 else f"{p} NA")
    ratios = [k110 / math.log(p) for p, logp, sg, k110 in rows if k110]
    print(f"\nkstar(1.10)/log p : min={min(ratios):.2f} mean={sum(ratios)/len(ratios):.2f} "
          f"max={max(ratios):.2f}   => empirical C ~ {max(ratios):.1f}")
    print("wrote threshold.csv")


if __name__ == "__main__":
    main()
