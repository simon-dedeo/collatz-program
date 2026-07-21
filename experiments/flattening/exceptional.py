"""Find primes with genuinely small <2,3> (candidate exceptional set) and test
whether flatness FAILS on them. Uses |<2,3>| = lcm(ord_p2, ord_p3) (F_p* cyclic)."""
import csv
import math
import numpy as np
from math import lcm, comb
from sympy import primerange
from exact_dp import dp_counts


def order_capped(a, p, cap):
    """ord_p(a) if <= cap, else None (abort early)."""
    x = a % p
    o = 1
    while x != 1:
        x = (x * a) % p
        o += 1
        if o > cap:
            return None
    return o


def find_small_subgroup(pmax, sg_cap):
    """Primes p (5..pmax), p!|6, with |<2,3>| = lcm(ord2,ord3) <= sg_cap."""
    out = []
    for p in primerange(5, pmax + 1):
        if p == 3:
            continue
        o2 = order_capped(2, p, sg_cap)
        if o2 is None:
            continue
        o3 = order_capped(3, p, sg_cap)
        if o3 is None:
            continue
        sg = lcm(o2, o3)
        if sg <= sg_cap:
            out.append((p, sg, sg / (p - 1), o2, o3))
    return out


def flatness_at(p, k, m):
    cnt = dp_counts(p, k)
    Ckm = int(comb(k, m))
    pr = cnt[m].astype(np.float64) / Ckm
    linf = float(pr.max())
    coll = float((pr * pr).sum())
    l2 = max(coll - 1.0 / p, 0.0)
    support = int((cnt[m] > 0).sum())
    return linf, linf * p, l2, support


def main():
    print("=== primes p<=10^6 with smallest |<2,3>| relative to p ===")
    cand = find_small_subgroup(1_000_000, 400)
    # rank by relative size (how small the subgroup is compared to p)
    cand.sort(key=lambda x: x[2])
    print(f"found {len(cand)} primes with |<2,3>|<=400")
    for p, sg, rel, o2, o3 in cand[:30]:
        print(f"  p={p:7d} sg={sg:4d} (~p^{math.log(sg)/math.log(p):.3f}) "
              f"rel={rel:.2e} ord2={o2} ord3={o3}")

    print("\n=== flatness test on the most extreme exceptional primes (m=k/2) ===")
    tested = cand[:14]
    with open("exceptional.csv", "w", newline="") as f:
        w = csv.writer(f)
        w.writerow(["p", "sg", "sg_exp", "rel", "logp", "k", "k_over_logp",
                    "m", "linf_ratio", "l2", "support", "support_over_p"])
        for p, sg, rel, o2, o3 in tested:
            logp = math.log(p)
            sg_exp = math.log(sg) / logp
            for k in [24, 36, 48, 60]:
                if comb(k, k // 2) >= 2**62:
                    continue
                m = k // 2
                linf, lr, l2, support = flatness_at(p, k, m)
                w.writerow([p, sg, f"{sg_exp:.3f}", f"{rel:.3e}", f"{logp:.3f}",
                            k, f"{k/logp:.2f}", m, f"{lr:.4f}", f"{l2:.3e}",
                            support, f"{support/p:.4f}"])
                if k == 60:
                    print(f"  p={p:7d} sg={sg:4d}(p^{sg_exp:.2f}) k={k} k/logp={k/logp:.1f}"
                          f"  linf_ratio={lr:9.3f}  L2={l2:.2e}  supp={support}/{p}"
                          f"={support/p:.3f}")
    print("\nwrote exceptional.csv")


if __name__ == "__main__":
    main()
