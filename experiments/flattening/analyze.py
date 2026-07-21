"""Analyze flatness.csv: characterize exceptional set, print verdict."""
import csv
from collections import defaultdict


def load(fn):
    with open(fn) as f:
        return list(csv.DictReader(f))


def main():
    rows = load("flatness.csv")
    # At the largest k, m closest to k/2, per prime.
    kmax = max(int(r["k"]) for r in rows)
    best = {}
    for r in rows:
        if int(r["k"]) != kmax:
            continue
        p = int(r["p"])
        m, half = int(r["m"]), kmax / 2
        if p not in best or abs(m - half) < abs(best[p][0] - half):
            best[p] = (m, r)

    recs = []
    for p, (m, r) in best.items():
        recs.append((p, int(r["sg"]), float(r["sg_over_pm1"]),
                     int(r["ord2"]), int(r["ord3"]),
                     float(r["linf_ratio"]), float(r["c_l2"]),
                     float(r["collision"]) * p))

    print(f"=== At k={kmax}, m~k/2, per prime (linf_ratio=p*maxPr, 1=uniform) ===")
    print("Worst 15 by linf_ratio:")
    for p, sg, sgr, o2, o3, lr, cl2, cr in sorted(recs, key=lambda x: -x[5])[:15]:
        print(f"  p={p:4d} sg={sg:4d} sg/(p-1)={sgr:.3f} ord2={o2:4d} ord3={o3:4d}"
              f"  linf_ratio={lr:8.3f}  c_l2={cl2:6.2f}")
    print("Best 8 by linf_ratio:")
    for p, sg, sgr, o2, o3, lr, cl2, cr in sorted(recs, key=lambda x: x[5])[:8]:
        print(f"  p={p:4d} sg={sg:4d} sg/(p-1)={sgr:.3f} ord2={o2:4d} ord3={o3:4d}"
              f"  linf_ratio={lr:8.3f}  c_l2={cl2:6.2f}")

    # Correlation: does small sg predict bad flatness?
    print("\n=== flatness vs subgroup size (k=%d) ===" % kmax)
    buckets = defaultdict(list)
    for p, sg, sgr, o2, o3, lr, cl2, cr in recs:
        if sgr >= 0.999:
            b = "full (<2,3>=F_p*)"
        elif sgr >= 0.5:
            b = "large (>=0.5)"
        elif sgr >= 0.1:
            b = "medium [0.1,0.5)"
        else:
            b = "small (<0.1)"
        buckets[b].append(lr)
    for b in ["full (<2,3>=F_p*)", "large (>=0.5)", "medium [0.1,0.5)", "small (<0.1)"]:
        v = buckets[b]
        if v:
            print(f"  {b:22s} n={len(v):3d}  linf_ratio: "
                  f"min={min(v):.2f} med={sorted(v)[len(v)//2]:.2f} max={max(v):.2f}")

    # Threshold: which primes fail flatness (linf_ratio > 3) at kmax?
    fails = [(p, sg, sgr, lr) for p, sg, sgr, o2, o3, lr, cl2, cr in recs if lr > 3.0]
    print(f"\n=== primes with linf_ratio>3 at k={kmax} (candidate exceptional) ===")
    for p, sg, sgr, lr in sorted(fails, key=lambda x: x[0]):
        print(f"  p={p:4d} sg={sg:4d} sg/(p-1)={sgr:.3f} linf_ratio={lr:.2f}")
    print(f"  ({len(fails)} of {len(recs)} primes)")

    # Decay analysis
    print("\n=== decay.csv: linf_ratio vs k ===")
    d = load("decay.csv")
    byp = defaultdict(list)
    for r in d:
        byp[int(r["p"])].append((int(r["k"]), float(r["linf_ratio"]), float(r["l2"])))
    for p in sorted(byp):
        seq = sorted(byp[p])
        sg = [r["sg"] for r in d if int(r["p"]) == p][0]
        ks = [8, 16, 24, 32, 40, 50]
        vals = {k: lr for k, lr, l2 in seq}
        s = "  ".join(f"k{k}={vals.get(k, float('nan')):.2f}" for k in ks if k in vals)
        print(f"  p={p:4d} sg={sg}: {s}")


if __name__ == "__main__":
    main()
