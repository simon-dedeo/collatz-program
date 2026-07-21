"""Sweep exact B mod p flatness over primes p<=500, several k, m band.
Writes flatness.csv (per p,k,m) and decay.csv (fine k-decay for a few primes)."""
import csv
import math
import numpy as np
from exact_dp import dp_counts, multiplicative_order, subgroup_size


def primes_upto(n):
    sieve = np.ones(n + 1, dtype=bool)
    sieve[:2] = False
    for i in range(2, int(n**0.5) + 1):
        if sieve[i]:
            sieve[i * i::i] = False
    return [int(x) for x in np.nonzero(sieve)[0]]


def metrics(cnt_row, p, Ckm):
    """cnt_row: length-p exact counts for fixed (k,m). Returns dict of flatness stats."""
    pr = cnt_row.astype(np.float64) / Ckm
    linf = float(pr.max())
    collision = float((pr * pr).sum())        # sum Pr^2
    l2 = collision - 1.0 / p                    # sum (Pr-1/p)^2  (>=0)
    l2 = max(l2, 0.0)
    support = int((cnt_row > 0).sum())
    return linf, collision, l2, support


def exp_p(val, p):
    """exponent e with val ~ p^{-e}; returns -log(val)/log(p) or inf."""
    if val <= 0:
        return float("inf")
    return -math.log(val) / math.log(p)


def main():
    ps = [p for p in primes_upto(500) if p not in (2, 3)]
    kgrid = [12, 16, 20, 24, 30, 40, 50]
    mfracs = [0.3, 0.4, 0.5, 0.6, 0.7]

    # precompute diagnostics
    diag = {}
    for p in ps:
        diag[p] = (multiplicative_order(2, p), multiplicative_order(3, p),
                   subgroup_size(p))

    with open("flatness.csv", "w", newline="") as f:
        w = csv.writer(f)
        w.writerow(["p", "k", "m", "logp", "k_over_logp", "ord2", "ord3",
                    "sg", "sg_over_pm1", "Ckm", "linf", "linf_ratio",
                    "collision", "coll_ratio", "l2", "c_linf", "c_l2"])
        for p in ps:
            ord2, ord3, sg = diag[p]
            logp = math.log(p)
            for k in kgrid:
                cnt = dp_counts(p, k)   # (k+1, p) exact
                ms = sorted({max(1, min(k - 1, round(fr * k))) for fr in mfracs})
                for m in ms:
                    Ckm = int(math.comb(k, m))
                    linf, collision, l2, support = metrics(cnt[m], p, Ckm)
                    w.writerow([
                        p, k, m, f"{logp:.4f}", f"{k/logp:.3f}", ord2, ord3,
                        sg, f"{sg/(p-1):.4f}", Ckm,
                        f"{linf:.6e}", f"{linf*p:.4f}",
                        f"{collision:.6e}", f"{collision*p:.4f}",
                        f"{l2:.6e}", f"{exp_p(linf,p):.4f}",
                        f"{exp_p(l2,p)-1:.4f}",
                    ])
    print("wrote flatness.csv rows for", len(ps), "primes")

    # fine k-decay for representative primes: generic (full subgroup) vs exceptional
    reps = [101, 131, 251, 7, 31, 73, 683 if False else 341]  # 341 not prime; fix below
    reps = [p for p in [101, 131, 251, 7, 31, 73] if p in ps]
    with open("decay.csv", "w", newline="") as f:
        w = csv.writer(f)
        w.writerow(["p", "sg", "sg_over_pm1", "k", "m", "linf", "linf_ratio",
                    "l2", "c_linf", "c_l2"])
        for p in reps:
            ord2, ord3, sg = diag[p]
            for k in range(8, 51, 2):
                cnt = dp_counts(p, k)
                m = k // 2
                Ckm = int(math.comb(k, m))
                linf, collision, l2, support = metrics(cnt[m], p, Ckm)
                w.writerow([p, sg, f"{sg/(p-1):.4f}", k, m,
                            f"{linf:.6e}", f"{linf*p:.4f}", f"{l2:.6e}",
                            f"{exp_p(linf,p):.4f}", f"{exp_p(l2,p)-1:.4f}"])
    print("wrote decay.csv for primes", reps)


if __name__ == "__main__":
    main()
