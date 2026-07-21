"""Decisive scale experiment (coordinator steering).
At k = C log p (C in {2,3,4,5}) compare THREE quantities:
 (A) short-orbit single-generator worst frequency:
        W2(p,B) = max_{c!=0} |sum_{j<B} e_p(c 2^j)| / B         [naive proxy]
 (B) actual walk worst single frequency (Bernoulli mixed-radix):
        Fw(p,k) = max_{xi!=0} |hat mu_k(xi)|                     [real object]
 (C) fixed-weight L-inf, worst over m in band [eta k,(1-eta)k]:
        Linf(p,k) = max_m max_a p*|Pr(B=a,|w|=m) - 1/p|         [THE theorem]
If (A) stays ~1 while (B),(C) decay: theorem TRUE at k~log p, but single-generator
cancellation is NOT the mechanism (=> proof must use 2-3 coupling / sum-product).
"""
import csv, math
import numpy as np
from exact_dp import dp_counts


def short_orbit_worst(p, B):
    """max over c!=0 of |sum_{j<B} e_p(c 2^j)| / B."""
    pw = [pow(2, j, p) for j in range(B)]          # 2^j mod p
    c = np.arange(1, p)[:, None]                    # (p-1,1)
    ang = 2 * np.pi * (c * np.array(pw)[None, :] % p) / p
    S = np.abs(np.exp(1j * ang).sum(axis=1))        # (p-1,)
    return float(S.max()) / B


def bernoulli_hat(p, k):
    """worst |hat mu_k(xi)|, xi!=0, Bernoulli(1/2), via exact DP + FFT."""
    cnt = dp_counts(p, k)                            # (k+1,p)
    mu = cnt.sum(axis=0).astype(np.float64) / (2.0 ** k)   # marginal over m
    hat = np.fft.fft(mu)                             # hat[xi]=sum_b mu[b] e^{-2pi i xi b/p}
    return float(np.max(np.abs(hat[1:])))


def fixed_weight_linf(p, k, eta=0.30):
    cnt = dp_counts(p, k)
    lo, hi = max(1, int(math.ceil(eta * k))), min(k - 1, int((1 - eta) * k))
    worst = 0.0
    for m in range(lo, hi + 1):
        Ckm = math.comb(k, m)
        pr = cnt[m].astype(np.float64) / Ckm
        worst = max(worst, float(np.max(np.abs(pr - 1.0 / p))) * p)
    return worst


def main():
    primes = [101, 251, 601, 1201, 2003, 4057, 6553]
    with open("scale_test.csv", "w", newline="") as f:
        w = csv.writer(f)
        w.writerow(["p", "logp", "C", "k", "shortorbit_W2", "walk_worstFourier",
                    "fixedwt_linf_ratio"])
        for p in primes:
            lp = math.log(p)
            for C in (2, 3, 4, 5):
                k = int(round(C * lp))
                if math.comb(k, k // 2) >= 2 ** 62:
                    continue
                W2 = short_orbit_worst(p, k)
                Fw = bernoulli_hat(p, k)
                Li = fixed_weight_linf(p, k)
                w.writerow([p, f"{lp:.3f}", C, k, f"{W2:.4f}", f"{Fw:.3e}",
                            f"{Li:.4f}"])
    # print summary
    print("p     C  k   shortorbit_W2   walk_worstFourier  fixedwt_linf_ratio")
    with open("scale_test.csv") as f:
        for r in csv.DictReader(f):
            print(f"{int(r['p']):5d} {r['C']}  {int(r['k']):2d}   "
                  f"{float(r['shortorbit_W2']):.3f}          "
                  f"{float(r['walk_worstFourier']):.2e}          "
                  f"{float(r['fixedwt_linf_ratio']):.3f}")
    print("\nW2~1 => no single-generator cancellation at this scale;",
          "walk/fixedwt small => theorem holds via 2-3 coupling.")


if __name__ == "__main__":
    main()
