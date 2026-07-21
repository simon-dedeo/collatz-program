"""
Exact distribution of the mixed-radix cycle numerator B mod p.

For a length-k binary word w of Hamming weight m with odd positions
0 <= i_1 < ... < i_m < k,
    B(w) = sum_{r=1}^m 3^{m-r} 2^{i_r}   (Boehm-Sontacchi cycle numerator).
Online recursion (B_0 = 0, process j = 0..k-1):
    B_{j+1} = B_j            if eps_j = 0
    B_{j+1} = 3 B_j + 2^j    if eps_j = 1

We want the EXACT distribution of B mod p over all C(k,m) words of weight m,
positions chosen uniformly. Exact transfer-matrix DP:
    cnt[t][b] = number of length-(prefix) words using t ones with B == b (mod p).
Transition at position j (c = 2^j mod p):
    eps=0: cnt'[t][b]   += cnt[t][b]
    eps=1: cnt'[t+1][(3b+c)%p] += cnt[t][b]
Complexity O(k * m * p), fully exact (integer counts).

int64 is exact while C(k,m) < 2^63; k <= 62 is safe. Use dtype='object' for
larger k (slower but exact).
"""
import numpy as np
from math import comb, gcd


def dp_counts(p, k, dtype=np.int64):
    """Return cnt array of shape (k+1, p): cnt[m, b] = #words of length k,
    weight m, with B(w) == b (mod p)."""
    cnt = np.zeros((k + 1, p), dtype=dtype)
    cnt[0, 0] = 1
    c = 1  # 2^j mod p, j=0 -> 2^0 = 1
    idx = np.arange(p)
    for j in range(k):
        tgt = (3 * idx + c) % p          # scatter permutation for eps=1
        newc = cnt.copy()                # eps=0 contributions
        ones = np.zeros_like(cnt)
        ones[1:, tgt] = cnt[:-1, :]      # eps=1: t->t+1, b->(3b+c)%p
        newc += ones
        cnt = newc
        c = (c * 2) % p
    return cnt


def brute_counts(p, k):
    """O(2^k) reference: enumerate all words, exact."""
    cnt = np.zeros((k + 1, p), dtype=np.int64)
    for mask in range(1 << k):
        B = 0
        m = 0
        for j in range(k):
            if (mask >> j) & 1:
                B = (3 * B + pow(2, j, p)) % p
                m += 1
        cnt[m, B] += 1
    return cnt


def multiplicative_order(a, p):
    if a % p == 0:
        return 0
    o = 1
    x = a % p
    while x != 1:
        x = (x * a) % p
        o += 1
    return o


def subgroup_size(p):
    """|<2,3>| in F_p^*."""
    seen = set()
    stack = [1 % p]
    seen.add(1 % p)
    while stack:
        x = stack.pop()
        for g in (2, 3):
            y = (x * g) % p
            if y not in seen:
                seen.add(y)
                stack.append(y)
    return len(seen)


if __name__ == "__main__":
    # Self-check: DP vs brute force on small cases.
    ok = True
    for p in (5, 7, 11, 13):
        for k in (6, 10, 12):
            a = dp_counts(p, k)
            b = brute_counts(p, k)
            if not np.array_equal(a, b):
                ok = False
                print(f"MISMATCH p={p} k={k}")
            # row sums must equal C(k,m)
            for m in range(k + 1):
                assert int(a[m].sum()) == comb(k, m), (p, k, m)
    print("self-check:", "PASS" if ok else "FAIL")
    # sanity on orders/subgroup
    for p in (5, 7, 31, 73):
        print(f"p={p} ord2={multiplicative_order(2,p)} ord3={multiplicative_order(3,p)} "
              f"|<2,3>|={subgroup_size(p)} p-1={p-1}")
