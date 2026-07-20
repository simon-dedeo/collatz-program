#!/usr/bin/env python3
"""Part A: verify the cylinder-residue bijection (Lemma 1) for H(n)=floor(3n/2).

Checks, for k = 1..20:
  (A1) n mod 2^k -> (e_0,...,e_{k-1}) is injective (hence bijective onto {0,1}^k);
  (A2) well-definedness: the first k parities of n depend only on n mod 2^k
       (random lifts n + t*2^k, t in {1,2,3}, plus random n < 2^40);
  (A3) opposite-parity lifts: e_k(n + 2^k) = 1 - e_k(n) for all n < 2^k (k <= 14).
"""
import numpy as np

def words(narr, k):
    """codes of first-k parity words of the integers in narr (int64 safe for k<=25, n<2^25)."""
    a = narr.copy()
    code = np.zeros_like(a)
    for i in range(k):
        code |= (a & 1) << i
        a = a + (a >> 1)          # floor(3a/2) for a >= 0
    return code

ok = True
for k in range(1, 21):
    n = np.arange(1 << k, dtype=np.int64)
    c = words(n, k)
    u = np.unique(c)
    inj = (len(u) == (1 << k))
    ok &= inj
    if k in (1, 5, 10, 15, 20) or not inj:
        print(f"(A1) k={k:2d}: distinct words = {len(u)} / {1<<k}  {'OK' if inj else 'FAIL'}")
assert ok, "bijection FAILED"

rng = np.random.default_rng(0)
for k in (5, 12, 20):
    n = rng.integers(0, 1 << k, size=2000).astype(np.int64)
    base = words(n, k)
    for t in (1, 2, 3):
        assert np.array_equal(words(n + (t << k), k), base)
    big = rng.integers(0, 1 << 40, size=2000).astype(np.int64)
    assert np.array_equal(words(big, k), words(big & ((1 << k) - 1), k))
    print(f"(A2) k={k:2d}: first k parities depend only on n mod 2^k  OK")

for k in range(1, 15):
    n = np.arange(1 << k, dtype=np.int64)
    def ekth(m, k):
        a = m.copy()
        for _ in range(k):
            a = a + (a >> 1)
        return a & 1
    assert np.array_equal(ekth(n + (1 << k), k), 1 - ekth(n, k))
print("(A3) e_k(n + 2^k) = 1 - e_k(n) for all n < 2^k, k = 1..14  OK")
print("PART A: all checks passed.")
