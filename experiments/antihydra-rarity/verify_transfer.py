#!/usr/bin/env python3
"""Part C: exact transfer (Proposition 3): for each C and k,
  #{ 0 <= n < 2^k : counter path of seed n stays in [0,C] for steps 1..k }  ==  |L_C(k)|
LHS computed by actually iterating H(n)=floor(3n/2) on all seeds; RHS by word DP.
Also verifies the Theorem-4 bound  #{n <= x} <= 2*K_C*x^theta at x = 2^k - 1.
"""
import math
import numpy as np

def seed_count(C, k):
    n = np.arange(1 << k, dtype=np.int64)
    a = n.copy()
    b = np.zeros(1 << k, dtype=np.int64)
    alive = np.ones(1 << k, dtype=bool)
    for _ in range(k):
        e = a & 1
        b += 2 - 3 * e
        alive &= (b >= 0) & (b <= C)
        a = a + (a >> 1)
    return int(alive.sum())

def word_count(C, k):
    dp = [0] * (C + 1); dp[0] = 1
    for _ in range(k):
        nd = [0] * (C + 1)
        for s in range(C + 1):
            if dp[s]:
                if s + 2 <= C: nd[s + 2] += dp[s]
                if s - 1 >= 0: nd[s - 1] += dp[s]
        dp = nd
    return sum(dp)

def perron(C):
    A = np.zeros((C + 1, C + 1))
    for s in range(C + 1):
        if s + 2 <= C: A[s, s + 2] = 1
        if s - 1 >= 0: A[s, s - 1] = 1
    w, v = np.linalg.eig(A)
    i = np.argmax(w.real)
    return w.real[i], np.abs(v[:, i].real)

k = 20
for C in (1, 2, 3, 4, 6, 10, 40):
    sc, wc = seed_count(C, k), word_count(C, k)
    line = f"  C={C:2d} k={k}: seeds={sc:8d}  words={wc:8d}  {'EQUAL' if sc == wc else 'MISMATCH'}"
    if C >= 2 and sc > 0:
        rho, vec = perron(C)
        K = vec[0] * float(np.sum(1.0 / vec))
        x = (1 << k) - 1
        bound = 2 * K * x ** math.log2(rho)
        line += f"  thm4 bound={bound:.1f} ({'OK' if sc <= bound else 'FAIL'})"
    print(line)
    assert sc == wc

# also spot-check equality across k for C=6
for kk in (4, 8, 12, 16, 22):
    assert seed_count(6, kk) == word_count(6, kk)
print("  C=6, k in {4,8,12,16,22}: equality holds")
print("PART C: exact transfer verified.")
