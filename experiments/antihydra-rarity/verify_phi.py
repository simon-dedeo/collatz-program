#!/usr/bin/env python3
"""Parts D & E: golden-ratio population law and late-halt tail.

(D1) q_k = 2^-k * #{words of length k whose counter hits -1 by step k} increases to
     1/phi = phi - 1 = 0.6180...; from start height b: limit phi^-(b+1).
(D2) first-passage counts f_l satisfy f_l = [l=1] + sum_{i+j+m=l-1} f_i f_j f_m.
(D3) seeds n < 2^k with no '11' in first k parities number exactly Fib(k+2).
(E)  fraction of words with b_T = -1 is <= 2^{-cT}, c = 5/3 - log2(3);
     halting-in-[t0,k] count <= 19 * 2^{k - c*t0}.
Writes qk_table.csv (k, q_k, 1/phi - q_k).
"""
import csv, math
from fractions import Fraction
import numpy as np

PHI = (1 + 5**0.5) / 2
c = 5/3 - math.log2(3)

def q_seq(kmax, b0=0):
    """exact fractions: cumulative halted mass q_k from start height b0, fair coin."""
    dp = {b0: Fraction(1)}
    dead = Fraction(0)
    out = []
    for _ in range(kmax):
        nd = {}
        for s, p in dp.items():
            nd[s + 2] = nd.get(s + 2, Fraction(0)) + p / 2
            if s == 0:
                dead += p / 2
            else:
                nd[s - 1] = nd.get(s - 1, Fraction(0)) + p / 2
        dp = nd
        out.append(dead)
    return out

qs = q_seq(700)
with open('qk_table.csv', 'w', newline='') as f:
    w = csv.writer(f); w.writerow(['k', 'q_k', '1/phi - q_k'])
    for k in (1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 700):
        qk = float(qs[k - 1]); w.writerow([k, f"{qk:.12f}", f"{1/PHI - qk:.3e}"])
print(f"(D1) q_k -> 1/phi: q_100={float(qs[99]):.10f}  q_700={float(qs[699]):.12f}  "
      f"1/phi={1/PHI:.12f}  gap={1/PHI - float(qs[699]):.2e}")
assert all(qs[i] <= qs[i + 1] for i in range(len(qs) - 1))
for b in (1, 2, 3):
    qb = float(q_seq(400, b0=b)[-1])
    print(f"     start height b={b}: q_400={qb:.9f}  vs phi^-(b+1)={PHI**(-(b+1)):.9f}")

# (D2) first-passage recurrence vs direct DP
def fp_counts(L):
    """f[l] = #words of length l whose counter (from 0) first hits -1 at step l."""
    dp = {0: 1}; f = [0] * (L + 1)
    for l in range(1, L + 1):
        nd = {}
        for s, m in dp.items():
            nd[s + 2] = nd.get(s + 2, 0) + m
            if s == 0: f[l] += m
            else: nd[s - 1] = nd.get(s - 1, 0) + m
        dp = nd
    return f
L = 40
f = fp_counts(L)
for l in range(1, L + 1):
    conv = sum(f[i] * f[j] * f[l - 1 - i - j]
               for i in range(1, l - 1) for j in range(1, l - 1 - i))
    assert f[l] == (1 if l == 1 else 0) + conv, l
print(f"(D2) f_l = [l=1] + triple convolution, l <= {L}: OK  (f_1,f_4,f_7,f_10 = "
      f"{f[1]},{f[4]},{f[7]},{f[10]})")
assert abs(sum(f[l] * 0.5**l for l in range(1, L + 1)) - float(qs[L - 1])) < 1e-15

# (D3) no-11 seeds are Fibonacci-many
def no11_count(k):
    a = np.arange(1 << k, dtype=np.int64); prev = np.zeros(1 << k, dtype=np.int64)
    ok = np.ones(1 << k, dtype=bool)
    for i in range(k):
        e = a & 1
        if i: ok &= ~((prev == 1) & (e == 1))
        prev = e; a = a + (a >> 1)
    return int(ok.sum())
fib = [0, 1]
while len(fib) < 30: fib.append(fib[-1] + fib[-2])
for k in (5, 10, 15, 20):
    n11 = no11_count(k)
    assert n11 == fib[k + 2], (k, n11, fib[k + 2])
    print(f"(D3) k={k:2d}: #no-11 seeds mod 2^k = {n11} = Fib({k+2})  OK")

# (E) late-halt tail: exact word counts with b_T = -1, vs 2^(k-cT); halting window bound
def level_hits(kmax):
    """h[T] = #words of length T with counter value -1 at step T (no survival constraint)."""
    out = {}
    for T in range(1, kmax + 1):
        if (2 * T + 1) % 3 == 0:
            out[T] = math.comb(T, (2 * T + 1) // 3)
    return out
hits = level_hits(60)
worst = max(hits[T] / 2**(T * (1 - c) )  for T in hits)   # want <= 1, i.e. hits <= 2^{T H(1/3)}
print(f"(E) max_T<=60 [#(b_T=-1 words) / 2^(T*H(1/3))] = {worst:.4f}  (<= 1: {worst <= 1})")
k, t0 = 60, 30
halt_ct = sum(hits[T] * 2**(k - T) for T in hits if t0 <= T <= k)
bound = 19 * 2**k * 2**(-c * t0)
print(f"    #words length {k} with b_T=-1 some T in [{t0},{k}] = {halt_ct:.3e} <= "
      f"19*2^(k-c*t0) = {bound:.3e}: {halt_ct <= bound}")
print("PARTS D,E: all checks passed; q_k table in qk_table.csv")
