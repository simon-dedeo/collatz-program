#!/usr/bin/env python3
"""Part B: window automaton A_C on states {0..C}: s ->(e=0) s+2 (if <=C), s ->(e=1) s-1 (if >=0).

Outputs theta_table.csv: C, rho(C), theta(C)=log2 rho(C), rho(C)^3, K_C.
Checks: strict monotonicity (C>=2), limit theta -> log2(3)-2/3, exact char polys C<=8,
golden-ratio non-coincidence (exact for C<=12 via sympy, numeric for C<=40),
and |L_C(k)| <= K_C * rho^k for k <= 60 (exact-integer DP vs float bound).
"""
import csv, math
import numpy as np
import sympy as sp

H13 = math.log2(3) - 2/3          # = H(1/3), binary entropy
PHI = (1 + 5**0.5) / 2

def adj(C):
    A = np.zeros((C + 1, C + 1))
    for s in range(C + 1):
        if s + 2 <= C: A[s, s + 2] = 1
        if s - 1 >= 0: A[s, s - 1] = 1
    return A

def perron(A):
    w, v = np.linalg.eig(A)
    i = np.argmax(w.real)
    rho = w.real[i]
    vec = np.abs(v[:, i].real)
    return rho, vec

rows = []
for C in range(1, 41):
    A = adj(C)
    rho, vec = perron(A)
    if C == 1:
        rho, K = 0.0, float('nan')
    else:
        K = vec[0] * np.sum(1.0 / vec)
    theta = math.log2(rho) if rho > 0 else float('-inf')
    rows.append((C, rho, theta, rho**3, K))

with open('theta_table.csv', 'w', newline='') as f:
    w = csv.writer(f)
    w.writerow(['C', 'rho', 'theta=log2rho', 'rho^3', 'K_C'])
    for r in rows:
        w.writerow([r[0], f"{r[1]:.10f}", f"{r[2]:.10f}", f"{r[3]:.10f}", f"{r[4]:.6f}"])

print("C, rho, theta (selected):")
for C in (1, 2, 3, 4, 5, 6, 8, 12, 16, 24, 32, 40):
    r = rows[C - 1]
    print(f"  C={r[0]:2d}  rho={r[1]:.8f}  theta={r[2]:+.8f}  rho^3={r[3]:.8f}")
print(f"limit target: rho_inf = 3*2^(-2/3) = {3 * 2**(-2/3):.8f},  theta_inf = H(1/3) = {H13:.8f}")

mono = all(rows[i][1] < rows[i + 1][1] - 1e-12 for i in range(1, 39))
below = all(r[1] < 3 * 2**(-2/3) for r in rows)
print(f"strict monotonicity rho(2)<...<rho(40): {mono};  all rho(C) < 3*2^(-2/3): {below}")

# exact characteristic polynomials, C <= 8; golden-ratio divisibility check C <= 12
x = sp.symbols('x')
print("exact char polys (factored), C = 1..8:")
for C in range(1, 9):
    M = sp.Matrix(adj(C).astype(int))
    p = M.charpoly(x).as_expr()
    print(f"  C={C}: {sp.factor(p)}")
gm = sp.Poly(x**2 - x - 1, x)
for C in range(1, 13):
    M = sp.Matrix(adj(C).astype(int))
    p = sp.Poly(M.charpoly(x).as_expr(), x)
    assert sp.rem(p, gm, x) != 0 or p.rem(gm).is_zero is False
    assert not sp.rem(p.as_expr(), gm.as_expr(), x).is_zero
print("golden-ratio check: x^2-x-1 divides NO char poly, C <= 12 (exact)")
d = min(abs(r[1] - PHI) for r in rows)
C6 = rows[5]
print(f"min_C<=40 |rho(C)-phi| = {d:.6f}; rho(5)^3={rows[4][3]:.6f} < phi^3={PHI**3:.6f} < rho(6)^3={C6[3]:.6f}")

# integer DP for |L_C(k)| and the K_C * rho^k bound
def Lcount(C, k):
    dp = [0] * (C + 1); dp[0] = 1
    for _ in range(k):
        nd = [0] * (C + 1)
        for s in range(C + 1):
            if dp[s]:
                if s + 2 <= C: nd[s + 2] += dp[s]
                if s - 1 >= 0: nd[s - 1] += dp[s]
        dp = nd
    return sum(dp)

for C in (2, 3, 4, 6, 10, 20):
    rho, vec = perron(adj(C)); K = vec[0] * np.sum(1.0 / vec)
    bad = [k for k in range(1, 61) if Lcount(C, k) > K * rho**k * (1 + 1e-9)]
    print(f"  C={C:2d}: |L_C(k)| <= K_C*rho^k for k=1..60: {'OK' if not bad else f'FAIL {bad}'}"
          f"  (K_C={K:.4f})")
print("PART B done; table in theta_table.csv")
