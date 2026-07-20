#!/usr/bin/env python3
r"""Numerical verification (numpy) for docs/notes/carries-spectrum.md.

Chain: Diaconis-Fulman carries-for-multiplication chain K_{k,b} (arXiv:0806.3583, Sec. 5.2).
State space {0,...,k-1}; from carry c, with input digit d uniform on {0,...,b-1}:
    c' = floor((k*d + c)/b).

CLAIM (Theorem 1 of the note), for gcd(k,b) = 1:
    det(xI - K_{k,b}) = (x - 1) * prod_O (x^{|O|} - b^{-|O|}),
product over orbits O of the map x -> b*x mod k on (Z/k) \ {0}.

Checks performed:
  A. base b=2, m in {3,5,7,9,11,13,15,21,27,33,81,243}:
     - eigenvalue multiset of K vs predicted multiset (greedy matching, max error)
     - det(zI - K) vs formula at random complex test points (max relative error)
  B. general base: DF's printed example (b=10, k=7) matrix reproduced entry-by-entry,
     plus spot checks (b,k) in {(10,7),(3,5),(10,9),(4,7),(6,35),(3,8),(5,12)}.
  C. exact power identity K^L = Pi + b^{-L} (I - Pi), L = ord_k(b), Pi = uniform projector.
  D. exact total-variation formula from state 0:  d_TV(K_0^r, pi) = t(k-t)/(k b^r), t = b^r mod k.
  E. affine variant (constant addend q): extended chain on {0,...,m} is block-triangular
     with extra eigenvalue 1/b; check spectrum and whether 1/2 is defective (Jordan) for m=3, b=2.
"""
import numpy as np
from fractions import Fraction
from math import gcd

rng = np.random.default_rng(20260720)


def build_K(k, b):
    """DF multiplication-carries transition matrix, states 0..k-1."""
    K = np.zeros((k, k))
    for c in range(k):
        for d in range(b):
            K[c, (k * d + c) // b] += 1.0 / b
    return K


def orbits(k, b):
    """Orbits of x -> b*x mod k on (Z/k) \\ {0}."""
    seen, orbs = set(), []
    for x in range(1, k):
        if x in seen:
            continue
        orb, y = [], x
        while y not in seen:
            seen.add(y)
            orb.append(y)
            y = (b * y) % k
        orbs.append(orb)
    return orbs


def predicted_eigs(k, b):
    """{1} together with, for each orbit of size rho, the rho-th roots of b^{-rho}."""
    eigs = [1.0 + 0j]
    for O in orbits(k, b):
        rho = len(O)
        eigs.extend((1.0 / b) * np.exp(2j * np.pi * j / rho) for j in range(rho))
    return np.array(eigs)


def match_error(a, bb):
    """Greedy bipartite matching of two same-size complex multisets; max matched distance."""
    a = list(a)
    bb = list(bb)
    err = 0.0
    for z in a:
        j = min(range(len(bb)), key=lambda i: abs(bb[i] - z))
        err = max(err, abs(bb[j] - z))
        bb.pop(j)
    return err


def formula_at(z, k, b):
    val = (z - 1.0)
    for O in orbits(k, b):
        rho = len(O)
        val *= z ** rho - float(b) ** (-rho)
    return val


print("=" * 88)
print("A. base b=2 : eigenvalue multisets and det(zI-K) vs formula")
print("=" * 88)
print(f"{'m':>4} {'deg':>4} {'orbit sizes':<28} {'eig match err':>14} {'det rel err':>14}")
for m in [3, 5, 7, 9, 11, 13, 15, 21, 27, 33, 81, 243]:
    assert m % 2 == 1
    K = build_K(m, 2)
    # sanity: doubly stochastic
    assert np.allclose(K.sum(0), 1) and np.allclose(K.sum(1), 1)
    ev = np.linalg.eigvals(K)
    pe = predicted_eigs(m, 2)
    e_match = match_error(pe, ev)
    # determinant check at random points on |z| = 2 (well-conditioned)
    rel = 0.0
    for _ in range(20):
        z = 2.0 * np.exp(2j * np.pi * rng.random())
        lhs = np.linalg.det(z * np.eye(m) - K)
        rhs = formula_at(z, m, 2)
        rel = max(rel, abs(lhs - rhs) / abs(rhs))
    osz = sorted((len(O) for O in orbits(m, 2)), reverse=True)
    ostr = ",".join(map(str, osz)) if len(osz) <= 8 else ",".join(map(str, osz[:8])) + ",..."
    print(f"{m:>4} {m:>4} {ostr:<28} {e_match:>14.3e} {rel:>14.3e}")

print()
print("=" * 88)
print("B. general base b (gcd(k,b)=1), incl. DF's printed example b=10,k=7")
print("=" * 88)
# DF (arXiv:0806.3583 p.13): 10*K for b=10, k=7
DF_matrix = np.array([
    [2, 1, 2, 1, 2, 1, 1],
    [2, 1, 2, 1, 1, 2, 1],
    [2, 1, 1, 2, 1, 2, 1],
    [1, 2, 1, 2, 1, 2, 1],
    [1, 2, 1, 2, 1, 1, 2],
    [1, 2, 1, 1, 2, 1, 2],
    [1, 1, 2, 1, 2, 1, 2],
]) / 10.0
K107 = build_K(7, 10)
print("DF printed matrix (b=10,k=7) reproduced exactly:", np.array_equal(K107, DF_matrix))
print(f"{'(b,k)':>10} {'orbit sizes':<20} {'eig match err':>14} {'det rel err':>14}")
for (b, k) in [(10, 7), (3, 5), (10, 9), (4, 7), (6, 35), (3, 8), (5, 12)]:
    assert gcd(b, k) == 1
    K = build_K(k, b)
    ev = np.linalg.eigvals(K)
    pe = predicted_eigs(k, b)
    e_match = match_error(pe, ev)
    rel = 0.0
    for _ in range(20):
        z = 2.0 * np.exp(2j * np.pi * rng.random())
        lhs = np.linalg.det(z * np.eye(k) - K)
        rhs = formula_at(z, k, b)
        rel = max(rel, abs(lhs - rhs) / abs(rhs))
    osz = sorted((len(O) for O in orbits(k, b)), reverse=True)
    print(f"{str((b,k)):>10} {str(osz):<20} {e_match:>14.3e} {rel:>14.3e}")

print()
print("=" * 88)
print("C. exact power identity  K^L = Pi + b^{-L}(I - Pi),  L = ord_k(b)")
print("=" * 88)


def ord_mod(b, k):
    o, x = 1, b % k
    while x != 1:
        x = (x * b) % k
        o += 1
    return o


print(f"{'(b,k)':>10} {'L=ord_k(b)':>10} {'max abs deviation':>18}")
for (b, k) in [(2, 3), (2, 5), (2, 9), (2, 27), (2, 15), (10, 7), (3, 8)]:
    K = build_K(k, b)
    L = ord_mod(b, k)
    Pi = np.ones((k, k)) / k
    KL = np.linalg.matrix_power(K, L)
    dev = np.abs(KL - (Pi + b ** (-float(L)) * (np.eye(k) - Pi))).max()
    print(f"{str((b,k)):>10} {L:>10} {dev:>18.3e}")

print()
print("=" * 88)
print("D. exact TV from state 0:  d_TV(K_0^r, pi) = t(k-t)/(k b^r),  t = b^r mod k")
print("=" * 88)
print(f"{'(b,k)':>10} {'r':>3} {'d_TV (matrix)':>16} {'t(k-t)/(k b^r)':>16}")
for (b, k) in [(2, 7), (2, 27), (10, 7)]:
    K = build_K(k, b)
    row = np.zeros(k)
    row[0] = 1.0
    for r in range(1, 7):
        row = row @ K if r > 1 else (np.eye(k)[0] @ np.linalg.matrix_power(K, 1))
        tv = 0.5 * np.abs(row - 1.0 / k).sum()
        t = pow(b, r, k)
        exact = Fraction(t * (k - t), k * b ** r)
        print(f"{str((b,k)):>10} {r:>3} {tv:>16.10f} {float(exact):>16.10f}"
              + ("   OK" if abs(tv - float(exact)) < 1e-12 else "   MISMATCH"))

print()
print("=" * 88)
print("E. affine variant: constant addend q, chain on {0,...,m} past the bits of q (b=2)")
print("=" * 88)
# Homogeneous extended kernel (positions past the bits of q): state space {0,...,m},
# c' = floor((m*bbit + c)/2). From c<=m-1 this is the pure chain; state m is transient.


def build_K_ext(m):
    Ke = np.zeros((m + 1, m + 1))
    for c in range(m + 1):
        for bbit in (0, 1):
            Ke[c, (m * bbit + c) // 2] += 0.5
    return Ke


for m in [3, 9]:
    Ke = build_K_ext(m)
    ev = np.sort_complex(np.linalg.eigvals(Ke))
    pe = np.sort_complex(np.append(predicted_eigs(m, 2), 0.5))
    print(f"m={m}: extended-chain eigs match  spec(K_m) U {{1/2}}:",
          f"max err {match_error(pe, ev):.3e}")
    # defectiveness of eigenvalue 1/2: rank(Ke - I/2) vs (m+1) - algebraic multiplicity
    alg = int(np.sum(np.abs(ev - 0.5) < 1e-8))
    geo = (m + 1) - np.linalg.matrix_rank(Ke - 0.5 * np.eye(m + 1), tol=1e-10)
    print(f"       eigenvalue 1/2: algebraic mult {alg}, geometric mult {geo}"
          + ("  -> Jordan block (defective)" if geo < alg else "  -> semisimple"))

print()
print("All checks complete.")
